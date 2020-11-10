# Copyright Brown University & Xi'an Jiaotong University
# 
# Licensed under the Apache License, Version 2.0 (the "License");
#
# Author: Peng Zheng
# Email:  zeepean@gmail.com
#

import p4_hlir.hlir
import sys
import copy
import math
from pprint import pprint
import json
from p4_hlir.hlir.dependencies import *
import p4_hlir.graphs.hlir_info as info
import p4_hlir.hlir.p4_imperatives as p4_imperatives

from collections import OrderedDict

import os
from collections import defaultdict

class Dependency:
    CONTROL_FLOW = 0
    REVERSE_READ = 1
    SUCCESSOR = 2
    ACTION = 3
    MATCH = 4

    _types = {REVERSE_READ: "REVERSE_READ",
              SUCCESSOR: "SUCCESSOR",
              ACTION: "ACTION",
              MATCH: "MATCH"}

    @staticmethod
    def get(type_):
        return Dependency._types[type_]



class Node:
    CONDITION = 0
    TABLE = 1
    TABLE_ACTION = 2
    def __init__(self, name, type_, p4_node):
        self.type_ = type_
        self.name = name
        self.edges = {}
        self.p4_node = p4_node
        self.id = -1
        self.SP4_tb_width = -1
        self.SP4_tb_depth = 1

    def add_edge(self, node, edge):
        if node in self.edges:
            print('Trying to add second edge from node %s name %s'
                  ' to node %s name %s'
                  ' existing edge %s type %s'
                  ' new edge %s type %s'
                  '' % (self, self.name,
                        node, node.name,
                        self.edges[node], self.edges[node].type_,
                        edge, edge.type_))
        assert(node not in self.edges)
        self.edges[node] = edge

class Edge:
    def __init__(self, dep = None):
        self.attributes = {}
        if not dep:
            self.type_ = Dependency.CONTROL_FLOW
            self.dep = None
            return

        if isinstance(dep, ReverseReadDep):
            self.type_ = Dependency.REVERSE_READ
        elif isinstance(dep, SuccessorDep):
            self.type_ = Dependency.SUCCESSOR
        elif isinstance(dep, ActionDep):
            self.type_ = Dependency.ACTION
        elif isinstance(dep, MatchDep):
            self.type_ = Dependency.MATCH
        else:
            assert(False)
        self.dep = dep

def munge_condition_str(s):
    """if conditions can be quite long.  In practice the graphs can be a
    bit less unwieldy if conditions containing and/or are split
    across multiple lines.
    """
    return s.replace(' and ', ' and\n').replace(' or ', ' or\n')


class Graph:
    def __init__(self, name):
        self.name = name
        self.nodes = {}
        self.root = None
        ## record map of table name and table id 
        self.SP4_id2name = {}
        self.SP4_name2id = {}
        self.SP4_edges = []
        self.SP4_reuse_id = []
        ## adjacency list
        self.SP4_adj_list = None
        self.SP4_merged_graph_edges = []
        self.SP4_merge_id = []
        self.SP4_table_info = {}
        self.tb_info = {}

        self.tbid2index = {}

    def get_node(self, node_name):
        return self.nodes.get(node_name, None)

    def add_node(self, node):
        self.nodes[node.name] = node

    def set_root(self, node):
        self.root = node

    def SP4_gen_real_graph_node_edges(self, h):
        SP4_nodes_by_name = list(sorted(self.nodes.values(),
                                    key=lambda node: node.name))

        ## record map of table name and table id 
        self.SP4_id2name = {}
        self.SP4_name2id = {}
        self.SP4_edges = []
        # set conditional tables to be represented as boxes
        n_id = 1
        for node in SP4_nodes_by_name:
            node.id = n_id
            if type(h.p4_nodes[node.name]) is p4_hlir.hlir.p4_tables.p4_table:
                if hasattr(h.p4_nodes[node.name], 'size'):
                    node.SP4_tb_depth = h.p4_tables[node.name].size
                node.SP4_tb_width = info.match_field_info(h.p4_tables[node.name])['total_field_width']
            self.SP4_id2name[n_id] = node.name
            self.SP4_name2id[node.name] = n_id
            # print 'id = ', node.id, 'name = ',node.name

            node_label = node.name
            n_id = n_id + 1

        for node in SP4_nodes_by_name:
            node_tos_by_name = sorted(list(node.edges.keys()),
                                      key=lambda node: node.name)
            for node_to in node_tos_by_name:
                self.SP4_edges.append((node.id, node_to.id))
                # print 'edge:', node.id, '->', node_to.id, node.name, '-->', node_to.name
                edge = node.edges[node_to]
                # print '------'
                # for each in list(node.edges.keys()):
                #     print each.name

    def SP4_get_table_info(self, h):
        self.SP4_table_info['P4_MATCH_LPM'] = []

        for each in self.SP4_name2id:
            if type(h.p4_nodes[each]) is p4_hlir.hlir.p4_tables.p4_conditional_node:                                     
                continue

            if len(h.p4_tables[each].match_fields) < 1:
                if 'no_match' in self.SP4_table_info:                
                    self.SP4_table_info['no_match'].append(each)
                else:
                    self.SP4_table_info['no_match'] = []
                    self.SP4_table_info['no_match'].append(each)
                continue

            match_type = h.p4_tables[each].match_fields[0][1]
            depth = self.nodes[each].SP4_tb_depth
            width = self.nodes[each].SP4_tb_width

            if str(match_type) in self.SP4_table_info:                
                self.SP4_table_info[str(match_type)].append((each, depth, width))
            else:
                self.SP4_table_info[str(match_type)] = []
                self.SP4_table_info[str(match_type)].append((each, depth, width))
            


    def SP4_get_table_info_summary(self, h):

        self.tb_info = {key: {} for key in self.SP4_table_info}
        for key in self.SP4_table_info:
            self.tb_info[key]['table_num'] = 0
            self.tb_info[key]['total_entries'] = 0
            self.tb_info[key]['total_resouce'] = 0

        for each in self.SP4_table_info:
            print each
            tb_num = 0
            total_depth = 0
            total_resouce = 0

            if each == 'no_match':
                for tb in self.SP4_table_info[each]:
                    # print tb
                    tb_num = tb_num + 1
                self.tb_info[each]['table_num'] = tb_num

            else:    
                for tbname, d, w in self.SP4_table_info[each]:
                    tb_num = tb_num + 1
                    total_depth = total_depth + d
                    total_resouce = total_resouce + d*w
                self.tb_info[each]['table_num'] = tb_num
                self.tb_info[each]['total_entries'] = total_depth
                self.tb_info[each]['total_resouce'] = total_resouce
        print '    Table info summary:', self.tb_info
        for key in self.SP4_table_info:
            print '    ', key, self.tb_info[key]['table_num'], \
                  self.tb_info[key]['total_entries'],\
                  self.tb_info[key]['total_resouce']



    def SP4_search_reuse_node(self, s_node, h_r, g_r):

        if type(s_node) is p4_hlir.hlir.p4_tables.p4_conditional_node:
            return -1
        
        if type(s_node) is p4_hlir.hlir.p4_tables.p4_table:
            # TODO: FIX the bug
            if len(s_node.match_fields) < 1:
                return -1
            s_match_type = s_node.match_fields[0][1]
            s_match_width = self.nodes[s_node.name].SP4_tb_width

            # print '   SP4-merge-001 snode,stype,width = ',s_node.name, s_match_type, s_match_width

            for r_node in g_r.nodes:
                if g_r.nodes[r_node].type_ == 0:
                    continue

                # TODO: FIX the bug
                # print '::zp::',type(h_r.p4_tables[r_node].match_fields[0])
                if len(h_r.p4_tables[r_node].match_fields) < 1:
                    # print '::bug-001::<2'
                    continue
                
                r_match_type = h_r.p4_tables[r_node].match_fields[0][1]

                if r_match_type != s_match_type:
                    continue

                r_match_width = g_r.nodes[r_node].SP4_tb_width
                if r_match_width != s_match_width:
                    continue

                reuse_id = g_r.SP4_name2id[r_node]
                if reuse_id in g_r.SP4_reuse_id:
                    continue
                print 'INFO|MERGE|SP4_search_reuse_node: snode,stype,width = ',s_node.name, s_match_type, s_match_width
                print 'INFO|MERGE|SP4_search_reuse_node: rnode,rtype,width = ',r_node, r_match_type, r_match_width
                print 'INFO|MERGE|SP4_search_reuse_node: reuse_id', reuse_id
                return reuse_id
                
        return -1

    def SP4_reduce_reuse_tables(self,h):
        '''reduce the resued tables from the current graph, calculate resource purpose.
        '''
        
        for each_id in self.SP4_merge_id:
            each = self.SP4_id2name[each_id]

            match_type = h.p4_tables[each].match_fields[0][1]
            depth = self.nodes[each].SP4_tb_depth
            width = self.nodes[each].SP4_tb_width

            self.tb_info[str(match_type)]['table_num'] = self.tb_info[str(match_type)]['table_num'] - 1
            self.tb_info[str(match_type)]['total_entries'] = self.tb_info[str(match_type)]['total_entries'] - depth
            self.tb_info[str(match_type)]['total_resouce'] = self.tb_info[str(match_type)]['total_resouce'] - depth*width

        DBG_print_table_summary = 0
        if DBG_print_table_summary:
            print '    AFTER MERGE::Table info summary:', self.tb_info
            print '    ', self.tb_info['P4_MATCH_TERNARY']['table_num'], \
                        self.tb_info['P4_MATCH_TERNARY']['total_entries'], \
                        self.tb_info['P4_MATCH_TERNARY']['total_resouce'], \
                        self.tb_info['P4_MATCH_EXACT']['table_num'], \
                        self.tb_info['P4_MATCH_EXACT']['total_entries'], \
                        self.tb_info['P4_MATCH_EXACT']['total_resouce'], \
                        self.tb_info['P4_MATCH_RANGE']['table_num'], \
                        self.tb_info['P4_MATCH_RANGE']['total_entries'], \
                        self.tb_info['P4_MATCH_RANGE']['total_resouce'], \
                        self.tb_info['P4_MATCH_VALID']['table_num'], \
                        self.tb_info['P4_MATCH_VALID']['total_entries'], \
                        self.tb_info['P4_MATCH_VALID']['total_resouce'], \
                        self.tb_info['P4_MATCH_LPM']['table_num'], \
                        self.tb_info['P4_MATCH_LPM']['total_entries'], \
                        self.tb_info['P4_MATCH_LPM']['total_resouce'], \
                        self.tb_info['no_match']['table_num']

    def SP4_gen_shadow_graph_node_edges(self, h_s, g_r, h_r):
        SP4_nodes_by_name = list(sorted(self.nodes.values(),
                                    key=lambda node: node.name))

        ## record map of table name and table id 
        self.SP4_id2name = {}
        self.SP4_name2id = {}
        self.SP4_edges = []

        # set conditional tables to be represented as boxes
        n_id = 1000
        for node in SP4_nodes_by_name:
            if type(h_s.p4_nodes[node.name]) is p4_hlir.hlir.p4_tables.p4_table:
                if hasattr(h_s.p4_nodes[node.name], 'size'):
                    node.SP4_tb_depth = h_s.p4_tables[node.name].size
                node.SP4_tb_width = info.match_field_info(h_s.p4_tables[node.name])['total_field_width']

            reuse_id = self.SP4_search_reuse_node(h_s.p4_nodes[node.name], h_r, g_r)
            # reuse_id = 0# g_r.SP4_name2id[reuse_node]
            if reuse_id > -1:
                node.id = reuse_id
                self.SP4_id2name[reuse_id] = node.name
                self.SP4_name2id[node.name] = reuse_id
                g_r.SP4_reuse_id.append(reuse_id)
            else:
                node.id = n_id
                self.SP4_id2name[n_id] = node.name
                self.SP4_name2id[node.name] = n_id
                
                node_label = node.name
                n_id = n_id + 1


        for node in SP4_nodes_by_name:
            node_tos_by_name = sorted(list(node.edges.keys()),
                                      key=lambda node: node.name)
            for node_to in node_tos_by_name:
                self.SP4_edges.append((node.id, node_to.id))
                # print 'edge:', node.id, '->', node_to.id, node.name, '-->', node_to.name
                edge = node.edges[node_to]
                # print '------'
                # for each in list(node.edges.keys()):
                #     print each.name

    def SP4_init_adj_list(self):
        # dbg info
        tmp_dbg = 0
        if tmp_dbg:                
            print ' sp4 merge: init adj list:'
            print self.SP4_id2name

        ## construct adj list
        self.SP4_adj_list = {key: [] for key in self.SP4_id2name}
        for u,v in self.SP4_edges:
            self.SP4_adj_list[u].append(v)

    def SP4_isReachable(self, s, d):
        # for test
        if d in self.SP4_adj_list[s]:
            return True
        else:
            return False

        # Mark all the vertices as not visited
        visited = {}
        for v in self.SP4_id2name:
            visited[v] = False
  
        # Create a queue for BFS
        queue=[]
        # Mark the source node as visited and enqueue it
        queue.append(s)
        visited[s] = True
  
        while queue:
            #Dequeue a vertex from queue 
            n = queue.pop(0)
             
            # If this adjacent node is the destination node,
            # then return true
            if n == d:
                return True
 
            #  Else, continue to do BFS
            for i in self.SP4_adj_list[n]:
                if visited[i] == False:
                    queue.append(i)
                    visited[i] = True
        # If BFS is complete without visited d
        return False

    def SP4_get_merged_graph(self, g_2):
        
        for u in self.SP4_reuse_id:
        
            for v in self.SP4_reuse_id:

                if v == u:
                    continue

                if self.SP4_isReachable(u, v) and g_2.SP4_isReachable(v, u):
                    if (u,v) in self.SP4_merged_graph_edges:
                        continue
                    self.SP4_merged_graph_edges.append((u,v))
                    
    def SP4_write_graph_to_file(self, gen_dir, filebase, g_2):

        filename_out = os.path.join(gen_dir, filebase + "_table_graph.csv")
        v_num = len(self.SP4_reuse_id)
        e_num = len(self.SP4_merged_graph_edges)

        for i in xrange(v_num):
            self.tbid2index[self.SP4_reuse_id[i]] = i + 1


        with open(filename_out, "w") as out:
            
            out.write('p edge '+str(v_num)+' '+str(e_num)+"\n")

            for v in self.SP4_reuse_id:
                name1 = self.SP4_id2name[v]
                depth1 = self.nodes[name1].SP4_tb_depth
                
                name2 = g_2.SP4_id2name[v]
                depth2 = g_2.nodes[name2].SP4_tb_depth

                w = max(depth1, depth2)
                ## TODO: fix it
                if w < 0:
                    w = 1
                out.write('n '+str(self.tbid2index[v])+ " " + str(w) + "\n")

            for u,v in self.SP4_merged_graph_edges:
                out.write('e '+str(self.tbid2index[u]) + " " + str(self.tbid2index[v]) + "\n")


    def topo_sorting(self):
        if not self.root: return False

        # slightly annoying because the graph is directed, we use a topological
        # sorting algo
        # see http://en.wikipedia.org/wiki/Topological_sorting#Algorithms
        # (second algo)
        def visit(cur, sorted_list):
            if cur.mark == 1:
                return False
            if cur.mark != 2:
                cur.mark = 1
                for node_to, edge in cur.edges.items():
                    if not visit(node_to, sorted_list):
                        return False
                cur.mark = 2
                sorted_list.insert(0, cur)
            return True

        has_cycle = False
        sorted_list = []
        for n in self.nodes.values():
            # 0 is unmarked, 1 is temp, 2 is permanent
            n.mark = 0
        for n in self.nodes.values():
            if n.mark == 0:
                if not visit(n, sorted_list):
                    has_cycle = True
                    break
        for n in self.nodes.values():
            del n.mark

        return has_cycle, sorted_list

    def critical_path(self, direction, show_conds = False,
        debug = False,
                      debug_key_result_widths = False,
                      crit_path_edge_attr_name = None,
                      almost_crit_path_edge_attr_name = None,
                      almost_crit_path_delta = 20):

        # If direction == 'forward', calculate the longest paths from
        # the beginning (nodes with no in-edges) to the end (nodes
        # with on out-edges).  This gives the earliest time that each
        # node can be scheduled, subject to the constraints specified
        # by the edges.

        # If direction == 'backward', calculate the longest paths from
        # the end back to the beginning, following edges in the
        # reverse direction.  If we take those path lengths x and
        # replace them with (max_path_length - x), that should give
        # the latest time that each node can be scheduled, subject to
        # the constraints specified by the edges.

        has_cycle, forward_sorted_list = self.topo_sorting()
        assert(not has_cycle)
        dir_edges = {}
        
        if direction == 'forward':
            sorted_list = copy.copy(forward_sorted_list)
            for node_from in forward_sorted_list:
                dir_edges[node_from] = node_from.edges
        else:
            # Calculate set of edges into each node, from the forward
            # edges.
            sorted_list = copy.copy(forward_sorted_list)
            sorted_list.reverse()
            for node_to in sorted_list:
                dir_edges[node_to] = {}
            # In this for loop 'node_from' and 'node_to' are the
            # direction of the edge in the original dependencies.  In
            # dir_edges we are intentionally reversing that direction.
            for node_from in sorted_list:
                for node_to, edge in node_from.edges.items():
                    dir_edges[node_to][node_from] = edge

        max_path = {}
        crit_path_edges_into = defaultdict(dict)
        for table in sorted_list:
            if table not in max_path:
                max_path[table] = 0
            for node_to, edge in dir_edges[table].items():
                if edge.type_ > 0 and 'min_latency' in edge.attributes:
                    this_path_len = (max_path[table] +
                                     edge.attributes['min_latency'])
                    table_on_a_crit_path = False
                    if node_to in max_path:
                        if this_path_len > max_path[node_to]:
                            max_path[node_to] = this_path_len
                            table_on_a_crit_path = True
                            # Found new path longer than any
                            # previously known, so clear out the
                            # critical path edges remembered so far,
                            # since they are definitely not any more.
                            crit_path_edges_into[node_to] = {}
                        elif this_path_len == max_path[node_to]:
                            table_on_a_crit_path = True
                    else:
                        max_path[node_to] = this_path_len
                        table_on_a_crit_path = True
                    if table_on_a_crit_path:
                        # Update list of tables/edges into node_to
                        # that are on a critical path.
                        crit_path_edges_into[node_to][table] = edge
                else:
                    assert(edge.type_ <= 0)
                    assert('min_latency' not in edge.attributes)
                   # print('dbg critical_path found an edge with no min_latency'
                   #       ' attributes: from %s to %s type_ %s'
                   #       '' % (table.name, node_to.name, edge.type_))

        max_path_length = 0
        for table in sorted_list:
            if max_path[table] > max_path_length:
                max_path_length = max_path[table]

        if direction == 'backward':
            # Replace maximum paths x with (max_path_length - x)
            for table in sorted_list:
                max_path[table] = (max_path_length - max_path[table])

        if debug:
            print('')
            print('')
            print('direction %s' % (direction))
            print('')
        # Including table names in sort keys helps make the order
        # repeatable across multiple runs.
        tables_by_max_path = sorted(sorted_list,
                                    key=lambda t: [max_path[t], t.name])
        for table in tables_by_max_path:
            if table in crit_path_edges_into:
                # Again, this sorting makes the output repeatable
                # across runs.
                crit_path_edges_by_table_name = sorted(
                    crit_path_edges_into[table].keys(),
                    key=lambda x: x.name)
                for from_table in crit_path_edges_by_table_name:
                    edge = crit_path_edges_into[table][from_table]
                    dname = Dependency._types.get(edge.type_, 'unknown')
                    x = max_path[from_table]
                    y = edge.attributes['min_latency']
                    z = max_path[table]
                    if direction == 'forward':
                        print_op = '+'
                    if direction == 'backward':
                        print_op = '-'
                        y = -y
                    if x + y != z:
                        print('dbg assert direction %s'
                              ' from_table.name %s max_path %s'
                              ' table.name %s max_path %s'
                              ' edge.type_ %s dname %s min_latency %s'
                              '' % (direction,
                                    from_table.name, x,
                                    table.name, z,
                                    edge.type_, dname, y))
                    assert (x + y == z)
                    if debug:
                        print("%-35s %-3s  %3d%s%2d = %3d  %s"
                              "" % (from_table.name, dname[0:3],
                                    max_path[from_table],
                                    print_op,
                                    edge.attributes['min_latency'],
                                    max_path[table],
                                    table.name))
                    if crit_path_edge_attr_name is not None:
                        edge.attributes[crit_path_edge_attr_name] = True
            else:
                if direction == 'forward':
                    assert (max_path[table] == 0)
                elif direction == 'backward':
                    assert (max_path[table] == max_path_length)
                print("%-35s %-3s  %8s %3d  %s"
                      "" % ("(no predecessor)", "-", "",
                            max_path[table], table.name))

        if almost_crit_path_edge_attr_name is not None:
            for table in sorted_list:
                for node_to, edge in table.edges.items():
                    y = edge.attributes.get('min_latency', None)
                    if y is None:
                        continue
                    x = max_path[from_table]
                    z = max_path[table]
                    if (x + y < z) and (x + y > z - almost_crit_path_delta):
                        edge.attributes[almost_crit_path_edge_attr_name] = True

        return max_path_length, max_path

        
    def count_min_stages(self, show_conds = False,
        #
                         debug = False,
                         debug_key_result_widths = False):
        has_cycle, sorted_list = self.topo_sorting()
        assert(not has_cycle)
        nb_stages = 0
        stage_list = []
        stage_dependencies_list = []
        stage_dependencies_table_list = []
        if debug:
            print('------------------------------')
            print('Debug count_min_stages')
            print("from table/condition       dependency type stage to table/condition")
            print("-------------------------- --------------- ----- ------------------")
        for table in sorted_list:
            d_type_ = 0
            d_table_from_ = '(none)'
            i = nb_stages - 1
            while i >= 0:
                stage = stage_list[i]
                stage_dependencies = stage_dependencies_list[i]
                if table in stage_dependencies:
                    d_type_ = stage_dependencies[table]
                    d_table_from_ = stage_dependencies_table_list[i][table].name
                    assert(d_type_ > 0)
                    break
                else:
                    i -= 1
            orig_i = i
            if d_type_ == 0:
                i += 1
            elif d_type_ >= Dependency.ACTION:
                i += 1
            if debug:
                if d_type_ in Dependency._types:
                    dname = Dependency._types[d_type_]
                else:
                    dname = 'unknown'
                print("%-26s %d %-12s  %2d+%d  %s"
                      "" % (d_table_from_, d_type_, dname,
                            orig_i, i - orig_i, table.name))
            if i == nb_stages:
                stage_list.append(set())
                stage_dependencies_list.append(defaultdict(int))
                stage_dependencies_table_list.append({})
                nb_stages += 1
                
            stage = stage_list[i]
            stage_dependencies = stage_dependencies_list[i]
            stage.add(table)
            for node_to, edge in table.edges.items():
                type_ = edge.type_
                if type_ > 0 and type_ > stage_dependencies[node_to]:
                    stage_dependencies[node_to] = type_                
                    stage_dependencies_table_list[i][node_to] = table
        if debug:
            print('------------------------------')
        if debug_key_result_widths:
            print('------------------------------')
            print('Debug table search key and table result widths')
            print('------------------------------')
            for stage in stage_list:
                for table in sorted(stage, key=lambda t: t.name):
                    if not show_conds and table.type_ is Node.CONDITION:
                        continue
                    pprint.pprint(info.match_field_info(table.p4_node))
                    pprint.pprint(info.result_info(table.p4_node))
            print('------------------------------')
        
        lines = []
        lines.append("      search")
        lines.append("      key    result")
        lines.append("stage width  width  table/condition name")
        lines.append("----- ------ ------ --------------------")
        stage_num = 0
        total_key_width = 0
        total_result_width = 0
        for stage in stage_list:
            stage_num += 1
            stage_key_width = 0
            stage_result_width = 0
            lines2 = []
            # Sorting here is simply to try to get a more consistent
            # output from one run of the program to the next.
            for table in sorted(stage, key=lambda t: t.name):
                if not show_conds and table.type_ is Node.CONDITION:
                    continue
                key_width = info.match_field_info(table.p4_node)['total_field_width']
                result_width = info.result_info(table.p4_node)['result_width']
                lines2.append("%5d %6d %6d %s" % (stage_num, key_width,
                                                  result_width, table.name))
                stage_key_width += key_width
                stage_result_width += result_width
            lines.append("--- stage %d of %d total search key width %d"
                         " result width %d"
                         "" % (stage_num, nb_stages, stage_key_width,
                               stage_result_width))
            lines += lines2
            total_key_width += stage_key_width
            total_result_width += stage_result_width
        for line in lines:
            print(line)
        print("For all stages, total search key width %d result width %d"
              "" % (total_key_width, total_result_width))

        max_path = {}
        path_length = 0
        for stage in stage_list:
            for table in stage:
                max_path[table] = path_length
            path_length += 1
        return nb_stages, max_path


    def generate_dot(self, out = sys.stdout,
        #
                     show_control_flow = True,
                     show_condition_str = True,
                     show_fields = True,
                     earliest_time = None,
                     latest_time = None,
                     show_min_max_scheduled_times = False,
                     show_only_critical_dependencies = False,
                     forward_crit_path_edge_attr_name = None,
                     backward_crit_path_edge_attr_name = None):
        styles = {Dependency.CONTROL_FLOW: "style=dotted",
                  Dependency.REVERSE_READ: "color=orange",
                  Dependency.SUCCESSOR: "color=green",
                  Dependency.ACTION: "color=blue",
                  Dependency.MATCH: "color=red"}
        on_crit_path_style = "style=bold"
        off_crit_path_style = "style=dashed"
        out.write("digraph " + self.name + " {\n")

        # The uses of the 'sorted' function below are not necessary
        # for correct behavior, but are done to try to make the
        # contents of the dot output file in a more consistent order
        # from one run of this program to the next.  By default,
        # Python dicts and sets can have their iteration order change
        # from one run of a program to the next because the hash
        # function changes from one run to the next.
        nodes_by_name = list(sorted(self.nodes.values(),
                                    key=lambda node: node.name))

        # set conditional tables to be represented as boxes
        for node in nodes_by_name:
            node_attrs = ""
            node_label = node.name
            if node.type_ == Node.CONDITION:
                node_attrs = " shape=box"
                if show_condition_str:
                    node_label += (
                        "\\n" +
                        munge_condition_str(str(node.p4_node.condition)))
            if show_min_max_scheduled_times:
                early = "-"
                if earliest_time and node in earliest_time:
                    early = "%s" % (earliest_time[node])
                late = "-"
                if latest_time and node in latest_time:
                    late = "%s" % (latest_time[node])
                node_label += "\\n" + early + "," + late
            node_attrs += " label=\"" + node_label + "\""
            if show_min_max_scheduled_times:
                if early == late and early != "-":
                    node_attrs += " style=bold"
                else:
                    node_attrs += " style=dashed"
            out.write(node.name + " [" + node_attrs + "];\n")

        for node in nodes_by_name:
            node_tos_by_name = sorted(list(node.edges.keys()),
                                      key=lambda node: node.name)
            for node_to in node_tos_by_name:
                edge = node.edges[node_to]
                # print '------'
                # for each in list(node.edges.keys()):
                #     print each.name
                # pprint.pprint(vars(edge))
                if not show_control_flow and edge.type_ == Dependency.CONTROL_FLOW:
                    continue
                if show_only_critical_dependencies:
                    fwd = edge.attributes.get(forward_crit_path_edge_attr_name,
                                              False)
                    bkwd = edge.attributes.get(backward_crit_path_edge_attr_name,
                                               False)
                    if not (fwd or bkwd):
                        continue
                
                edge_label = ""
                edge_attrs = ""
                if edge.type_ != Dependency.CONTROL_FLOW and show_fields:
                    dep_fields = []
                    # edge.dep can be None with my recent changes to
                    # split tables into a separate match and action node,
                    # because the edge between them has edge.dep of None.
                    if edge.dep is not None:
                        for field in edge.dep.fields:
                            dep_fields.append(str(field))
                    dep_fields = sorted(dep_fields)
                    edge_label = ",\n".join(dep_fields)
                    
                if edge.type_ == Dependency.SUCCESSOR:
                    if isinstance(edge.dep.value, bool):
                        if edge_label != "":
                            edge_label += "\n"
                        if edge.dep.value == False:
                            edge_label += "False"
                            edge_attrs += " arrowhead = diamond"
                        else:
                            edge_label += "True"
                            #edge_attrs += " arrowhead = dot"
                    elif isinstance(edge.dep.value, p4_imperatives.p4_action):
                        edge_label += edge.dep.value.name
                    elif isinstance(edge.dep.value, tuple):
                        tmp_names = map(lambda v: v.name, edge.dep.value)
                        edge_label += ',\n'.join(tmp_names)
                    else:
                        print("dbg successor type(edge.dep.value) %s"
                              " edge.dep.value=%s"
                              "" % (type(edge.dep.value), edge.dep.value))
                        assert False
                if show_only_critical_dependencies:
                    if fwd and bkwd:
                        edge_attrs += " " + on_crit_path_style
                    elif fwd:
                       # if edge_label != "":
                       #     edge_label = "\n" + edge_label
                       # edge_label = "f" + edge_label
                        pass
                    elif bkwd:
                       # if edge_label != "":
                       #     edge_label = "\n" + edge_label
                       # edge_label = "b" + edge_label
                        pass
                    else:
                        edge_attrs += " " + off_crit_path_style
                if edge_label != "":
                    edge_attrs = ("label=\"" + edge_label + "\"" +
                                  " decorate=true " + edge_attrs)
                out.write(node.name + " -> " + node_to.name +\
                          " [" + styles[edge.type_] + \
                          " " + edge_attrs + "]" + ";\n")
        out.write("}\n")


def printOrderedDict(obj):
    print 'DBG|INFO|OD:', obj.keys()
    cnt = 0
    for a, b in obj.items():
        print '     type:', type(b)
        print '      key:', a
        print '    value:', pprint(vars(b))
        cnt = cnt + 1
    print '    count = ', cnt

def print_table_names(p4_tables):
    print p4_tables.keys()

def merge_headers(h_mg, h_r, h_meta):
    print 'LOG|MERGE|p4_headers'
    #h_mg.p4_headers.update(h_r.p4_headers)
    #h_mg.p4_headers.update(h_meta.p4_headers)

def merge_header_instancesCopy(h_mg, h_r, h_meta):
    print 'LOG|MERGE|p4_header instances'
    h_mg.p4_header_instances.update(h_r.p4_header_instances)
    h_mg.p4_header_instances.update(h_meta.p4_header_instances)



def merge_header_instances(h_mg, h_r, h_meta):
    added_from_r = []
    counter = 0
    header_type_added = []
    print 'LOG|MERGE|p4_header instances'
    # For each header in r and mg
    for header_nameR, header_instR in h_r.p4_header_instances.items():
	eqType = ''
	header = ''
	if  not header_instR.metadata:
		for header_nameMG, header_instMG in h_mg.p4_header_instances.items():
			if header_instMG in added_from_r:
				continue
			if header_instMG.metadata:
				continue
			#if this is second merge, dont find equivalence with virtual flag
			if header_nameMG == 'upvn':
				continue
			#also ignore upvn metadata, may delete later if not needed
			if header_nameMG == 'upvn_metadata':
				continue
			# See if headerMG is in StrongEquivalenceList or SimpleEquivalenceList
			# if it is, match with next header of MG
			if header_nameMG in h_r.lStrongEq:
				continue
			if header_nameMG in h_r.lSimpleEq.values():
				continue
			
			# Determine equivalence type
			eqType = check_equivalent_headers(header_instMG, header_instR)
			if eqType == 'Strong Equivalence' or eqType == 'Simple Equivalence':
				header = header_nameMG
	    			break
			if eqType == 'Weak Equivalence':
				header = header_nameMG

		if eqType == 'Weak Equivalence':
			print 'WARNING!! HEADERS MAY BE EQUIVALENT: ', header_nameR, header		 
			#check_header_and_add(h_mg, h_r, header_instR, header)
			h_r.lWeakEq[header_nameR] = header
			added_from_r.append(header_instR)
			if header_instR.header_type not in header_type_added:
				header_type_added.append(header_instR.header_type)
		elif eqType == 'No Equivalence' and header != '':
			print 'WARNING!! HEADERS MAY BE EQUIVALENT: ', header_nameR, header	
	 		h_r.lWeakEq[header_nameR] = header
			#check_header_and_add(h_mg, h_r, header_instR, header)
			added_from_r.append(header_instR)
			if header_instR.header_type not in header_type_added:
				header_type_added.append(header_instR.header_type)
		elif eqType == 'Strong Equivalence':
			h_r.lStrongEq[header_nameR] = header
			added_from_r.append(header_instR)
			if header_instR.header_type not in header_type_added:
				header_type_added.append(header_instR.header_type)
		elif eqType == 'Simple Equivalence':
			h_r.lSimpleEq[header_nameR] = header
			added_from_r.append(header_instR)
			if header_instR.header_type not in header_type_added:
				header_type_added.append(header_instR.header_type)
		else:
			check_header_and_add(h_mg, h_r, header_instR, header)
			added_from_r.append(header_instR)
			if header_instR.header_type.name not in h_mg.p4_headers:
				h_mg.p4_headers[header_instR.header_type.name] = header_instR.header_type
			else:
				if header_instR.header_type not in header_type_added:
					#rename header type and add
					header_instR.header_type.name = header_instR.name + '_t'
					h_mg.p4_headers[header_instR.header_type.name] = header_instR.header_type
					header_type_added.append(header_instR.header_type)
			
	#if metadata
	else:
		counter = counter + 1
		if header_nameR == 'standard_metadata':
			continue
		for header_nameMG, header_instMG in h_mg.p4_header_instances.items():
			if header_instMG in added_from_r:
				continue
			if not header_instMG.metadata:
				continue	
			if header_nameMG == 'standard_metadata':
				continue
			eqType = check_equivalent_headers(header_instMG, header_instR)
			if eqType == 'Strong Equivalence' or eqType == 'Simple Equivalence':
				header = header_nameMG
	    			break
			if eqType == 'Weak Equivalence':
				header = header_nameMG
				#break
		#if it is weak equivalence
		if eqType == 'Weak Equivalence':
			print 'WARNING!! HEADERS MAY BE EQUIVALENT: ', header_nameR, header
			h_r.lWeakEq[header_nameR] = header
			added_from_r.append(header_instR)
			if header_instR.header_type not in header_type_added:
				header_type_added.append(header_instR.header_type)
		#if some weak equivalence was found in the process, but the final result was no equivalence
		elif eqType == 'No Equivalence' and header != '':
			print 'WARNING!! HEADERS MAY BE EQUIVALENT: ', header_nameR, header	
	 		h_r.lWeakEq[header_nameR] = header
			added_from_r.append(header_instR)
			if header_instR.header_type not in header_type_added:
				header_type_added.append(header_instR.header_type)
		elif eqType == 'Strong Equivalence':
			h_r.lStrongEq[header_nameR] = header
			added_from_r.append(header_instR)
			if header_instR.header_type not in header_type_added:
				header_type_added.append(header_instR.header_type)
		elif eqType == 'Simple Equivalence':
			h_r.lSimpleEq[header_nameR] = header
			added_from_r.append(header_instR)
			if header_instR.header_type not in header_type_added:
				header_type_added.append(header_instR.header_type)
		else:
			check_header_and_add(h_mg, h_r, header_instR, header)
			added_from_r.append(header_instR)
			if header_instR.header_type.name not in h_mg.p4_headers:
				h_mg.p4_headers[header_instR.header_type.name] = header_instR.header_type
			else:
				if header_instR.header_type not in header_type_added:
					#rename header type and add
					header_instR.header_type.name = header_instR.name + '_t'
					h_mg.p4_headers[header_instR.header_type.name] = header_instR.header_type
					header_type_added.append(header_instR.header_type)
    #h_mg.p4_header_instances.update(h_meta.p4_header_instances)
    h_mg.p4_header_instances['upvn'] = h_meta.p4_header_instances['upvn']
    h_mg.p4_headers['upvn_t'] = h_meta.p4_headers['upvn_t']
    
    h_mg.p4_header_instances['upvn_metadata'] = h_meta.p4_header_instances['upvn_metadata']
    h_mg.p4_headers['upvn_metadata_t'] = h_meta.p4_headers['upvn_metadata_t']
    #h_mg.p4_header_instances['shadow_metadata'] = h_meta.p4_header_instances['shadow_metadata']
	

def check_header_and_add(h_mg, h_r, header_instR, header):
	#If header name already exists, rename to add
	if header_instR.name in h_mg.p4_header_instances:
		newName = header_instR.name + 'NEW'
		header_instR.name = newName
		header_instR.base_name = newName
		if header != '':
			h_r.lWeakEq[newName] = header 
		h_mg.p4_header_instances[newName] = header_instR
	else:
		h_mg.p4_header_instances[header_instR.name] = header_instR

	

def check_equivalent_headers(header_instMG, header_instR):
	sameWidthFields = True
	sameNameFields = True
	#if same number of fields, check if they are simple/strong equivalent, or weakly equivalent
	if len(header_instR.fields) == len(header_instMG.fields):
		if header_instMG.name != header_instR.name:
			sameNameFields = False
		mg_length = 0
		r_length = 0
		for i in xrange(len(header_instMG.fields)):
			mg_length += header_instMG.fields[i].width
			r_length += header_instR.fields[i].width
			if header_instMG.fields[i].width != header_instR.fields[i].width:
				sameWidthFields = False
			if header_instMG.fields[i].name != header_instR.fields[i].name:
				sameNameFields = False
			
		#if at the end of the cycle, sameWidthFields is still true, 
		#then headers are either strong or simply equivalent
		if sameWidthFields:
			if sameNameFields:
				return 'Strong Equivalence'
			else:
				return 'Simple Equivalence'
		#if individual field width is different but total width is the same, headers are weakly equivalent
		elif mg_length == r_length:
			return 'Weak Equivalence'
	
	#if length is different, headers can be weakly equivalent at most
	else:
		mg_length = 0
		r_length = 0
		for i in xrange(len(header_instMG.fields)):
			mg_length += header_instMG.fields[i].width
			

		for i in xrange(len(header_instR.fields)):
			r_length += header_instR.fields[i].width

		if mg_length == r_length:
			return  'Weak Equivalence'
	return 'No Equivalence'
		 


# for both AB and Diff merging
def merge_header_actions(h_mg, h_r, h_meta):
    ## TODO-low: reduce the duplicated actions 
    print 'LOG|MERGE|actions'
    h_mg.p4_actions.update(h_r.p4_actions)
    h_mg.p4_actions.update(h_meta.p4_actions)

def AB_merge_p4_tables(h_mg, h_r, h_meta):
    print 'LOG|MERGE|8 p4 tables:'
    print 'LOG|MERGE|  Shadow  tables:', h_mg.p4_tables.keys()
    print 'LOG|MERGE|  Product tables:', h_r.p4_tables.keys()

    h_mg.p4_tables.update(h_r.p4_tables)
    h_mg.p4_tables.update(h_meta.p4_tables)
    print 'LOG|MERGE|  Merged  tables', h_mg.p4_tables.keys()

    assert(len(h_mg.p4_ingress_ptr) == 1)
    ingress_ptr_s = h_mg.p4_ingress_ptr.keys()[0]
    ingress_ptr_r = h_r.p4_ingress_ptr.keys()[0]
    print '    DBG in-/egress_ptr_r:', ingress_ptr_r.name, h_r.p4_egress_ptr
    print '    DBG in-/egress_ptr_s:', ingress_ptr_s.name, h_mg.p4_egress_ptr
    # pprint( vars( h_meta.p4_tables['shadow_traffic_control'] ))
    for e in h_mg.p4_tables["shadow_traffic_control"].next_:
        if e.name == 'SP4_add_upvn' or e.name == 'goto_testing_pipe':
            h_mg.p4_tables["shadow_traffic_control"].next_[e] = h_mg.p4_nodes[ingress_ptr_s.name]    
        if e.name == 'SP4_remove_upvn' or e.name == 'goto_production_pipe':
            h_mg.p4_tables["shadow_traffic_control"].next_[e] = h_mg.p4_nodes[ingress_ptr_r.name]
        print 'LOG|MERGE|add STC nexts:', h_mg.p4_tables["shadow_traffic_control"].next_[e]
        pass

    # TODO: remove the duplicate nodes in set
    # key = h_mg.p4_ingress_ptr.keys()[0]
    ingress_ptr_key   = h_mg.p4_tables['shadow_traffic_control']
    ingress_ptr_value = h_mg.p4_ingress_ptr[ingress_ptr_s].union(h_r.p4_ingress_ptr[ingress_ptr_r])
    h_mg.p4_ingress_ptr.clear()
    h_mg.p4_ingress_ptr[ingress_ptr_key] = ingress_ptr_value

    # SECTION ADDED BY DUARTE SEQUEIRA
    # MERGE EGRESS STAGE STARTING FROM META CONDITIONAL NODE

    egress_ptr_s = h_mg.p4_egress_ptr 
    h_mg.p4_egress_ptr = h_mg.p4_conditional_nodes["_condition_0"]
    h_mg.p4_egress_ptr.next_[True] = egress_ptr_s
    h_mg.p4_egress_ptr.next_[False] = h_r.p4_egress_ptr
    
    return 

def set_parser_default_table_STC(p4_parse_states, h_mg):

    for _, parser_state in p4_parse_states.items():
        print 'DBG|SP4_merge|new parser names:', parser_state.name
        for branch_case, next_state in parser_state.branch_to.items():
            
            if branch_case == p4_hlir.hlir.p4_parser.P4_DEFAULT:
                if isinstance(next_state, p4_hlir.hlir.p4_tables.p4_conditional_node) or \
                   isinstance(next_state, p4_hlir.hlir.p4_tables.p4_table):
                    # TODO: check it
                    new_branch = "P4_DEFAULT", h_mg.p4_tables['shadow_traffic_control']
                    parser_state.branch_to[branch_case] = h_mg.p4_tables['shadow_traffic_control']
            else:
                # print 'DBG|SP4_Merge|Parser: type branch_case', type(branch_case), branch_case
                if isinstance(next_state, p4_hlir.hlir.p4_tables.p4_conditional_node) or \
                   isinstance(next_state, p4_hlir.hlir.p4_tables.p4_table):
			parser_state.branch_to[branch_case] = h_mg.p4_tables['shadow_traffic_control']


def rename_parser_states(p4_parse_states, h_mg):
    '''
    Add preffix 'shadow_' to the name of all parser states;
    also update the default branch to table to 'shadow_traffic_control'
    '''
    start_states = p4_parse_states['start']

    accessible_parse_states = set()
    accessible_parse_states_ordered_name = []
    new_parser_name = {}

    def find_accessible_parse_states(parse_state):
        if parse_state in accessible_parse_states:
            return
        accessible_parse_states.add(parse_state)
        accessible_parse_states_ordered_name.append(parse_state.name)
        for _, next_state in parse_state.branch_to.items():
            if isinstance(next_state, p4_hlir.hlir.p4.p4_parse_state):
                find_accessible_parse_states(next_state)
    
    find_accessible_parse_states(start_states)
    print '    DBG|SP4_merge|parser names:', accessible_parse_states_ordered_name
    
    ## 01 rename all the parser state's name
    for parser_name in accessible_parse_states_ordered_name:
        if parser_name == 'start':
            continue
        new_parser_name[parser_name] = 'shadow_' + parser_name
        p4_parse_states[new_parser_name[parser_name]] = p4_parse_states.pop(parser_name)
        p4_parse_states[new_parser_name[parser_name]].name = new_parser_name[parser_name]

    ## 02 modify all the default tables which the parser branch to
    set_parser_default_table_STC(p4_parse_states, h_mg)


    return
    ## todo: check the return_statement
    for _, parser_state in p4_parse_states.items():
        return_type = parser_state.return_statement[0]
        print 'return_type = ', return_type, type(parser_state.return_statement)
        if return_type == "immediate":   
            state = parser_state.return_statement[1]
            if state in accessible_parse_states_ordered_name:
                del parser_state.return_statement
                parser_state.return_statement = ('immediate', new_parser_name[state])
                print 'DBG|004 parser_state.return_statement=', parser_state.return_statement
        elif return_type == "select":
            select_fields = parser_state.return_statement[1]
            select_cases = parser_state.return_statement[2] # a list of cases
            print 'DBG|005: select fields', select_fields
            print 'DBG|006: select cases', select_cases, type(select_cases)

            old_case_list = []
            new_case_list = []

            for case in select_cases:
                print 'DBG|007: case', case, type(case)
                value_list = case[0]
                if case[1] in accessible_parse_states_ordered_name:
                    print 'DBG|SP4_merge|parser rename select:', case[1]
                    old_case_list.append(case)
                    new_case = case[0], new_parser_name[case[1]]
                    new_case_list.append(new_case)
                else:
                    print 'DBG|SP4_merge|parser rename sekect err:', case[1]

            for case in old_case_list:
                select_cases.remove(case)
            for case in new_case_list:
                select_cases.append(case)

            print 'DBG|007: select cases', select_cases, type(select_cases)

#Original parse state merge for P4Visor
def merge_parser_statesOriginal(h_mg, h_r, h_meta):
	## 01 check the two P4 program start from the same parser state
    if 'start' not in h_mg.p4_parse_states.keys() or \
       'parse_ethernet' not in h_mg.p4_parse_states.keys():
        print 'ERR|p4c_bm|SP4_merge: missing parse_ethernet in testing P4 program'
        raise(False)
    if 'start' not in h_r.p4_parse_states.keys() or \
       'parse_ethernet' not in h_mg.p4_parse_states.keys():
        print 'ERR|p4c_bm|SP4_merge: missing parse_ethernet in real P4 program'
        raise(False)        

    ## 02 modify name of tables in shadow parser states: add '_shadow' suffix
    ## todo(low-priority): check if there are repeated parser state name
    rename_parser_states(h_mg.p4_parse_states, h_mg)

    # Check wheather parser_eth_shadow has the transition key
    # If not, create one for parse shadow tag
    if len(h_mg.p4_parse_states['shadow_parse_ethernet'].branch_on) == 0:
        h_mg.p4_parse_states['shadow_parse_ethernet'].branch_on = \
                                h_meta.p4_parse_states['parse_ethernet'].branch_on

    ## 03 add meta parser state
    h_mg.p4_parse_states['parse_upvn'] = h_meta.p4_parse_states['parse_upvn']
    
    # copy parse_eth's branch_to to parse_upvn
    parse_state_eth = h_mg.p4_parse_states['shadow_parse_ethernet']
    eth_branch_to = parse_state_eth.branch_to
    h_mg.p4_parse_states['parse_upvn'].branch_to.clear()
    h_mg.p4_parse_states['parse_upvn'].branch_to.update(eth_branch_to)

    # clear parse_eth's branch_to then add shadow tag state(0x8100)
    parse_state_eth.branch_to.clear()
    branch_case = 0x8100
    next_state = h_mg.p4_parse_states['parse_upvn']
    parse_state_eth.branch_to[branch_case] = next_state

    branch_case_default = p4_hlir.hlir.p4_parser.P4_DEFAULT
    next_state_default = h_mg.p4_tables['shadow_traffic_control']
    parse_state_eth.branch_to[branch_case_default] = next_state_default

    # fix the call sequence of parse_upvn 
    # TO improve 
    parse_state = h_mg.p4_parse_states['parse_upvn']
    op_type = p4_hlir.hlir.p4_parser.parse_call.extract
    op_header = h_mg.p4_header_instances['upvn']
    call = op_type, op_header
    parse_state.call_sequence = []
    parse_state.call_sequence.append(call)

    ## 04 add real parser states in, used shadow_start as the merged start state
    set_parser_default_table_STC(h_r.p4_parse_states, h_mg)
    for parser_name, parser_state in h_r.p4_parse_states.items():
        OPT_PRINT_NEW_PARSER = 0
        if OPT_PRINT_NEW_PARSER:
            print '    OPT_PRINT_NEW_PARSER|:'
            print pprint(vars(parser_state))
        if parser_name == 'start':
            continue
        elif parser_name == 'parse_ethernet':
            print "    pass parser state parse_ethernet"
            r_eth_branch_to = parser_state.branch_to
            h_mg.p4_parse_states['shadow_parse_ethernet'].branch_to.update(r_eth_branch_to)
            print r_eth_branch_to
            continue
        h_mg.p4_parse_states[parser_name] = parser_state
    

    OPT_PRINT_MERGED_PARSER = 0
    if OPT_PRINT_MERGED_PARSER:
        print '\n\n\nDBG|merge parser|print merged parser|:'
        printOrderedDict(h_mg.p4_parse_states)
    

#break p4c_bm/SP4_merge.py:1314

def merge_parser_states(h_mg, h_r, h_meta, virtual):  		
    #if its the first time merging, modify h_mg (at this point, its a perfect copy of h_s)
    first_merge = 'parse_upvn' not in h_mg.p4_parse_states
    if first_merge:
	    #use pvid for now
	    h_mg.p4_parse_states['parse_upvn'] = h_meta.p4_parse_states['parse_upvn']
	 
	    branch_case_default = p4_hlir.hlir.p4_parser.P4_DEFAULT
	    #if start state has select statement , ie. current(0, n), pass it to upvn state with added id
	    if h_mg.p4_parse_states['start'].branch_on != []:
		    #pass the branch_to from start to parse_upvn
		    for key, state in h_mg.p4_parse_states['start'].branch_to.items():
		    	h_mg.p4_parse_states['parse_upvn'].branch_to[key] = state
		    #copy select field from start to parse_upvn
		    h_mg.p4_parse_states['parse_upvn'].branch_on.append(h_mg.p4_parse_states['start'].branch_on[0])
		    h_mg.p4_parse_states['start'].branch_on = []
		    tempDict = OrderedDict()
		    tempDict[branch_case_default] = h_mg.p4_parse_states['parse_upvn']
		    h_mg.p4_parse_states['start'].branch_to = tempDict
		    set_parser_default_table_STC(h_mg.p4_parse_states, h_mg)
		    add_shadow_field_to_states(h_mg)
	   
	    #if start has default transition to ethernet
	    else: 
		    parse_eth_state = h_mg.p4_parse_states['start'].branch_to[branch_case_default]
		    h_mg.p4_parse_states['start'].branch_to.clear()
		    h_mg.p4_parse_states['start'].branch_to[branch_case_default] = h_mg.p4_parse_states['parse_upvn']
		    
		    
		    #add select fields and transitions to upvn state, i.e.,
		    #select(upvn.pvid)
		    #1 : parse_ethernet
		    tempDict = OrderedDict()
		    tempDict[branch_case_default] = parse_eth_state
		    h_mg.p4_parse_states['parse_upvn'].branch_to = tempDict
		    

		    ## 04 add real parser states in, used shadow_start as the merged start state
		    set_parser_default_table_STC(h_mg.p4_parse_states, h_mg)
		    add_shadow_field_to_states(h_mg)

    set_parser_default_table_STC(h_r.p4_parse_states, h_mg)
    #set everything back to 0
    if not first_merge:
    	clear_topo_order(h_mg)
    fill_topo_order(h_mg, h_r)
    extract = p4_hlir.hlir.p4_parser.parse_call.extract
    sort_parser_states(h_r, h_mg)

    for parser_nameR, parser_stateR in h_r.p4_parse_states.items():
	if parser_nameR == 'start':
            	continue
	#if the start state has default transition to first state
	if parser_stateR.topo_level == 1 and h_r.p4_parse_states['start'].branch_on == []:
		width = 0
		fill = ''
		#if the current parse upvn state is selecting on current
		if len(h_mg.p4_parse_states['parse_upvn'].branch_on) != 1:
			width = h_mg.p4_parse_states['parse_upvn'].branch_on[1][1] - h_mg.p4_parse_states['parse_upvn'].branch_on[1][0]
			fill = fill.zfill(width)
		if first_merge:
			pvid = '1111' + fill
			mask = '1111' + fill
			h_mg.p4_parse_states['parse_upvn'].branch_to[(int(pvid,2) , int(mask,2))] = parser_stateR
			parser_stateR.prev.add(h_mg.p4_parse_states['parse_upvn'])
		else:
			pvid = bin(int(virtual,16))[2:].zfill(4) + fill
			mask = '1111' + fill
			h_mg.p4_parse_states['parse_upvn'].branch_to[(int(pvid, 2), int(mask,2))] = parser_stateR
			parser_stateR.prev.add(h_mg.p4_parse_states['parse_upvn'])

		
	#case where start selects on current(0,n)
	elif h_r.p4_parse_states['start'] in parser_stateR.prev:
		add_current_to_upvn(h_mg, h_r.p4_parse_states['start'], first_merge, virtual)
		
	header_R = ''
	#if the node is purely conditional
	if parser_stateR.call_sequence == []:
		pass
	#If header has an equivalent in mg, find and share state
	elif parser_stateR.call_sequence[0][0] == extract:
		header_R = parser_stateR.call_sequence[0][1].name
	if header_R in h_r.lStrongEq:
		share_state(h_r, h_mg, parser_stateR, h_r.lStrongEq[header_R], h_meta, first_merge, virtual)
	elif header_R in h_r.lSimpleEq:
		share_state(h_r, h_mg, parser_stateR, h_r.lSimpleEq[header_R], h_meta, first_merge, virtual)
	elif header_R in h_r.lWeakEq:
		share_weakly_equivalent_states(h_r, h_mg, parser_stateR, header_R, h_r.lWeakEq[header_R], h_meta, first_merge, virtual)
	else:
		rename_and_add_state(h_r, h_mg, parser_stateR, h_meta, first_merge, virtual)

    print

#function used to sort h_r states by topological level,
#ensuring states are added in the correct sequence
def sort_parser_states(h_r, h_mg):
	#this dict contains the states of h_r, organized by topological level
	#e.g., (0,[start]),(1,[ethernet]),(2,[ipv4]),(3,[tcp,udp])
	topo_level_dict = OrderedDict()
	for name, state in h_r.p4_parse_states.items():
		level = state.topo_level
		if level not in topo_level_dict:
			topo_level_dict[level]= [state]
		else:
			topo_level_dict[level].append(state)

	#sorted dict containing all states
	newDict = OrderedDict()
	#for each topological level of the graph
	for i in range(len(topo_level_dict)):
		#if only one state in this topo level
		if len(topo_level_dict[i]) == 1:
			#simply append to the dict
			newDict[topo_level_dict[i][0].name] = topo_level_dict[i][0]

		#if multiple states are at the same level, sort based on 
		#the topo lovel of the equivalent state in h_mg
		else:
			sorted_topo_level = sort_same_topo_level(topo_level_dict[i], h_mg, h_r)
			for state in sorted_topo_level:
				newDict[state.name] = state

	h_r.p4_parse_states = newDict


#break p4c_bm/SP4_merge.py:1420
#sort states at the same topological level to determine the
#order in which the states must be added
def sort_same_topo_level(states, h_mg, h_r):
	extract = p4_hlir.hlir.p4_parser.parse_call.extract
	final_list = []
	level_list = []
	for stateR in states:
		#extracted header in the state
		if stateR.call_sequence[0][0] == extract:
			headerR = stateR.call_sequence[0][1]
		#no extracted header, state won't be shared, so it can be 
		#added first		
		else:
			final_list.insert(0,stateR)
			#level of equivalent state is defined as 0
			level_list.insert(0,0)
			continue
		#in case a header is extracted, see if there is an equivalent
		#header
		headerMG = ''
		headerMG = get_eq_header_in_mg(h_mg, h_r, headerR)

		#if no equivalent header was found, no equivalent state exists,
		#state can be added first
		if headerMG == '':
			final_list.insert(0,stateR)
			#level of equivalent state is defined as 0
			level_list.insert(0,0)
			continue
		#if there is an equivalent header, find equivalent state and its
		#topo level, and place in the correct position
		else:
			stateMG = ''
			for _, stateTemp in h_mg.p4_parse_states.items():
				if len(stateTemp.call_sequence) > 0:
					if stateTemp.call_sequence[0][1].name == headerMG :
						stateMG = stateTemp
						break

			#if no equivalent state, added first
			if stateMG == '':
				final_list.insert(0,stateR)
				#level of equivalent state is defined as 0
				level_list.insert(0,0)
				continue

			mg_topo = stateMG.topo_level
			found = False
			for i in range(len(level_list)):
				#if the level at index i is equal or greater,
				#it means the current state must be added before
				if mg_topo <= level_list[i]:
					final_list.insert(i, state)
					level_list.insert(i, mg_topo)
					found = True
					break
			#if no state (so far) has an equal or higher equivalent topo
			#level, the state must be added last
			if not found:
				final_list.append(state)
				level_list.append(mg_topo)

	return final_list
			
		
#returns the equivalent header in h_mg, if it exists			
def get_eq_header_in_mg(h_mg, h_r, headerR):
	if headerR.name in h_r.lStrongEq:
		headerMG_name = h_r.lStrongEq[headerR.name]
		return h_mg.p4_header_instances[headerMG_name]

	elif headerR.name in h_r.lSimpleEq:
		headerMG_name = h_r.lSimpleEq[headerR.name]
		return h_mg.p4_header_instances[headerMG_name]

	elif headerR.name in h_r.lWeakEq:
		headerMG_name = h_r.lWeakEq[headerR.name]
		return h_mg.p4_header_instances[headerMG_name]

	return ''

def get_select_size(state):
	size = 0
	if state.branch_on == []:
		return 0
	else:
		for field in state.branch_on:
			if not isinstance(field, tuple):
				size = size + field.width
			else:
				size = size + (field[1] - field[0])
		return size


def calculate_transitions(hlir):
	counter = 0
	min_size = 100000000
	max_size = 0
	total = 0
	counter_select = 0
	f = open('tmpText.txt', 'w')
	for _, state in hlir.p4_parse_states.items():		
		size = get_select_size(state)
		total = total + size
		#counter = counter + ((size / 33) + 1 ) * len(state.branch_to)	
		counter = counter + len(state.branch_to)
		f.write('--------------States and transitions:--------\n')
		#f.write(state.name + ' ----> ' + str(((size / 33) + 1 ) * len(state.branch_to)) + '\n')
		f.write(state.name + ' ----> ' +  str(len(state.branch_to)) + '\n')
		if len(state.branch_on) == 0:
			continue	
		counter_select = counter_select + 1	
		if size >= max_size:
			max_size = size
		if size <= min_size:
			min_size = size
	avg = total / counter_select
	f.close()
	return avg, max_size, min_size, counter

def get_eval(hlir):
	avg, s_max, s_min, transitions = calculate_transitions(hlir)
	states = len(hlir.p4_parse_states)
	headers =len(hlir.p4_header_instances)
	return avg, s_max, s_min, transitions, states, headers

def share_weakly_equivalent_states(h_r, h_mg, parser_stateR, header_nameR, header_nameMG, h_meta, first_merge, virtual):
	diff_fields = []
	headerR = h_r.p4_header_instances[header_nameR]
	headerMG = h_mg.p4_header_instances[header_nameMG]
	for fieldR in headerR.fields:	
		offsetR = fieldR.offset
		widthR = fieldR.width
		found = False
		for fieldMG in headerMG.fields:
			 if fieldMG.offset == offsetR and fieldMG.width == widthR:
				found = True
				break
		if not found:
			diff_fields.append(fieldR)

	 
	state_MG = ''
	for _, stateTemp in h_mg.p4_parse_states.items():
		if len(stateTemp.call_sequence) > 0:
			if stateTemp.call_sequence[0][1].name == header_nameMG :
				state_MG = stateTemp
				break

	#if there is no select statement on both states, share state normally
	if parser_stateR.branch_on == [] and len(state_MG.branch_on) == 1:
		share_state(h_r, h_mg, parser_stateR, header_nameMG, h_meta, first_merge, virtual)
	#if there is select statement:
	else:
		same = True
		#see if each field used is present in merged header
		for field in parser_stateR.branch_on:
			if field in diff_fields:
				same = False

		#see if every field used in mg is present in R
		for field in state_MG.branch_on:
			if field.name == 'upvn':
				pass
			fieldsR = get_fields(field, headerR)
			if len(fieldsR) > 1:
				same = False
				break
			if fieldsR[0].offset != field.offset or fieldsR[0].width != field.width:
				same = False
				break 
		#if there is a direct translation from these fields to the ones in the merged header, normal share
		if same:
			share_state(h_r, h_mg, parser_stateR, header_nameMG, h_meta, first_merge, virtual)

		#edge case: must translate from header_R fields to merged header fields to select correctly		
		else:
			#see if states can be shared
			#check if uses same metadata
			if check_same_metadata(h_r,h_mg, parser_stateR):
				rename_and_add_state(h_r, h_mg, parser_stateR, h_meta, first_merge, virtual)
				return
			#check if multiple extracted headers are all equivalent
			if not same_extracted_headers(h_r, parser_stateR, state_MG):
				rename_and_add_state(h_r, h_mg, parser_stateR, h_meta, first_merge, virtual)
				return 
			if not correct_topo_level(parser_stateR, state_MG, h_r, h_mg):
				rename_and_add_state(h_r, h_mg, parser_stateR, h_meta, first_merge, virtual)
				return

			h_r.topo_level = parser_stateR.topo_level
			h_mg.topo_level = state_MG.topo_level

			fields_to_add = get_fields_to_add(parser_stateR, headerMG)
			modify_mg_transitions(state_MG, fields_to_add)
			modify_r_transitions(parser_stateR, state_MG, headerR, first_merge, virtual)
			#add transitions		
			for key, state in parser_stateR.branch_to.items():
				h_mg.p4_parse_states[state_MG.name].branch_to[key] = state
				if not isinstance(state, p4_hlir.hlir.p4_table):
					state.prev.add(state_MG)
					
						
			
			#Change parse state object in previous transitions
			for state in parser_stateR.prev:
				for key, tempState in state.branch_to.items():
					if tempState == parser_stateR:
						state.branch_to[key] = state_MG

			#add translation between old and new name
			h_r.merged_map[parser_stateR.name] = state_MG.name 

	

#fields_to_add: list of fields from mg that contain the field from header_R 
#example: field_R = [0:3]; header_mg = [(f1, [0:2]),(f2, [3:5])] -> mg_diff = [f1,f2]
def get_fields_to_add(parser_stateR, headerMG):
	fields_to_add = []
	for fieldR in parser_stateR.branch_on:
		for fieldMG in headerMG.fields:
			if fieldMG.offset > fieldR.offset + fieldR.width -1 or fieldMG.offset + fieldMG.width -1 < fieldR.offset:
				pass
			else:
				fields_to_add.append(fieldMG)
	return fields_to_add

#every transition must change
def modify_r_transitions(parser_stateR, state_MG, headerR, first_merge, virtual):
	tempDict = OrderedDict()
	default = p4_hlir.hlir.p4_parser.P4_DEFAULT
	widthMG = 0
	for field in state_MG.branch_on:
		if field.name == 'pvid':
			continue
		widthMG = widthMG + field.width
	widthR = 0
	for field in parser_stateR.branch_on:
		widthR = widthR + field.width

	for key, next_state in parser_stateR.branch_to.items():
		if isinstance(key, int):
			realKey = format(key, 'b')
			realKey = realKey.zfill(widthR)
			newKey = ''
			newMask = ''
			for field in state_MG.branch_on:	
				fields_r = get_fields(field, headerR) 
				if field.name == 'pvid':
					continue
				for fieldR in fields_r:	
					select_offsetR = get_start_in_select(fieldR, parser_stateR)				
					field_start = fieldR.offset
					field_end = field_start + fieldR.width - 1
					for i in range(fieldR.width):
						if field_start + i < field.offset or field_start + i > field.offset + field.width - 1:
							pass
						else:
							if fieldR in parser_stateR.branch_on:

								newKey = newKey + realKey[select_offsetR + i]
								newMask = newMask + '1'
							else:
								newKey = newKey + '0'
								newMask = newMask + '0'
			flag = ''
			if first_merge:
				flag = '1111'
			else:
				flag = bin(int(virtual,16))[2:].zfill(4)
			newKey = flag + newKey
			newMask = '1111' + newMask
			tempDict[(int(newKey, 2), int(newMask,2))] = next_state

		if key == default:
			flag = ''
			if first_merge:
				flag = '1111'
			else:
				flag = bin(int(virtual,16))[2:].zfill(4)
			padding = ''.zfill(widthMG)
			newKey = flag + padding
			newMask = '1111' + padding
			tempDict[(int(newKey, 2), int(newMask,2))] = next_state

	parser_stateR.branch_to = tempDict

def get_start_in_select(fieldR, stateR):
	offset = 0
	for field in stateR.branch_on:
		if field != fieldR:
			if isinstance(field, tuple):
				offset = offset + field[1] - field[0]
			else:
				offset = offset + field.width
		else:
			return offset
#get list of fields in header from R that include this field from MG
def get_fields(fieldMG, headerR):
	fields = []
	for fieldR in headerR.fields:
		if fieldR.offset > fieldMG.offset + fieldMG.width -1 or fieldR.offset + fieldR.width -1 < fieldMG.offset:
			pass
		else:
				fields.append(fieldR)
	return fields


def modify_mg_transitions(state_MG, fields_to_add):
	same = True
	for field in fields_to_add:
		if field not in state_MG.branch_on:
			same = False
	if not same:	
		for field in fields_to_add:
			tempDict = OrderedDict()
			if field not in state_MG.branch_on:
				state_MG.branch_on.append(field)
				for key_mask, next_state in state_MG.branch_to.items():
					key = key_mask[0]
					mask = key_mask[1]
					key = format(key, 'b')
					mask = format(mask, 'b')
					padding = ''.zfill(field.width)
					key = key + padding
					mask = mask + padding
					tempDict[(int(key,2), int(mask,2))] = next_state
		
				state_MG.branch_to = tempDict


def add_current_to_upvn(h_mg, start, first_merge, virtual):
	default = p4_hlir.hlir.p4_parser.P4_DEFAULT
	#verify if parse_upvn already has a current(0,n) select field
	if len(h_mg.p4_parse_states['parse_upvn'].branch_on) != 1:
		#if the same key is present, just add transitions with pvid
		if start.branch_on[0] in h_mg.p4_parse_states['parse_upvn'].branch_on:
			width = start.branch_on[0][1] - start.branch_on[0][0]	
			#hex_width = 0
			#if width % 4 != 0:
				#hex_width = width / 4 + 1
			#else:
				#hex_width = width / 4				
			for key, state in start.branch_to.items():
				newKey = ''
				if first_merge:
					newKey = format(int('f', 16), 'b')
				else:
					newKey = format(int(virtual, 16), 'b')
				
				if key == default:
					fill = ''
					fill = fill.zfill(width)
					newKey = newKey + fill
					mask = '1111' + fill
				else:
					bin_key = format(key, 'b')
					bin_key = bin_key.zfill(width)
					newKey = newKey + bin_key
					mask = '1' * (4 + width)

				#add transition to upvn state
				h_mg.p4_parse_states['parse_upvn'].branch_to[(int(newKey, 2), int(mask, 2))] = state
				if not isinstance(state, p4_hlir.hlir.p4_table): 
					state.prev.add(h_mg.p4_parse_states['parse_upvn'])

		# if both states have different current(x,y) selects, create new current with 'x' as the minimum 'x' from 
		# both states and 'y' as the maximum between 'y's. Then add padding for each transition depending on the
		# new bits selected on
		else:	
			mg_current = h_mg.p4_parse_states['parse_upvn'].branch_on[1]
			r_current = start.branch_on[0]
			new_x = min(mg_current[0], r_current[0])
			new_y = max(mg_current[1], r_current[1])
			new_current = (new_x, new_y)

			#process for mg (add padding for new bits selected on) if needed
			if new_current != mg_current:
				add_left = mg_current[0] - new_x
				add_right = new_y - mg_current[1]
				newDict = OrderedDict()
				for key, next_state in h_mg.p4_parse_states['parse_upvn'].branch_to.items():
					pvid = format(key[0], 'b')[:4]
					original = format(key[0], 'b')[4:]
					original = '0' * add_left + original
					original = original + '0' * add_right
					new_value = pvid + original

					mask = format(key[0], 'b')[4:]
					mask = '0' * add_left + mask
					mask = mask + '0' * add_right
					new_mask = '1111' + mask

					newDict[(int(new_value,2), int(new_mask,2))] = next_state
				
				h_mg.p4_parse_states['parse_upvn'].branch_to = newDict

			#process for r (add padding for new bits selected on) if needed, add pvid and merge
			width = r_current[1] - r_current[0]
			add_left = r_current[0] - new_x
			add_right = new_y - r_current[1]
			pvid = ''
			if first_merge:
				pvid = format(int('f', 16), 'b')
			else:
				pvid = format(int(virtual, 16), 'b')
			for key, next_state in start.branch_to.items():
				if isinstance(key, int):
					original = format(key, 'b').zfill(width)
					original = '0' * add_left + original
					original = original + '0' * add_right
					new_value = pvid + original
					
					mask = '1' * width
					mask = '0' * add_left + mask
					mask = mask + '0' * add_right
					new_mask = '1111' + mask
					
					h_mg.p4_parse_states['parse_upvn'].branch_to[(int(new_value, 2), int(new_mask, 2))] = next_state
				elif key == default:
					new_width = new_y - new_x
					new_value = pvid + ''.zfill(new_width)
					new_mask = '1111' + ''.zfill(new_width)

					h_mg.p4_parse_states['parse_upvn'].branch_to[(int(new_value, 2), int(new_mask, 2))] = next_state

			h_mg.p4_parse_states['parse_upvn'].branch_on.remove(mg_current)
			h_mg.p4_parse_states['parse_upvn'].branch_on.append(new_current)

	#if there is no current in the parse_upvn state, add and modify transitions
	else:
		h_mg.p4_parse_states['parse_upvn'].branch_on.append(start.branch_on[0])
		width = start.branch_on[0][1] - start.branch_on[0][0]	
		#hex_width = 0
		#if width % 4 != 0:
			#hex_width = width / 4 + 1
		#else:
			#hex_width = width / 4	
	
		padding = ''
		padding = padding.zfill(width)
		tempDict = OrderedDict()
		for key, state in h_mg.p4_parse_states['parse_upvn'].branch_to.items():
			keyOld = format(key[0], 'b')
			keyNew = keyOld + padding
			mask = 	'1111' + padding
			tempDict[(int(keyNew,2), int(mask,2))] = state
		h_mg.p4_parse_states['parse_upvn'].branch_to = tempDict

		#add transitions from h_r
		for key, state in start.branch_to.items():
			newKey = ''
			if first_merge:
				newKey = format(int('f', 16), 'b')
			else:
				newKey = format(int(virtual, 16), 'b')
				
			if key == default:
				fill = ''
				fill = fill.zfill(width)
				newKey = newKey + fill
				mask = '1111' + fill
			else:
				bin_key = format(key, 'b')
				bin_key = bin_key.zfill(width)
				newKey = newKey + bin_key
				mask = '1' * (4 + width)

			#add transition to upvn state
			h_mg.p4_parse_states['parse_upvn'].branch_to[(int(newKey, 2), int(mask,2))] = state
			if not isinstance(state, p4_hlir.hlir.p4_table):
				state.prev.add(h_mg.p4_parse_states['parse_upvn'])
			

def add_shadow_field_to_states(h_mg):
	for _, state in h_mg.p4_parse_states.items():
		if state.name == 'start':
			continue
		if state.return_statement[0] != 'immediate' and state.name != 'parse_upvn':
			state.branch_on.insert(0, h_mg.p4_header_instances['upvn'].fields[0])
		add_select_fields_2(h_mg, state)	

def rename_and_add_state(h_r, h_mg, parse_stateR, h_meta, first_merge, virtual):
	#check special case where eq headers could not be extracted by eq states
	extract = p4_hlir.hlir.p4_parser.parse_call.extract
	for call in parse_stateR.call_sequence:
		if call[0] == extract:
			#check if the header is in the current dictionary
			header = call[1]
			if header.name not in h_mg.p4_header_instances:
				#add header instance and type to h_mg
				check_header_and_add(h_mg, h_r, header, '')
				header.header_type.name = header.name + '_t'
				h_mg.p4_headers[header.header_type.name] = header.header_type
	#check if renaming is necessary
	if parse_stateR.return_statement[0] == 'select':
		if parse_stateR.name in h_mg.p4_parse_states:
			oldName = parse_stateR.name
			if first_merge:
				parse_stateR.name = parse_stateR.name + 'NEW'
			else:
				parse_stateR.name = parse_stateR.name + 'NEW' + virtual
			h_mg.p4_parse_states[parse_stateR.name] = parse_stateR
			add_select_fields(h_r, parse_stateR, first_merge, virtual)
			parse_stateR.return_statement[1].insert(0, 'upvn.pvid')
			parse_stateR.branch_on.insert(0, h_meta.p4_header_instances['upvn'].fields[0])
			#add translation between old and new name
			h_r.merged_map[oldName] = parse_stateR.name
		else:
			add_select_fields(h_r, parse_stateR, first_merge, virtual)
			parse_stateR.return_statement[1].insert(0, 'upvn.pvid')
			parse_stateR.branch_on.insert(0, h_meta.p4_header_instances['upvn'].fields[0])
			h_mg.p4_parse_states[parse_stateR.name] = parse_stateR
			#add translation between old and new name (same in this case)
			h_r.merged_map[parse_stateR.name] = parse_stateR.name
	#if immediate (e.g. tcpNEW)	
	else:
		if parse_stateR.name in h_mg.p4_parse_states:
			oldName = parse_stateR.name
			if first_merge:
				parse_stateR.name = parse_stateR.name + 'NEW'
			else:
				parse_stateR.name = parse_stateR.name + 'NEW' + virtual
			h_mg.p4_parse_states[parse_stateR.name] = parse_stateR
			add_select_fields(h_r, parse_stateR, first_merge, virtual)
			parse_stateR.branch_on.insert(0, h_meta.p4_header_instances['upvn'].fields[0])
			#add translation between old and new name
			h_r.merged_map[oldName] = parse_stateR.name
		else:
			h_mg.p4_parse_states[parse_stateR.name] = parse_stateR
			add_select_fields(h_r, parse_stateR, first_merge, virtual)
			parse_stateR.branch_on.insert(0, h_meta.p4_header_instances['upvn'].fields[0])
			#add translation between old and new name (same in this case)
			h_r.merged_map[parse_stateR.name] = parse_stateR.name


def add_select_fields(h_r, parser_stateR, first_merge, virtual):
	default = p4_hlir.hlir.p4_parser.P4_DEFAULT
	if parser_stateR.return_statement[0] == 'select':
		width = 0
		# calculate the total width of select fields
		for field in parser_stateR.branch_on:
			if not isinstance(field, tuple):				
				width = field.width + width
			else:
				width = (field[1] - field[0]) + width
		newDict = OrderedDict()
		for transition_2 in parser_stateR.branch_to.items():		
			if isinstance(transition_2[0], int):	
				
				bin_key = format(transition_2[0], 'b')
				bin_key = bin_key.zfill(width)
				# Add id (for now, fake value)
				if first_merge:
					bin_key = format(int('f', 16), 'b') + bin_key 
				else:
					bin_key = format(int(virtual, 16), 'b') + bin_key 
				mask = '1'* len(bin_key)
				newDict[(int(bin_key, 2), int(mask,2))] = transition_2[1]
			# do need to modify first value to hold the flag
			elif isinstance(transition_2[0], tuple):
				bin_key = format(transition_2[0][0], 'b')
				bin_key = bin_key.zfill(width)
				# Add id (for now, fake value)
				if first_merge:
					bin_key = format(int('f', 16), 'b') + bin_key 
				else:
					bin_key = format(int(virtual, 16), 'b') + bin_key  
				#take care of mask
				mask = format(transition_2[0][1], 'b')
				mask = mask.zfill(width)
				mask = '1111' + mask
				newDict[(int(bin_key, 2), int(mask,2))] = transition_2[1]

			elif transition_2[0] == default:
				fill = ''
				fill = fill.zfill(width)
				
				if first_merge:
					bin_key = format(int('f', 16), 'b') + fill
					mask = '1111' + fill
				else:
					bin_key = format(int(virtual, 16), 'b') + fill
					mask = '1111' + fill
				newDict[(int(bin_key,2), int(mask, 2))] = transition_2[1]
		parser_stateR.branch_to = newDict
        #if its immediate, change default transition to virtual id transition
	elif parser_stateR.return_statement[0] == 'immediate':
		default = p4_hlir.hlir.p4_parser.P4_DEFAULT
		if first_merge:
			parser_stateR.branch_to[(0xf, 0xf)] = parser_stateR.branch_to.pop(default)
		else:
			parser_stateR.branch_to[(int(virtual,16), 0xf)] = parser_stateR.branch_to.pop(default)


def add_select_fields_2(h_r, parser_stateR):
	default = p4_hlir.hlir.p4_parser.P4_DEFAULT
	if parser_stateR.return_statement[0] == 'select':
		width = 0
		# calculate the total width of select fields
		for field in parser_stateR.branch_on:
			if not isinstance(field, tuple):			
				if field.name == 'pvid':
					continue
				width = field.width + width
			#if select is of type current(0,n)			
			else:
				width = (field[1] - field[0]) + width

		newDict = OrderedDict()
		for transition_2 in parser_stateR.branch_to.items():
			if isinstance(transition_2[0], int):
				bin_key = format(transition_2[0], 'b')
				bin_key = bin_key.zfill(width)
				# Add id (for now, fake value)
				bin_key = '0001' + bin_key 
				# Create mask (f's for each position, meaning care about all)
				mask = '1' * len(bin_key)
				newDict[(int(bin_key, 2), int(mask, 2))] = transition_2[1]
			# modify first value to hold the flag
			if isinstance(transition_2[0], tuple):
				bin_key = format(transition_2[0][0], 'b')
				bin_key = bin_key.zfill(width)
				# Add id (for now, fake value)
				bin_key = '0001' + bin_key  
				mask = format(transition_2[0][1], 'b')
				mask = mask.zfill(width)
				mask = '1111' + mask
				newDict[(int(bin_key, 2), int(mask, 2))] = transition_2[1]
			elif transition_2[0] == default:
				bin_key = ''
				bin_key = bin_key.zfill(width)
				bin_key = '0001' + bin_key
				mask = ''
				mask = mask.zfill(width)
				mask = '1111' + mask
				newDict[(int(bin_key, 2), int(mask, 2))] = transition_2[1]
		parser_stateR.branch_to = newDict
	#add transition case before sharing
	elif parser_stateR.return_statement[0] == 'immediate':
		parser_stateR.branch_on.insert(0, h_r.p4_header_instances['upvn'].fields[0])
		default = p4_hlir.hlir.p4_parser.P4_DEFAULT
		parser_stateR.branch_to[(0x1, 0xf)] = parser_stateR.branch_to.pop(default)
			
def calculate_diff_fields(parser_stateR, state_MG, h_r):
	mg_diff = []
	common_fields = OrderedDict()
	#for each field in the merged select
	for field in state_MG.branch_on:
		#ignore shadow flag
		if field.name == 'pvid':
			continue
		header_MG = field.instance
		header_R = get_header_if_eq(h_r, header_MG) 
		#if this header doesnt exist in R, it wont be in the select, so we append to mg_diff
		if header_R == '':
			mg_diff.append(field)
		else:
			#see if in stateR this field is used
			pos = field.instance.fields.index(field)
			field_R = header_R.fields[pos]
			#if this field is NOT used in the stateR, append to list
			if field_R not in parser_stateR.branch_on:
				mg_diff.append(field)
			else:
				common_fields[field] = field_R
	r_diff = []
	for field in parser_stateR.branch_on:
		if field not in common_fields.values():
			r_diff.append(field)
	return mg_diff, r_diff, common_fields
	
		
#get the header in h_r that is equivalent to header_MG
#(note: does not work to get equivalent header in h_mg,
#since the equivalence list only exist in h_r)
def get_header_if_eq(h_r, header_MG):
	if header_MG.name in h_r.lStrongEq:
		header_nameR = h_r.lStrongEq[header_MG.name]
		header_R = h_r.p4_header_instances[header_nameR]
		return header_R
	
	for header_nameR, temp in h_r.lSimpleEq.items():
		if temp == header_MG.name:
			header_R = h_r.p4_header_instances[header_nameR]
			return header_R	

	#special case for weak equivalent sharing
	if header_MG.name in h_r.lWeakEq.values():
		for header_nameR, temp in h_r.lWeakEq.items():
			if temp == header_MG.name:
				header_R = h_r.p4_header_instances[header_nameR]
				return header_R
	
	else:
		return ''	

def add_select_fields_shared(h_r, h_mg, parser_stateR, state_MG, h_meta, first_merge, virtual):
	mg_diff, r_diff, common_fields = calculate_diff_fields(parser_stateR, state_MG, h_r)
	#add ignore values for new fields in mg's transitions
	add_ignore_fields(state_MG, r_diff)
	add_fields_to_r(state_MG, parser_stateR, mg_diff, r_diff, common_fields, h_mg, h_r)
	if virtual == '3':
		print
	if parser_stateR.return_statement[0] == 'select':
		width = 0
		for field in state_MG.branch_on:
			if field.name == 'pvid':
				continue
			if not isinstance(field, tuple):
				width = field.width + width
			else:
				width = (field[1] - field[0]) + width
		newDict = OrderedDict()
		for transition_2 in parser_stateR.branch_to.items():
			#redundant code, transitions are all in tuple and default format 
			if isinstance(transition_2[0], int):
				bin_key = format(transition_2[0], 'b')
				bin_key = bin_key.zfill(width)
				# Add id 
				if first_merge:
					bin_key = format(int('f', 16), 'b') + bin_key 
				else:
					bin_key = format(int(virtual, 16), 'b') + bin_key 
				newDict[int(bin_key, 2)] = transition_2[1]

			if isinstance(transition_2[0], tuple):
				bin_key = format(transition_2[0][0], 'b')
				bin_key = bin_key.zfill(width)
				# Add id 
				if first_merge:
					bin_key = format(int('f', 16), 'b') + bin_key 
				else:
					bin_key = format(int(virtual, 16), 'b') + bin_key 
				
				#mask is dealt with in add_fields_to_r
				newDict[(int(bin_key, 2), transition_2[0][1])] = transition_2[1]
			else:
				bin_key = ''
				bin_key = bin_key.zfill(width)
				#add the virtual id
				if first_merge:
					bin_key = format(int('f', 16), 'b') + bin_key
				else:
					bin_key = format(int(virtual, 16), 'b') + bin_key
				#create mask 
				mask = ''
				mask = mask.zfill(width)
				mask = '1111' + mask				
				newDict[(int(bin_key, 2), int(mask, 2))] = transition_2[1]
		parser_stateR.branch_to = newDict
	#if its immediate, add virtual id and transition
	else:
		parser_stateR.branch_on.insert(0, h_meta.p4_header_instances['upvn'].fields[0])
		default = p4_hlir.hlir.p4_parser.P4_DEFAULT
		#if the state in mg is selecting on upvn.pvid only
		if len(state_MG.branch_on) == 1:
			if first_merge:
				parser_stateR.branch_to[(0xf, 0xf)] = parser_stateR.branch_to.pop(default)
			else:
				parser_stateR.branch_to[(int(virtual, 16), 0xf)] = parser_stateR.branch_to.pop(default)
		else:
			width = 0
			for field in state_MG.branch_on:
				if not isinstance(field, tuple):			
					if field.name == 'pvid':
						continue
					width = field.width + width
				#if select is of type current(0,n)			
				else:
					width = (field[1] - field[0]) + width
			

			fill = ''
			fill = fill.zfill(width)
			if first_merge:
				value = format(int('f', 16), 'b') + fill
				mask = '1111' + fill
				parser_stateR.branch_to[(int(value, 2), int(mask, 2))] = parser_stateR.branch_to.pop(default)
			else:
				value = format(int(virtual, 16), 'b') + fill
				mask = '1111' + fill
				parser_stateR.branch_to[(int(value,2), int(mask,2))] = parser_stateR.branch_to.pop(default)


def add_fields_to_r(state_MG, parser_stateR, mg_diff, r_diff, common_fields, h_mg, h_r):
	r_width = 0
	for field in parser_stateR.branch_on:
		if not isinstance(field, tuple):
			r_width = r_width + field.width
		else:
			r_width = r_width + field[1] - field[0]
	
	# for each transition case in r 
	new_branch_to = OrderedDict()
	for value, next_state in parser_stateR.branch_to.items():
		if isinstance(value, int):
			new_value = ''
			mask = ''
			field_value = OrderedDict()
			bin_key = format(value, 'b')
			bin_key = bin_key.zfill(r_width)	
			
			#create map field -> respective transition values
			i = 0
			for field in parser_stateR.branch_on:
				if not isinstance(field, tuple):
					f_width = field.width
				else:
					f_width = field[1] - field[0]

		
				field_value[field] = bin_key[i:i + f_width]
				i = i + f_width
				
			#add each field value to new transition value, from mg
			for field_mg in state_MG.branch_on:
				if field_mg.name == 'pvid':
					continue
				#if this field doesnt exist in R, add ignore values
				if field_mg in mg_diff:
					fill = ''
					width = field_mg.width
					fill = fill.zfill(width)
					new_value = new_value + fill
					mask = mask + fill
				#if this field exists in R, but not in MG, add portion of value and correct mask
				elif field_mg in r_diff:
					new_value = new_value + field_value[field_mg]
					width = field_mg.width
					mask = mask + '1' * width
				#if this field exists in both
				else:
					field_in_r = common_fields[field_mg]
					new_value = new_value + field_value[field_in_r]
					width = field_in_r.width
					mask = mask + '1' * width
			#add f for the virtual id on the mask, for value its done in next step
			new_branch_to[(int(new_value,2), int('1111' + mask, 2))] = next_state

		elif isinstance(value, tuple):
			new_value = ''
			mask = ''
			field_value = OrderedDict()
			bin_key = format(value[0], 'b')
			bin_key = bin_key.zfill(r_width)
			field_mask = OrderedDict
			bin_mask = format(value[1], 'b')	
			bin_mask = bin_mask.zfill(r_width)
			
			#create map field -> respective transition values
			i = 0
			for field in parser_stateR.branch_on:
				if not isinstance(field, tuple):
					f_width = field.width
				else:
					f_width = field[1] - field[0]

		
				field_value[field] = bin_key[i:i + f_width]
				field_mask[field] = bin_mask[i:i + f_width]
				i = i + f_width

			#add each field value to new transition value, from mg
			for field_mg in state_MG.branch_on:
				if field_mg.name == 'pvid':
					continue
				#if this field doesnt exist in R, add ignore values
				if field_mg in mg_diff:
					width = field_mg.width
					fill = fill.zfill(width)
					new_value = new_value + fill
					mask = mask + fill
				#if this field exists in R, but not in MG, add portion of value and correct mask
				if field_mg in r_diff:
					new_value = new_value + field_value[field_mg]
					mask = mask + field_mask[field_mg]
				#if this field exists in both
				else:
					field_in_r = common_fields[field_mg]
					new_value = new_value + field_value[field_in_r]
					mask = mask + field_mask[field_in_r]
			#add f for the virtual id on the mask, for value its done in next step
			new_branch_to[(int(new_value,2), int('1111' + mask, 2))] = next_state


		else:
			new_branch_to[value] = next_state
	parser_stateR.branch_to = new_branch_to

	# After the transition cases have been corrected, remove every field from R from the MG state.
	# This must be done because in the merged json, those fields do not exist
	new_branch_on = []
	for field in state_MG.branch_on:
		if field not in parser_stateR.branch_on:
			new_branch_on.append(field)
		else:
			fieldMG = find_fieldMG(field, h_r, h_mg)
			new_branch_on.append(fieldMG)
	state_MG.branch_on = new_branch_on
	
def add_ignore_fields(stateMG, r_diff):
	width = 0	
	for field in r_diff:
		if not isinstance(field, tuple):
			width = width + field.width
		else:
			width = width + field[1] - field[0]
		
		stateMG.branch_on.append(field)
	if width != 0:
		
		newDict = OrderedDict()
		for transition_2 in stateMG.branch_to.items():
			
			if isinstance(transition_2[0], tuple):
				bin_key = format(transition_2[0][0], 'b')	
				mask = format(transition_2[0][1], 'b')	
				fill = ''
				fill = fill.zfill(width)
				bin_key = bin_key + fill
				mask = mask + fill
				newDict[(int(bin_key, 2), int(mask, 2))] = transition_2[1]
		stateMG.branch_to = newDict

#this function finds the equivalent field in the mg header. This is necessary, as in
#the merged json, the field from R will no longer exist, and so cannot be selected on
def find_fieldMG(fieldR, h_r, h_mg):
	headerR = fieldR.instance
	start = fieldR.offset
	if headerR.name in h_r.lWeakEq:
		headerMG = h_mg.p4_header_instances[h_r.lWeakEq[headerR.name]]
		for field in headerMG.fields:
			if field.offset == start:
				return field
	headerMG = ''	
	if headerR.name in h_r.lStrongEq:
		headerMG = h_mg.p4_header_instances[h_r.lStrongEq[headerR.name]]
	else:
		headerMG = h_mg.p4_header_instances[h_r.lSimpleEq[headerR.name]]

	for field in headerMG.fields:
			if field.offset == start:
				return field

def check_same_metadata(h_r, h_mg, parser_stateR):
	#check if metadata modified in parser_stateR is present in h_mg
	for call in parser_stateR.call_sequence:
		header_nameMG = ''
		if call[0] == p4_hlir.hlir.p4_parser.parse_call.set:
			field_R = call[1]
			header_R = field_R.instance
			if header_R.name in h_r.lStrongEq:
				header_nameMG = h_r.lStrongEq[header_R.name]

			if header_R.name in h_r.lSimpleEq:
				for key, value in h_r.lSimpleEq.items():
					if value == header_R.name:
						header_nameMG = key
						break
			if header_nameMG == '':
				continue
			else:
				header_MG = h_mg.p4_header_instances[header_nameMG]
				index = header_R.fields.index(field_R)
				field_MG = header_MG.fields[index]
				if header_MG.name in h_mg.my_lists:
					if field_MG.name in h_mg.my_lists[header_MG.name]:
						return True
	return False	
	
def share_state(h_r, h_mg, parser_stateR, header_MG, h_meta, first_merge, virtual):
	#find extracting state
	state_MG = ''
	for _, stateTemp in h_mg.p4_parse_states.items():
		if len(stateTemp.call_sequence) > 0:
			if stateTemp.call_sequence[0][1].name == header_MG :
				state_MG = stateTemp
				break
	if state_MG != '':
		#check if uses same metadata
		if check_same_metadata(h_r,h_mg, parser_stateR):
			rename_and_add_state(h_r, h_mg, parser_stateR, h_meta, first_merge, virtual)
			return
		#check if multiple extracted headers are all equivalent
		if not same_extracted_headers(h_r, parser_stateR, state_MG):
			rename_and_add_state(h_r, h_mg, parser_stateR, h_meta, first_merge, virtual)
			return 
		if not correct_topo_level(parser_stateR, state_MG, h_r, h_mg):
			rename_and_add_state(h_r, h_mg, parser_stateR, h_meta, first_merge, virtual)
			return
		add_select_fields_shared(h_r, h_mg, parser_stateR, state_MG, h_meta, first_merge, virtual)
		h_r.topo_level = parser_stateR.topo_level
		h_mg.topo_level = state_MG.topo_level
		#add transitions		
		for key, state in parser_stateR.branch_to.items():
			h_mg.p4_parse_states[state_MG.name].branch_to[key] = state
			if not isinstance(state, p4_hlir.hlir.p4_table):
				state.prev.add(state_MG)
				
					
		
		#Change parse state object in previous transitions
		for state in parser_stateR.prev:
			for key, tempState in state.branch_to.items():
				if tempState == parser_stateR:
					state.branch_to[key] = state_MG

		#add translation between old and new state names
		h_r.merged_map[parser_stateR.name] = state_MG.name


def correct_topo_level(parser_stateR, state_MG, h_r, h_mg):
	if parser_stateR.name == 'parse_udp' and state_MG.name == 'parse_ipv6':
		print
	if parser_stateR.topo_level >= h_r.topo_level and state_MG.topo_level >= h_mg.topo_level:
		return True
	else:
		return False

def same_extracted_headers(h_r, state_R, state_MG):
	extract = p4_hlir.hlir.p4_parser.parse_call.extract
	extract_R = []
	for entry in state_R.call_sequence:
		if entry[0] == extract:
			extract_R.append(entry[1])
	extract_MG = []
	for entry in state_MG.call_sequence:
		if entry[0] == extract:
			extract_MG.append(entry[1])

	#if each header is strong, simple or weakly equivalent, share state
	if len(extract_R) != len(extract_MG):
		return False
	same = True
	for i in range(len(extract_R)):
		name_R = extract_R[i].name
		name_MG = extract_MG[i].name
		if name_R in h_r.lWeakEq:
			if h_r.lWeakEq[name_R] == name_MG:
				continue
			else:
				same = False
				break
		if name_R in h_r.lStrongEq:
			if h_r.lStrongEq[name_R] == name_MG:
				continue
			else:
				same = False
				break
		if name_R in h_r.lSimpleEq:
			if h_r.lSimpleEq[name_R] == name_MG:
				continue
			else:
				same = False
				break
	return same
		

def clear_topo_order(h_mg):
	h_mg.topo_level = 0
	for name, state in h_mg.p4_parse_states.items():
		state.topo_level = 0
		state.pos_bitstream = []


def fill_topo_order(h_mg, h_r):
	#attributing topological levels to the merged program
	recursive_fill(h_mg.p4_parse_states['parse_upvn'], 0)

	#attributing topological levels to the added program
	recursive_fill(h_r.p4_parse_states['start'], 0)


#function used to give each state a topological level
#curr_state -> state being updated
#level -> candidate level 
def recursive_fill(curr_state, level):
	states = []
	#get all states reachable by this state (no duplicates)
	for key , state in curr_state.branch_to.items():
		if state not in states:
			states.append(state)
	
	#if the level received from the last state is greater
	#than the one the state currently has, we update 
	if level > curr_state.topo_level:
		curr_state.topo_level = level
		
	#for every reachable state, call the function with 
	#the current state's topological level + 1 
	for state in states:
		if not isinstance(state, p4_hlir.hlir.p4_table):
			recursive_fill(state, curr_state.topo_level + 1)

def delete_transitions_and_id(state):
	id_remove = True
	if state.name == 'start':
		return
	#number of programs sharing this state	
	prog_count = get_shared_program_count(state)
	width = 0
	for field in state.branch_on:
		if isinstance(field,tuple):
			width = width + field[1] - field[0]
		else:
			width = width + field.width
	#create copy of original branch_to dictionary
	tempDict = OrderedDict()
	for keyTemp, valueTemp in state.branch_to.items():
		tempDict[keyTemp] = valueTemp

	#list of redundant cases to be removed
	temp_remove = []
	#for every transition of the state
	for key, next_state in state.branch_to.items():
		if key not in tempDict:
			continue
		keyBin = format(key[0], 'b')
		keyBin = keyBin.zfill(width)
		realValue = keyBin[4:]

		mask = format(key[1], 'b')
		mask = mask.zfill(width)
		realMask = mask[4:]
		for key2, next_state2 in state.branch_to.items():
			if key == key2:
				continue

			keyBin2 = format(key2[0], 'b')
			keyBin2 = keyBin2.zfill(width)
			realValue2 = keyBin2[4:]

			mask2 = format(key2[1], 'b')
			mask2 = mask2.zfill(width)
			realMask2 = mask2[4:]
			
			#if the two transitions have the same transition condition and following state
			#then they are temporarily added to the remove list
			if realValue == realValue2 and realMask == realMask2 and next_state == next_state2:
				temp_remove.append(key2)
	
		#if every program sharing this state has the same transition as the current (key, next_state) pair
		#remove all redundant transition
		if len(temp_remove) == prog_count - 1:
			for case in temp_remove:
				tempDict.pop(case)
			#change the remaining transition, from id+field mask f+f
			# to 0+field mask 0+f
			if realValue == '':
				realValue = '0'
			if realMask == '':
				realMask = '0'
			
			if (int(realValue,2),int(realMask,2)) == (0,0):
				default = p4_hlir.hlir.p4_parser.P4_DEFAULT
				tempDict[default] = tempDict.pop(key)
			else:
				tempDict[(int(realValue,2),int(realMask,2))] = tempDict.pop(key)
		else:
			id_remove = False
		temp_remove = []
	
	
	#after removing redundant transitions, check if pvid can be removed
	if id_remove:
		del state.branch_on[0]
	state.branch_to = tempDict
		
		
	
def get_shared_program_count(state):
	temp_list = []	
	for key, nextState in state.branch_to.items():
		#original key (i.e., pvid + field in binary format)
		originalBin = format(key[0], 'b')
		width = 0
		for field in state.branch_on:
			if isinstance(field,tuple):
				width = width + field[1] - field[0]
			else:
				width = width + field.width
		#original key with leftmost bits added if needed
		originalBin = originalBin.zfill(width)
		#program id, present in the first 4 bits
		program_id = originalBin[:4]
		if program_id not in temp_list:
			temp_list.append(program_id)
	return len(temp_list)

def delete_virtual_parser(h_mg):
	#if after deleting duplicate transitions there is only one transition 
	#from shadow state, then all programs transition to the same state, and 
	#so there is no need for this parse state, and next state can extract 
	#the virtual header 
	if len(h_mg.p4_parse_states['parse_upvn'].branch_to.items()) == 1:
		extract = p4_hlir.hlir.p4_parser.parse_call.extract
		default = p4_hlir.hlir.p4_parser.P4_DEFAULT
		state = h_mg.p4_parse_states['parse_upvn'].branch_to.items()[0][1]
		start = h_mg.p4_parse_states['start']
		start.branch_to[default] = state
		state.prev.pop()
		state.prev.add(start)
		h_mg.p4_parse_states.pop('parse_upvn')	
		virtual = h_mg.p4_header_instances['upvn']
		state.call_sequence.insert(0, (extract, virtual)) 



def add_set_metadata(h_mg):
	#change to custom metadata
	field = h_mg.p4_header_instances['upvn_metadata'].fields[0]
	state_id = 0
	for name, state in h_mg.p4_parse_states.items():
		if state.name == 'start' or state.name == 'parse_upvn' :
			continue
		value = int(math.pow(2, state_id))
		expression = p4_hlir.hlir.p4_expressions.p4_expression(field, '+', value)
		set_meta = p4_hlir.hlir.p4_parser.parse_call.set
		statement = (set_meta, field, expression)
		state.call_sequence.append(statement)
		state.id = state_id
		state_id = state_id + 1
		

def SP4_AB_merge_p4_objects(p4_v1_1, h_r, h_s, h_meta):
    ### The following is the merged HLIR

  ## 1. init hlir
    if p4_v1_1:
        from p4_hlir_v1_1.main import HLIR
        primitives_res = 'primitives_v1_1.json'
    else:
        from p4_hlir.main import HLIR
        primitives_res = 'primitives.json'
    h_mg = HLIR()

  ## 2. add objects of shadow program
    h_mg.p4_actions.update(h_s.p4_actions)       
    h_mg.p4_control_flows.update(h_s.p4_control_flows)
    h_mg.p4_headers.update(h_s.p4_headers )
    h_mg.p4_header_instances.update(h_s.p4_header_instances )
    h_mg.p4_fields.update(h_s.p4_fields )
    h_mg.p4_field_lists.update(h_s.p4_field_lists )
    h_mg.p4_field_list_calculations.update(h_s.p4_field_list_calculations )
    h_mg.p4_parser_exceptions.update(h_s.p4_parser_exceptions )
    h_mg.p4_parse_value_sets.update(h_s.p4_parse_value_sets)
    h_mg.p4_parse_states.update(h_s.p4_parse_states )
    h_mg.p4_counters.update(h_s.p4_counters)
    h_mg.p4_meters.update(h_s.p4_meters)
    h_mg.p4_registers.update(h_s.p4_registers )
    h_mg.p4_nodes.update(h_s.p4_nodes )
    h_mg.p4_tables.update(h_s.p4_tables )
    h_mg.p4_action_profiles.update(h_s.p4_action_profiles  )
    h_mg.p4_action_selectors.update(h_s.p4_action_selectors )
    h_mg.p4_conditional_nodes.update(h_s.p4_conditional_nodes)

    h_mg.calculated_fields = h_s.calculated_fields

    h_mg.p4_ingress_ptr = h_s.p4_ingress_ptr
    h_mg.p4_egress_ptr = h_s.p4_egress_ptr
    h_mg.my_lists = h_s.my_lists


  ## 3. Merging each object of real program and h_meta
    ## TODO(low-priority): seperate each merge to single function 

    ### 3.X1 merge p4 fields
    '''All the header and metadata fields'''
    print 'LOG|MERGE|X1 p4 feilds:'
    h_mg.p4_fields.update(h_r.p4_fields)
    h_mg.p4_fields.update(h_meta.p4_fields)

    # 3.X2 merge p4 nodes
    print 'LOG|MERGE|X2 p4 nodes:'
    h_mg.p4_nodes.update(h_r.p4_nodes)
    h_mg.p4_nodes.update(h_meta.p4_nodes)

    # 3.X3 merge conditional nodes
    print 'LOG|MERGE|X3 p4_conditional_nodes:'
    h_mg.p4_conditional_nodes.update(h_r.p4_conditional_nodes)
    h_mg.p4_conditional_nodes.update(h_meta.p4_conditional_nodes)


    # 3.X4 merge calculated fields
    print 'LOG|MERGE|X4 calculated_fields'
    h_mg.calculated_fields.extend(h_meta.calculated_fields)
    h_mg.calculated_fields.extend(h_r.calculated_fields)
    print '            |Merged:', h_mg.calculated_fields

    # 3.X5 merge ingress ptr: moved to tables merging

    # 3.X6 merge egress ptr
    # ZP : this ptr should be the goto table of ShadowP4
    #      used to identify weather the traffic is of real or shadow
    print 'LOG|MERGE| X5 p4_egress_ptr'
    print h_mg.p4_egress_ptr
    print h_r.p4_egress_ptr


    ### 3.1 merge headers
    merge_headers(h_mg, h_r, h_meta)

    ### 3.2 merge header instances
    merge_header_instances(h_mg, h_r, h_meta)

    # 3.3 merge fields lists
    print 'LOG|MERGE|3 p4 feilds lists:'
    # ZP: this contains only one: ipv4_checksum_list
    h_mg.p4_field_lists.update(h_r.p4_field_lists)

    # 3.4 merge fields lists calculations
    print 'LOG|MERGE|4 p4_field_list_calculations:'
    h_mg.p4_field_list_calculations.update(h_r.p4_field_list_calculations)


    ### 3.5 merge action 
    merge_header_actions(h_mg, h_r, h_meta)

    # 3.6 merge p4 action selectors
    # ZP: null
    print 'LOG|MERGE|6 p4_action_selectors:'
    h_mg.p4_action_selectors.update(h_r.p4_action_selectors)

    # 3.7 merge action profiles
    print 'LOG|MERGE|7 action profiles:'
    # ZP: null
    h_mg.p4_action_profiles.update(h_mg.p4_action_profiles)


    # 3.8 merge p4 tables
    AB_merge_p4_tables(h_mg, h_r, h_meta)


    # 3.9 merge counters
    print 'LOG|MERGE|9 counters'
    h_mg.p4_counters.update(h_r.p4_counters)

    # 3.10 merge meter
    print 'LOG|MERGE|10 meters'
    h_mg.p4_meters.update(h_r.p4_meters)


    # 3.11 merge register
    print 'LOG|MERGE|11 register'
    h_mg.p4_registers.update(h_r.p4_registers)


    ### 3.12 merge control flows
    print 'LOG|MERGE|12 control flows'
    # TODO: double-check here: nothing to do
    print '    shadow control flow:', type(h_mg.p4_control_flows['egress'])
    pprint(vars(h_mg.p4_control_flows['ingress']))
    pprint(vars(h_mg.p4_control_flows['egress']))


    # 3.13 merge parse value sets
    # ZP: null
    print 'LOG|MERGE|13 p4_parse_value_sets:'
    h_mg.p4_parse_value_sets.update(h_r.p4_parse_value_sets)


    # 3.14 merge parse states
    print 'LOG|MERGE|14 p4_parse_states:'
    merge_parser_states(h_mg, h_r, h_meta)

    # 3.15 merge parser exceptions
    # ZP: null
    print 'LOG|MERGE|15 parser exceptions:'
    h_mg.p4_parser_exceptions.update(h_r.p4_parser_exceptions)

    return h_mg




#---------------------------------------------------------#
#---------------------- diff testing ---------------------#
#---------------------------------------------------------#

def DF_set_nodes_with_next_none(entry, visited, next_set_state):
    visited.add(entry)
    for e in entry.next_:
        if entry.next_[e] == None:
            entry.next_[e] = next_set_state
        elif type(entry.next_[e]) is p4_hlir.hlir.p4_tables.p4_table:
            if not entry.next_[e] in visited:
                DF_set_nodes_with_next_none(entry.next_[e], visited, next_set_state)
            pass
        elif type(entry.next_[e]) is p4_hlir.hlir.p4_tables.p4_conditional_node:
            if not entry.next_[e] in visited:
                DF_set_nodes_with_next_none(entry.next_[e], visited, next_set_state)
            pass
    return

def DF_merge_p4_tables_Original(h_mg, h_r, h_s, h_meta):
    print 'LOG|MERGE|8 p4 tables:'
    print 'LOG|MERGE|  Shadow  tables:', h_s.p4_tables.keys()
    print 'LOG|MERGE|  Product tables:', h_r.p4_tables.keys()
    print 'LOG|MERGE|  Metadata tables:', h_meta.p4_tables.keys()

    h_mg.p4_tables.update(h_r.p4_tables)
    h_mg.p4_tables.update(h_meta.p4_tables)

    print 'LOG|MERGE|  Merged  tables', h_mg.p4_tables.keys()
    print 'LOG|MERGE|  Merged  conditions', h_mg.p4_conditional_nodes.keys()
    # print 'LOG|MERGE|  Merged  conditions', printOrderedDict( h_mg.p4_conditional_nodes)
    print 'LOG|MERGE|  Merged  nodes', h_mg.p4_nodes.keys()

    assert(len(h_mg.p4_ingress_ptr) == 1)
    ingress_ptr_s = h_s.p4_ingress_ptr.keys()[0]
    ingress_ptr_r = h_r.p4_ingress_ptr.keys()[0]
    ingress_ptr_mg = h_mg.p4_ingress_ptr.keys()[0]
    
    print '    DBG in-/egress_ptr_r:', ingress_ptr_r.name, h_r.p4_egress_ptr
    print '    DBG in-/egress_ptr_s:', ingress_ptr_s.name, h_s.p4_egress_ptr
    print '    DBG in-/egress_ptr_m:', ingress_ptr_mg.name, h_mg.p4_egress_ptr

    # insert testing ingress pipeline
    print 'LOG|MERGE|8.1  Metadata conditions:', printOrderedDict(h_meta.p4_conditional_nodes)
    visited = set()
    DF_set_nodes_with_next_none(ingress_ptr_s, visited, h_mg.p4_nodes["record_shadow_result"])
    h_mg.p4_conditional_nodes["_condition_0"].next_[False] = h_mg.p4_nodes[ingress_ptr_s.name]

    # insert production ingress pipeline
    print 'LOG|MERGE|8.2  Nodes conditions:', printOrderedDict(h_r.p4_nodes)
    visited = set()
    DF_set_nodes_with_next_none(ingress_ptr_r, visited, h_mg.p4_nodes["_condition_1"])
    h_mg.p4_conditional_nodes["_condition_0"].next_[True] = h_mg.p4_nodes[ingress_ptr_r.name]

    # set shadow traffic control branch
    for e in h_mg.p4_tables["shadow_traffic_control"].next_:
        if e.name == 'SP4_remove_upvn' or e.name == 'goto_production_pipe':
            h_mg.p4_tables["shadow_traffic_control"].next_[e] = h_mg.p4_nodes[ingress_ptr_r.name]
        print 'LOG|MERGE|add STC nexts:', h_mg.p4_tables["shadow_traffic_control"].next_[e]
        pass

    ## egress merge
    egress_ptr_mg = h_mg.p4_egress_ptr

    egress_ptr_mg.next_[True] = h_s.p4_egress_ptr
    egress_ptr_mg.next_[False] = h_r.p4_egress_ptr
    
    return

def DF_merge_p4_tables(h_mg, h_r, h_s, h_meta):
	h_mg.p4_tables.update(h_meta.p4_tables)

def SP4_DF_merge_p4_objects(p4_v1_1, h_r, h_s, h_meta, virtual):
    ### The following is the merged HLIR

  ## 1. init merged hlir
    if p4_v1_1:
        from p4_hlir_v1_1.main import HLIR
        primitives_res = 'primitives_v1_1.json'
    else:
        from p4_hlir.main import HLIR
        primitives_res = 'primitives.json'
    h_mg = HLIR()
  

  #if it is not the first merging process, h_mg = h_s
    if 'upvn' in h_s.p4_header_instances:
	h_mg = h_s
    else:
  ## 2. add objects of shadow program
	    h_mg.p4_actions.update(h_s.p4_actions)       
	    h_mg.p4_control_flows.update(h_s.p4_control_flows)
	    h_mg.p4_headers.update(h_s.p4_headers )
	    h_mg.p4_header_instances.update(h_s.p4_header_instances )
	    h_mg.p4_fields.update(h_s.p4_fields )
	    h_mg.p4_field_lists.update(h_s.p4_field_lists )
	    h_mg.p4_field_list_calculations.update(h_s.p4_field_list_calculations )
	    h_mg.p4_parser_exceptions.update(h_s.p4_parser_exceptions )
	    h_mg.p4_parse_value_sets.update(h_s.p4_parse_value_sets)
	    h_mg.p4_parse_states.update(h_s.p4_parse_states )
	    h_mg.p4_counters.update(h_s.p4_counters)
	    h_mg.p4_meters.update(h_s.p4_meters)
	    h_mg.p4_registers.update(h_s.p4_registers )
	    h_mg.p4_nodes.update(h_s.p4_nodes )
	    h_mg.p4_tables.update(h_s.p4_tables )
	    h_mg.p4_action_profiles.update(h_s.p4_action_profiles  )
	    h_mg.p4_action_selectors.update(h_s.p4_action_selectors )
	    h_mg.p4_conditional_nodes.update(h_s.p4_conditional_nodes)

	    h_mg.calculated_fields = h_s.calculated_fields

	    h_mg.p4_ingress_ptr = h_meta.p4_ingress_ptr
	    h_mg.p4_egress_ptr = h_meta.p4_egress_ptr
	    h_mg.my_lists = h_s.my_lists


  ## 3. Merging each object of real program and h_meta
    ## TODO(low-priority): separate each merge to single function 

    ### 3.X1 merge p4 fields
    '''All the header and metadata fields'''
    # ZP: 5 fields added in the test case:
    # : ingress_metadata_SP4.test_packet_generate_rate
    # : ingress_metadata_SP4.real_packet_cnt_flag
    # : ingress_metadata_SP4.shadow_pkt_flag
    # : ingress_metadata_SP4._padding
    # : ipv4.flags_SP4 ipv4.flags_SP4
    print 'LOG|MERGE|X1 p4 fields:'
    h_mg.p4_fields.update(h_r.p4_fields)
    h_mg.p4_fields.update(h_meta.p4_fields)

    # 3.X2 merge p4 nodes
    print 'LOG|MERGE|X2 p4 nodes:'
    print 'LOG|MERGE|  Shadow nodes:', h_s.p4_nodes.keys()
    print 'LOG|MERGE|  Product nodes:', h_r.p4_nodes.keys()
    print 'LOG|MERGE|  Metadata nodes:', h_meta.p4_nodes.keys()

    h_mg.p4_nodes.update(h_r.p4_nodes)
    h_mg.p4_nodes.update(h_meta.p4_nodes)
    print 'LOG|MERGE|  Merged nodes:', h_mg.p4_nodes.keys()

    # 3.X3 merge conditional nodes
    print 'LOG|MERGE|X3 p4_conditional_nodes:'
    h_mg.p4_conditional_nodes.update(h_r.p4_conditional_nodes)
    h_mg.p4_conditional_nodes.update(h_meta.p4_conditional_nodes)

    # 3.X4 merge calculated fields
    print 'LOG|MERGE|X4 calculated_fields'
    h_mg.calculated_fields.extend(h_meta.calculated_fields)
    h_mg.calculated_fields.extend(h_r.calculated_fields)
    print '            |Merged:', h_mg.calculated_fields

    # 3.X5 merge ingress ptr: moved to tables merging

    # 3.X6 merge egress ptr done
    # ZP : this ptr should be the goto table of ShadowP4
    #      used to identify weather the traffic is of real or shadow
    print 'LOG|MERGE| X5 p4_egress_ptr'
    print h_mg.p4_egress_ptr
    print h_r.p4_egress_ptr


    ### 3.1 merge headers
    merge_headers(h_mg, h_r, h_meta)

    ### 3.2 merge header instances
    merge_header_instances(h_mg, h_r, h_meta)

    # 3.3 merge fields lists
    print 'LOG|MERGE|3 p4 fields lists:'
    # ZP: this contains only one: ipv4_checksum_list
    h_mg.p4_field_lists.update(h_r.p4_field_lists)

    # 3.4 merge fields lists calculations
    print 'LOG|MERGE|4 p4_field_list_calculations:'
    h_mg.p4_field_list_calculations.update(h_r.p4_field_list_calculations)


    ### 3.5 merge action 
    merge_header_actions(h_mg, h_r, h_meta)

    # 3.6 merge p4 action selectors
    # ZP: null
    print 'LOG|MERGE|6 p4_action_selectors:'
    h_mg.p4_action_selectors.update(h_r.p4_action_selectors)

    # 3.7 merge action profiles
    print 'LOG|MERGE|7 action profiles:'
    # ZP: null
    h_mg.p4_action_profiles.update(h_mg.p4_action_profiles)


    # 3.8 merge p4 tables
    DF_merge_p4_tables(h_mg, h_r, h_s, h_meta)


    # 3.9 merge counters-
    print 'LOG|MERGE|9 counters'
    h_mg.p4_counters.update(h_r.p4_counters)

    # 3.10 merge meter
    print 'LOG|MERGE|10 meters'
    h_mg.p4_meters.update(h_r.p4_meters)

    # 3.11 merge register
    print 'LOG|MERGE|11 register'
    h_mg.p4_registers.update(h_r.p4_registers)


    ### 3.12 merge control flows
    print 'LOG|MERGE|12 control flows'
    # TODO: double-check here: nothing to do
    print '    shadow control flow:', type(h_mg.p4_control_flows['egress'])
    pprint(vars(h_mg.p4_control_flows['ingress']))
    pprint(vars(h_mg.p4_control_flows['egress']))


    # 3.13 merge parse value sets
    # ZP: null
    print 'LOG|MERGE|13 p4_parse_value_sets:'
    h_mg.p4_parse_value_sets.update(h_r.p4_parse_value_sets)


    # 3.14 merge parse states
    print 'LOG|MERGE|14 p4_parse_states:'
    merge_parser_states(h_mg, h_r, h_meta, virtual)

    # 3.15 merge parser exceptions
    # ZP: null
    print 'LOG|MERGE|15 parser exceptions:'
    h_mg.p4_parser_exceptions.update(h_r.p4_parser_exceptions)

    return h_mg


class SP4_graph_nodes_edges(object):
    """docstring for SP4_get_graph_node_edges"""
    def __init__(self, arg):
        super(SP4_get_graph_node_edges, self).__init__()
        self.arg = arg
        
def SP4_get_graph_node_edges(graph):
    h_ingress_nodes_by_name = list(sorted(graph.nodes.values(),
                                key=lambda node: node.name))

    ## record map of table name and table id 
    h_ingress_id2name = {}
    h_ingress_ids = []
    h_ingress_edges = []
    # set conditional tables to be represented as boxes
    n_id = 1
    for node in h_ingress_nodes_by_name:
        node.id = n_id
        h_ingress_ids.append(n_id)
        h_ingress_id2name[node.name] = n_id
        print 'id = ', node.id, 'name = ',node.name

        node_label = node.name
        n_id = n_id + 1

    for node in h_ingress_nodes_by_name:
        node_tos_by_name = sorted(list(node.edges.keys()),
                                  key=lambda node: node.name)
        for node_to in node_tos_by_name:
            h_ingress_edges.append((node.id, node_to.id))
            print 'edge:', node.id, '->', node_to.id, node.name, '-->', node_to.name
            edge = node.edges[node_to]
            print '------'
            for each in list(node.edges.keys()):
                print each.name




# graph = dependency_graph.build_table_graph_ingress()
def generate_dot(graph, out = sys.stdout,
    show_control_flow = True,
                 show_condition_str = True,
                 show_fields = True,
                 earliest_time = None,
                 latest_time = None,
                 show_min_max_scheduled_times = False,
                 show_only_critical_dependencies = False,
                 forward_crit_path_edge_attr_name = None,
                 backward_crit_path_edge_attr_name = None):
    styles = {Dependency.CONTROL_FLOW: "style=dotted",
              Dependency.REVERSE_READ: "color=orange",
              Dependency.SUCCESSOR: "color=green",
              Dependency.ACTION: "color=blue",
              Dependency.MATCH: "color=red"}
    on_crit_path_style = "style=bold"
    off_crit_path_style = "style=dashed"
    out.write("digraph " + graph.name + " {\n")

    # The uses of the 'sorted' function below are not necessary
    # for correct behavior, but are done to try to make the
    # contents of the dot output file in a more consistent order
    # from one run of this program to the next.  By default,
    # Python dicts and sets can have their iteration order change
    # from one run of a program to the next because the hash
    # function changes from one run to the next.
    nodes_by_name = list(sorted(graph.nodes.values(),
                                key=lambda node: node.name))

    
    # set conditional tables to be represented as boxes
    # (i) get all the nodes
    for node in nodes_by_name:
        node_attrs = ""
        node_label = node.name
        if node.type_ == Node.CONDITION:
            node_attrs = " shape=box"
            if show_condition_str:
                node_label += (
                    "\\n" +
                    munge_condition_str(str(node.p4_node.condition)))
        if show_min_max_scheduled_times:
            early = "-"
            if earliest_time and node in earliest_time:
                early = "%s" % (earliest_time[node])
            late = "-"
            if latest_time and node in latest_time:
                late = "%s" % (latest_time[node])
            node_label += "\\n" + early + "," + late
        node_attrs += " label=\"" + node_label + "\""
        if show_min_max_scheduled_times:
            if early == late and early != "-":
                node_attrs += " style=bold"
            else:
                node_attrs += " style=dashed"
        out.write(node.name + " [" + node_attrs + "];\n")
    
    # (ii) get all the edges
    for node in nodes_by_name:
        node_tos_by_name = sorted(list(node.edges.keys()),
                                  key=lambda node: node.name)
        for node_to in node_tos_by_name:
            edge = node.edges[node_to]
            if not show_control_flow and edge.type_ == Dependency.CONTROL_FLOW:
                continue
            if show_only_critical_dependencies:
                fwd = edge.attributes.get(forward_crit_path_edge_attr_name,
                                          False)
                bkwd = edge.attributes.get(backward_crit_path_edge_attr_name,
                                           False)
                if not (fwd or bkwd):
                    continue
            
            edge_label = ""
            edge_attrs = ""
            if edge.type_ != Dependency.CONTROL_FLOW and show_fields:
                dep_fields = []
                # edge.dep can be None with my recent changes to
                # split tables into a separate match and action node,
                # because the edge between them has edge.dep of None.
                if edge.dep is not None:
                    for field in edge.dep.fields:
                        dep_fields.append(str(field))
                dep_fields = sorted(dep_fields)
                edge_label = ",\n".join(dep_fields)
                
            if edge.type_ == Dependency.SUCCESSOR:
                if isinstance(edge.dep.value, bool):
                    if edge_label != "":
                        edge_label += "\n"
                    if edge.dep.value == False:
                        edge_label += "False"
                        edge_attrs += " arrowhead = diamond"
                    else:
                        edge_label += "True"
                        #edge_attrs += " arrowhead = dot"
                elif isinstance(edge.dep.value, p4_imperatives.p4_action):
                    edge_label += edge.dep.value.name
                elif isinstance(edge.dep.value, tuple):
                    tmp_names = map(lambda v: v.name, edge.dep.value)
                    edge_label += ',\n'.join(tmp_names)
                else:
                    print("dbg successor type(edge.dep.value) %s"
                          " edge.dep.value=%s"
                          "" % (type(edge.dep.value), edge.dep.value))
                    assert False
            if show_only_critical_dependencies:
                if fwd and bkwd:
                    edge_attrs += " " + on_crit_path_style
                elif fwd:
                   # if edge_label != "":
                   #     edge_label = "\n" + edge_label
                   # edge_label = "f" + edge_label
                    pass
                elif bkwd:
                   # if edge_label != "":
                   #     edge_label = "\n" + edge_label
                   # edge_label = "b" + edge_label
                    pass
                else:
                    edge_attrs += " " + off_crit_path_style
            if edge_label != "":
                edge_attrs = ("label=\"" + edge_label + "\"" +
                              " decorate=true " + edge_attrs)
            out.write(node.name + " -> " + node_to.name +\
                      " [" + styles[edge.type_] + \
                      " " + edge_attrs + "]" + ";\n")
    
    out.write("}\n")


def _graph_get_or_add_node(graph, p4_node):
    node = graph.get_node(p4_node.name)
    if not node:
        if isinstance(p4_node, p4_hlir.hlir.p4_conditional_node):
            type_ = Node.CONDITION
        else:
            type_ = Node.TABLE
        node = Node(p4_node.name, type_, p4_node)
        graph.add_node(node)
    return node

def generate_graph(p4_root, name):
    graph = Graph(name)
    next_tables = {p4_root}
    visited = set()

    root_set = False

    while next_tables:
        nt = next_tables.pop()
        if nt in visited: continue
        if not nt: continue

        visited.add(nt)

        node = _graph_get_or_add_node(graph, nt)
        if not root_set:
            graph.set_root(node)
            root_set = True

        for table, dep in nt.dependencies_for.items():
            node_to = _graph_get_or_add_node(graph, table)
            edge = Edge(dep)
            node.add_edge(node_to, edge)

        next_ = set(nt.next_.values())
        for table in next_:
            if table and table not in nt.dependencies_for:
                node_to = _graph_get_or_add_node(graph, table)
                edge = Edge()
                node.add_edge(node_to, edge)

        next_tables.update(next_)
        
    return graph


# returns a rmt_table_graph object for ingress
def build_table_graph_ingress(hlir, split_match_action_events=False,
                              min_match_latency=None,
                              min_action_latency=None):
    if split_match_action_events:
        assert min_match_latency
        assert min_action_latency
        return generate_graph2(hlir.p4_ingress_ptr.keys()[0], "ingress",
                               min_match_latency, min_action_latency)
    else:
        return generate_graph(hlir.p4_ingress_ptr.keys()[0], "ingress")

# returns a rmt_table_graph object for egress
def build_table_graph_egress(hlir, split_match_action_events=False,
                             min_match_latency=None,
                             min_action_latency=None):
    if split_match_action_events:
        assert min_match_latency
        assert min_action_latency
        return generate_graph2(hlir.p4_egress_ptr, "egress",
                               min_match_latency, min_action_latency)
    else:
        return generate_graph(hlir.p4_egress_ptr, "egress")



