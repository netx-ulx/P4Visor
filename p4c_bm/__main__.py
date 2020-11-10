# Copyright Brown University & Xi'an Jiaotong University
# 
# Licensed under the Apache License, Version 2.0 (the "License");
#
# Author: Peng Zheng
# Email:  zeepean@gmail.com
#

# -*- coding: utf-8 -*-

import argparse
import os
import sys
import gen_json
import gen_pd
import json
from itertools import permutations
from random import randrange
import datetime
from collections import OrderedDict
from pkg_resources import resource_string
import version
from copy import deepcopy
from pprint import pprint
from p4_hlir.hlir import table_dependency
from p4_hlir.hlir import p4_tables
from p4_hlir.graphs import dependency_graph

import p4_hlir.graphs.hlir_info as info
import p4_hlir.graphs.dot as dot
import SP4_merge

import numpy as np
import matplotlib as mpl 
import matplotlib.pyplot as plt 

def get_parser():
    parser = argparse.ArgumentParser(description='P4Visor compiler bmv2 arguments')
    parser.add_argument('--real_source', metavar='source', type=str,
                        help='A source file to include in the P4 program.')

    parser.add_argument('--shadow_source', dest='shadow_source', type=str,
                        help='A shadow P4 program source file to merge.',
                        required=False)

    parser.add_argument('--json_s', dest='json_s', type=str,
                        help='Dump the JSON representation to shdow P4 file.',
                        required=False)

    parser.add_argument('--json_mg', dest='json_mg', type=str,
                        help='Dump the JSON representation to merged P4 file.',
                        required=False)

    parser.add_argument('-l', '--list', nargs = '*', required= False)
    
    parser.add_argument('--gen_dir', dest='gen_dir', type=str,
                        help='The dir for the generated shadow configure files and graphs.',
                        required=False)

    parser.add_argument('--json', dest='json', type=str,
                        help='Dump the JSON representation to production file.',
                        required=False)

    parser.add_argument('--gen-fig', action='store_true',
                        help='Generate the figures of parser and control flow ',
                        default=False)

    parser.add_argument('--AB-testing', action='store_true',
                        help='A-B testing compiler',
                        default=False)

    parser.add_argument('--Diff-testing', action='store_true',
                        help='Differential testing compiler',
                        default=False)

    parser.add_argument('--pd', dest='pd', type=str,
                        help='Generate PD C/C++ code for this P4 program'
                        ' in this directory. Directory must exist.',
                        required=False)
    parser.add_argument('--pd-from-json', action='store_true',
                        help='Generate PD from a JSON file, not a P4 file',
                        default=False)
    parser.add_argument('--p4-prefix', type=str,
                        help='P4 name use for API function prefix',
                        default="prog", required=False)
    parser.add_argument('--field-aliases', type=str,
                        help='Path to file containing field aliases. '
                        'In this file, each line contains a mapping with this '
                        'format: "<alias> <full name of field>"',
                        required=False)
    parser.add_argument('--p4-v1.1', action='store_true',
                        help='Run the compiler on a p4 v1.1 program',
                        default=False, required=False)
    parser.add_argument('--version', '-v', action='version',
                        version=version.get_version_str())
    parser.add_argument('--primitives', action='append', default=[],
                        help="A JSON file which contains additional primitive \
                        declarations")
    parser.add_argument('--plugin', dest='plugin_list', action="append",
                        default=[],
                        help="list of plugins to generate templates")
    # parser.add_argument('--openflow-mapping-dir',
    #                     help="Directory of openflow mapping files")
    # parser.add_argument('--openflow-mapping-mod',
    #                     help="Openflow mapping module name -- not a file name")
    parser.add_argument('--keep-pragmas', action='store_true',
                        help="Propagate pragmas to JSON file when applicable",
                        default=False)
    return parser


# to be used for a destination file
def _validate_path(path):
    path = os.path.abspath(path)
    if not os.path.isdir(os.path.dirname(path)):
        print path, "is not a valid path because",\
            os.path.dirname(path), "is not a valid directory"
        sys.exit(1)
    if os.path.exists(path) and not os.path.isfile(path):
        print path, "exists and is not a file"
        sys.exit(1)
    return path


# to be used for a source file
def _validate_file(path):
    path = _validate_path(path)
    if not os.path.exists(path):
        print path, "does not exist"
        sys.exit(1)
    return path


def _validate_dir(path):
    path = os.path.abspath(path)
    if not os.path.isdir(path):
        print path, "is not a valid directory"
        sys.exit(1)
    return path

def _get_p4_basename(p4_source):
    return os.path.splitext(os.path.basename(p4_source))[0]


# print the graph, start from one table
def print_graph(entry, tab = ""):
    for k, next_table in entry.next_.items():
        print tab, entry, "---", k, "--->", next_table
        if next_table: print_graph(next_table, tab + "  ")

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
def build_table_graph_ingress(hlir):
    return generate_graph(hlir.p4_ingress_ptr.keys()[0], "ingress")

# returns a rmt_table_graph object for egress
def build_table_graph_egress(hlir):
    return generate_graph(hlir.p4_egress_ptr, "egress")

def build_hlir(hlir, preprocessor_args, args):
	from p4_hlir.main import HLIR
        primitives_res = 'primitives.json'
	# if no -D__TARGET_* flag defined, we add a default bmv2 one
	if True not in map(lambda f: "-D__TARGET_" in f, preprocessor_args):
		hlir.add_preprocessor_args("-D__TARGET_BMV2__")
	for parg in preprocessor_args:
		hlir.add_preprocessor_args(parg)

	# in addition to standard P4 primitives
	more_primitives = json.loads(resource_string(__name__, primitives_res))
	hlir.add_primitives(more_primitives)

	# user-provided primitives
	for primitive_path in args.primitives:
		_validate_file(primitive_path)
		with open(primitive_path, 'r') as f:
			hlir.add_primitives(json.load(f))

	if not hlir.build(analyze=False, program_version=10000):
		print "Error while building real P4 HLIR"
		sys.exit(1)

	return hlir

def merge_sequence(sequence, preprocessor_args, args, dir_path):
	from p4_hlir.main import HLIR
	h_meta = HLIR(dir_path)
	h_meta = build_hlir(h_meta, preprocessor_args, args)

	h_s = HLIR(sequence[0])
	h_s = build_hlir(h_s, preprocessor_args, args)

	h_r = HLIR(sequence[1])
	h_r = build_hlir(h_r, preprocessor_args, args)

	# create first merge
	h_mg = SP4_merge.SP4_DF_merge_p4_objects(False, h_r, h_s, h_meta, '')
	pvid = 2
	for name in sequence[2:]:
		hlir = HLIR(name)
		hlir = build_hlir(hlir, preprocessor_args, args)
		h_mg = SP4_merge.SP4_DF_merge_p4_objects(False, hlir, h_mg, h_meta, str(pvid))
		pvid = pvid + 1
	
	#delete duplicate transitions
	for key, state in h_mg.p4_parse_states.items():
		SP4_merge.delete_transitions_and_id(state)
		
	SP4_merge.delete_virtual_parser(h_mg)
	SP4_merge.add_set_metadata(h_mg)

	total_mg, select_max_mg, select_min_mg, transitions_mg , states_mg, headers_mg = SP4_merge.get_eval(h_mg)
	return transitions_mg

def print_all_select_entries(h_mg):
	import p4_hlir
	default = p4_hlir.hlir.p4_parser.P4_DEFAULT
	print_file = open('select_entries.txt', 'w')
	for name, state in h_mg.p4_parse_states.items():
		print_file.write('--------' + name + '---------- \n')
		for key, next_state in state.branch_to.items():
			if key == default:
				print_file.write(key.value + ' ---------> ' + next_state.name + '\n')
			else:
				print_file.write(str(key) + ' ---------> ' + next_state.name + '\n')
		print_file.write('\n')
	print_file.close()


def main():
    parser = get_parser()
    input_args = sys.argv[1:]
    args, unparsed_args = parser.parse_known_args()

    # parse preprocessor flags
    has_remaining_args = False
    preprocessor_args = []
    for a in unparsed_args:
        if a[:2] == "-D":
            input_args.remove(a)
            preprocessor_args.append(a)
        elif a[:2] == "-I":
            input_args.remove(a)
            preprocessor_args.append(a)
        else:
            has_remaining_args = True

    # trigger error
    if has_remaining_args:
        parser.parse_args(input_args)

    if args.json:
        path_json = _validate_path(args.json)

    if args.json_s:
        path_json_s = _validate_path(args.json_s)

    if args.json_mg:
        path_json_mg = _validate_path(args.json_mg)

    if args.field_aliases:
        path_field_aliases = _validate_file(args.field_aliases)
    else:
        path_field_aliases = None

    GEN_FIG = getattr(args, 'gen_fig')
    AB_T = getattr(args, 'AB_testing')
    DF_T = getattr(args, 'Diff_testing')
    if AB_T + DF_T == False:
        print "Please add args AB-testing or Diff-testing"
        sys.exit(1)
    if AB_T == True and DF_T == True:
        print "Please only use one args AB-testing or Diff-testing"
        sys.exit(1)
    p4_v1_1 = getattr(args, 'p4_v1.1')
    if p4_v1_1:
        try:
            import p4_hlir_v1_1  # NOQA
        except ImportError:  # pragma: no cover
            print "You requested P4 v1.1 but the corresponding p4-hlir",\
                "package does not seem to be installed"
            sys.exit(1)

    from_json = False
    if args.pd:
        path_pd = _validate_dir(args.pd)
        if args.pd_from_json:
            if not os.path.exists(args.source):
                print "Invalid JSON source"
                sys.exit(1)
            from_json = True

    if from_json:
        with open(args.source, 'r') as f:
            json_dict = json.load(f)
    else:
        if p4_v1_1:
            from p4_hlir_v1_1.main import HLIR
            primitives_res = 'primitives_v1_1.json'
        else:
            from p4_hlir.main import HLIR
            primitives_res = 'primitives.json'

    ## 0. build shadow meta HLIR and json
        dir_path = os.path.dirname(os.path.realpath(__file__)) 
        if AB_T:
            testing_case = 1
            dir_path = dir_path + '/SP4_metas_ab.p4'
            print 'LOG|read AB testing meta', dir_path
            h_meta = HLIR(dir_path)
        elif DF_T:
            testing_case = 2
            dir_path = dir_path + '/SP4_metas_diff.p4'
            print 'LOG|read Diff testing meta', dir_path
            h_meta = HLIR(dir_path)
        # if no -D__TARGET_* flag defined, we add a default bmv2 one
        if True not in map(lambda f: "-D__TARGET_" in f, preprocessor_args):
            h_meta.add_preprocessor_args("-D__TARGET_BMV2__")
        for parg in preprocessor_args:
            h_meta.add_preprocessor_args(parg)

        # in addition to standard P4 primitives
        more_primitives = json.loads(resource_string(__name__, primitives_res))
        h_meta.add_primitives(more_primitives)
        if AB_T:
            if not h_meta.build_shadow_metadata_AB(analyze=False):
                print "ERR|p4c_bm|main|Error while building shadow metadata HLIR"
                sys.exit(1)
        if DF_T:
            if not h_meta.build_shadow_metadata_DF(analyze=False):
                print "ERR|p4c_bm|main|Error while building shadow metadata HLIR"
                sys.exit(1)
        
	
    ## 1. build production program HLIR and json
        h_r = HLIR(args.real_source)

        # if no -D__TARGET_* flag defined, we add a default bmv2 one
        if True not in map(lambda f: "-D__TARGET_" in f, preprocessor_args):
            h_r.add_preprocessor_args("-D__TARGET_BMV2__")
        for parg in preprocessor_args:
            h_r.add_preprocessor_args(parg)

        # in addition to standard P4 primitives
        more_primitives = json.loads(resource_string(__name__, primitives_res))
        h_r.add_primitives(more_primitives)

        # user-provided primitives
        for primitive_path in args.primitives:
            _validate_file(primitive_path)
            with open(primitive_path, 'r') as f:
                h_r.add_primitives(json.load(f))

        if not h_r.build(analyze=False, program_version=10000):
            print "Error while building real P4 HLIR"
            sys.exit(1)
	 
        OPT_generate_real_json = True
        if OPT_generate_real_json:
            json_dict = gen_json.json_dict_create(h_r, path_field_aliases, p4_v1_1,
                                                args.keep_pragmas)

            if args.json:
                print "OPT|MAIN|Generating real P4 json output to", path_json
                with open(path_json, 'w') as fp:
                    json.dump(json_dict, fp, indent=4, separators=(',', ': '))

        OPT_generate_real_graph = GEN_FIG
        if OPT_generate_real_graph:
            ## generate graphs
            OPT_gen_graph_parser = True
            OPT_gen_graph_table = True
            OPT_gen_graph_deps = True
            basename = _get_p4_basename(args.real_source)
            gen_dir = args.gen_dir
            print "Generating files in directory", gen_dir            
            if OPT_gen_graph_parser:
                dot.export_parse_graph(h_r, basename, gen_dir, no_dot=True)
            if OPT_gen_graph_table:
                dot.export_table_graph(h_r, basename, gen_dir, predecessors=False, no_dot=True)
            if OPT_gen_graph_deps:
                dot.export_table_dependency_graph(h_r, basename, gen_dir, show_conds = True, no_dot=True)

	#Create file with preliminar ids for h_r states
	h_r_translation_name = args.real_source.split('/')[2]
	h_r_translation_name = h_r_translation_name[:len( h_r_translation_name)-3]
	h_r_translation_name = 'evaluation/translations/' + h_r_translation_name + '_translation.txt'
	
	h_r_f = open(h_r_translation_name, "w") 
	r_id = 0
	h_r_f.write(str(15) + '\n')
	for name, state in h_r.p4_parse_states.items():
		if name == 'start':
			continue
		h_r_f.write(name + ' ' + str(r_id) + '\n')
		r_id = r_id + 1
	
	h_r_f.close()
	


	#TEST BUILD 1:
	# BUILD H_R2 USING SAME SOURCE FROM H_R
	hlir_list = []
	tmp_pvid = 2
	
	if args.list:
		for p_name in args.list:
			hlir = HLIR(p_name)

			# if no -D__TARGET_* flag defined, we add a default bmv2 one
			if True not in map(lambda f: "-D__TARGET_" in f, preprocessor_args):
			    hlir.add_preprocessor_args("-D__TARGET_BMV2__")
			for parg in preprocessor_args:
			    hlir.add_preprocessor_args(parg)

			# in addition to standard P4 primitives
			more_primitives = json.loads(resource_string(__name__, primitives_res))
			hlir.add_primitives(more_primitives)

			# user-provided primitives
			for primitive_path in args.primitives:
			    _validate_file(primitive_path)
			    with open(primitive_path, 'r') as f:
				hlir.add_primitives(json.load(f))

			if not hlir.build(analyze=False, program_version=10000):
			    print "Error while building real P4 HLIR"
			    sys.exit(1)

			hlir_list.append(hlir)
  			
			#Create _translation file
			h_diff_translation_name = p_name.split('/')[2]
			h_diff_translation_name = h_diff_translation_name[:len( h_diff_translation_name)-3]
			h_diff_translation_name = 'evaluation/translations/' + h_diff_translation_name + '_translation.txt'
			h_diff_f = open(h_diff_translation_name, "w") 

			diff_id = 0
			h_diff_f.write(str(tmp_pvid) + '\n')
			tmp_pvid = tmp_pvid + 1
			for name, state in hlir.p4_parse_states.items():
				if name == 'start':
					continue
				h_diff_f.write(name + ' ' + str(diff_id) + '\n')
				diff_id = diff_id + 1
			
			h_diff_f.close()
			
			



    ## 2. build testing program HLIR and json
        if args.shadow_source:
            h_s = HLIR(args.shadow_source) ## shadow hlir

            # if no -D__TARGET_* flag defined, we add a default bmv2 one
            if True not in map(lambda f: "-D__TARGET_" in f, preprocessor_args):
                h_s.add_preprocessor_args("-D__TARGET_BMV2__")
            for parg in preprocessor_args:
                h_s.add_preprocessor_args(parg)

            more_primitives = json.loads(resource_string(__name__, primitives_res))
            h_s.add_primitives(more_primitives)

            if not h_s.build(analyze=False, program_version=20000, config_dir=args.gen_dir):
                print "Error while building shadow P4 HLIR"
                sys.exit(1)

            OPT_generate_shadow_json = True
            if OPT_generate_shadow_json:
                json_dict_s = gen_json.json_dict_create(h_s, path_field_aliases, p4_v1_1,
                                                args.keep_pragmas)
                if args.json_s:
                    print "OPT|MAIN|Generating shadow P4 json output to", path_json_s
                    with open(path_json_s, 'w') as fp:
                        json.dump(json_dict_s, fp, indent=4, separators=(',', ': '))

            OPT_generate_shadow_graph = GEN_FIG
            if OPT_generate_shadow_graph:
                ## generate graphs
                gen_dir = args.gen_dir
                print "Generating files in directory", gen_dir
                OPT_gen_graph_parser = True
                OPT_gen_graph_table = True
                OPT_gen_graph_deps = True
                basename = _get_p4_basename(args.shadow_source)
                if OPT_gen_graph_parser:
                    dot.export_parse_graph(h_s, basename, gen_dir, no_dot=True)
                if OPT_gen_graph_table:
                    dot.export_table_graph(h_s, basename, gen_dir, predecessors=False, no_dot=True)
                if OPT_gen_graph_deps:
                    dot.export_table_dependency_graph(h_s, basename, gen_dir,
                                                    show_conds = True, no_dot=True)
            # return
	    #Create file with preliminar ids for h_r states
	    h_s_translation_name = args.shadow_source.split('/')[2]
	    h_s_translation_name = h_s_translation_name[:len( h_s_translation_name)-3]
	    h_s_translation_name = 'evaluation/translations/' + h_s_translation_name + '_translation.txt'
	
	    h_s_f = open(h_s_translation_name, "w") 
	    s_id = 0
	    h_s_f.write(str(1)+ '\n')
	    for name, state in h_s.p4_parse_states.items():
		    if name == 'start':
			    continue
		    h_s_f.write(name + ' ' + str(s_id) + '\n')
		    s_id = s_id + 1
	
	    h_s_f.close()


    ## 3. build dependency graph for the merged program


        ## 3.1.1 build real program ingress/egress graph
            h_r_ingress_graph = SP4_merge.build_table_graph_ingress(h_r)
            h_r_egress_graph = SP4_merge.build_table_graph_egress(h_r)   

            # DBG: print the dot file
            tmp_print_dot_file = False
            if tmp_print_dot_file:
                h_r_ingress_graph.generate_dot()

            ## 3.1.2 get real ingress/egress graph
            h_r_ingress_graph.SP4_gen_real_graph_node_edges(h_r)
            h_r_egress_graph.SP4_gen_real_graph_node_edges(h_r)

            ## 3.1.3 get shadow adj list
            h_r_ingress_graph.SP4_init_adj_list()
            h_r_egress_graph.SP4_init_adj_list()


        ## 3.2.1 build shadow program ingress/egress graph
            h_s_ingress_graph = SP4_merge.build_table_graph_ingress(h_s)
            h_s_egress_graph = SP4_merge.build_table_graph_egress(h_s) 

            ## 3.2.2 get shadow program ingress/egress graph
                  ## and calculate common structured graph
                  ## identify resued id to the reused tables
            h_s_ingress_graph.SP4_gen_shadow_graph_node_edges(h_s, h_r_ingress_graph, h_r)
            h_s_egress_graph.SP4_gen_shadow_graph_node_edges(h_s, h_r_egress_graph, h_r)

            ## 3.2.3 update shadow program reuse tables
            h_s_ingress_graph.SP4_reuse_id = h_r_ingress_graph.SP4_reuse_id
            h_s_egress_graph.SP4_reuse_id = h_r_egress_graph.SP4_reuse_id

            ## 3.2.4 get shadow adj list
            h_s_ingress_graph.SP4_init_adj_list()
            h_s_egress_graph.SP4_init_adj_list()


            ## DBG: get tables for each pipeline
            DBG_get_tables_for_pipeline = 0
            if DBG_get_tables_for_pipeline:        
                for each in h_r_ingress_graph.SP4_name2id:
                    # print each, 'the id is:', h_r_ingress_graph.SP4_name2id[each]
                    print each, 'the id is:', h_r_ingress_graph.nodes[each].id
                    print each, 'the type is:', h_r_ingress_graph.nodes[each].type_

                    if type(h.p4_nodes[each]) is p4_tables.p4_conditional_node:                                     
                        continue
                    print each, 'the width is:', h_r_ingress_graph.nodes[each].SP4_tb_width
                    print each, 'the depth is:', h_r_ingress_graph.nodes[each].SP4_tb_depth

            ## OPTION: print table resource info
            OPT_get_tables_summary = 1
            if OPT_get_tables_summary:  
                h_s_ingress_graph.SP4_get_table_info(h_s)
                print '    Shadow ingress:'
                h_s_ingress_graph.SP4_get_table_info_summary(h_s)

                h_s_egress_graph.SP4_get_table_info(h_s)
                print '    Shadow egress:'
                h_s_egress_graph.SP4_get_table_info_summary(h_s)


                h_r_ingress_graph.SP4_get_table_info(h_r)
                print '    real ingress:'
                h_r_ingress_graph.SP4_get_table_info_summary(h_r)

                h_r_egress_graph.SP4_get_table_info(h_r)
                print '    real egress:'
                h_r_egress_graph.SP4_get_table_info_summary(h_r)

            # return

        ## 3.3 get the WMIS graph

            ## DBG: checkout all the graph info before merge
            DBG_check_all_all_graph = 1
            if DBG_check_all_all_graph:
                print '\nDBG|MAIN|graph info: h_r:'      
                print h_r_ingress_graph.SP4_id2name
                print h_r_egress_graph.SP4_id2name

                print '\nDBG|MAIN|graph info: h_s:'
                print h_s_ingress_graph.SP4_id2name
                print
                print h_s_egress_graph.SP4_id2name

                print 'DBG|MAIN|h_r ingress reused tables:', h_r_ingress_graph.SP4_reuse_id
                print 'DBG|MAIN|h_r egress reused tables:', h_r_egress_graph.SP4_reuse_id


            h_s_ingress_graph.SP4_get_merged_graph(h_r_ingress_graph)
            h_s_egress_graph.SP4_get_merged_graph(h_r_egress_graph)

            ## DBG: checkout all the resued tables info
            DBG_check_all_all_graph = 1
            if DBG_check_all_all_graph:
                print '\n    bm main-009: reused tables:'
                print h_s_ingress_graph.SP4_reuse_id
                print h_s_egress_graph.SP4_reuse_id

                print '    bm main-010: merged graph'
                print h_s_ingress_graph.SP4_merged_graph_edges
                print h_s_egress_graph.SP4_merged_graph_edges

        ## 3.4 print the MWIS gragh to file and call hurestic alg.
            ## Report merging graph info
            print '\nLOG|MERGE|merging graph info:'
            print '          Prod ingress nodes num = ', len(h_r_ingress_graph.SP4_id2name), '  edges num = ', len(h_r_ingress_graph.SP4_edges)
            print '          Test ingress nodes num = ', len(h_s_ingress_graph.SP4_id2name), '  edges num = ', len(h_s_ingress_graph.SP4_edges)
            print '               ingress reused num = ', len(h_s_ingress_graph.SP4_reuse_id)
            print ' '
            print '          Prod engress nodes num = ', len(h_r_egress_graph.SP4_id2name), '  edges num = ', len(h_r_egress_graph.SP4_edges)
            print '          Test engress nodes num = ', len(h_s_egress_graph.SP4_id2name), '  edges num = ', len(h_s_egress_graph.SP4_edges)
            print '               egress reused num = ', len(h_s_egress_graph.SP4_reuse_id)


            ## 3.4.1 write to file
            ingress_out = 'ingress'
            egress_out  = 'egress'
            h_s_ingress_graph.SP4_write_graph_to_file(args.gen_dir, ingress_out, h_r_ingress_graph)
            h_s_egress_graph.SP4_write_graph_to_file(args.gen_dir, egress_out, h_r_egress_graph)

            ## 3.4.2 call the heuristic written by C
            print 'INFO|MAIN|call wmis:'
            gen_dir = args.gen_dir
            ingress_table_graph = os.path.join(gen_dir, "ingress_table_graph.csv")

            dir_path = os.path.dirname(os.path.realpath(__file__))
            dir_path_mwis = dir_path + '/../mwis/bin'

            # ingress_table_edge   = os.path.join(gen_dir, "ingress_table_edge.csv")
            ingress_res_file     = os.path.join(gen_dir, "ingress_wmis.res")
            cmd =  dir_path_mwis + '/mwis '+ingress_table_graph+' -o '+ingress_res_file + " >> /tmp/tmp.res"
            print cmd
            os.system(cmd)

            dir_path_mwis = dir_path + '/../mwis/GWMIN_alg/bin'
            cmd2 = dir_path_mwis + '/mwis '+ingress_table_graph+' '+ingress_res_file + " >> /tmp/tmp.res"
            print cmd2
            os.system(cmd2)
            # return

    ## 4.0 read heuristic result

            # read the heuristic result
            #file = open(ingress_res_file, "r") 
            #for each in file.readlines():
                #h_s_ingress_graph.SP4_merge_id.append(int(each))
            
            # TODO: fix the number later
            #h_s_egress_graph.SP4_merge_id.append(1)

            #if OPT_get_tables_summary:                
                #h_r_ingress_graph.SP4_reduce_reuse_tables(h_s)
	    first_time = datetime.datetime.now()
	    if False:
		    ## RUNNING ALL PERMUTATIONS FOR BEST MERGE SEQUENCE
		    prog_paths_list = []
		    if args.list:
		    	prog_paths_list = args.list
		    
		    prog_paths_list.append(args.shadow_source)
		    prog_paths_list.append(args.real_source)

		    #all possible permutations 
		    perms = list(permutations(prog_paths_list))
		    min_transitions = 1000000
		    best = ''
		    dir_path = dir_path + '/SP4_metas_diff.p4'
		    count = 1
		    for current in perms:
			current_file = open('current.txt', 'w')
			current_file.write(str(current))
			current_file.close()
		    	transitions = merge_sequence(current, preprocessor_args, args, dir_path)
			if transitions < min_transitions:
				min_transitions = transitions
				best = current
		    
		    best_merge_file = open('best_merge_sequence.txt', 'w')
		    best_merge_file.write(str(best)+'\n')
		    best_merge_file.write(str(min_transitions))
		    best_merge_file.close()

	    last_time = datetime.datetime.now()

	    if False:
		dir_path = dir_path + '/SP4_metas_diff.p4'
		prog_paths_list = []
		if args.list:
			prog_paths_list = args.list
		    
		prog_paths_list.append(args.shadow_source)
		prog_paths_list.append(args.real_source)
		average_transitions = open('average_transitions.txt','w')
		data_to_plot = []
		mpl.use('agg')
		#all possible permutations 
		perms = list(permutations(prog_paths_list))
		counter = 0
		for i in range(20):
			tmp_list = []
			for j in range(10):
				index = randrange(len(perms))
				transitions = merge_sequence(perms[index], preprocessor_args, args, dir_path)
				tmp_list.append(transitions)
				
			best_result = min(tmp_list)
			
			average_transitions.write('Best result in Test ' + str(counter) + ': ' + str(best_result) + 
								' transitions. \n')
			average_transitions.write('Average result in Test ' + str(counter) + ': ' + str( (sum(tmp_list) / len(tmp_list)) ) +
								' transitions. \n')
			average_transitions.write('Sample standard deviation in Test ' + str(counter) + ': ' + str(np.std(tmp_list, ddof=1)) + '\n')
			average_transitions.write('90th Percentile in Test '  + str(counter) + ': ' + str(np.percentile(tmp_list, 90)) + '\n')
			average_transitions.write('10th Percentile in Test '  + str(counter) + ': ' + str(np.percentile(tmp_list, 10)) + '\n \n')

			data_to_plot.append(tmp_list)
			
			counter = counter + 1
		average_transitions.close()
		# Create a figure instance
		fig = plt.figure(1, figsize=(9, 6))

		# Create an axes instance
		ax = fig.add_subplot(111)

		# Create the boxplot
		bp = ax.boxplot(data_to_plot)

		# Save the figure
		fig.savefig('box_plot.png', bbox_inches='tight')
					

    ## 5.0 merging hlir
            if AB_T:
                h_mg = SP4_merge.SP4_AB_merge_p4_objects(p4_v1_1, h_r, h_s, h_meta)
            elif DF_T:
		#EVALUATION METRICS FOR R AND S
		total_s, select_max_s, select_min_s, transitions_s , states_s, headers_s = SP4_merge.get_eval(h_s)		
		total_r, select_max_r, select_min_r, transitions_r , states_r, headers_r = SP4_merge.get_eval(h_r)


		
                h_mg = SP4_merge.SP4_DF_merge_p4_objects(p4_v1_1, h_r, h_s, h_meta, '')
		hlir_dict = OrderedDict()
		pvid = 2

		#EVALUATION METRICS FOR ADDITIONAL PROGRAMS
		for hlir in hlir_list:
			total_r2, select_max_r2, select_min_r2, transitions_r2 , states_r2, headers_r2 = SP4_merge.get_eval(hlir)
			hlir_dict[hlir] = (total_r2, select_max_r2, select_min_r2, transitions_r2 , states_r2, headers_r2)
			h_mg = SP4_merge.SP4_DF_merge_p4_objects(p4_v1_1, hlir, h_mg, h_meta, str(pvid))
			pvid += 1
		
		
		#delete duplicate transitions
	        for key, state in h_mg.p4_parse_states.items():
			SP4_merge.delete_transitions_and_id(state)
		
		SP4_merge.delete_virtual_parser(h_mg)
		SP4_merge.add_set_metadata(h_mg)
		
		
		difference = last_time - first_time
	    	time_file = open('time.txt','w')
		time_file.write(str(difference.total_seconds()))
		time_file.close()

		#EVALUATION METRICS - AFTER MERGE
		total_mg, select_max_mg, select_min_mg, transitions_mg , states_mg, headers_mg = SP4_merge.get_eval(h_mg)
		
		print_all_select_entries(h_mg)

		#add new id (id in merged program) of each state for h_r program
		r_file = open(h_r_translation_name, 'r')
		r_entries = r_file.readlines()
		r_file.close()
		new_r_file = open(h_r_translation_name, 'w')
		for line in r_entries:
 			if line == r_entries[0]:
				new_r_file.write(line)
				continue
			line = line[:len(line)-1]
			line = line.split(' ')
			state_mg = h_r.merged_map[line[0]]
			id_in_mg = h_mg.p4_parse_states[state_mg].id
			line.append(str(id_in_mg) +'\n')
			line = ' '.join(line)
			new_r_file.write(line)
		new_r_file.close()

		#add new id (id in merged program) of each state for h_s program
		s_file = open(h_s_translation_name, 'r')
		s_entries = s_file.readlines()
		s_file.close()
		new_s_file = open(h_s_translation_name, 'w')
		
		for line in s_entries:
 			if line == s_entries[0]:
				new_s_file.write(line)
				continue
			line = line[:len(line)-1]
			line = line.split(' ')
			id_in_mg = h_mg.p4_parse_states[line[0]].id
			line.append(str(id_in_mg) +'\n')
			line = ' '.join(line)
			new_s_file.write(line)
		new_s_file.close()
		
		#for each extra program, add new id (id in merged program)
		if args.list:
			for hlir in hlir_list:
           			p_name = hlir.source_files[0]
				h_diff_translation_name = p_name.split('/')[2]
				h_diff_translation_name = h_diff_translation_name[:len( h_diff_translation_name)-3]
				h_diff_translation_name = 'evaluation/translations/' + h_diff_translation_name + '_translation.txt'
				diff_file = open(h_diff_translation_name, 'r')
				diff_entries = diff_file.readlines()
				diff_file.close()
				new_diff_file = open(h_diff_translation_name, 'w')
				
				for line in diff_entries:
					if line == diff_entries[0]:
						new_diff_file.write(line)
						continue
					line = line[:len(line)-1]
					line = line.split(' ')
					mg_name = hlir.merged_map[line[0]]
					id_in_mg = h_mg.p4_parse_states[mg_name].id
					line.append(str(id_in_mg) +'\n')
					line = ' '.join(line)
					new_diff_file.write(line)
				new_diff_file.close()
		
		tmp = h_r.source_files[0]
		h_r_name = tmp.split('/')[2]

		tmp = h_s.source_files[0]
		h_s_name = tmp.split('/')[2]

		f = open("evalFinal.txt", "w")
    		f.write('BEFORE THE MERGE\n')	
    		f.write('----------------HEADERS-------------------- \n')
		f.write('Number of headers of program '+ h_s_name + ': ' + str(headers_s) + '\n')
    		f.write('Number of headers of program '+ h_r_name + ': ' + str(headers_r) + '\n')
		for hlir in hlir_list:
			tmp = hlir.source_files[0]
			hlir_name = tmp.split('/')[2]
			f.write('Number of headers of program '+ hlir_name + ': ' + str(hlir_dict[hlir][5]) + '\n')

            	f.write('----------------STATES--------------------- \n')
	        f.write('Number of states of program '+ h_s_name + ': ' + str(states_s) + '\n')
	        f.write('Number of states of program '+ h_r_name + ': ' + str(states_r) + '\n')
		for hlir in hlir_list:
			tmp = hlir.source_files[0]
			hlir_name = tmp.split('/')[2]
			f.write('Number of states of program '+ hlir_name + ': ' + str(hlir_dict[hlir][4]) + '\n')

	        f.write('--------------TRANSITIONS------------------ \n')
	        f.write('Number of transitions of program '+ h_s_name + ': ' + str(transitions_s) + '\n')
	        f.write('Number of transitions of program '+ h_r_name + ': ' + str(transitions_r) + '\n')
		for hlir in hlir_list:
			tmp = hlir.source_files[0]
			hlir_name = tmp.split('/')[2]
			f.write('Number of transitions of program '+ hlir_name + ': ' + str(hlir_dict[hlir][3]) + '\n')

		f.write('--------------SELECT SIZE------------------ \n')
		f.write('Max, min and average select width of program '+ h_s_name + ': ' + str(select_max_s) + ' | ' + str(select_min_s)+' | ' + str(total_s) + '\n')
		f.write('Max, min and average select width of program '+ h_r_name + ': ' + str(select_max_r) + ' | ' + str(select_min_r)+ ' | ' + str(total_r) +'\n')
		for hlir in hlir_list:
			tmp = hlir.source_files[0]
			hlir_name = tmp.split('/')[2]
			f.write('Max, min and average select width of program '+ hlir_name + ': ' + str(hlir_dict[hlir][1]) + ' | ' + str(hlir_dict[hlir][2])+ ' | ' + str(hlir_dict[hlir][0]) +'\n')

		f.write('\n \n\n\n')
		#######################################################

		f.write('AFTER THE MERGE\n')	
    		f.write('----------------HEADERS-------------------- \n')
		f.write('Number of headers of merged program: ' + str(headers_mg) + '\n')

            	f.write('----------------STATES--------------------- \n')
	        f.write('Number of states of merged program: ' + str(states_mg) + '\n')

	        f.write('--------------TRANSITIONS------------------ \n')
	        f.write('Number of transitions of merged program: ' + str(transitions_mg) + '\n')
		
		f.write('--------------SELECT SIZE------------------ \n')
		f.write('Max, min and average select width of merged program: ' + str(select_max_mg) + ' | ' + str(select_min_mg)+ ' | ' + str(total_mg) +  '\n')
		f.write('\n')
		f.write('STATE IDS: \n')
		state_id = 0
		for name, state in h_mg.p4_parse_states.items():
			if name == 'start' or name == 'parse_upvn':
				continue
			f.write(name + ' : ' + str(state_id) + '\n')
			state_id = state_id +1
		f.close()

	    json_dict_mg = gen_json.json_dict_create(h_mg, path_field_aliases, p4_v1_1,
                                              args.keep_pragmas)

            print "Generating MERGED P4 json output to", path_json_mg
            with open(path_json_mg, 'w') as fp:
                json.dump(json_dict_mg, fp, indent=4, separators=(',', ': '))

            OPT_generate_merge_graph = GEN_FIG
            if OPT_generate_merge_graph:
                ## generate graphs
                gen_dir = args.gen_dir
                print "Generating files in directory", gen_dir
                OPT_gen_graph_parser = True
                OPT_gen_graph_table = True
                OPT_gen_graph_deps = True
                basename = "merged_graph"
                if OPT_gen_graph_parser:
                    dot.export_parse_graph(h_mg, basename, gen_dir, no_dot=True)
                if OPT_gen_graph_table:
                    dot.export_table_graph(h_mg, basename, gen_dir, predecessors=False, no_dot=True)
                if OPT_gen_graph_deps:
                    dot.export_table_dependency_graph(h_s, basename, gen_dir,
                                                    show_conds = True, no_dot=True)

    if args.pd:
        print "Generating PD source files in", path_pd
        gen_pd.generate_pd_source(json_dict, path_pd, args.p4_prefix, args)


if __name__ == "__main__":  # pragma: no cover
    main()
