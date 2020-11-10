// This is P4 sample source for portKnockFirewall

#include "includes_portknock/headers.p4"
#include "includes_portknock/parser.p4"
#include "includes_portknock/egress.p4"


#define REGISTER_SIZE 512

// the program uses a register to keep information about the status of each flow
register flow_status {
    width : 8;
    instance_count : REGISTER_SIZE;
}


action load_state() {
    modify_field_with_hash_based_offset(my_metadata.index,0,src_ip_hash,REGISTER_SIZE);
    register_read(my_metadata.flow_status, flow_status, my_metadata.index);
}

action forward_or_drop(next_state, egress_spec) {
    register_write(flow_status, my_metadata.index, next_state);
    modify_field(standard_metadata.egress_spec, egress_spec);
}

table state_table {
    actions {
      load_state;
    }
}

table transition_table {
    reads {
	  my_metadata.flow_status : exact;
	  tcp.dstPort : ternary;
    }
    actions {
	  forward_or_drop;
    }
}

control ingress {
    // load the status in which this specific flow is
    apply(state_table);
    // according to the status and the tcp dst port, apply a transition
    apply(transition_table);
}

