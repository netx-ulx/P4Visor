/*
# Copyright Brown University & Xi'an Jiaotong University
# 
# Licensed under the Apache License, Version 2.0 (the "License");
#
# Author: Peng Zheng
# Email:  zeepean@gmail.com
#*/
/***************************************************************
 * SP4 header
 ***************************************************************/

header_type upvn_t {
    fields {
        pvid : 4;
        p_map : 16;
    }
}

header_type upvn_metadata_t {
    fields {
        p_map : 16; 

    }
}


header_type intrinsic_metadata_t {
    fields {
        mcast_grp : 4;
        egress_rid : 4;
        mcast_hash : 16;
        lf_field_list : 32;
        resubmit_flag : 16;
        recirculate_flag : 8;
    }
}


header_type ethernet_t {
    fields {
        dstAddr : 48;
        srcAddr : 48;
        etherType : 16;
    }
}

header_type ipv4_t {
    fields {
        version : 4;
        ihl : 4;
        diffserv : 8;
        totalLen : 16;
        identification : 16;
        flags : 3;
        fragOffset : 13;
        ttl : 8;
        protocol : 8;
        hdrChecksum : 16;
        srcAddr : 32;
        dstAddr: 32;
    }
}
header ipv4_t ipv4;
/***************************************************************
 * SP4 header and header instance
 ***************************************************************/

header upvn_t upvn;

metadata upvn_metadata_t upvn_metadata;
metadata intrinsic_metadata_t intrinsic_metadata;


field_list shadow_recirculate_meta {
    upvn_metadata;
    standard_metadata;
}


/***************************************************************
 * SP4 parser
 ***************************************************************/

#define ETHERTYPE_SHADOW 0x8100 //0x0fff


header ethernet_t ethernet;

parser start {
    return parse_ethernet;
}

parser parse_ethernet {
    extract(ethernet);
    return select(latest.etherType) {
        // ETHERTYPE_IPV4 : parse_ipv4;
        ETHERTYPE_SHADOW : parse_upvn;
        default: ingress;
    }
}

// #define ETHERTYPE_IPV4 0x0800
parser parse_upvn {
    extract(upvn);
    return select(latest.pvid){
        default: ingress;
    }
}


action set_nhop(port) {
    modify_field(standard_metadata.egress_spec, port);
    modify_field(upvn.p_map, upvn_metadata.p_map);
}
/* This table used to mark specific real pkts to shadow pkts*/

table shadow_traffic_control {
  reads {
        standard_metadata.ingress_port : exact;
    }
    actions {
        set_nhop;
    }
    size: 1024;
}



control ingress {
    apply(shadow_traffic_control); // todo fix it: add bit to handle resubmited packet

    

}

control egress {
    
}
