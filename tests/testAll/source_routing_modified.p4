/*
Copyright 2013-present Barefoot Networks, Inc. 
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

header_type easyroute_head_t {
    fields {
        preamble: 64;
        num_valid: 32;
    }
}

header easyroute_head_t easyroute_head;

header_type ethernet_t {
    fields {
        dstAddr : 48;
        srcAddr : 48;
        etherType : 16;
    }
}
header ethernet_t ethernet;

header_type easyroute_port_t {
    fields {
        port: 8;
    }
}

header easyroute_port_t easyroute_port;
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
parser start {
    return select(current(0, 64)) {
        0: parse_head;
        default: parse_ethernet;
    }
}

parser parse_head {
    extract(easyroute_head);
    return select(latest.num_valid) {
        0: ingress;
        default: parse_port;
    }
}

parser parse_port {
    extract(easyroute_port);
    return ingress;
}
parser parse_ethernet {
    extract(ethernet);
    return select(ethernet.etherType){
	0x800 : parse_ipv4;
	default : ingress;
    }
}

parser parse_ipv4 {
    extract(ipv4);
    return ingress;
}


action _drop() {
    drop();
}

action route() {
    modify_field(standard_metadata.egress_spec, easyroute_port.port);
    add_to_field(easyroute_head.num_valid, -1);
    remove_header(easyroute_port);
}

table route_pkt {
    reads {
        easyroute_port: valid;
    }
    actions {
        _drop;
        route;
    }
    size: 1;
}

control ingress {
    apply(route_pkt);
}

control egress {
    // leave empty
}
