// Template headers.p4 file for portKnockFirewall which includes:
// - ethernet, IP and TCP headers;
// - user-defined metadata to store register index and flow status for every processed packet.

header_type flow_metadata_t {
    fields {
	flow_status : 8;
	index : 16;
     }
}


metadata flow_metadata_t my_metadata;

header_type ethernet_t {
    fields {
        dstAddr : 48;
        srcAddr : 48;
        etherType : 16;
    }
}

header ethernet_t ethernet;

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

field_list l3_hash_fields {
    ipv4.srcAddr;
}

field_list_calculation src_ip_hash {
    input {
        l3_hash_fields;
    }
    algorithm : crc16;
    output_width : 16;
}

header_type tcp_t {
    fields {
        srcPort : 16;
        dstPort : 16;
        seqNo : 32;
        ackNo : 32;
        dataOffset : 4;
        res : 3;
	ecn : 3;
	ctrl : 6;
        window : 16;
        checksum : 16;
        urgentPtr : 16;
    }
}

header tcp_t tcp;
