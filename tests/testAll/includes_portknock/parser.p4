// Template parser.p4 file for portKnockFirewall

// This parses the protocols defined in ./headers.p4

#define ETHERTYPE_IPV4 0x0800


parser start {
    return parse_ethernet;
}

parser parse_ethernet {
    extract(ethernet);
    return select(latest.etherType) {
        ETHERTYPE_IPV4 : parse_ipv4;
        default: ingress;
    }
}


parser parse_ipv4 {
    extract(ipv4);
    return select(latest.protocol) {
        6 : parse_tcp;
        default: ingress;
    }
}

parser parse_tcp {
    extract(tcp);
    return ingress;
}

