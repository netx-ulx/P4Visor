// From now on, logic of the egress pipeline

action send() {
  no_op();
}

action _drop() {
  drop();
}

table send_table {
    reads {
        standard_metadata.egress_port : exact;
    }
    actions {
	send;
        _drop;
    }
}

control egress {
  apply(send_table);
}
