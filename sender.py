# Set log level to benefit from Scapy warnings
import logging
logger = logging.getLogger("scapy")
logger.setLevel(logging.INFO)
logger.addHandler(logging.StreamHandler())

from scapy.all import *

class Upvn(Packet):
    name = "Upvn header"
    fields_desc = [ BitField("pvid", 0, 4),
                    BitField("p_map", 0, 20),
		  ]
class EasyRoute_Head(Packet):
    name = "First header in source route program"
    fields_desc = [ BitField("preamble", 0, 64),
                    BitField("num_valid", 1, 32),
		  ]

class EasyRoute_Port(Packet):
    name = "First header in source route program"
    fields_desc = [BitField("port", 2, 8)]

class CPU_header(Packet):
    name = "First header in simple router with ARP program"
    fields_desc = [ BitField("zeros", 0, 64),
                    BitField("reason", 2, 16),
                    BitField("port", 2, 16),
		  ]
class Mtag(Packet):
    name = "mtag header"
    fields_desc = [ BitField("up1", 0, 8),
                    BitField("up2", 0, 8),
                    BitField("down1", 0, 8),
		    BitField("down2", 0, 8),
		    BitField("type", 0, 16),
		  ]

class vpc(Packet):
   name = "mtag header"
   fields_desc = [ BitField("srcSw", 0, 48),
                    BitField("dstSw", 0, 48),
                    BitField("customer", 0, 32),
		    BitField("srcAddr", 0, 32),
		    BitField("dstAddr", 0, 32),	
		    BitField("etherType", 0, 16),
		  ]

class arp_rarp_ipv4(Packet):
    name = "mtag header"
    fields_desc = [ BitField("srcHwAddr", 0, 48),
                    BitField("srcProtoAddr", 0, 32),
                    BitField("dstHwAddr", 0, 48),
		    BitField("dstProtoAddr", 0, 32),		    
		  ]
def send(name):
    #empty metadata
    y = 0 

    #program id
    id_file = open('evaluation/translations/' + name + '_translation.txt' , 'r')
    lines = id_file.readlines()
    id_file.close()
    x = int(lines[0])

    packet_file = open('evaluation/packets/' + name + '_packets.txt' , 'r')
    packets = packet_file.readlines()
    packet_file.close()
    for line in packets:
        print 'Packet format: ' + line
	exec('p = ' + line)
	sendp(p, iface = 'veth1')


if __name__ == "__main__":
    interact(mydict=globals(), mybanner='Sender script for programs: type send("program_name") to execute. \n' +
					'E.g.: to test program flowlet.p4, type send("flowlet")')
