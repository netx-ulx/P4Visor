# Set log level to benefit from Scapy warnings
import logging
logger = logging.getLogger("scapy")
logger.setLevel(logging.INFO)
logger.addHandler(logging.StreamHandler())

from scapy.all import *
from binascii import hexlify


def receive(name):
        packet_file = open('evaluation/packets/' + name + '_packets.txt' , 'r')
    	packets = packet_file.readlines()
    	packet_file.close()
	pkt_num = len(packets)
    	pkt_list = sniff(iface = 'veth3', count= pkt_num)	
	shadow_file = open('evaluation/original_results/' + name +'_original_result.txt', 'w')
	for pkt in pkt_list :
		pktHex = hexlify(str(pkt))
		hex_tables = pktHex[1:5]
		tables = format(int(hex_tables, 16), 'b')
		tables = tables[::-1]
		count = 0
		answer = ''
		for char in tables:
			if char == '1':
				answer= answer + str(count) + ' '
			count = count + 1
		shadow_file.write(answer +'\n')
	shadow_file.close() 	
	
if __name__ == "__main__":
    interact(mydict=globals(), mybanner="Receiver script for shadow programs: type receive(*program_name*) to execute. \n"+
					 'E.g.: to test program flowlet.p4, type receive("flowlet")')
