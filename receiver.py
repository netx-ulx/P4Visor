# Set log level to benefit from Scapy warnings
import logging
logger = logging.getLogger("scapy")
logger.setLevel(logging.INFO)
logger.addHandler(logging.StreamHandler())
from collections import OrderedDict
from scapy.all import *
from binascii import hexlify
class Test(Packet):
    name = "Test packet"
    fields_desc = [ BitField("pvid", 2, 4),
                    BitField("p_map", 2, 20),
		  ]

def receive(name):
	translation = OrderedDict()
	translation_file = open('evaluation/translations/' + name + '_translation.txt', 'r')
	tmp_translation = translation_file.readlines()
	#del program id in first line (not used here)
	del tmp_translation[0]
	for line in tmp_translation:
		line = line.split(' ')
		id_r = line[1]
		id_mg = line[2]
		id_mg = id_mg[:len(id_mg)-1]
		translation[id_r] = id_mg

	original = open('evaluation/original_results/' + name + '_original_result.txt', 'r')
	# ['0 1\n', '0 1 2\n']
	original_pkt_list = original.readlines()
	# will be in this format: ['0 1', '0 1 2']
	original_pkt_list = [line[:len(line)-1] for line in original_pkt_list]
		

	# will be in this format: ['0 1', '0 1 2']
	merged_list = []

	packet_file = open('evaluation/packets/' + name + '_packets.txt' , 'r')
    	packets = packet_file.readlines()
    	packet_file.close()
	pkt_num = len(packets)

    	pkt_list = sniff(iface = 'veth3', count=pkt_num)	
	for pkt in pkt_list :
		pktHex = hexlify(str(pkt))
		hex_states = pktHex[1:5]
		states = format(int(hex_states, 16), 'b')
		states = states[::-1]
		answer = ''
		count = 0
		for char in states:
			if char == '1':
				answer= answer + str(count) + ' '
			count = count + 1
		answer = answer[:len(answer)]
		merged_list.append(answer) 

	print 'TESTING ISOLATION AND CORRECTNESS: \n'
	for i in range (len(original_pkt_list)):
		print 'Packet ' + str(i) 
		print 'Original states : ' + original_pkt_list[i]
		states_r = original_pkt_list[i].split(' ')
		del states_r[len(states_r)-1]
		print 'Merged states : ' + merged_list[i]
		states_mg = merged_list[i].split(' ')
		for j in range(len(states_r)):
			print states_r[j]+ ' should translate to: ' + translation[states_r[j]] 
			if translation[states_r[j]] not in states_mg:
				print 'FOUND ERROR IN PACKET : ' + str(i)
				return
			print translation[states_r[j]] + ' was visited. \n'
		print '\n'
	
	print 'All tests passed!'
	
	
if __name__ == "__main__":
    interact(mydict=globals(), mybanner="Receiver script for merged programs: type receive(*program_name*) to execute. \n"+
					 'E.g.: to test program flowlet.p4, type receive("flowlet")')
