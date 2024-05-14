import argparse
import os
import shlex
import string
from multiprocessing import Pool
import sys


def generate_command(plus = True, server_exp = False):
    cmd_srvs = ""
    if server_exp:
        for n_s in [2,4,8]:
            cmd_srvs  += f"head -n {n_s+1} /local/Eiger-PORT/eval-scripts/vicci_dcl_config/16_clients_in_kodiak > /local/Eiger-PORT/eval-scripts/vicci_dcl_config/{n_s}_clients_in_kodiak_temp; mv /local/Eiger-PORT/eval-scripts/vicci_dcl_config/{n_s}_clients_in_kodiak_temp /local/Eiger-PORT/eval-scripts/vicci_dcl_config/{n_s}_clients_in_kodiak; head -n {n_s+1} /local/Eiger-PORT/eval-scripts/vicci_dcl_config/16_in_kodiak > /local/Eiger-PORT/eval-scripts/vicci_dcl_config/{n_s}_in_kodiak_temp; mv /local/Eiger-PORT/eval-scripts/vicci_dcl_config/{n_s}_in_kodiak_temp /local/Eiger-PORT/eval-scripts/vicci_dcl_config/{n_s}_in_kodiak ; "
        cmd_srvs += "cp /local/Eiger-PORT/eval-scripts/vicci_dcl_config/16_in_kodiak /local/Eiger-PORT/eval-scripts/vicci_dcl_config/32_in_kodiak ; cp /local/Eiger-PORT/eval-scripts/vicci_dcl_config/16_clients_in_kodiak /local/Eiger-PORT/eval-scripts/vicci_dcl_config/32_clients_in_kodiak ; "          
        for i in range(33,49):
            cmd_srvs +=  f"echo cassandra_ips=node{i} >> /local/Eiger-PORT/eval-scripts/vicci_dcl_config/32_in_kodiak ; "
        for i in range(49,65):
            cmd_srvs +=  f"echo cassandra_ips=node{i} >> /local/Eiger-PORT/eval-scripts/vicci_dcl_config/32_clients_in_kodiak ; "
        cmd_srvs += "sed -i 's/public static final int num_clients = 8;/public static final int num_clients = 16;/' /local/Eiger-PORT/Eiger-PORT/src/java/org/apache/cassandra/utils/LamportClock.java ; "

    if plus:
        cmd = " \" sudo usermod -s /bin/bash luca_mul ; cd /local ; sudo rm -r ./* ; git clone https://github.com/lucamul/EIGER-PORT-PLUS.git ; mv /local/EIGER_PORT/* /local ; sudo rm -r EIGER_PORT ; sed -i 's/node-/node/g' /local/Eiger-PORT/eval-scripts/vicci_dcl_config/16_clients_in_kodiak /local/Eiger-PORT/eval-scripts/vicci_dcl_config/16_in_kodiak ; " + cmd_srvs + "cd Eiger-PORT ; ./install-dependencies.bash ; cd Eiger-PORT ; ant ; ant ; ant ; ant; cd tools/stress ; ant ; cd ../../../eiger ; ant ; ant ; ant  ; ant ; cd tools/stress ; ant\""
    else:
        cmd = " \" sudo usermod -s /bin/bash luca_mul ; cd /local ; sudo rm -r ./* ; git clone https://github.com/princeton-sns/Eiger-PORT.git ; mv /local/EIGER_PORT/* /local ; sudo rm -r EIGER_PORT ; sed -i 's/node-/node/g' /local/Eiger-PORT/eval-scripts/vicci_dcl_config/16_clients_in_kodiak /local/Eiger-PORT/eval-scripts/vicci_dcl_config/16_in_kodiak ; " + cmd_srvs + "cd Eiger-PORT ; ./install-dependencies.bash ; cd Eiger-PORT ; ant ; ant ; ant ; ant; cd tools/stress ; ant ; cd ../../../eiger ; ant ; ant ; ant  ; ant ; cd tools/stress ; ant\""
    return cmd

def generate_setup_cmd(key):
    formatted_key = key.replace('\n', '').strip()
    escaped_key = formatted_key.replace('"', r'\"')

    cmd = f" \"mkdir -p ~/.ssh ; echo {escaped_key} >> ~/.ssh/authorized_keys ; chmod 700 ~/.ssh ; chmod 600 ~/.ssh/authorized_keys\""
    return cmd

def run_cmd(h,command):
    print(h)
    os.system("ssh -o StrictHostKeyChecking=no " + h + command)

def run_setup(h,command):
    username, domain = h.split("@")
    cmd = "ssh-keygen -f \"/home/luca/.ssh/known_hosts\" -R \"" +  domain + "\""
    os.system(cmd)
    os.system("ssh -o StrictHostKeyChecking=no " + h + command)

def setup(hosts, setup, plus, server_exp):
    if setup:
        username, domain = hosts[0].split("@")
        cmd = "ssh-keygen -f \"/home/luca/.ssh/known_hosts\" -R \"" +  domain + "\""
        
        os.system(cmd)

        os.system(f'ssh -o StrictHostKeyChecking=no {hosts[0]} \"ssh-keygen -t rsa -N \'\' -f ~/.ssh/id_rsa\"')
        key = os.popen(f'ssh -o StrictHostKeyChecking=no {hosts[0]} \"cat ~/.ssh/id_rsa.pub\"').read()
        cmd = generate_setup_cmd(key)
        with Pool(processes=len(hosts)-1) as pool:
            pool.starmap(run_setup, [(h,cmd) for h in hosts[1:]])
    else:
        cmd = generate_command(plus, server_exp)

        with Pool(processes=len(hosts)) as pool:
            pool.starmap(run_cmd, [(host, cmd) for host in hosts])

hosts_port = [ # enter nodes here
]

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Run Eiger-PORT')
    parser.add_argument('--setup', action='store_true', help='setup the hosts')
    parser.add_argument('--plus', action='store_true', help='use plus')
    parser.add_argument('--server_exp', action='store_true', help='use server_exp')
    
    args = parser.parse_args()

    setup(hosts_port, args.setup, args.plus, args.server_exp)
