# Eiger-PORT+
## 1. Background
Eiger-PORT+ presents an improvement over the Eiger-PORT algorithm (https://github.com/princeton-sns/Eiger-PORT). This codebase is built upon the original Eiger-PORT one, with modifications on the code where necessary, meaning the Eiger-PORT folder in this codebase presents an implementation of Eiger-PORT+.

## 2. System Requirements
The experiments were run using Emulab d170 nodes on Ubuntu 16.04 STD. Unless stated otherwise 16 clients and 16 servers were used, plus one node to run the code from.

## 3. Build
Everything can be built from setup_cluster.py:
 1. Insert the list of nodes of your cluster (extra node to run from in position 0 of the list, we 
 will call this node0). 
 2. Run the script as: ```python3 setup_cluster.py --setup``` to configure passwordless ssh in between every node.
  3. Run the script as:  ```python3 setup_cluster.py``` if you want to run the original Eiger-PORT
  4. Run the script as:  ```python3 setup_cluster.py --plus``` if you want to run Eiger-PORT+
  5. Run the script as:  ```python3 setup_cluster.py --server_exp``` if you want to run the number of servers experiments and hence you ware working with 64+1 total machines.

Steps 3, 4, 5 are mutually exclusive, i.e. once you run one of them run all the experiments you need and collect the data, then you can run another one. These steps will copy and build the code on the codebase, from that moment onwards everything should be run on the node0 in the cluster.

## 4. Run Experiments
1. On node0 to run the experiments change directory with ```cd /local/Eiger-PORT/eval-scripts/experiments```
2. Open ```latency_throughput.bash``` and edit it according to the experiment you want to perform
3. Run as: ```./latency_throughput.bash 16```
You will have to run the Eiger-PORT+ code then re-run setup_cluster to switch the node to Eiger-PORT.

**4.1 Number of Clients** \
In latency_throughput.bash
1. Uncomment
    ```#for thread in 2 4 8 16 32 64 128 256 512; do ```
2. Comment out
     ```for thread in 4; do```
3. run ```latency_throughput.bash 16```

**4.2 Latency vs. Throughput** \
Same as number of clients.

**4.3 Number of Servers** \
In latency_throughput.bash
1. Uncomment
    ```#for thread in 32; do ```
2. Comment out
     ```for thread in 4; do```
3. run ```latency_throughput.bash x``` where x is the number of server of the data point you're looking for.

**4.4 Zipfian Constant** \
In the dynamic_common file 
1. Delete
    ```data_file_name=$1_$2_$3_$4_$5_$6_$7_$8_$9+${10}+data ```
2. Write
     ``` data_file_name=$1_$2_$3_$4_$5_$6_$7_$8_$9_${10}+${13}+data``` \
\
In latency_throughput.bash
1. Delete
    ```#for thread in 4; do ```
2. Write
     ```for zipfian_constant in 0 0.7 0.8 0.9 0.99 1.1 1.2; do```

3. run ```latency_throughput.bash 16```

## 4. Process results
The results of your experiment will be in ```cd /local/Eiger-PORT/eval-scripts/experiments/dynamic```, the latest experiment is in a folder called latest. Copy the data processing scripts into the experiment folder, then edit process_latency.bash according to your experiment options, finally run calc_latency_throughput.bash to calculate latency and throughput. 

The results used in the publication can be found in ```results/paperResults``` as csv files.

## 5. More information
For more information please visit the original Eiger-PORT codebase which goes more into details.