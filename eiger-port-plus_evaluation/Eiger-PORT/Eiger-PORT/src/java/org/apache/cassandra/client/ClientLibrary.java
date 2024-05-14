package org.apache.cassandra.client;

import java.net.InetAddress;
import java.nio.ByteBuffer;
import java.nio.charset.CharacterCodingException;
import java.util.*;
import java.util.Map.Entry;

import org.apache.cassandra.db.IColumn;
import org.apache.cassandra.db.RowPosition;
import org.apache.cassandra.dht.*;
import org.apache.cassandra.hadoop.ConfigHelper;
import org.apache.cassandra.thrift.*;
import org.apache.cassandra.thrift.Cassandra.AsyncClient.batch_mutate_call;
import org.apache.cassandra.thrift.Cassandra.AsyncClient.get_range_slices_by_time_call;
import org.apache.cassandra.thrift.Cassandra.AsyncClient.get_range_slices_call;
import org.apache.cassandra.thrift.Cassandra.AsyncClient.multiget_count_by_time_call;
import org.apache.cassandra.thrift.Cassandra.AsyncClient.multiget_count_call;
import org.apache.cassandra.thrift.Cassandra.AsyncClient.multiget_slice_by_time_call;
import org.apache.cassandra.thrift.Cassandra.AsyncClient.multiget_slice_call;
import org.apache.cassandra.thrift.Cassandra.AsyncClient.set_keyspace_call;
import org.apache.cassandra.thrift.Cassandra.AsyncClient.transactional_batch_mutate_cohort_call;
import org.apache.cassandra.thrift.Cassandra.AsyncClient.transactional_batch_mutate_coordinator_call;
import org.apache.cassandra.utils.*;
import org.apache.cassandra.utils.ColumnOrSuperColumnHelper.EvtAndLvt;
import org.apache.hadoop.conf.Configuration;
import org.apache.thrift.TException;
import org.apache.thrift.async.TAsyncClientManager;
import org.apache.thrift.protocol.TBinaryProtocol;
import org.apache.thrift.protocol.TProtocol;
import org.apache.thrift.transport.*;

/**
 * This client library provide the extra functionality needed for COPS2.
 * Namely:
 * 1) Tracking and attaching dependencies for causal consistency.
 * 2) Read (get) transactions
 * 3) Write (put) transactions
 * <p>
 * This should be used instead of directly calling any thrift functions.
 *
 * @author wlloyd
 */
public class ClientLibrary {
    private final HashMap<InetAddress, Cassandra.Client> addressToClient = new HashMap<InetAddress, Cassandra.Client>();
    private final HashMap<InetAddress, Cassandra.AsyncClient> addressToAsyncClient = new HashMap<InetAddress, Cassandra.AsyncClient>();

    private final ClientContext clientContext = new ClientContext();
    private final ConsistencyLevel consistencyLevel;
    private final IPartitioner partitioner;
    private final RingCache ringCache;

    private final Random randomizer = new Random();

    // HL: get current thread id. client_id should be per client thread: nodeIP+thread_id. nodeIP alone is used for GC
    private final long client_thread;
    // assemble client_id
    private final long client_id;

    private Map<String, Integer> localServerIPAndPorts;
    private String keyspace;

    // keep track some stats
    /*
    private static final boolean COLLECT_STATS = true;
    private static final long PRINT_STATS_INTERVAL = 20000; // milliseconds

    private int numFirstRounds = 0;
    private int numFirstRoundRPCs = 0;

    private int numSecondRounds = 0;
    private int numSecondRoundKeys = 0;
    private int numSecondRoundRPCs = 0;

    private Long lastTime = null;

    private Long lastSingleWriteTime = null;
    private List<Long> writeLatencies = new ArrayList<Long>();
    private static final boolean COLLECT_SIMPLE_WRITE_LATENCY = true;
    private int numWrites = 0;
    */

    //private final Logger logger = LoggerFactory.getLogger(ClientLibrary.class);


    public ClientLibrary(Map<String, Integer> localServerIPAndPorts, String keyspace, ConsistencyLevel consistencyLevel)
            throws Exception {
        // if (logger.isTraceEnabled()) {
        //     logger.trace("ClientLibrary(localServerIPAndPorts = {}, keyspace = {}, consistencyLevel = {})", new Object[]{localServerIPAndPorts, keyspace, consistencyLevel});
        //}

        this.localServerIPAndPorts = localServerIPAndPorts;
        this.keyspace = keyspace;


        for (Entry<String, Integer> ipAndPort : localServerIPAndPorts.entrySet()) {
            String ip = ipAndPort.getKey();
            Integer port = ipAndPort.getValue();

            TTransport tFramedTransport = new TFramedTransport(new TSocket(ip, port));
            TProtocol binaryProtoOnFramed = new TBinaryProtocol(tFramedTransport);
            Cassandra.Client client = new Cassandra.Client(binaryProtoOnFramed);
            tFramedTransport.open();
            addressToClient.put(InetAddress.getByName(ip), client);

            TNonblockingTransport tNonblockingTransport = new TNonblockingSocket(ip, port);
            //TODO: 1 or many clientManagers?!?
            TAsyncClientManager clientManager = new TAsyncClientManager();
            Cassandra.AsyncClient asyncClient = new Cassandra.AsyncClient(new TBinaryProtocol.Factory(), clientManager, tNonblockingTransport);
            addressToAsyncClient.put(InetAddress.getByName(ip), asyncClient);

            // Set the keyspace for both synchronous and asynchronous clients
            client.set_keyspace(keyspace, LamportClock.sendTimestamp());

            BlockingQueueCallback<set_keyspace_call> callback = new BlockingQueueCallback<set_keyspace_call>();
            asyncClient.set_keyspace(keyspace, LamportClock.sendTimestamp(), callback);
            callback.getResponseNoInterruption();
        }

        String partitionerName = addressToClient.values().iterator().next().describe_partitioner();

        this.partitioner = FBUtilities.newPartitioner(partitionerName);

        Configuration conf = new Configuration();
        ConfigHelper.setOutputPartitioner(conf, partitionerName);
        ConfigHelper.setOutputInitialAddress(conf, localServerIPAndPorts.entrySet().iterator().next().getKey());
        ConfigHelper.setOutputRpcPort(conf, localServerIPAndPorts.entrySet().iterator().next().getValue().toString());
        ConfigHelper.setOutputColumnFamily(conf, keyspace, "ColumnFamilyEntryIgnored");
        this.ringCache = new RingCache(conf);

        this.consistencyLevel = consistencyLevel;

        // HL: initialize client_id
        client_thread = Thread.currentThread().getId();
        client_id = (LamportClock.nodeIP << 32) | (client_thread & 0xFFFFFFFF);
    }
    /*
    public void printStats() {
        System.err.println("STATS @ " + this.hashCode() + ": " + numFirstRounds + " " + numFirstRoundRPCs + " "
                + numSecondRounds + " " + numSecondRoundKeys + " " + numSecondRoundRPCs);
    }
    */
    private String printKey(ByteBuffer key) {
        try {
            return ByteBufferUtil.string(key) + "=" + ByteBufferUtil.bytesToHex(key);
        } catch (CharacterCodingException e) {
            return "????=" + ByteBufferUtil.bytesToHex(key);
        }
    }

    private String printKeys(Collection<ByteBuffer> keys) {
        StringBuilder sb = new StringBuilder("{");
        for (ByteBuffer key : keys) {
            sb.append(printKey(key));
            sb.append(", ");
        }
        sb.delete(sb.length() - 2, sb.length());
        sb.append("}");
        return sb.toString();
    }

    public void printWriteLatencies(List<Long> arr) {

        int l = arr.size();
        List<Long> trimmed = new ArrayList<Long>(arr.subList(l * 3 / 4, l * 31 / 32));

        l = trimmed.size();
        if (l == 0) return;

        Collections.sort(trimmed);

        String str = "";
        for (int i = 1; i < 100; i++) {
            str = str + i + "=" + trimmed.get((int) (l * i / 100.0)) + ",";
        }
        str = str + "99.9=" + trimmed.get((int) (l * 99.9 / 100.0));

        //System.err.println("WRITE LATENCY @ " + this.hashCode() + ": " + str);

    }

    /**
     * @param key
     * @return new thrift async client for this key; update the map addressToAsyncClient
     * @throws Exception
     */
    private Cassandra.AsyncClient createNewAsyncClient(ByteBuffer key) throws Exception {
        List<InetAddress> addrs = ringCache.getEndpoint(key);
        Cassandra.AsyncClient client = null;
        InetAddress localServerAddress = null;

        // Find the entry for the server responsible for this key
        // in the map addressToAsyncClient
        for (InetAddress addr : addrs) {
            if (addressToAsyncClient.containsKey(addr)) {
                //assert client == null : "We should only have 1 match for this key in the local datacenter";
                //client = addressToAsyncClient.get(addr);
                localServerAddress = addr;
                break;
            }
        }

        // Find the ip and port of the server to make new connection
        for (Entry<String, Integer> ipAndPort : localServerIPAndPorts.entrySet()) {
            String ip = ipAndPort.getKey();
            Integer port = ipAndPort.getValue();

            InetAddress addr = InetAddress.getByName(ip);

            // if there's no entry for localServerAddress
            // create a new one
            if (localServerAddress == null) {
                localServerAddress = addr;
            }

            // Create new thrift async client and update the map addressToAsyncClient
            if (localServerAddress.equals(addr)) {
                client = createNewAsyncClient(ip, port);
                // update map
                addressToAsyncClient.put(localServerAddress, client);
                break;

            }
        }
        return client;
    }

    /**
     * @param ip   address of the server for this async client to connect
     * @param port port of the server to make new connection
     * @return new thrift async client
     * @throws Exception
     */
    private Cassandra.AsyncClient createNewAsyncClient(String ip, Integer port) throws Exception {

        TNonblockingTransport tNonblockingTransport = new TNonblockingSocket(ip, port);
        //TODO: 1 or many clientManagers?!?
        TAsyncClientManager clientManager = new TAsyncClientManager();
        Cassandra.AsyncClient asyncClient = new Cassandra.AsyncClient(new TBinaryProtocol.Factory(), clientManager, tNonblockingTransport);
        addressToAsyncClient.put(InetAddress.getByName(ip), asyncClient);
        BlockingQueueCallback<set_keyspace_call> callback = new BlockingQueueCallback<set_keyspace_call>();
        asyncClient.set_keyspace(keyspace, LamportClock.sendTimestamp(), callback);
        callback.getResponseNoInterruption();

        return asyncClient;

    }

    // HL: find relevant server
    private String findServer(ByteBuffer key) {
        List<InetAddress> addrs = ringCache.getEndpoint(key);
        for (InetAddress addr : addrs) {
            String full_ip = addr.getHostName();
            String ip = full_ip.replace("-big-lan", "");    // ip is of the form: node-x
            if (localServerIPAndPorts.containsKey(ip)) {
                // this is a local server, is what we need
                return ip;
            }
        }
        assert false : "We should always be able to find a local server for this key.";
        return "";
    }

    private Cassandra.AsyncClient findAsyncClient(ByteBuffer key) {
        List<InetAddress> addrs = ringCache.getEndpoint(key);
        Cassandra.AsyncClient client = null;
        for (InetAddress addr : addrs) {
            if (addressToAsyncClient.containsKey(addr)) {
                assert client == null : "We should only have 1 match for this key in the local datacenter";
                client = addressToAsyncClient.get(addr);
            }
        }
        assert client != null : "There must be a match for this key in this datacenter";
        return client;
    }

    private Map<Cassandra.AsyncClient, List<ByteBuffer>> partitionByAsyncClients(Collection<ByteBuffer> keys) {
        Map<Cassandra.AsyncClient, List<ByteBuffer>> asyncClientToKeys = new HashMap<Cassandra.AsyncClient, List<ByteBuffer>>();
        for (ByteBuffer key : keys) {
            Cassandra.AsyncClient asyncClient = findAsyncClient(key);
            if (!asyncClientToKeys.containsKey(asyncClient)) {
                asyncClientToKeys.put(asyncClient, new ArrayList<ByteBuffer>());
            }
            asyncClientToKeys.get(asyncClient).add(key);
        }
        return asyncClientToKeys;
    }


    private Cassandra.Client findClient(ByteBuffer key) {
        List<InetAddress> addrs = ringCache.getEndpoint(key);
        Cassandra.Client client = null;
        for (InetAddress addr : addrs) {
            if (addressToClient.containsKey(addr)) {
                assert client == null : "We should only have 1 match for this key in the local datacenter";
                client = addressToClient.get(addr);
            }
        }
        assert client != null : "There must be a match for this key in this datacenter";
        return client;
    }

    public Cassandra.Client getAnyClient() {
        return addressToClient.values().iterator().next();
    }

    public ClientContext getContext() {
        return clientContext;
    }

    public List<ColumnOrSuperColumn> get_slice(ByteBuffer key, ColumnParent column_parent, SlicePredicate predicate)
            throws InvalidRequestException, UnavailableException, TimedOutException, TException {
        //if (logger.isTraceEnabled()) {
        //    logger.trace("get_slice(key = {}, column_parent = {}, predicate = {})", new Object[]{printKey(key),column_parent, predicate});
        //}

        GetSliceResult result = findClient(key).get_slice(key, column_parent, predicate, consistencyLevel, LamportClock.sendTimestamp());
        LamportClock.updateTime(result.lts);
        for (Iterator<ColumnOrSuperColumn> cosc_it = result.value.iterator(); cosc_it.hasNext(); ) {
            ColumnOrSuperColumn cosc = cosc_it.next();
            try {
                clientContext.addDep(key, cosc);
            } catch (NotFoundException nfe) {
                // we can get exceptions from recently deleted columns that
                // weren't included in the slice, let's remove them
                cosc_it.remove();

                // get_slice should return an empty list instead of throwing a
                // not found exception, so no need to worry about removing all
                // results
            }
        }
        //if (logger.isTraceEnabled()) {
        //    logger.trace("get_slice result = {}", result.value);
        //}
        return result.value;
    }

    private void substituteValidFirstRoundResults(MultigetSliceResult result, Map<ByteBuffer, List<ColumnOrSuperColumn>> firstRoundResults) {
        //Look for any results with 'first_round_was_valid' set and then
        //substitute in the first round results for them
        for (Entry<ByteBuffer, List<ColumnOrSuperColumn>> keyAndCoscList : result.value.entrySet()) {
            ByteBuffer key = keyAndCoscList.getKey();
            List<ColumnOrSuperColumn> coscList = keyAndCoscList.getValue();

            int coscListIndex = -1;
            for (ColumnOrSuperColumn cosc : coscList) {
                coscListIndex++;

                if (cosc.isSetColumn()) {
                    if (cosc.column.isSetFirst_round_was_valid() && cosc.column.first_round_was_valid) {
                        Column firstRoundColumn = firstRoundResults.get(key).get(coscListIndex).column;
                        assert ByteBufferUtil.bytesToHex(cosc.column.name).equals(ByteBufferUtil.bytesToHex(firstRoundColumn.name))
                                : "First and second round column names dont match" + ByteBufferUtil.bytesToHex(cosc.column.name)
                                + "!=" + ByteBufferUtil.bytesToHex(firstRoundColumn.name);
                        firstRoundColumn.latest_valid_time = cosc.column.latest_valid_time;
                        cosc.column = firstRoundColumn;
                    }
                } else if (cosc.isSetCounter_column() || cosc.isSetCounter_super_column()) {
                    //WL TODO Add this logic
                    assert false : "Not yet handled";
                } else {
                    assert cosc.isSetSuper_column();

                    int superColumnListIndex = -1;
                    for (Column column : cosc.super_column.columns) {
                        superColumnListIndex++;

                        if (column.isSetFirst_round_was_valid() && column.first_round_was_valid) {
                            Column firstRoundColumn = firstRoundResults.get(key).get(coscListIndex).super_column.getColumns().get(superColumnListIndex);
                            assert column.name == firstRoundColumn.name : "First and second round column names dont match" + column.name + "!=" + firstRoundColumn.name;

                            // Update the LVT of the firstRoundColumn to reflect its full validity interval
                            firstRoundColumn.latest_valid_time = column.latest_valid_time;
                            column = firstRoundColumn;
                        }
                    }
                }
            }
        }
    }


    public interface CopsTestingConcurrentWriteHook {
        void issueWrites();
    }

    public Map<ByteBuffer, List<ColumnOrSuperColumn>> transactional_multiget_slice(List<ByteBuffer> allKeys, ColumnParent column_parent, SlicePredicate predicate)
            throws Exception {
        return transactional_multiget_slice(allKeys, column_parent, predicate, null, null);
    }

    //this version is for testing only
    public Map<ByteBuffer, List<ColumnOrSuperColumn>> transactional_multiget_slice(List<ByteBuffer> allKeys, ColumnParent column_parent, SlicePredicate predicate, CopsTestingConcurrentWriteHook afterFirstReadWriteHook, CopsTestingConcurrentWriteHook afterFirstRoundWriteHook)
            throws Exception {
        //Split up into one request for each server in the local cluster
        Map<Cassandra.AsyncClient, List<ByteBuffer>> asyncClientToFirstRoundKeys = partitionByAsyncClients(allKeys);

        //Haonan: find the read_ts based on readTSMap, read_ts = GST = min of lst of *all* servers
        long read_ts = LamportClock.getReadTS();

        //Send read requests in parallel
        Queue<BlockingQueueCallback<multiget_slice_call>> firstRoundCallbacks = new LinkedList<BlockingQueueCallback<multiget_slice_call>>();
        for (Entry<Cassandra.AsyncClient, List<ByteBuffer>> entry : asyncClientToFirstRoundKeys.entrySet()) {
            Cassandra.AsyncClient asyncClient = entry.getKey();
            List<ByteBuffer> keysForThisClient = entry.getValue();

            BlockingQueueCallback<multiget_slice_call> callback = new BlockingQueueCallback<multiget_slice_call>();
            firstRoundCallbacks.add(callback);
            asyncClient.multiget_slice(keysForThisClient, column_parent, predicate, consistencyLevel, LamportClock.sendTimestamp(), read_ts, client_id, callback);
        }

        Map<ByteBuffer, List<ColumnOrSuperColumn>> keyToResult = new HashMap<ByteBuffer, List<ColumnOrSuperColumn>>();
        for (BlockingQueueCallback<multiget_slice_call> callback : firstRoundCallbacks) {
            MultigetSliceResult result = callback.getResponseNoInterruption().getResult();
            LamportClock.updateTime(result.lts);

            // update ReadTSMap
            // use first key, all keys in this callback should be from the same server.
            String server = findServer(result.value.keySet().iterator().next());
            LamportClock.updateReadTsMap(server, result.lst);

            for (Entry<ByteBuffer, List<ColumnOrSuperColumn>> entry : result.value.entrySet()) {
                ByteBuffer key = entry.getKey();
                List<ColumnOrSuperColumn> coscList = entry.getValue();
                keyToResult.put(key, coscList);
            }
        }

        //Add dependencies on anything returned and removed deleted columns
        for (Entry<ByteBuffer, List<ColumnOrSuperColumn>> entry : keyToResult.entrySet()) {
            ByteBuffer key = entry.getKey();
            List<ColumnOrSuperColumn> coscList = entry.getValue();

            for (Iterator<ColumnOrSuperColumn> cosc_it = coscList.iterator(); cosc_it.hasNext(); ) {
                ColumnOrSuperColumn cosc = cosc_it.next();
                try {
                    clientContext.addDep(key, cosc);
                } catch (NotFoundException nfe) {
                    //remove deleted results, it's okay for all result to be removed
                    cosc_it.remove();
                }
            }
        }

        // Haonan: note, we should NOT update readTS here.

        return keyToResult;
    }

    //this version is for micro-benchmarking only
    public Map<ByteBuffer, List<ColumnOrSuperColumn>> forced_2round_multiget_slice(List<ByteBuffer> allKeys, ColumnParent column_parent, SlicePredicate predicate)
            throws Exception {
        //if (logger.isTraceEnabled()) {
        //    logger.trace("forced_2round_multiget_slice(allKeys = {}, column_parent = {}, predicate = {})", new Object[]{printKeys(allKeys), column_parent, predicate});
        //}
        //Split up into one request for each server in the local cluster
        Map<Cassandra.AsyncClient, List<ByteBuffer>> asyncClientToFirstRoundKeys = partitionByAsyncClients(allKeys);

        //Send Round 1 Requests
        Queue<BlockingQueueCallback<multiget_slice_call>> firstRoundCallbacks = new LinkedList<BlockingQueueCallback<multiget_slice_call>>();
        for (Entry<Cassandra.AsyncClient, List<ByteBuffer>> entry : asyncClientToFirstRoundKeys.entrySet()) {
            Cassandra.AsyncClient asyncClient = entry.getKey();
            List<ByteBuffer> keysForThisClient = entry.getValue();

            BlockingQueueCallback<multiget_slice_call> callback = new BlockingQueueCallback<multiget_slice_call>();
            firstRoundCallbacks.add(callback);

            //if (logger.isTraceEnabled()) { logger.trace("round 1: get " + printKeys(keysForThisClient) + " from " + asyncClient); }
            asyncClient.multiget_slice(keysForThisClient, column_parent, predicate, consistencyLevel, LamportClock.sendTimestamp(), 0L, 0L, callback);
        }

        //Gather responses, track both max_evt and min_lvt
        long overallMaxEvt = Long.MIN_VALUE;
        long overallMinLvt = Long.MAX_VALUE;

        Map<ByteBuffer, List<ColumnOrSuperColumn>> keyToResult = new HashMap<ByteBuffer, List<ColumnOrSuperColumn>>();
        NavigableMap<Long, List<ByteBuffer>> lvtToKeys = new TreeMap<Long, List<ByteBuffer>>();
        for (BlockingQueueCallback<multiget_slice_call> callback : firstRoundCallbacks) {

            MultigetSliceResult result = callback.getResponseNoInterruption().getResult();
            LamportClock.updateTime(result.lts);

            for (Entry<ByteBuffer, List<ColumnOrSuperColumn>> entry : result.value.entrySet()) {
                ByteBuffer key = entry.getKey();
                List<ColumnOrSuperColumn> coscList = entry.getValue();
                keyToResult.put(key, coscList);

                //find the evt and lvt for the entire row
                EvtAndLvt evtAndLvt = ColumnOrSuperColumnHelper.extractEvtAndLvt(coscList);
                if (!lvtToKeys.containsKey(evtAndLvt.getLatestValidTime())) {
                    lvtToKeys.put(evtAndLvt.getLatestValidTime(), new LinkedList<ByteBuffer>());
                }
                lvtToKeys.get(evtAndLvt.getLatestValidTime()).add(key);
                //if (logger.isTraceEnabled()) { logger.trace("round 1 response for " + printKey(key) + " evt: " + evtAndLvt.getEarliestValidTime() + " lvt: " + evtAndLvt.getLatestValidTime()); }

                overallMaxEvt = Math.max(overallMaxEvt, evtAndLvt.getEarliestValidTime());
                overallMinLvt = Math.min(overallMinLvt, evtAndLvt.getLatestValidTime());
            }
        }
        //if (logger.isTraceEnabled()) { logger.trace("Min LVT:" + overallMinLvt + "  Max EVT: " + overallMaxEvt); }

        //Always Execute 2nd round for micro-benchmarking
        if (true) {
            //get the smallest lvt > maxEvt
            long chosenTime = lvtToKeys.navigableKeySet().higher(overallMaxEvt);

            List<ByteBuffer> secondRoundKeys = new LinkedList<ByteBuffer>();
            secondRoundKeys.addAll(allKeys);

            //Send Round 2 Requests
            Map<Cassandra.AsyncClient, List<ByteBuffer>> asyncClientToSecondRoundKeys = partitionByAsyncClients(secondRoundKeys);
            Queue<BlockingQueueCallback<multiget_slice_by_time_call>> secondRoundCallbacks = new LinkedList<BlockingQueueCallback<multiget_slice_by_time_call>>();
            for (Entry<Cassandra.AsyncClient, List<ByteBuffer>> entry : asyncClientToSecondRoundKeys.entrySet()) {
                Cassandra.AsyncClient asyncClient = entry.getKey();
                List<ByteBuffer> keysForThisClient = entry.getValue();

                BlockingQueueCallback<multiget_slice_by_time_call> callback = new BlockingQueueCallback<multiget_slice_by_time_call>();
                secondRoundCallbacks.add(callback);

                //if (logger.isTraceEnabled()) { logger.trace("round 2: get " + printKeys(keysForThisClient) + " from " + asyncClient); }

                asyncClient.multiget_slice_by_time(keysForThisClient, column_parent, predicate, consistencyLevel, chosenTime, LamportClock.sendTimestamp(), callback);
            }

            //Gather second round responses
            for (BlockingQueueCallback<multiget_slice_by_time_call> callback : secondRoundCallbacks) {
                MultigetSliceResult result = callback.getResponseNoInterruption().getResult();
                LamportClock.updateTime(result.lts);

                substituteValidFirstRoundResults(result, keyToResult);

                //if (logger.isTraceEnabled()) { logger.trace("round 2 responses for " + printKeys(result.getValue().keySet())); }

                keyToResult.putAll(result.getValue());
            }
        }

        //Add dependencies on anything returned and removed deleted columns
        for (Entry<ByteBuffer, List<ColumnOrSuperColumn>> entry : keyToResult.entrySet()) {
            ByteBuffer key = entry.getKey();
            List<ColumnOrSuperColumn> coscList = entry.getValue();

            for (Iterator<ColumnOrSuperColumn> cosc_it = coscList.iterator(); cosc_it.hasNext(); ) {
                ColumnOrSuperColumn cosc = cosc_it.next();
                try {
                    clientContext.addDep(key, cosc);
                } catch (NotFoundException nfe) {
                    //remove deleted results, it's okay for all result to be removed
                    cosc_it.remove();
                }
            }
        }
        //if (logger.isTraceEnabled()) {
        //    logger.trace("forced_2round_multiget_slice result = {}", keyToResult);
        //}
        return keyToResult;
    }

    public Map<ByteBuffer, List<ColumnOrSuperColumn>> multiget_slice(List<ByteBuffer> keys, ColumnParent column_parent, SlicePredicate predicate)
            throws Exception {
        //if (logger.isTraceEnabled()) {
        //logger.trace("multiget_slice(keys = {}, column_parent = {}, predicate = {})", new Object[]{printKeys(keys), column_parent, predicate});
        //}

        //Split up into one request for each server in the local cluster
        Map<Cassandra.AsyncClient, List<ByteBuffer>> asyncClientToKeys = partitionByAsyncClients(keys);

        //Send Requests
        Queue<BlockingQueueCallback<multiget_slice_call>> callbacks = new LinkedList<BlockingQueueCallback<multiget_slice_call>>();
        for (Entry<Cassandra.AsyncClient, List<ByteBuffer>> entry : asyncClientToKeys.entrySet()) {
            Cassandra.AsyncClient asyncClient = entry.getKey();
            List<ByteBuffer> keysForThisClient = entry.getValue();

            BlockingQueueCallback<multiget_slice_call> callback = new BlockingQueueCallback<multiget_slice_call>();
            callbacks.add(callback);

            asyncClient.multiget_slice(keysForThisClient, column_parent, predicate, consistencyLevel, LamportClock.sendTimestamp(), 0L, 0L, callback);
        }

        //Gather responses
        Map<ByteBuffer, List<ColumnOrSuperColumn>> combinedResults = new HashMap<ByteBuffer, List<ColumnOrSuperColumn>>();
        for (BlockingQueueCallback<multiget_slice_call> callback : callbacks) {
            MultigetSliceResult result = callback.getResponseNoInterruption().getResult();
            LamportClock.updateTime(result.lts);

            //Add dependencies on anything returned and removed deleted columns
            for (Entry<ByteBuffer, List<ColumnOrSuperColumn>> entry : result.value.entrySet()) {
                ByteBuffer key = entry.getKey();
                List<ColumnOrSuperColumn> coscList = entry.getValue();

                for (Iterator<ColumnOrSuperColumn> cosc_it = coscList.iterator(); cosc_it.hasNext(); ) {
                    ColumnOrSuperColumn cosc = cosc_it.next();
                    try {
                        clientContext.addDep(key, cosc);
                    } catch (NotFoundException nfe) {
                        //remove deleted results, it's okay for all result to be removed
                        cosc_it.remove();
                    }
                }
            }
            combinedResults.putAll(result.value);
        }
        //if (logger.isTraceEnabled()) {
        //    logger.trace("multiget_slice result = {}", combinedResults);
        //}
        return combinedResults;
    }

    public ColumnOrSuperColumn get(ByteBuffer key, ColumnPath column_path)
            throws InvalidRequestException, NotFoundException, UnavailableException, TimedOutException, TException {
        //if (logger.isTraceEnabled()) {
        //    logger.trace("get(key = {}, column_path = {})", new Object[]{printKey(key),column_path});
        //}

        GetResult result = findClient(key).get(key, column_path, consistencyLevel, LamportClock.sendTimestamp());
        LamportClock.updateTime(result.lts);
        clientContext.addDep(key, result.value);
        //if (logger.isTraceEnabled()) {
        //    logger.trace("get result = {}", result.value);
        //}
        return result.value;
    }

    public int get_count(ByteBuffer key, ColumnParent column_parent, SlicePredicate predicate)
            throws InvalidRequestException, UnavailableException, TimedOutException, TException {
        //if (logger.isTraceEnabled()) {
        //    logger.trace("get_count(key = {}, column_parent = {}, predicate = {})", new Object[]{printKey(key),column_parent, predicate});
        //}

        GetCountResult result = findClient(key).get_count(key, column_parent, predicate, consistencyLevel, LamportClock.sendTimestamp());
        LamportClock.updateTime(result.lts);
        clientContext.addDeps(result.deps);
        //if (logger.isTraceEnabled()) {
        //    logger.trace("get_count result = {}", result.value);
        //}
        return result.value;
    }

    public Map<ByteBuffer, Integer> transactional_multiget_count(List<ByteBuffer> keys, ColumnParent column_parent, SlicePredicate predicate)
            throws Exception {
        //if (logger.isTraceEnabled()) {
        //    logger.trace("transactional_multiget_count(keys = {}, column_parent = {}, predicate = {})", new Object[]{printKeys(keys), column_parent, predicate});
        //}

        //Split up into one request for each server in the local cluster
        Map<Cassandra.AsyncClient, List<ByteBuffer>> asyncClientToKeys = new HashMap<Cassandra.AsyncClient, List<ByteBuffer>>();
        for (ByteBuffer key : keys) {
            Cassandra.AsyncClient asyncClient = findAsyncClient(key);
            if (!asyncClientToKeys.containsKey(asyncClient)) {
                asyncClientToKeys.put(asyncClient, new ArrayList<ByteBuffer>());
            }
            asyncClientToKeys.get(asyncClient).add(key);
        }

        Queue<BlockingQueueCallback<multiget_count_call>> firstRoundCallbacks = new LinkedList<BlockingQueueCallback<multiget_count_call>>();
        for (Entry<Cassandra.AsyncClient, List<ByteBuffer>> entry : asyncClientToKeys.entrySet()) {
            Cassandra.AsyncClient asyncClient = entry.getKey();
            List<ByteBuffer> keysForThisClient = entry.getValue();

            BlockingQueueCallback<multiget_count_call> callback = new BlockingQueueCallback<multiget_count_call>();
            firstRoundCallbacks.add(callback);

            asyncClient.multiget_count(keysForThisClient, column_parent, predicate, consistencyLevel, LamportClock.sendTimestamp(), callback);
        }

        //Gather responses, track both max_evt and min_lvt
        long overallMaxEvt = Long.MIN_VALUE;
        long overallMinLvt = Long.MAX_VALUE;

        Map<ByteBuffer, Integer> keyToCount = new HashMap<ByteBuffer, Integer>();
        Map<ByteBuffer, Set<Dep>> keyToDeps = new HashMap<ByteBuffer, Set<Dep>>();
        NavigableMap<Long, List<ByteBuffer>> lvtToKeys = new TreeMap<Long, List<ByteBuffer>>();
        for (BlockingQueueCallback<multiget_count_call> callback : firstRoundCallbacks) {
            MultigetCountResult result = callback.getResponseNoInterruption().getResult();
            LamportClock.updateTime(result.lts);

            for (Entry<ByteBuffer, CountWithMetadata> entry : result.value.entrySet()) {
                ByteBuffer key = entry.getKey();
                int count = entry.getValue().count;
                long earliestValidTime = entry.getValue().earliest_valid_time;
                long latestValidTime = entry.getValue().latest_valid_time;
                Set<Dep> deps = entry.getValue().deps;

                keyToCount.put(key, count);
                keyToDeps.put(key, deps);

                if (!lvtToKeys.containsKey(latestValidTime)) {
                    lvtToKeys.put(latestValidTime, new LinkedList<ByteBuffer>());
                }
                lvtToKeys.get(latestValidTime).add(key);
                //if (logger.isTraceEnabled()) { logger.trace("round 1 response for " + printKey(key) + " = " + count + " evt: " + earliestValidTime + " lvt: " + latestValidTime); }

                overallMaxEvt = Math.max(overallMaxEvt, earliestValidTime);
                overallMinLvt = Math.min(overallMinLvt, latestValidTime);
            }
        }
        //if (logger.isTraceEnabled()) { logger.trace("Min LVT:" + overallMinLvt + "  Max EVT: " + overallMaxEvt); }

        //Execute 2nd round if necessary
        if (overallMinLvt < overallMaxEvt) {
            //get the smallest lvt > maxEvt
            long chosenTime = lvtToKeys.navigableKeySet().higher(overallMaxEvt);

            List<ByteBuffer> secondRoundKeys = new LinkedList<ByteBuffer>();
            for (List<ByteBuffer> keyList : lvtToKeys.headMap(chosenTime).values()) {
                secondRoundKeys.addAll(keyList);
            }

            //TODO: remove this later
            //invalid all results for second round keys (sanity check, not strictly necessary)
            for (ByteBuffer key : secondRoundKeys) {
                keyToCount.remove(key);
                keyToDeps.remove(key);
            }

            //Send Round 2 Requests
            Map<Cassandra.AsyncClient, List<ByteBuffer>> asyncClientToSecondRoundKeys = partitionByAsyncClients(secondRoundKeys);
            Queue<BlockingQueueCallback<multiget_count_by_time_call>> secondRoundCallbacks = new LinkedList<BlockingQueueCallback<multiget_count_by_time_call>>();
            for (Entry<Cassandra.AsyncClient, List<ByteBuffer>> entry : asyncClientToSecondRoundKeys.entrySet()) {
                Cassandra.AsyncClient asyncClient = entry.getKey();
                List<ByteBuffer> keysForThisClient = entry.getValue();

                BlockingQueueCallback<multiget_count_by_time_call> callback = new BlockingQueueCallback<multiget_count_by_time_call>();
                secondRoundCallbacks.add(callback);

                //if (logger.isTraceEnabled()) { logger.trace("round 2: get " + printKeys(keysForThisClient) + " from " + asyncClient); }

                asyncClient.multiget_count_by_time(keysForThisClient, column_parent, predicate, consistencyLevel, chosenTime, LamportClock.sendTimestamp(), callback);
            }

            //Gather second round responses
            for (BlockingQueueCallback<multiget_count_by_time_call> callback : secondRoundCallbacks) {
                MultigetCountResult result = callback.getResponseNoInterruption().getResult();
                LamportClock.updateTime(result.lts);

                assert false : "Need to substituteValidFirstRoundResults";
                //WL TODO substituteValidFirstRoundResults(result, keyToResult);

                //if (logger.isTraceEnabled()) { logger.trace("round 2 responses for " + printKeys(result.getValue().keySet())); }

                for (Entry<ByteBuffer, CountWithMetadata> entry : result.getValue().entrySet()) {
                    keyToCount.put(entry.getKey(), entry.getValue().count);
                }
            }
        }

        //Add dependencies from counts we return
        for (Set<Dep> deps : keyToDeps.values()) {
            clientContext.addDeps(deps);
        }

        //if (logger.isTraceEnabled()) {
        //    logger.trace("multiget_count result = {}", keyToCount);
        //}
        return keyToCount;
    }

    public Map<ByteBuffer, Integer> multiget_count(List<ByteBuffer> keys, ColumnParent column_parent, SlicePredicate predicate)
            throws Exception {
        //if (logger.isTraceEnabled()) {
        //logger.trace("multiget_count(keys = {}, column_parent = {}, predicate = {})", new Object[]{printKeys(keys), column_parent, predicate});
        //}

        //Split up into one request for each server in the local cluster
        Map<Cassandra.AsyncClient, List<ByteBuffer>> asyncClientToKeys = new HashMap<Cassandra.AsyncClient, List<ByteBuffer>>();
        for (ByteBuffer key : keys) {
            Cassandra.AsyncClient asyncClient = findAsyncClient(key);
            if (!asyncClientToKeys.containsKey(asyncClient)) {
                asyncClientToKeys.put(asyncClient, new ArrayList<ByteBuffer>());
            }
            asyncClientToKeys.get(asyncClient).add(key);
        }

        Queue<BlockingQueueCallback<multiget_count_call>> callbacks = new LinkedList<BlockingQueueCallback<multiget_count_call>>();
        for (Entry<Cassandra.AsyncClient, List<ByteBuffer>> entry : asyncClientToKeys.entrySet()) {
            Cassandra.AsyncClient asyncClient = entry.getKey();
            List<ByteBuffer> keysForThisClient = entry.getValue();

            BlockingQueueCallback<multiget_count_call> callback = new BlockingQueueCallback<multiget_count_call>();
            callbacks.add(callback);

            asyncClient.multiget_count(keysForThisClient, column_parent, predicate, consistencyLevel, LamportClock.sendTimestamp(), callback);
        }

        Map<ByteBuffer, Integer> combinedResults = new HashMap<ByteBuffer, Integer>();
        for (BlockingQueueCallback<multiget_count_call> callback : callbacks) {
            MultigetCountResult result = callback.getResponseNoInterruption().getResult();
            LamportClock.updateTime(result.lts);
            for (Entry<ByteBuffer, CountWithMetadata> entry : result.value.entrySet()) {
                combinedResults.put(entry.getKey(), entry.getValue().count);
                clientContext.addDeps(entry.getValue().deps);
            }
        }
        //if (logger.isTraceEnabled()) {
        //    logger.trace("multiget_count result = {}", combinedResults);
        //}
        return combinedResults;
    }

    private Range<Token> intersect(Range<Token> serverRange, AbstractBounds<Token> requestedRange) {
        // TODO: Might be subtle bugs because one's a range and the other's a bounds
        if (serverRange.contains(requestedRange.left) && serverRange.contains(requestedRange.right)) {
            //case 1: serverRange fully encompasses requestedRange
            return new Range<Token>(requestedRange.left, requestedRange.right, partitioner);
        } else if (requestedRange.contains(serverRange.left) && requestedRange.contains(serverRange.right)) {
            //case 2: serverRange is fully encompasses by requestedRange
            //serverRange is already the intersection
            return new Range<Token>(serverRange.left, serverRange.right);
        } else if (serverRange.contains(requestedRange.left) && requestedRange.contains(serverRange.right)) {
            //case 3: serverRange overlaps on the left: sR.left < rR.left < sR.right < rR.right
            return new Range<Token>(requestedRange.left, serverRange.right, partitioner);
        } else if (requestedRange.contains(serverRange.left) && serverRange.contains(requestedRange.right)) {
            //case 4: serverRange overlaps on the right rR.left < sR.left < rR.right < sR.right
            return new Range<Token>(serverRange.left, requestedRange.right, partitioner);
        } else if (!serverRange.contains(requestedRange.left) && !serverRange.contains(requestedRange.right) &&
                !requestedRange.contains(serverRange.left) && !requestedRange.contains(serverRange.right)) {
            //case 5: totally disjoint
            return null;
        } else {
            assert false : "Failed intersecting serverRange = (" + serverRange.left + ", " + serverRange.right + ") and requestedRange = (" + requestedRange.left + ", " + requestedRange.right + ")";
            return null;
        }
    }

    public List<KeySlice> get_range_slices(ColumnParent column_parent, SlicePredicate predicate, KeyRange range)
            throws Exception {
        //if (logger.isTraceEnabled()) {
        //            logger.trace("get_range_slices(column_parent = {}, predicate = {}, range = {})", new Object[]{column_parent, predicate, range});
        //}

        //turn the KeyRange into AbstractBounds that are easier to reason about
        AbstractBounds<Token> requestedRange;
        if (range.start_key == null) {
            Token.TokenFactory tokenFactory = partitioner.getTokenFactory();
            Token left = tokenFactory.fromString(range.start_token);
            Token right = tokenFactory.fromString(range.end_token);
            requestedRange = new Bounds<Token>(left, right, partitioner);
        } else {
            AbstractBounds<RowPosition> rowPositionBounds = new Bounds<RowPosition>(RowPosition.forKey(range.start_key, partitioner), RowPosition.forKey(range.end_key, partitioner));
            requestedRange = rowPositionBounds.toTokenBounds();
        }

        //Split up into one request for each server in the local cluster
        Map<Cassandra.AsyncClient, List<Range<Token>>> asyncClientToRanges = new HashMap<Cassandra.AsyncClient, List<Range<Token>>>();
        for (Entry<Range<Token>, InetAddress> entry : ringCache.getRangeMap().entries()) {
            Range<Token> serverRange = entry.getKey();
            InetAddress addr = entry.getValue();

            Cassandra.AsyncClient asyncClient = addressToAsyncClient.get(addr);
            if (asyncClient == null) {
                //this addr is not in the local datacenter
                continue;
            }

            // We want to restrict the range we ask for from each server to be
            // the intersection of its range and the requested range
            serverRange = intersect(serverRange, requestedRange);
            if (serverRange == null) {
                //no intersection, so nothing to request from this server
                continue;
            }

            if (!asyncClientToRanges.containsKey(asyncClient)) {
                asyncClientToRanges.put(asyncClient, new ArrayList<Range<Token>>());
            }
            asyncClientToRanges.get(asyncClient).add(serverRange);
        }

        //Need to merge the adjacent ranges into a single keyRange to request from each local server
        Map<Cassandra.AsyncClient, KeyRange> asyncClientToKeyRange = new HashMap<Cassandra.AsyncClient, KeyRange>();
        for (Entry<Cassandra.AsyncClient, List<Range<Token>>> entry : asyncClientToRanges.entrySet()) {
            Cassandra.AsyncClient asyncClient = entry.getKey();
            List<Range<Token>> rangeList = entry.getValue();

            List<AbstractBounds<Token>> normalizedBounds = AbstractBounds.normalize(rangeList);
            assert normalizedBounds.size() == 1 : "All parts of a server ranges should be adjacent : " + normalizedBounds;
            AbstractBounds<Token<String>> serverRange = new Bounds<Token<String>>(normalizedBounds.get(0).left, normalizedBounds.get(0).right, partitioner);

            //WL TODO: Should be a more elegant way to extract tokens
            String leftToken = serverRange.left.toString();
            String rightToken = serverRange.right.toString();
            //Remove brackets from tokens (they only show up when we have the ByteOrderPartitioner I think)
            if (leftToken.indexOf("[") != -1) {
                leftToken = leftToken.substring(leftToken.indexOf("[") + 1, leftToken.indexOf("]"));
                rightToken = rightToken.substring(rightToken.indexOf("[") + 1, rightToken.indexOf("]"));
            }


            KeyRange rangeForThisClient = new KeyRange();
            rangeForThisClient.setStart_token(leftToken);
            rangeForThisClient.setEnd_token(rightToken);

            asyncClientToKeyRange.put(asyncClient, rangeForThisClient);
        }

        Queue<BlockingQueueCallback<get_range_slices_call>> callbacks = new LinkedList<BlockingQueueCallback<get_range_slices_call>>();
        for (Entry<Cassandra.AsyncClient, KeyRange> entry : asyncClientToKeyRange.entrySet()) {
            Cassandra.AsyncClient asyncClient = entry.getKey();
            KeyRange rangeForThisClient = entry.getValue();

            BlockingQueueCallback<get_range_slices_call> callback = new BlockingQueueCallback<get_range_slices_call>();
            callbacks.add(callback);

            asyncClient.get_range_slices(column_parent, predicate, rangeForThisClient, consistencyLevel, LamportClock.sendTimestamp(), callback);
        }

        List<KeySlice> combinedResults = new ArrayList<KeySlice>();
        for (BlockingQueueCallback<get_range_slices_call> callback : callbacks) {
            GetRangeSlicesResult result = callback.getResponseNoInterruption().getResult();
            LamportClock.updateTime(result.lts);

            for (KeySlice keySlice : result.value) {
                ByteBuffer key = keySlice.key;
                List<ColumnOrSuperColumn> coscList = keySlice.columns;

                for (Iterator<ColumnOrSuperColumn> cosc_it = coscList.iterator(); cosc_it.hasNext(); ) {
                    ColumnOrSuperColumn cosc = cosc_it.next();
                    try {
                        clientContext.addDep(key, cosc);
                    } catch (NotFoundException nfe) {
                        //remove deleted results, it's okay for all result to be removed
                        cosc_it.remove();
                    }
                }
            }
            combinedResults.addAll(result.value);
        }
        //if (logger.isTraceEnabled()) {
        //    logger.trace("get_range_slices result = {}", combinedResults);
        //}
        return combinedResults;
    }

    public List<KeySlice> transactional_get_range_slices(ColumnParent column_parent, SlicePredicate predicate, KeyRange range)
            throws Exception {
        //if (logger.isTraceEnabled()) {
        //    logger.trace("transactional_get_range_slices(column_parent = {}, predicate = {}, range = {})", new Object[]{column_parent, predicate, range});
        //}

        //turn the KeyRange into AbstractBounds that are easier to reason about
        AbstractBounds<Token> requestedRange;
        if (range.start_key == null) {
            Token.TokenFactory tokenFactory = partitioner.getTokenFactory();
            Token left = tokenFactory.fromString(range.start_token);
            Token right = tokenFactory.fromString(range.end_token);
            requestedRange = new Bounds<Token>(left, right, partitioner);
        } else {
            AbstractBounds<RowPosition> rowPositionBounds = new Bounds<RowPosition>(RowPosition.forKey(range.start_key, partitioner), RowPosition.forKey(range.end_key, partitioner));
            requestedRange = rowPositionBounds.toTokenBounds();
        }

        //Split up into one request for each server in the local cluster
        Map<Cassandra.AsyncClient, List<Range<Token>>> asyncClientToRanges = new HashMap<Cassandra.AsyncClient, List<Range<Token>>>();
        for (Entry<Range<Token>, InetAddress> entry : ringCache.getRangeMap().entries()) {
            Range<Token> serverRange = entry.getKey();
            InetAddress addr = entry.getValue();

            Cassandra.AsyncClient asyncClient = addressToAsyncClient.get(addr);
            if (asyncClient == null) {
                //this addr is not in the local datacenter
                continue;
            }

            // We want to restrict the range we ask for from each server to be
            // the intersection of its range and the requested range
            serverRange = intersect(serverRange, requestedRange);
            if (serverRange == null) {
                //no intersection, so nothing to request from this server
                continue;
            }

            if (!asyncClientToRanges.containsKey(asyncClient)) {
                asyncClientToRanges.put(asyncClient, new ArrayList<Range<Token>>());
            }
            asyncClientToRanges.get(asyncClient).add(serverRange);
        }

        //Need to merge the adjacent ranges into a single keyRange to request from each local server
        Map<Cassandra.AsyncClient, KeyRange> asyncClientToKeyRange = new HashMap<Cassandra.AsyncClient, KeyRange>();
        for (Entry<Cassandra.AsyncClient, List<Range<Token>>> entry : asyncClientToRanges.entrySet()) {
            Cassandra.AsyncClient asyncClient = entry.getKey();
            List<Range<Token>> rangeList = entry.getValue();

            List<AbstractBounds<Token>> normalizedBounds = AbstractBounds.normalize(rangeList);
            assert normalizedBounds.size() == 1 : "All parts of a server ranges should be adjacent : " + normalizedBounds;
            AbstractBounds<Token<String>> serverRange = new Bounds<Token<String>>(normalizedBounds.get(0).left, normalizedBounds.get(0).right, partitioner);

            //WL TODO: Should be a more elegant way to extract tokens
            String leftToken = serverRange.left.toString();
            String rightToken = serverRange.right.toString();
            //Remove brackets from tokens (they only show up when we have the ByteOrderPartitioner I think)
            if (leftToken.indexOf("[") != -1) {
                leftToken = leftToken.substring(leftToken.indexOf("[") + 1, leftToken.indexOf("]"));
                rightToken = rightToken.substring(rightToken.indexOf("[") + 1, rightToken.indexOf("]"));
            }

            KeyRange rangeForThisClient = new KeyRange();
            rangeForThisClient.setStart_token(leftToken);
            rangeForThisClient.setEnd_token(rightToken);

            asyncClientToKeyRange.put(asyncClient, rangeForThisClient);
        }

        Queue<BlockingQueueCallback<get_range_slices_call>> firstRoundCallbacks = new LinkedList<BlockingQueueCallback<get_range_slices_call>>();
        for (Entry<Cassandra.AsyncClient, KeyRange> entry : asyncClientToKeyRange.entrySet()) {
            Cassandra.AsyncClient asyncClient = entry.getKey();
            KeyRange rangeForThisClient = entry.getValue();

            BlockingQueueCallback<get_range_slices_call> callback = new BlockingQueueCallback<get_range_slices_call>();
            firstRoundCallbacks.add(callback);

            asyncClient.get_range_slices(column_parent, predicate, rangeForThisClient, consistencyLevel, LamportClock.sendTimestamp(), callback);
        }

        //Gather responses, track both max_evt and min_lvt
        long overallMaxEvt = Long.MIN_VALUE;
        long overallMinLvt = Long.MAX_VALUE;

        //keyToColumns should be in sorted order, clients (at least some of my testing code) assumes this
        SortedMap<ByteBuffer, List<ColumnOrSuperColumn>> keyToColumns = new TreeMap<ByteBuffer, List<ColumnOrSuperColumn>>();
        Map<ByteBuffer, Set<Dep>> keyToDeps = new HashMap<ByteBuffer, Set<Dep>>();

        //WL TODO Add support for doing queries to secondary indices

        NavigableMap<Long, List<ByteBuffer>> lvtToKeys = new TreeMap<Long, List<ByteBuffer>>();
        for (BlockingQueueCallback<get_range_slices_call> callback : firstRoundCallbacks) {
            GetRangeSlicesResult result = callback.getResponseNoInterruption().getResult();
            LamportClock.updateTime(result.lts);

            for (KeySlice keySlice : result.value) {
                ByteBuffer key = keySlice.key;
                List<ColumnOrSuperColumn> coscList = keySlice.columns;

                //find the evt and lvt for the entire row
                EvtAndLvt evtAndLvt = ColumnOrSuperColumnHelper.extractEvtAndLvt(coscList);
                if (!lvtToKeys.containsKey(evtAndLvt.getLatestValidTime())) {
                    lvtToKeys.put(evtAndLvt.getLatestValidTime(), new LinkedList<ByteBuffer>());
                }
                lvtToKeys.get(evtAndLvt.getLatestValidTime()).add(key);
                //if (logger.isTraceEnabled()) { logger.trace("round 1 response for " + printKey(key) + " evt: " + evtAndLvt.getEarliestValidTime() + " lvt: " + evtAndLvt.getLatestValidTime()); }

                overallMaxEvt = Math.max(overallMaxEvt, evtAndLvt.getEarliestValidTime());
                overallMinLvt = Math.min(overallMinLvt, evtAndLvt.getLatestValidTime());


                ClientContext tmpContext = new ClientContext();
                for (Iterator<ColumnOrSuperColumn> cosc_it = coscList.iterator(); cosc_it.hasNext(); ) {
                    ColumnOrSuperColumn cosc = cosc_it.next();
                    try {
                        tmpContext.addDep(key, cosc);
                    } catch (NotFoundException nfe) {
                        //remove deleted results, it's okay for all result to be removed
                        cosc_it.remove();
                    }
                }
                keyToColumns.put(key, coscList);
                keyToDeps.put(key, tmpContext.getDeps());
            }
        }
        //if (logger.isTraceEnabled()) { logger.trace("Min LVT:" + overallMinLvt + "  Max EVT: " + overallMaxEvt); }

        //Execute 2nd round if necessary
        if (overallMinLvt < overallMaxEvt) {
            //get the smallest lvt > maxEvt
            long chosenTime = lvtToKeys.navigableKeySet().higher(overallMaxEvt);

            List<ByteBuffer> secondRoundKeys = new LinkedList<ByteBuffer>();
            for (List<ByteBuffer> keyList : lvtToKeys.headMap(chosenTime).values()) {
                secondRoundKeys.addAll(keyList);
            }

            //Really do need to remove results for get_range_slices_by_time
            //invalid all results for second round keys (sanity check, not strictly necessary)
            for (ByteBuffer key : secondRoundKeys) {
                keyToColumns.remove(key);
                keyToDeps.remove(key);
            }

            Set<ByteBuffer> allKnownKeys = keyToColumns.keySet();
            Map<Cassandra.AsyncClient, List<ByteBuffer>> asyncClientToKnownKeys = partitionByAsyncClients(allKnownKeys);

            Queue<BlockingQueueCallback<get_range_slices_by_time_call>> secondRoundCallbacks = new LinkedList<BlockingQueueCallback<get_range_slices_by_time_call>>();
            for (Entry<Cassandra.AsyncClient, KeyRange> entry : asyncClientToKeyRange.entrySet()) {
                Cassandra.AsyncClient asyncClient = entry.getKey();
                KeyRange rangeForThisClient = entry.getValue();

                BlockingQueueCallback<get_range_slices_by_time_call> callback = new BlockingQueueCallback<get_range_slices_by_time_call>();
                secondRoundCallbacks.add(callback);

                List<ByteBuffer> knownKeys = asyncClientToKnownKeys.get(asyncClient);
                if (knownKeys == null) {
                    //knownKeys can't be null for thrift encoding
                    knownKeys = new LinkedList<ByteBuffer>();
                }
                asyncClient.get_range_slices_by_time(column_parent, predicate, rangeForThisClient, knownKeys, consistencyLevel, chosenTime, LamportClock.sendTimestamp(), callback);
            }

            for (BlockingQueueCallback<get_range_slices_by_time_call> callback : secondRoundCallbacks) {
                GetRangeSlicesResult result = callback.getResponseNoInterruption().getResult();
                LamportClock.updateTime(result.lts);

                for (KeySlice keySlice : result.value) {
                    ByteBuffer key = keySlice.key;
                    List<ColumnOrSuperColumn> coscList = keySlice.columns;

                    ClientContext tmpContext = new ClientContext();
                    for (Iterator<ColumnOrSuperColumn> cosc_it = coscList.iterator(); cosc_it.hasNext(); ) {
                        ColumnOrSuperColumn cosc = cosc_it.next();
                        try {
                            tmpContext.addDep(key, cosc);
                        } catch (NotFoundException nfe) {
                            //remove deleted results, it's okay for all result to be removed
                            cosc_it.remove();
                        }
                    }
                    keyToColumns.put(key, coscList);
                    keyToDeps.put(key, tmpContext.getDeps());
                }
            }
        }

        //Add dependencies from counts we return
        for (Set<Dep> deps : keyToDeps.values()) {
            clientContext.addDeps(deps);
        }

        List<KeySlice> combinedResults = new ArrayList<KeySlice>();
        for (Entry<ByteBuffer, List<ColumnOrSuperColumn>> entry : keyToColumns.entrySet()) {
            ByteBuffer key = entry.getKey();
            List<ColumnOrSuperColumn> coscList = entry.getValue();

            combinedResults.add(new KeySlice(key, coscList));
        }

        //if (logger.isTraceEnabled()) {
        //    logger.trace("transactional_get_range_slices result = {}", combinedResults);
        //}

        return combinedResults;
    }


    public List<KeySlice> get_indexed_slices(ColumnParent column_parent, IndexClause index_clause, SlicePredicate column_predicate)
            throws InvalidRequestException, UnavailableException, TimedOutException, TException {
        assert false : "get_indexed_slices is deprecated in cassandra, so it's not supported in cops2";
        return null;
    }

    public void insert(ByteBuffer key, ColumnParent column_parent, Column column)
            throws InvalidRequestException, UnavailableException, TimedOutException, TException {
        //if (logger.isTraceEnabled()) {
        //    logger.trace("insert(key = {}, column_parent = {}, column = {})", new Object[]{printKey(key),column_parent, column});
        //}

        //Set the timestamp (version) to 0 so the accepting datacenter sets it
        column.timestamp = 0;
        WriteResult result = findClient(key).insert(key, column_parent, column, consistencyLevel, clientContext.getDeps(), LamportClock.sendTimestamp());
        LamportClock.updateTime(result.lts);
        clientContext.clearDeps();
        clientContext.addDep(new Dep(key, result.version));
    }

    public void populate(Map<ByteBuffer, Map<String, List<Mutation>>> mutation_map)
            throws Exception {
        //if (logger.isTraceEnabled()) {
        //    logger.trace("batch_mutate(mutation_map = {})", new Object[]{mutation_map});
        //}

        //mutation_map: key -> columnFamily -> list<mutation>, mutation is a ColumnOrSuperColumn insert or a delete
        // 0 out all timestamps
        for (Map<String, List<Mutation>> cfToMutations : mutation_map.values()) {
            for (List<Mutation> mutations : cfToMutations.values()) {
                for (Mutation mutation : mutations) {
                    if (mutation.isSetColumn_or_supercolumn()) {
                        ColumnOrSuperColumnHelper.updateTimestamp(mutation.column_or_supercolumn, 0);
                    } else {
                        assert mutation.isSetDeletion();
                        mutation.deletion.timestamp = 0L;
                    }
                }
            }
        }

        //split it into a set of batch_mutations, one for each server in the cluster
        Map<Cassandra.AsyncClient, Map<ByteBuffer, Map<String, List<Mutation>>>> asyncClientToMutations = new HashMap<Cassandra.AsyncClient, Map<ByteBuffer, Map<String, List<Mutation>>>>();
        for (Entry<ByteBuffer, Map<String, List<Mutation>>> entry : mutation_map.entrySet()) {
            ByteBuffer key = entry.getKey();
            Map<String, List<Mutation>> mutations = entry.getValue();

            Cassandra.AsyncClient asyncClient = findAsyncClient(key);
            if (!asyncClientToMutations.containsKey(asyncClient)) {
                asyncClientToMutations.put(asyncClient, new HashMap<ByteBuffer, Map<String, List<Mutation>>>());
            }
            asyncClientToMutations.get(asyncClient).put(key, mutations);
        }

        boolean mutateSuccess = true;
        Exception mutateException = null;
        //We need to split up based key because even if keys are colocated on the same server here,
        //we can't guarentee they'll be colocated on the same server in other datacenters
        Queue<BlockingQueueCallback<batch_mutate_call>> callbacks = new LinkedList<BlockingQueueCallback<batch_mutate_call>>();
        for (Entry<Cassandra.AsyncClient, Map<ByteBuffer, Map<String, List<Mutation>>>> entry : asyncClientToMutations.entrySet()) {
            Cassandra.AsyncClient asyncClient = entry.getKey();
            Map<ByteBuffer, Map<String, List<Mutation>>> mutations = entry.getValue();

            BlockingQueueCallback<batch_mutate_call> callback = new BlockingQueueCallback<batch_mutate_call>();
            callbacks.add(callback);

            if (asyncClient.hasError()) {
                System.err.println("Batch_mutate: AAA! Why do I get this error: " + asyncClient.getError());
                ByteBuffer key = null;
                for (Entry<ByteBuffer, Map<String, List<Mutation>>> entry2 : mutations.entrySet()) {
                    key = entry2.getKey();
                    break;
                }
                asyncClient = createNewAsyncClient(key);
            }

            try {
                asyncClient.batch_mutate(mutations, consistencyLevel, clientContext.getDeps(), LamportClock.sendTimestamp(), callback);
            } catch (Exception e) {
                mutateSuccess = false;
                mutateException = e;
                continue;
            }
        }

        clientContext.clearDeps();

        for (BlockingQueueCallback<batch_mutate_call> callback : callbacks) {
            try {
                BatchMutateResult result = callback.getResponseNoInterruption().getResult();
                LamportClock.updateTime(result.lts);
                clientContext.addDeps(result.deps);
            } catch (Exception e) {
                mutateSuccess = false;
                mutateException = e;
                continue;
            }
        }
        if (!mutateSuccess) {
            throw mutateException;
        }

    }

    public void batch_mutate(Map<ByteBuffer, Map<String, List<Mutation>>> mutation_map)
            throws Exception {
        //if (logger.isTraceEnabled()) {
        //    logger.trace("batch_mutate(mutation_map = {})", new Object[]{mutation_map});
        //}

        //mutation_map: key -> columnFamily -> list<mutation>, mutation is a ColumnOrSuperColumn insert or a delete
        // 0 out all timestamps
        /*
        if (lastSingleWriteTime == null) {
            lastSingleWriteTime = System.currentTimeMillis();
        }
         */

        for (Map<String, List<Mutation>> cfToMutations : mutation_map.values()) {
            for (List<Mutation> mutations : cfToMutations.values()) {
                for (Mutation mutation : mutations) {
                    if (mutation.isSetColumn_or_supercolumn()) {
                        ColumnOrSuperColumnHelper.updateTimestamp(mutation.column_or_supercolumn, 0);
                    } else {
                        assert mutation.isSetDeletion();
                        mutation.deletion.timestamp = 0L;
                    }
                }
            }
        }

        //split it into a set of batch_mutations, one for each server in the cluster
        Map<Cassandra.AsyncClient, Map<ByteBuffer, Map<String, List<Mutation>>>> asyncClientToMutations = new HashMap<Cassandra.AsyncClient, Map<ByteBuffer, Map<String, List<Mutation>>>>();
        for (Entry<ByteBuffer, Map<String, List<Mutation>>> entry : mutation_map.entrySet()) {
            ByteBuffer key = entry.getKey();
            Map<String, List<Mutation>> mutations = entry.getValue();

            Cassandra.AsyncClient asyncClient = findAsyncClient(key);
            if (!asyncClientToMutations.containsKey(asyncClient)) {
                asyncClientToMutations.put(asyncClient, new HashMap<ByteBuffer, Map<String, List<Mutation>>>());
            }
            asyncClientToMutations.get(asyncClient).put(key, mutations);
            //numWrites++;
        }

        long startNano = System.nanoTime();
        boolean mutateSuccess = true;
        Exception mutateException = null;
        //We need to split up based key because even if keys are colocated on the same server here,
        //we can't guarentee they'll be colocated on the same server in other datacenters
        Queue<BlockingQueueCallback<batch_mutate_call>> callbacks = new LinkedList<BlockingQueueCallback<batch_mutate_call>>();
        for (Entry<Cassandra.AsyncClient, Map<ByteBuffer, Map<String, List<Mutation>>>> entry : asyncClientToMutations.entrySet()) {
            Cassandra.AsyncClient asyncClient = entry.getKey();
            Map<ByteBuffer, Map<String, List<Mutation>>> mutations = entry.getValue();

            BlockingQueueCallback<batch_mutate_call> callback = new BlockingQueueCallback<batch_mutate_call>();
            callbacks.add(callback);

            if (asyncClient.hasError()) {
                System.err.println("Batch_mutate: AAA! Why do I get this error: " + asyncClient.getError());
                ByteBuffer key = null;
                for (Entry<ByteBuffer, Map<String, List<Mutation>>> entry2 : mutations.entrySet()) {
                    key = entry2.getKey();
                    break;
                }
                asyncClient = createNewAsyncClient(key);
            }

            try {
                asyncClient.batch_mutate(mutations, consistencyLevel, clientContext.getDeps(), LamportClock.sendTimestamp(), callback);
            } catch (Exception e) {
                mutateSuccess = false;
                mutateException = e;
                continue;
            }
            /*
            if (COLLECT_SIMPLE_WRITE_LATENCY && (numWrites % 100 == 0 || (System.currentTimeMillis() - lastSingleWriteTime) >= PRINT_STATS_INTERVAL)) {
                printWriteLatencies(writeLatencies);
                lastSingleWriteTime = System.currentTimeMillis();
            }
            */
        }

        clientContext.clearDeps();
        /*
        int numCallbackReturns = 0;
        // latency of single write
        Set<Integer> idxSet = new HashSet<Integer>();
        while (numCallbackReturns < callbacks.size()) {
            int idx = 0;
            for (BlockingQueueCallback<batch_mutate_call> callback : callbacks) {
                if (callback.peekResponse() != null && !idxSet.contains(idx)) {
                    numCallbackReturns++;
                    long latencyNano = System.nanoTime() - startNano;
                    for (int i = 0; i < callback.peekResponse().getResult().deps.size(); i++) {
                        writeLatencies.add(latencyNano / 1000);
                    }
                    idxSet.add(idx);
                }
                idx++;
            }
        }
        */

        for (BlockingQueueCallback<batch_mutate_call> callback : callbacks) {
            try {
                BatchMutateResult result = callback.getResponseNoInterruption().getResult();
                LamportClock.updateTime(result.lts);
                clientContext.addDeps(result.deps);
            } catch (Exception e) {
                mutateSuccess = false;
                mutateException = e;
                continue;
            }
        }
        if (!mutateSuccess) {
            throw mutateException;
        }

    }

    public void transactional_batch_mutate(Map<ByteBuffer, Map<String, List<Mutation>>> mutation_map)
            throws Exception {
        //if (logger.isTraceEnabled()) {
        //    logger.trace("batch_mutate(mutation_map = {})", new Object[]{mutation_map});
        //}

        //mutation_map: key -> columnFamily -> list<mutation>, mutation is a ColumnOrSuperColumn insert or a delete
        // 0 out all timestamps
        for (Map<String, List<Mutation>> cfToMutations : mutation_map.values()) {
            for (List<Mutation> mutations : cfToMutations.values()) {
                for (Mutation mutation : mutations) {
                    if (mutation.isSetColumn_or_supercolumn()) {
                        ColumnOrSuperColumnHelper.updateTimestamp(mutation.column_or_supercolumn, 0);
                    } else {
                        assert mutation.isSetDeletion();
                        mutation.deletion.timestamp = 0L;
                    }
                }
            }
        }

        //split it into a set of batch_mutations, one for each server in the cluster
        Map<Cassandra.AsyncClient, Map<ByteBuffer, Map<String, List<Mutation>>>> asyncClientToMutations = new HashMap<Cassandra.AsyncClient, Map<ByteBuffer, Map<String, List<Mutation>>>>();
        for (Entry<ByteBuffer, Map<String, List<Mutation>>> entry : mutation_map.entrySet()) {
            ByteBuffer key = entry.getKey();
            Map<String, List<Mutation>> mutations = entry.getValue();

            Cassandra.AsyncClient asyncClient = findAsyncClient(key);
            if (!asyncClientToMutations.containsKey(asyncClient)) {
                asyncClientToMutations.put(asyncClient, new HashMap<ByteBuffer, Map<String, List<Mutation>>>());
            }
            asyncClientToMutations.get(asyncClient).put(key, mutations);
        }

        //pick a random key from a random participant to be the coordinator
        ByteBuffer coordinatorKey = null;
        int coordinatorIndex = (int) (Math.random() * asyncClientToMutations.size());
        int asyncClientIndex = 0;
        for (Map<ByteBuffer, Map<String, List<Mutation>>> keyToMutations : asyncClientToMutations.values()) {
            if (asyncClientIndex == coordinatorIndex) {
                Set<ByteBuffer> keys = keyToMutations.keySet();
                int coordinatorKeyIndex = (int) (Math.random() * keys.size());
                int keyIndex = 0;
                for (ByteBuffer key : keys) {
                    if (keyIndex == coordinatorKeyIndex) {
                        coordinatorKey = key;
                        break;
                    }
                    keyIndex++;
                }
                break;
            }
            asyncClientIndex++;
        }
        assert coordinatorKey != null;

        //get a unique transactionId
        long transactionId = getTransactionId();

        //We need to split up based key because even if keys are colocated on the same server here,
        //we can't guarentee they'll be colocated on the same server in other datacenters
        BlockingQueueCallback<transactional_batch_mutate_coordinator_call> coordinatorCallback = null;
        Queue<BlockingQueueCallback<transactional_batch_mutate_cohort_call>> cohortCallbacks = new LinkedList<BlockingQueueCallback<transactional_batch_mutate_cohort_call>>();
        // HL: get read_ts, also called gst, global safe time
        long gst = LamportClock.read_ts();
        // record coordinator server
        String coordinator_svr = findServer(coordinatorKey);
        for (Entry<Cassandra.AsyncClient, Map<ByteBuffer, Map<String, List<Mutation>>>> entry : asyncClientToMutations.entrySet()) {
            Cassandra.AsyncClient asyncClient = entry.getKey();
            Map<ByteBuffer, Map<String, List<Mutation>>> mutations = entry.getValue();

            if (mutations.containsKey(coordinatorKey)) {
                coordinatorCallback = new BlockingQueueCallback<transactional_batch_mutate_coordinator_call>();
                Set<ByteBuffer> allKeys = mutation_map.keySet();
                asyncClient.transactional_batch_mutate_coordinator(mutations, consistencyLevel, clientContext.getDeps(), coordinatorKey, allKeys, transactionId, LamportClock.sendTimestamp(), client_id, gst, coordinatorCallback);
            } else {
                BlockingQueueCallback<transactional_batch_mutate_cohort_call> callback = new BlockingQueueCallback<transactional_batch_mutate_cohort_call>();
                asyncClient.transactional_batch_mutate_cohort(mutations, coordinatorKey, transactionId, LamportClock.sendTimestamp(), client_id, gst, callback);
                cohortCallbacks.add(callback);
            }
        }

        clientContext.clearDeps();
        BatchMutateResult result = coordinatorCallback.getResponseNoInterruption().getResult();
        LamportClock.updateTime(result.lts);
        clientContext.addDeps(result.deps);

        //assert coordinator_svr != null : "coordinator should not be null!";
        LamportClock.updateReadTsMap(coordinator_svr, result.lst);

        // Also wait for cohorts so we can safely reuse these connections
        for (BlockingQueueCallback<transactional_batch_mutate_cohort_call> callback : cohortCallbacks) {
            short cohortResult = callback.getResponseNoInterruption().getResult();
            assert cohortResult == 0;
        }
    }

    /*
    private static AtomicInteger transactionHighBits = new AtomicInteger(0);
    private long getTransactionId()
    {
        //want transactionIds that distinguish ongoing transactions
        //top 16 bits, are an incrementing value from this node
        //next 32 bits, are this node's ip address
        //last 16 bits, are this node's port

        long top16 = transactionHighBits.incrementAndGet();
        long next32;
        if (DatabaseDescriptor.getBroadcastAddress() == null) {
          //Embedded Server
            next32 = 0;
        } else {
            next32 = ByteBuffer.wrap(DatabaseDescriptor.getBroadcastAddress().getAddress()).getInt();
        }
        long last16 = DatabaseDescriptor.getRpcPort();

        return (top16 << 48) + (next32 << 16) + last16;
    }
    */

    private long getTransactionId() {
        //Random 64bit longs should be enough to distinguish ongoing transactions for now
        //TODO: have client ids and have them increase ... fawn-kv style
        return randomizer.nextLong();
    }

    public void remove(ByteBuffer key, ColumnPath column_path)
            throws InvalidRequestException, UnavailableException, TimedOutException, TException {
        //if (logger.isTraceEnabled()) {
        //    logger.trace("remove(key = {}, column_path = {})", new Object[]{printKey(key),column_path});
        //}

        long timestamp = 0;
        WriteResult result = findClient(key).remove(key, column_path, timestamp, consistencyLevel, clientContext.getDeps(), LamportClock.sendTimestamp());
        LamportClock.updateTime(result.lts);
        clientContext.clearDeps();
        clientContext.addDep(new Dep(key, result.version));
    }

    public void truncate(String cfname)
            throws InvalidRequestException, UnavailableException, TimedOutException, TException {
        //COPS2 WL TODO: Decide what to do with truncate
        //truncate is a strongly consistent operation in cassandra
        //option one is simply to modify to wait for all deps to be satisfied everywhere before truncating
        //option two is to just truncate now and let ops pending to that CF do nothing (other than count for dep_checks)
        // option two sounds better to me

        //TODO: Set the timestamp (version) to 0 so the accepting datacenter sets it
        long returnTime = getAnyClient().truncate(cfname, clientContext.getDeps(), LamportClock.sendTimestamp());
        LamportClock.updateTime(returnTime);
        clientContext.clearDeps();
        clientContext.addDep(ClientContext.NOT_YET_SUPPORTED);
    }

    public void add(ByteBuffer key, ColumnParent column_parent, CounterColumn column)
            throws InvalidRequestException, UnavailableException, TimedOutException, TException {
        //if (logger.isTraceEnabled()) {
        //    logger.trace("add(key = {}, column_parent = {}, column = {})", new Object[]{printKey(key),column_parent, column});
        //}

        WriteResult result = findClient(key).add(key, column_parent, column, consistencyLevel, clientContext.getDeps(), LamportClock.sendTimestamp());
        LamportClock.updateTime(result.lts);
        clientContext.clearDeps();
        clientContext.addDep(new Dep(key, result.version));
    }

    public void remove_counter(ByteBuffer key, ColumnPath path)
            throws InvalidRequestException, UnavailableException, TimedOutException, TException {
        remove_counter(key, path, false);
    }

    public void remove_counter_safe(ByteBuffer key, ColumnPath path)
            throws InvalidRequestException, UnavailableException, TimedOutException, TException {
        remove_counter(key, path, true);
    }

    private void remove_counter(ByteBuffer key, ColumnPath path, boolean safe)
            throws InvalidRequestException, UnavailableException, TimedOutException, TException {
        //if (logger.isTraceEnabled()) {
        //    logger.trace("remove_counter(key = {}, path = {})", new Object[]{printKey(key),path});
        //}

        //clients must wait until their remove counter has propagated everywhere before reissuing adds to it, so to be "safe" you delete with ALL consistency
        WriteResult result = findClient(key).remove_counter(key, path, safe ? ConsistencyLevel.ALL : consistencyLevel, clientContext.getDeps(), LamportClock.sendTimestamp());
        LamportClock.updateTime(result.lts);
        clientContext.clearDeps();
        clientContext.addDep(new Dep(key, result.version));
    }

    public void login(AuthenticationRequest auth_request)
            throws AuthorizationException, TException, AuthenticationException {
        //WL TODO: Should I have dependencies on this operation?
        for (Cassandra.Client client : addressToClient.values()) {
            long returnTime = client.login(auth_request, LamportClock.sendTimestamp());
            LamportClock.updateTime(returnTime);
        }
    }

    public void set_keyspace(String keyspace)
            throws InvalidRequestException, TException {
        //WL TODO: Should I have dependencies on this operation?
        for (Cassandra.Client client : addressToClient.values()) {
            long returnTime = client.set_keyspace(keyspace, LamportClock.sendTimestamp());
            LamportClock.updateTime(returnTime);
        }
    }

}
