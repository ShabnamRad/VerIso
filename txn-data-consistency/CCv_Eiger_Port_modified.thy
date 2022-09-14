section \<open>Modified Eiger Port Protocol Satisfying CCv (Causal+)\<close>

theory CCv_Eiger_Port_modified
  imports Execution_Tests
begin

subsection \<open>Event system & Refinement from ET_ES to tps\<close>

subsubsection \<open>State\<close>

typedecl svr_id
type_synonym tstmp = nat
consts loc :: "key \<Rightarrow> svr_id" 

record 'v ep_version = "'v version" +
  v_ts :: tstmp
  v_gst :: tstmp
  v_is_pending :: bool

type_synonym 'v datastore = "key \<Rightarrow> 'v ep_version list"

definition ep_version_init :: "'v ep_version" where
  "ep_version_init \<equiv> \<lparr>v_value = undefined, v_writer = T0, v_readerset = {},
    v_ts = 0, v_gst = 0, v_is_pending = False\<rparr>"

\<comment> \<open>Server State\<close>
datatype state_wtxn = Ready | Prep tstmp | Commit
datatype state_rtxn = NotReg | Regd
record 'v server =
  wtxn_state :: "txid0 \<Rightarrow> key \<Rightarrow> state_wtxn"
  rtxn_state :: "txid0 \<Rightarrow> key \<Rightarrow> state_rtxn"
  clock :: tstmp
  lst :: tstmp
  pending_wtxns :: "txid0 \<rightharpoonup> tstmp"
  DS :: "'v datastore"

definition DS_init :: "'v datastore" where
  "DS_init \<equiv> (\<lambda>k. [ep_version_init])"

\<comment> \<open>Client State\<close>
datatype 'v state_txn = Idle | RtxnInProg "key set" "key \<rightharpoonup> 'v" | WtxnPrep "key \<rightharpoonup> 'v" |
  WtxnCommit tstmp "key \<rightharpoonup> 'v"
record 'v client =
  txn_state :: "'v state_txn"
  txn_sn :: sqn
  gst :: tstmp
  lst_map :: "svr_id \<Rightarrow> tstmp"
  cl_view :: view

\<comment> \<open>Global State\<close>
record 'v state = 
  cls :: "cl_id \<Rightarrow> 'v client"
  svrs :: "svr_id \<Rightarrow> 'v server"

subsubsection \<open>Events\<close>

datatype 'v ev =
  RInvoke cl_id "key set" sqn view "'v fingerpr"| Read cl_id key 'v | RDone cl_id "key \<rightharpoonup> 'v" |
  WInvoke cl_id "key \<rightharpoonup> 'v" | WCommit cl_id "key \<rightharpoonup> 'v" tstmp sqn view "'v fingerpr" | WDone cl_id |
  RegR svr_id txid0 key 'v v_id tstmp | PrepW svr_id txid0 key 'v tstmp | CommitW svr_id txid0 key |
  Skip2

abbreviation get_txn_cl :: "'v state \<Rightarrow> cl_id \<Rightarrow> txid0" where
  "get_txn_cl s cl \<equiv> Tn_cl (txn_sn (cls s cl)) cl"

(*Assumption: vl is ordered from the newest to the oldest*)
fun at :: "'v ep_version list \<Rightarrow> tstmp \<Rightarrow> 'v ep_version \<times> v_id" where
  "at [] ts = (ep_version_init, 0)" |
  "at (ver # vl) ts = (if ts \<ge> v_ts ver then (ver, length vl) else at vl ts)"

(*Assumption: vl is ordered from the newest to the oldest*)
fun newest_own_write :: "'v ep_version list \<Rightarrow> tstmp \<Rightarrow> cl_id \<rightharpoonup> 'v ep_version \<times> v_id" where
  "newest_own_write [] ts cl = None" |
  "newest_own_write (v # vl) ts cl =
    (if v_ts v \<ge> ts then
      (case v_writer v of
        T0 \<Rightarrow> newest_own_write vl ts cl |
        Tn (Tn_cl sn cl') \<Rightarrow> (if cl' = cl then Some (v, length vl) else newest_own_write vl ts cl))
     else None)"

(*Assumption: vl is ordered from the newest to the oldest*)
definition read_at :: "'v ep_version list \<Rightarrow> tstmp \<Rightarrow> cl_id \<Rightarrow> 'v \<times> v_id" where
  "read_at vl ts cl \<equiv> let (ver, i) = at vl ts in
    (case newest_own_write vl (v_ts ver) cl of
      None \<Rightarrow> (v_value ver, i) | Some (ver', i') \<Rightarrow> (v_value ver', i'))"

\<comment> \<open>Clint Events\<close>
definition read_invoke :: "cl_id \<Rightarrow> key set \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> 'v fingerpr \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read_invoke cl keys sn u F s s' \<equiv> 
    sn = txn_sn (cls s cl) \<and>
    u = cl_view (cls s cl) \<and>
    (\<forall>k. F k W = None) \<and> (\<forall>k. k \<notin> keys \<longrightarrow> F k R = None) \<and>
    (\<forall>k \<in> keys. \<exists>v i. F k R = Some v \<and>
     (v, i) = read_at (rev (DS (svrs s (loc k)) k)) (gst (cls s cl)) cl \<and>
     cl_view (cls s' cl) k = insert i (cl_view (cls s cl) k)) \<and>
    txn_state (cls s cl) = Idle \<and>
    txn_state (cls s' cl) = RtxnInProg keys (Map.empty) \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = max (gst (cls s cl)) (Min (range (lst_map (cls s cl)))) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    (\<forall>k'. k' \<notin> keys \<longrightarrow> cl_view (cls s' cl)k' = cl_view (cls s cl) k') \<and>
    svrs s' = svrs s"

fun find_and_read_val :: "'v ep_version list \<Rightarrow> txid0 \<rightharpoonup> 'v" where
  "find_and_read_val [] t = None" |
  "find_and_read_val (ver # vl) t =
    (if t \<in> v_readerset ver then Some (v_value ver) else find_and_read_val vl t)"

definition read :: "cl_id \<Rightarrow> key \<Rightarrow> 'v \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read cl k v s s' \<equiv> \<exists>keys vals.
    rtxn_state (svrs s (loc k)) (get_txn_cl s cl) k = Regd \<and>
    Some v = find_and_read_val (rev (DS (svrs s (loc k)) k)) (get_txn_cl s cl) \<and>
    txn_state (cls s cl) = RtxnInProg keys vals \<and> k \<in> keys \<and> vals k = None \<and>
    txn_state (cls s' cl) = RtxnInProg keys (vals (k \<mapsto> v)) \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) (loc k) = lst (svrs s (loc k)) \<and>
    (\<forall>l. l \<noteq> loc k \<longrightarrow> lst_map (cls s' cl) = lst_map (cls s cl)) \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    svrs s' = svrs s"

definition read_done :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read_done cl vals s s' \<equiv> (\<exists>keys.
    txn_state (cls s cl) = RtxnInProg keys vals \<and> dom vals = keys \<and>
    (\<forall>k\<in>keys. rtxn_state (svrs s (loc k)) (get_txn_cl s cl) k = Regd)) \<and>
    txn_state (cls s' cl) = Idle \<and>
    txn_sn (cls s' cl) = Suc (txn_sn (cls s cl)) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    svrs s' = svrs s"

definition write_invoke :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "write_invoke cl kv_map s s' \<equiv> 
    kv_map \<noteq> Map.empty \<and>
    txn_state (cls s cl) = Idle \<and>
    txn_state (cls s' cl) = WtxnPrep kv_map \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    svrs s' = svrs s"

definition write_commit :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> tstmp \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> 'v fingerpr \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "write_commit cl kv_map commit_t sn u F s s' \<equiv>
    sn = txn_sn (cls s cl) \<and>
    u = cl_view (cls s cl) \<and>
    (\<forall>k. F k R = None) \<and> (\<forall>k. F k W = kv_map k) \<and>
    txn_state (cls s cl) = WtxnPrep kv_map \<and>
    (\<forall>k \<in> dom kv_map. \<exists>prep_t.
      wtxn_state (svrs s (loc k)) (get_txn_cl s cl) k = Prep prep_t) \<and>
    commit_t = Max {prep_t. (\<exists>k \<in> dom kv_map.
      wtxn_state (svrs s (loc k)) (get_txn_cl s cl) k = Prep prep_t)} \<and>
    txn_state (cls s' cl) = WtxnCommit commit_t kv_map \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    \<comment> \<open>update cl_view\<close>
    svrs s' = svrs s"

definition write_done :: "cl_id \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "write_done cl s s' \<equiv> \<exists>kv_map commit_t.
    txn_state (cls s cl) = WtxnCommit commit_t kv_map \<and>
    (\<forall>k\<in>dom kv_map. wtxn_state (svrs s (loc k)) (get_txn_cl s cl) k = Commit) \<and>
    txn_state (cls s' cl) = Idle \<and>
    txn_sn (cls s' cl) = Suc (txn_sn (cls s cl)) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    (\<forall>l. l \<in> loc ` (dom kv_map) \<longrightarrow> lst_map (cls s' cl) l = lst (svrs s l)) \<and>
    (\<forall>l. l \<notin> loc ` (dom kv_map) \<longrightarrow> lst_map (cls s' cl) l = lst_map (cls s cl) l) \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    svrs s' = svrs s"

\<comment> \<open>Server Events\<close>
definition register_read :: "svr_id \<Rightarrow> txid0 \<Rightarrow> key \<Rightarrow> 'v \<Rightarrow> v_id \<Rightarrow> tstmp \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "register_read svr t k v i gst_ts s s' \<equiv> \<exists>keys vals.
    txn_state (cls s (get_cl_txn t)) = RtxnInProg keys vals \<and> k \<in> keys \<and> vals k = None \<and>
    (v, i) = read_at (rev (DS (svrs s svr) k)) gst_ts (get_cl_txn t) \<and>
    gst_ts = gst (cls s (get_cl_txn t)) \<and>
    loc k = svr \<and>
    rtxn_state (svrs s svr) t k = NotReg \<and>
    rtxn_state (svrs s' svr) t k = Regd \<and>
    (\<forall>t' k'. t' \<noteq> t \<or> k' \<noteq> k \<longrightarrow> rtxn_state (svrs s' svr) t' k' = rtxn_state (svrs s svr) t' k') \<and>
    wtxn_state (svrs s' svr) = wtxn_state (svrs s svr) \<and>
    clock (svrs s' svr) = Suc (clock (svrs s svr)) \<and>
    lst (svrs s' svr) = lst (svrs s svr) \<and>
    pending_wtxns (svrs s' svr) = pending_wtxns (svrs s svr) \<and>
    DS (svrs s' svr) k = (DS (svrs s svr) k) [i :=
      (DS (svrs s svr) k ! i)\<lparr>v_readerset := insert t (v_readerset (DS (svrs s svr) k ! i))\<rparr>] \<and>
    (\<forall>k'. k' \<noteq> k \<longrightarrow> DS (svrs s' svr) k' = DS (svrs s svr) k') \<and>
    cls s' = cls s"

definition prepare_write :: "svr_id \<Rightarrow> txid0 \<Rightarrow> key \<Rightarrow> 'v \<Rightarrow> tstmp \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "prepare_write svr t k v gst_ts s s' \<equiv> \<exists>kv_map.
    txn_state (cls s (get_cl_txn t)) = WtxnPrep kv_map \<and> k \<in> dom kv_map \<and> kv_map k = Some v \<and>
    gst_ts =  (gst (cls s (get_cl_txn t))) \<and> 
    loc k = svr \<and>
    wtxn_state (svrs s svr) t k = Ready \<and>
    wtxn_state (svrs s' svr) t k = Prep (clock (svrs s' svr)) \<and>
    (\<forall>t' k'. t' \<noteq> t \<or> k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' svr) t' k' = wtxn_state (svrs s svr) t' k') \<and>
    rtxn_state (svrs s' svr) = rtxn_state (svrs s svr) \<and>
    clock (svrs s' svr) = Suc (clock (svrs s svr)) \<and>
    lst (svrs s' svr) = lst (svrs s svr) \<and>
    pending_wtxns (svrs s' svr) t = Some (clock (svrs s svr)) \<and>
    (\<forall>t'. t' \<noteq> t \<longrightarrow> pending_wtxns (svrs s' svr) t' = pending_wtxns (svrs s svr) t') \<and>
    DS (svrs s' svr) k = DS (svrs s svr) k @
      [\<lparr>v_value = v, v_writer = Tn t, v_readerset = {}, v_ts = clock (svrs s svr),
       v_gst = gst_ts, v_is_pending = True\<rparr>] \<and>
    (\<forall>k'. k' \<noteq> k \<longrightarrow> DS (svrs s' svr) k' = DS (svrs s svr) k') \<and>
    cls s' = cls s"

fun find_and_commit :: "'v ep_version list \<Rightarrow> txid \<Rightarrow> tstmp \<Rightarrow> 'v ep_version list" where
  "find_and_commit [] t commit_t = []" |
  "find_and_commit (v # vl) t commit_t =
    (if v_writer v = t then
      v \<lparr>v_ts := commit_t, v_is_pending := False\<rparr> # vl
    else v # (find_and_commit vl t commit_t))"

definition commit_write :: "svr_id \<Rightarrow> txid0 \<Rightarrow> key \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "commit_write svr t k s s' \<equiv> \<exists>kv_map commit_t.
    txn_state (cls s (get_cl_txn t)) = WtxnCommit commit_t kv_map \<and> k \<in> dom kv_map \<and>
    loc k = svr \<and>
    (\<exists>prep_t. wtxn_state (svrs s svr) t k = Prep prep_t) \<and>
    wtxn_state (svrs s' svr) t k = Commit \<and>
    (\<forall>t' k'. t' \<noteq> t \<or> k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' svr) t' k' = wtxn_state (svrs s svr) t' k) \<and>
    rtxn_state (svrs s' svr) = rtxn_state (svrs s svr) \<and>
    clock (svrs s' svr) = clock (svrs s svr) \<and>
    lst (svrs s' svr) =
      (if dom (pending_wtxns (svrs s' svr)) = {} then clock (svrs s svr)
       else Min (ran (pending_wtxns (svrs s' svr)))) \<and>
    pending_wtxns (svrs s' svr) t = None \<and>
    (\<forall>t'. t' \<noteq> t \<longrightarrow> pending_wtxns (svrs s' svr) t' = pending_wtxns (svrs s svr) t') \<and>
    DS (svrs s' svr) k = find_and_commit (DS (svrs s svr) k) (Tn t) commit_t \<and>
    (\<forall>k'. k' \<noteq> k \<longrightarrow> DS (svrs s' svr) k' = DS (svrs s svr) k')"

subsubsection \<open>The Event System\<close>

definition state_init :: "'v state" where
  "state_init \<equiv> \<lparr> 
    cls = (\<lambda>cl. \<lparr> txn_state = Idle,
                  txn_sn = 0,
                  gst = 0,
                  lst_map = (\<lambda>svr. 0),
                  cl_view = view_init \<rparr>),
    svrs = (\<lambda>svr. \<lparr> wtxn_state = (\<lambda>t k. Ready),
                    rtxn_state = (\<lambda>t k. NotReg),
                    clock = 0,
                    lst = 0,
                    pending_wtxns = Map.empty,
                    DS = DS_init \<rparr>)
  \<rparr>"

fun state_trans :: "'v state \<Rightarrow> 'v ev \<Rightarrow> 'v state \<Rightarrow> bool" where
  "state_trans s (RInvoke cl keys sn u F) s' \<longleftrightarrow> read_invoke cl keys sn u F s s'" |
  "state_trans s (Read cl k v)            s' \<longleftrightarrow> read cl k v s s'" |
  "state_trans s (RDone cl kv_map)        s' \<longleftrightarrow> read_done cl kv_map s s'" |
  "state_trans s (WInvoke cl kv_map)      s' \<longleftrightarrow> write_invoke cl kv_map s s'" |
  "state_trans s (WCommit cl kv_map cts sn u F)  s' \<longleftrightarrow> write_commit cl kv_map cts sn u F s s'" |
  "state_trans s (WDone cl)               s' \<longleftrightarrow> write_done cl s s'" |
  "state_trans s (RegR svr t k v i gts)   s' \<longleftrightarrow> register_read svr t k v i gts s s'" |
  "state_trans s (PrepW svr t k v gts)    s' \<longleftrightarrow> prepare_write svr t k v gts s s'" |
  "state_trans s (CommitW svr t k)        s' \<longleftrightarrow> commit_write svr t k s s'" |
  "state_trans s Skip2 s' \<longleftrightarrow> s' = s"

definition tps :: "('v ev, 'v state) ES" where
  "tps \<equiv> \<lparr>
    init = (=) state_init,
    trans = state_trans
  \<rparr>"

lemmas tps_trans_defs = read_invoke_def read_def read_done_def write_invoke_def write_commit_def
  write_done_def register_read_def prepare_write_def commit_write_def

lemmas tps_defs = tps_def state_init_def

lemma tps_trans [simp]: "trans tps = state_trans" by (simp add: tps_def)

subsubsection \<open>Refinement\<close>

\<comment> \<open>Simulation function\<close>
definition get_ver :: "'v ep_version \<Rightarrow> 'v version" where
  "get_ver v \<equiv> \<lparr>v_value = v_value v, v_writer = v_writer v, v_readerset = v_readerset v\<rparr>"

\<comment> \<open>TODO: define this properly\<close>
definition kvs_of_s :: "'v state \<Rightarrow> 'v kv_store" where
  "kvs_of_s s = (\<lambda>k. map get_ver (DS (svrs s (loc k)) k))"

definition views_of_s :: "'v state \<Rightarrow> (cl_id \<Rightarrow> view)" where
  "views_of_s s = (\<lambda>cl. cl_view (cls s cl))"

definition sim :: "'v state \<Rightarrow> 'v config" where         
  "sim s = (kvs_of_s s, views_of_s s)"

(*lemmas update_kv_reads_all_defs = update_kv_reads_all_txn_def Let_def last_version_def
lemmas update_kv_all_defs = update_kv_reads_all_defs update_kv_writes_all_txn_def update_kv_all_txn_def*)
lemmas sim_defs = sim_def kvs_of_s_def views_of_s_def

\<comment> \<open>Mediator function\<close>
fun med :: "'v ev \<Rightarrow> 'v label" where
  "med (RInvoke cl _ sn u F) = ET cl sn u F" |
  "med (WCommit cl _ _ sn u F) = ET cl sn u F" |
  "med _ = ETSkip"

