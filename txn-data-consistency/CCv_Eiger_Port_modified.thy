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
datatype 'v state_wtxn = Ready | Prep tstmp 'v | Commit 'v
record 'v server =
  wtxn_state :: "txid0 \<Rightarrow> key \<Rightarrow> 'v state_wtxn"
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

\<comment> \<open>Global State\<close>
record 'v state = 
  cls :: "cl_id \<Rightarrow> 'v client"
  svrs :: "svr_id \<Rightarrow> 'v server"

subsubsection \<open>Events\<close>

datatype 'v ev = RInvoke cl_id "key set" | Read cl_id key 'v | RDone cl_id "key \<rightharpoonup> 'v" |
  WInvoke cl_id "key \<rightharpoonup> 'v" | WriteAll cl_id "key \<rightharpoonup> 'v" tstmp | WDone cl_id |
  WPrep svr_id txid0 key 'v | WCommit svr_id txid0 key | Skip2

fun at :: "'v ep_version list \<Rightarrow> tstmp \<Rightarrow> 'v ep_version" where
  "at [] ts = ep_version_init" |
  "at (ver # vl) ts = (if ts \<ge> v_ts ver then ver else at vl ts)"

fun newest_own_write :: "'v ep_version list \<Rightarrow> tstmp \<Rightarrow> cl_id \<Rightarrow> 'v ep_version option" where
  "newest_own_write [] ts cl = None" |
  "newest_own_write (v # vl) ts cl =
    (if v_ts v \<ge> ts then
      (case v_writer v of
        T0 \<Rightarrow> newest_own_write vl ts cl |
        Tn (Tn_cl sn cl') \<Rightarrow> (if cl' = cl then Some v else newest_own_write vl ts cl))
     else None)"

\<comment> \<open>Clint Events\<close>
definition read_invoke :: "cl_id \<Rightarrow> key set \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read_invoke cl keys s s' \<equiv> 
    txn_state (cls s cl) = Idle \<and>
    txn_state (cls s' cl) = RtxnInProg keys (Map.empty) \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = max (gst (cls s cl)) (Min (range (lst_map (cls s cl)))) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    svrs s' = svrs s"

definition read :: "cl_id \<Rightarrow> key \<Rightarrow> 'v \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read cl k v s s' \<equiv> \<exists>keys vals.
    txn_state (cls s cl) = RtxnInProg keys vals \<and> k \<in> keys \<and> vals k = None \<and>
    txn_state (cls s' cl) = RtxnInProg keys (vals (k \<mapsto> v)) \<and>
    v = (let vl = (DS (svrs s (loc k)) k); ver = at vl (gst (cls s cl)) in
      (case newest_own_write vl (v_ts ver) cl of None \<Rightarrow> v_value ver | Some ver' \<Rightarrow> v_value ver')) \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) (loc k) = lst (svrs s (loc k)) \<and>
    (\<forall>l. l \<noteq> loc k \<longrightarrow> lst_map (cls s' cl) = lst_map (cls s cl)) \<and>
    svrs s' = svrs s"

definition read_done :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read_done cl vals s s' \<equiv> \<exists>keys.
    txn_state (cls s cl) = RtxnInProg keys vals \<and> dom vals = keys \<and>
    txn_state (cls s' cl) = Idle \<and>
    txn_sn (cls s' cl) = Suc (txn_sn (cls s cl)) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    svrs s' = svrs s"

definition write_invoke :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "write_invoke cl kv_map s s' \<equiv> 
    txn_state (cls s cl) = Idle \<and>
    txn_state (cls s' cl) = WtxnPrep kv_map \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    svrs s' = svrs s"

definition write_all :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> tstmp \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "write_all cl kv_map commit_t s s' \<equiv>
    txn_state (cls s cl) = WtxnPrep kv_map \<and>
    (\<forall>k\<in>dom kv_map. \<exists>prep_t v.
      wtxn_state (svrs s (loc k)) (Tn_cl (txn_sn (cls s cl)) cl) k = Prep prep_t v \<and> 
      kv_map k = Some v \<and> prep_t \<le> commit_t) \<and>
    txn_state (cls s' cl) = WtxnCommit commit_t kv_map \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    svrs s' = svrs s"

definition write_done :: "cl_id \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "write_done cl s s' \<equiv> \<exists>kv_map commit_t.
    txn_state (cls s cl) = WtxnCommit commit_t kv_map \<and>
    (\<forall>k\<in>dom kv_map. \<exists>v. wtxn_state (svrs s (loc k)) (Tn_cl (txn_sn (cls s cl)) cl) k = Commit v \<and>
       kv_map k = Some v) \<and>
    txn_state (cls s' cl) = Idle \<and>
    txn_sn (cls s' cl) = Suc (txn_sn (cls s cl)) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    (\<forall>l. l \<in> loc ` (dom kv_map) \<longrightarrow> lst_map (cls s' cl) l = lst (svrs s l)) \<and>
    (\<forall>l. l \<notin> loc ` (dom kv_map) \<longrightarrow> lst_map (cls s' cl) l = lst_map (cls s cl) l) \<and>
    svrs s' = svrs s"

\<comment> \<open>Server Events\<close>
definition prepare_write :: "svr_id \<Rightarrow> txid0 \<Rightarrow> key \<Rightarrow> 'v \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "prepare_write svr t k v s s' \<equiv> \<exists>kv_map.
    txn_state (cls s (get_cl_txn t)) = WtxnPrep kv_map \<and> k \<in> dom kv_map \<and> kv_map k = Some v \<and>
    wtxn_state (svrs s svr) t k = Ready \<and>
    wtxn_state (svrs s' svr) t k = Prep (clock (svrs s' svr)) v \<and>
    (\<forall>t' k'. t' \<noteq> t \<or> k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' svr) t' = wtxn_state (svrs s svr) t') \<and>
    loc k = svr \<and>
    clock (svrs s' svr) = Suc (clock (svrs s svr)) \<and>
    lst (svrs s' svr) = lst (svrs s svr) \<and>
    pending_wtxns (svrs s' svr) t = Some (clock (svrs s svr)) \<and>
    (\<forall>t'. t' \<noteq> t \<longrightarrow> pending_wtxns (svrs s' svr) t' = pending_wtxns (svrs s svr) t') \<and>
    DS (svrs s' svr) k =
      \<lparr>v_value = v, v_writer = Tn t, v_readerset = {}, v_ts = clock (svrs s svr),
       v_gst = (gst (cls s (get_cl_txn t))), v_is_pending = True\<rparr> # DS (svrs s svr) k \<and>
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
    (\<exists>prep_t v. wtxn_state (svrs s svr) t k = Prep prep_t v \<and> kv_map k = Some v \<and>
      wtxn_state (svrs s' svr) t k = Commit v) \<and>
    (\<forall>t' k'. t' \<noteq> t \<or> k' \<noteq> k \<longrightarrow> pending_wtxns (svrs s' svr) t' = pending_wtxns (svrs s svr) t') \<and>
    loc k = svr \<and>
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
                  lst_map = (\<lambda>svr. 0) \<rparr>),
    svrs = (\<lambda>svr. \<lparr> wtxn_state = (\<lambda>t k. Ready),
                    clock = 0,
                    lst = 0,
                    pending_wtxns = Map.empty,
                    DS = DS_init \<rparr>)
  \<rparr>"

fun state_trans :: "'v state \<Rightarrow> 'v ev \<Rightarrow> 'v state \<Rightarrow> bool" where
  "state_trans s (RInvoke cl keys)        s' \<longleftrightarrow> read_invoke cl keys s s'" |
  "state_trans s (Read cl k v)            s' \<longleftrightarrow> read cl k v s s'" |
  "state_trans s (RDone cl kv_map)        s' \<longleftrightarrow> read_done cl kv_map s s'" |
  "state_trans s (WInvoke cl kv_map)      s' \<longleftrightarrow> write_invoke cl kv_map s s'" |
  "state_trans s (WriteAll cl kv_map cts) s' \<longleftrightarrow> write_all cl kv_map cts s s'" |
  "state_trans s (WDone cl)               s' \<longleftrightarrow> write_done cl s s'" |
  "state_trans s (WPrep svr t k v)        s' \<longleftrightarrow> prepare_write svr t k v s s'" |
  "state_trans s (WCommit svr t k)        s' \<longleftrightarrow> commit_write svr t k s s'" |
  "state_trans s Skip2 s' \<longleftrightarrow> s' = s"

definition tps :: "('v ev, 'v state) ES" where
  "tps \<equiv> \<lparr>
    init = (=) state_init,
    trans = state_trans
  \<rparr>"

lemmas tps_trans_defs = read_invoke_def read_def read_done_def write_invoke_def write_all_def
  write_done_def prepare_write_def commit_write_def

lemmas tps_defs = tps_def state_init_def

lemma tps_trans [simp]: "trans tps = state_trans" by (simp add: tps_def)
