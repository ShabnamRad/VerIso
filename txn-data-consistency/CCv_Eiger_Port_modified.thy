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
record 'v server =
  clock :: tstmp
  lst :: tstmp
  pending_wtxns :: "txid0 \<rightharpoonup> tstmp"
  DS :: "'v datastore"

\<comment> \<open>Client State\<close>
datatype 'v state_txn = Idle | RtxnInProg "key set" "key \<rightharpoonup> 'v" | WtxnInProg svr_id "key \<rightharpoonup> 'v"
record 'v client =
  txn_state :: "'v state_txn"
  txn_sn :: sqn
  gst :: tstmp
  lst_map :: "svr_id \<Rightarrow> tstmp"

\<comment> \<open>Global State\<close>
record 'v state = 
  svrs :: "svr_id \<Rightarrow> 'v server"
  cls :: "cl_id \<Rightarrow> 'v client"

\<comment> \<open>Events\<close>

datatype 'v ev = RInvoke "key set" cl_id | Read key 'v tstmp cl_id | RDone "key \<rightharpoonup> 'v" cl_id

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

definition read_invoke :: "key set \<Rightarrow> cl_id \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read_invoke keys cl s s' \<equiv> 
    txn_state (cls s cl) = Idle \<and>
    txn_state (cls s' cl) = RtxnInProg keys (Map.empty) \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = max (gst (cls s cl)) (Min (range (lst_map (cls s cl)))) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    svrs s' = svrs s"

definition read :: "key \<Rightarrow> 'v \<Rightarrow> cl_id \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read k v cl s s' \<equiv> \<exists>keys vals.
    txn_state (cls s cl) = RtxnInProg keys vals \<and> k \<in> keys \<and> vals k = None \<and>
    txn_state (cls s' cl) = RtxnInProg keys (vals (k \<mapsto> v)) \<and>
    v = (let vl = (DS (svrs s (loc k)) k); ver = at vl (gst (cls s cl)) in
      (case newest_own_write vl (v_ts ver) cl of None \<Rightarrow> v_value ver | Some ver' \<Rightarrow> v_value ver')) \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) (loc k) = lst (svrs s (loc k)) \<and>
    (\<forall>l. l \<noteq> loc k \<longrightarrow> lst_map (cls s' cl) = lst_map (cls s cl)) \<and>
    svrs s' = svrs s"

definition read_done :: "(key \<rightharpoonup> 'v) \<Rightarrow> cl_id \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read_done vals cl s s' \<equiv> \<exists>keys.
    txn_state (cls s cl) = RtxnInProg keys vals \<and> dom vals = keys \<and>
    txn_state (cls s' cl) = Idle \<and>
    txn_sn (cls s' cl) = Suc (txn_sn (cls s cl)) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    svrs s' = svrs s"


definition prepare_write :: "key \<Rightarrow> 'v \<Rightarrow> sqn \<Rightarrow> cl_id \<Rightarrow> tstmp \<Rightarrow> svr_id \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "prepare_write k v sn cl gst_ts svr s s' \<equiv>
    loc k = svr \<and>
    clock (svrs s' svr) = Suc (clock (svrs s svr)) \<and>
    lst (svrs s' svr) = lst (svrs s svr) \<and>
    pending_wtxns (svrs s' svr) (Tn_cl sn cl) = Some (clock (svrs s svr)) \<and>
    (\<forall>t'. t' \<noteq> Tn_cl sn cl \<longrightarrow> pending_wtxns (svrs s' svr) t' = pending_wtxns (svrs s svr) t') \<and>
    DS (svrs s' svr) k =
      \<lparr>v_value = v, v_writer = Tn (Tn_cl sn cl), v_readerset = {},
        v_ts = clock (svrs s svr), v_gst = gst_ts, v_is_pending = True\<rparr> # DS (svrs s svr) k \<and>
    (\<forall>k'. k' \<noteq> k \<longrightarrow> DS (svrs s' svr) k' = DS (svrs s svr) k') \<and>
    cls s' = cls s"

fun find_and_commit :: "'v ep_version list \<Rightarrow> txid \<Rightarrow> tstmp \<Rightarrow> 'v ep_version list" where
  "find_and_commit [] t commit_t = []" |
  "find_and_commit (v # vl) t commit_t =
    (if v_writer v = t then
      v \<lparr>v_ts := commit_t, v_is_pending := False\<rparr> # vl
    else v # (find_and_commit vl t commit_t))"

definition commit_write :: "key \<Rightarrow> sqn \<Rightarrow> cl_id \<Rightarrow> tstmp \<Rightarrow> svr_id \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "commit_write k sn cl commit_t svr s s' \<equiv>
    loc k = svr \<and>
    clock (svrs s' svr) = clock (svrs s svr) \<and>
    lst (svrs s' svr) =
      (if dom (pending_wtxns (svrs s' svr)) = {} then clock (svrs s svr)
       else Min (ran (pending_wtxns (svrs s' svr)))) \<and>
    pending_wtxns (svrs s' svr) (Tn_cl sn cl) = None \<and>
    (\<forall>t'. t' \<noteq> Tn_cl sn cl \<longrightarrow> pending_wtxns (svrs s' svr) t' = pending_wtxns (svrs s svr) t') \<and>
    DS (svrs s' svr) k = find_and_commit (DS (svrs s svr) k) (Tn (Tn_cl sn cl)) commit_t \<and>
    (\<forall>k'. k' \<noteq> k \<longrightarrow> DS (svrs s' svr) k' = DS (svrs s svr) k')"

(*definition write_coord :: "key \<Rightarrow> 'v \<Rightarrow> cl_id \<Rightarrow> tstmp \<Rightarrow> tstmp" where
  "write_coord k v cl ts \<equiv> "*)