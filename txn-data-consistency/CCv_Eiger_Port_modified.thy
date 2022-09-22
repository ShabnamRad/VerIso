section \<open>Modified Eiger Port Protocol Satisfying CCv (Causal+)\<close>

theory CCv_Eiger_Port_modified
  imports Execution_Tests
begin

subsection \<open>Event system & Refinement from ET_ES to tps\<close>

subsubsection \<open>State\<close>

type_synonym svr_id = key
type_synonym tstmp = nat

record 'v ep_version = "'v version" +
  v_ts :: tstmp
  v_gst :: tstmp
  v_is_pending :: bool

type_synonym 'v datastore = "key \<Rightarrow> 'v ep_version list"

definition ep_version_init :: "'v ep_version" where
  "ep_version_init \<equiv> \<lparr>v_value = undefined, v_writer = T0, v_readerset = {},
    v_ts = 0, v_gst = 0, v_is_pending = False\<rparr>"

\<comment> \<open>Server State\<close>
datatype state_wtxn = Ready | Prep tstmp v_id | Commit
record 'v server =
  wtxn_state :: "txid0 \<Rightarrow> state_wtxn"
  clock :: tstmp
  lst :: tstmp
  pending_wtxns :: "txid0 \<rightharpoonup> tstmp"
  DS :: "'v ep_version list"

definition DS_vl_init :: "'v ep_version list" where
  "DS_vl_init \<equiv> [ep_version_init]"

definition DS_init :: "'v datastore" where
  "DS_init \<equiv> (\<lambda>k. DS_vl_init)"

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
  RInvoke cl_id "key set" | Read cl_id key 'v | RDone cl_id "key \<rightharpoonup> 'v" sqn view |
  WInvoke cl_id "key \<rightharpoonup> 'v" | WCommit cl_id "key \<rightharpoonup> 'v" tstmp sqn view | WDone cl_id |
  RegR svr_id txid0 'v v_id tstmp | PrepW svr_id txid0 'v tstmp | CommitW svr_id txid0 | Skip2

definition svr_t'_unchanged where
  "svr_t'_unchanged t k s s' \<equiv> (\<forall>t'. t' \<noteq> t \<longrightarrow>
    wtxn_state (svrs s' k) t' = wtxn_state (svrs s k) t' \<and>
    pending_wtxns (svrs s' k) t' = pending_wtxns (svrs s k) t')"

definition other_insts_unchanged where
  "other_insts_unchanged e s s' \<equiv> (\<forall>e'. e' \<noteq> e \<longrightarrow> s' e' = s e')"

definition cls_svr_k'_t'_unchanged where
  "cls_svr_k'_t'_unchanged t k s s' \<equiv> cls s' = cls s \<and>
    other_insts_unchanged k (svrs s) (svrs s') \<and> svr_t'_unchanged t k s s'"

definition svrs_cls_cl'_unchanged where
  "svrs_cls_cl'_unchanged cl s s' \<equiv> svrs s' = svrs s \<and> other_insts_unchanged cl (cls s) (cls s')"

lemmas km_unchanged_defs = cls_svr_k'_t'_unchanged_def other_insts_unchanged_def svr_t'_unchanged_def
lemmas tm_unchanged_defs = svrs_cls_cl'_unchanged_def other_insts_unchanged_def
lemmas unchanged_defs = km_unchanged_defs svrs_cls_cl'_unchanged_def

definition tid_match :: "'v state \<Rightarrow> txid0 \<Rightarrow> bool" where
  "tid_match s t \<equiv> txn_sn (cls s (get_cl_txn t)) = get_sn_txn t"

abbreviation add_to_readerset :: "'v ep_version list \<Rightarrow> txid0 \<Rightarrow> v_id \<Rightarrow> 'v ep_version list" where
  "add_to_readerset vl t i \<equiv> vl [i := (vl ! i)\<lparr>v_readerset := insert t (v_readerset (vl ! i))\<rparr>]"

abbreviation commit_in_vl :: "'v ep_version list \<Rightarrow> tstmp \<Rightarrow> v_id \<Rightarrow> 'v ep_version list" where
  "commit_in_vl vl commit_t i \<equiv> vl [i := (vl ! i)\<lparr>v_ts := commit_t, v_is_pending := False\<rparr>]"

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
definition read_invoke :: "cl_id \<Rightarrow> key set \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read_invoke cl keys s s' \<equiv>
    txn_state (cls s cl) = Idle \<and>
    txn_state (cls s' cl) = RtxnInProg keys (Map.empty) \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = max (gst (cls s cl)) (Min (range (lst_map (cls s cl)))) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    svrs_cls_cl'_unchanged cl s s'"

fun find_and_read_val :: "'v ep_version list \<Rightarrow> txid0 \<rightharpoonup> 'v" where
  "find_and_read_val [] t = None" |
  "find_and_read_val (ver # vl) t =
    (if t \<in> v_readerset ver then Some (v_value ver) else find_and_read_val vl t)"

definition read :: "cl_id \<Rightarrow> key \<Rightarrow> 'v \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read cl k v s s' \<equiv> \<exists>keys vals.
    Some v = find_and_read_val (rev (DS (svrs s k))) (get_txn_cl s cl) \<and>
    txn_state (cls s cl) = RtxnInProg keys vals \<and> k \<in> keys \<and> vals k = None \<and>
    txn_state (cls s' cl) = RtxnInProg keys (vals (k \<mapsto> v)) \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) k = lst (svrs s k) \<and>
    (\<forall>k'. k' \<noteq> k \<longrightarrow> lst_map (cls s' cl) k' = lst_map (cls s cl) k') \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    svrs_cls_cl'_unchanged cl s s'"

definition read_done :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read_done cl kv_map sn u s s' \<equiv>
    sn = txn_sn (cls s cl) \<and>
    u = cl_view (cls s cl) \<and>
    (\<forall>k \<in> dom kv_map. \<exists>v i.
     (v, i) = read_at (rev (DS (svrs s k))) (gst (cls s cl)) cl \<and>
     cl_view (cls s' cl) k = insert i (cl_view (cls s cl) k)) \<and>
    (\<exists>keys. txn_state (cls s cl) = RtxnInProg keys kv_map \<and> dom kv_map = keys) \<and>
    txn_state (cls s' cl) = Idle \<and>
    txn_sn (cls s' cl) = Suc (txn_sn (cls s cl)) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    (\<forall>k. k \<notin> dom kv_map \<longrightarrow> cl_view (cls s' cl) k = cl_view (cls s cl) k) \<and>
    svrs_cls_cl'_unchanged cl s s'"

definition write_invoke :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "write_invoke cl kv_map s s' \<equiv> 
    kv_map \<noteq> Map.empty \<and>
    txn_state (cls s cl) = Idle \<and>
    txn_state (cls s' cl) = WtxnPrep kv_map \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    svrs_cls_cl'_unchanged cl s s'"

definition write_commit :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> tstmp \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "write_commit cl kv_map commit_t sn u s s' \<equiv>
    sn = txn_sn (cls s cl) \<and>
    u = cl_view (cls s cl) \<and>
    txn_state (cls s cl) = WtxnPrep kv_map \<and>
    (\<forall>k \<in> dom kv_map. \<exists>prep_t i.
      wtxn_state (svrs s k) (get_txn_cl s cl) = Prep prep_t i \<and>
      cl_view (cls s' cl) k = insert i (cl_view (cls s cl) k)) \<and> \<comment> \<open>use Let\<close>
    commit_t = Max {prep_t. (\<exists>k \<in> dom kv_map. \<exists>i.
      wtxn_state (svrs s k) (get_txn_cl s cl) = Prep prep_t i)} \<and>
    txn_state (cls s' cl) = WtxnCommit commit_t kv_map \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    (\<forall>k. k \<notin> dom kv_map \<longrightarrow> cl_view (cls s' cl) k = cl_view (cls s cl) k) \<and>
    svrs_cls_cl'_unchanged cl s s'"

definition write_done :: "cl_id \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "write_done cl s s' \<equiv> \<exists>kv_map commit_t.
    txn_state (cls s cl) = WtxnCommit commit_t kv_map \<and>
    (\<forall>k\<in>dom kv_map. wtxn_state (svrs s k) (get_txn_cl s cl) = Commit) \<and>
    txn_state (cls s' cl) = Idle \<and>
    txn_sn (cls s' cl) = Suc (txn_sn (cls s cl)) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    (\<forall>k. k \<in> dom kv_map \<longrightarrow> lst_map (cls s' cl) k = lst (svrs s k)) \<and>
    (\<forall>k. k \<notin> dom kv_map \<longrightarrow> lst_map (cls s' cl) k = lst_map (cls s cl) k) \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    svrs_cls_cl'_unchanged cl s s'"

\<comment> \<open>Server Events\<close>
definition register_read :: "svr_id \<Rightarrow> txid0 \<Rightarrow> 'v \<Rightarrow> v_id \<Rightarrow> tstmp \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "register_read svr t v i gst_ts s s' \<equiv>
    tid_match s t \<and>
    (\<exists>keys vals.
      txn_state (cls s (get_cl_txn t)) = RtxnInProg keys vals \<and> svr \<in> keys \<and> vals svr = None) \<and>
    (v, i) = read_at (rev (DS (svrs s svr))) gst_ts (get_cl_txn t) \<and>
    gst_ts = gst (cls s (get_cl_txn t)) \<and>
    wtxn_state (svrs s' svr) = wtxn_state (svrs s svr) \<and>
    clock (svrs s' svr) = Suc (clock (svrs s svr)) \<and>
    lst (svrs s' svr) = lst (svrs s svr) \<and>
    pending_wtxns (svrs s' svr) = pending_wtxns (svrs s svr) \<and>
    DS (svrs s' svr) = add_to_readerset (DS (svrs s svr)) t i \<and>
    cls_svr_k'_t'_unchanged t svr s s'"

definition prepare_write :: "svr_id \<Rightarrow> txid0 \<Rightarrow> 'v \<Rightarrow> tstmp \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "prepare_write svr t v gst_ts s s' \<equiv>
    tid_match s t \<and>
    (\<exists>kv_map.
      txn_state (cls s (get_cl_txn t)) = WtxnPrep kv_map \<and> svr \<in> dom kv_map \<and> kv_map svr = Some v) \<and>
    gst_ts =  (gst (cls s (get_cl_txn t))) \<and>
    wtxn_state (svrs s svr) t = Ready \<and>
    wtxn_state (svrs s' svr) t = Prep (clock (svrs s' svr)) (length (DS (svrs s svr))) \<and>
    clock (svrs s' svr) = Suc (clock (svrs s svr)) \<and>
    lst (svrs s' svr) = lst (svrs s svr) \<and>
    pending_wtxns (svrs s' svr) t = Some (clock (svrs s svr)) \<and>
    DS (svrs s' svr) = DS (svrs s svr) @
      [\<lparr>v_value = v, v_writer = Tn t, v_readerset = {}, v_ts = clock (svrs s svr),
       v_gst = gst_ts, v_is_pending = True\<rparr>] \<and>
    cls_svr_k'_t'_unchanged t svr s s'"

definition commit_write :: "svr_id \<Rightarrow> txid0 \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "commit_write svr t s s' \<equiv>
    tid_match s t \<and>
    (\<exists>kv_map commit_t.
      txn_state (cls s (get_cl_txn t)) = WtxnCommit commit_t kv_map \<and> svr \<in> dom kv_map \<and>
      (\<exists>prep_t i. wtxn_state (svrs s svr) t = Prep prep_t i \<and>
       DS (svrs s' svr) = commit_in_vl (DS (svrs s svr)) commit_t i)) \<and>
    wtxn_state (svrs s' svr) t = Commit \<and>
    clock (svrs s' svr) = clock (svrs s svr) \<and>
    lst (svrs s' svr) =
      (if dom (pending_wtxns (svrs s' svr)) = {} then clock (svrs s svr)
       else Min (ran (pending_wtxns (svrs s' svr)))) \<and>
    pending_wtxns (svrs s' svr) t = None \<and>
    cls_svr_k'_t'_unchanged t svr s s'"

subsubsection \<open>The Event System\<close>

definition state_init :: "'v state" where
  "state_init \<equiv> \<lparr> 
    cls = (\<lambda>cl. \<lparr> txn_state = Idle,
                  txn_sn = 0,
                  gst = 0,
                  lst_map = (\<lambda>svr. 0),
                  cl_view = view_init \<rparr>),
    svrs = (\<lambda>svr. \<lparr> wtxn_state = (\<lambda>t. Ready),
                    clock = 0,
                    lst = 0,
                    pending_wtxns = Map.empty,
                    DS = DS_vl_init \<rparr>)
  \<rparr>"

fun state_trans :: "'v state \<Rightarrow> 'v ev \<Rightarrow> 'v state \<Rightarrow> bool" where
  "state_trans s (RInvoke cl keys)        s' \<longleftrightarrow> read_invoke cl keys s s'" |
  "state_trans s (Read cl k v)            s' \<longleftrightarrow> read cl k v s s'" |
  "state_trans s (RDone cl kv_map sn u)   s' \<longleftrightarrow> read_done cl kv_map sn u s s'" |
  "state_trans s (WInvoke cl kv_map)      s' \<longleftrightarrow> write_invoke cl kv_map s s'" |
  "state_trans s (WCommit cl kv_map cts sn u)  s' \<longleftrightarrow> write_commit cl kv_map cts sn u s s'" |
  "state_trans s (WDone cl)               s' \<longleftrightarrow> write_done cl s s'" |
  "state_trans s (RegR svr t v i gts)     s' \<longleftrightarrow> register_read svr t v i gts s s'" |
  "state_trans s (PrepW svr t v gts)      s' \<longleftrightarrow> prepare_write svr t v gts s s'" |
  "state_trans s (CommitW svr t)          s' \<longleftrightarrow> commit_write svr t s s'" |
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
abbreviation pending_rtxn :: "'v state \<Rightarrow> txid0 \<Rightarrow> bool" where
  "pending_rtxn s t \<equiv> \<exists>keys kv_map. txn_state (cls s (get_cl_txn t)) = RtxnInProg keys kv_map \<and>
    txn_sn (cls s (get_cl_txn t)) = get_sn_txn t"

abbreviation pending_wtxn :: "'v state \<Rightarrow> txid \<Rightarrow> bool" where
  "pending_wtxn s t' \<equiv> case t' of T0 \<Rightarrow> False |
    Tn t \<Rightarrow> \<exists>kv_map. txn_state (cls s (get_cl_txn t)) = WtxnPrep kv_map \<and>
                txn_sn (cls s (get_cl_txn t)) = get_sn_txn t"

definition get_ver_committed_rd :: "'v state \<Rightarrow> 'v ep_version \<Rightarrow> 'v version" where
  "get_ver_committed_rd s v \<equiv>
   \<lparr>v_value = v_value v, v_writer = v_writer v, v_readerset = v_readerset v - {t. pending_rtxn s t}\<rparr>"

definition get_vl_committed_wr :: "'v state \<Rightarrow> 'v ep_version list \<Rightarrow> 'v ep_version list" where
  "get_vl_committed_wr s vl \<equiv> filter (\<lambda>v. v_is_pending v \<and> pending_wtxn s (v_writer v)) vl"

definition kvs_of_s :: "'v state \<Rightarrow> 'v kv_store" where
  "kvs_of_s s = (\<lambda>k. map (get_ver_committed_rd s) (get_vl_committed_wr s (DS (svrs s k))))"

definition views_of_s :: "'v state \<Rightarrow> (cl_id \<Rightarrow> view)" where
  "views_of_s s = (\<lambda>cl. cl_view (cls s cl))"

definition sim :: "'v state \<Rightarrow> 'v config" where         
  "sim s = (kvs_of_s s, views_of_s s)"

lemmas sim_defs = sim_def kvs_of_s_def views_of_s_def

\<comment> \<open>Mediator function\<close>
fun med :: "'v ev \<Rightarrow> 'v label" where
  "med (RDone cl kv_map sn u) = ET cl sn u (\<lambda>k op. case op of R \<Rightarrow> kv_map k | W \<Rightarrow> None)" |
  "med (WCommit cl kv_map _ sn u) = ET cl sn u (\<lambda>k op. case op of R \<Rightarrow> None | W \<Rightarrow> kv_map k)" |
  "med _ = ETSkip"

