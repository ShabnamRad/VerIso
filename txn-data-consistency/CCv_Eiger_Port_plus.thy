section \<open>Eiger Port Plus Protocol Satisfying CCv (Causal+)\<close>

theory CCv_Eiger_Port_plus
  imports Execution_Tests "HOL-Library.Multiset"
begin

subsection \<open>Event system & Refinement from ET_ES to tps\<close>

subsubsection \<open>State\<close>

type_synonym svr_id = key
type_synonym tstmp = nat

\<comment> \<open>Server State\<close>
datatype 'v ver_state = No_Ver | Prep tstmp 'v | Commit tstmp 'v "txid0 set"
type_synonym 'v state_wtxn = "txid \<Rightarrow> 'v ver_state"
record 'v server =
  wtxn_state :: "'v state_wtxn"
  clock :: tstmp
  lst :: tstmp

definition wts_dom :: "'v state_wtxn \<Rightarrow> txid set" where
  "wts_dom wts \<equiv> {t. wts t \<noteq> No_Ver}"

abbreviation wts_emp :: "'v state_wtxn" where
  "wts_emp \<equiv> (\<lambda>t. No_Ver)"

\<comment> \<open>Client State\<close>
datatype 'v state_txn =
  Idle | RtxnInProg "key set" "key \<rightharpoonup> ('v \<times> txid)" | WtxnPrep "key \<rightharpoonup> 'v" | WtxnCommit tstmp "key \<rightharpoonup> 'v"

type_synonym view_txid = "key \<Rightarrow> txid set"

record 'v client =
  txn_state :: "'v state_txn"
  txn_sn :: sqn
  gst :: tstmp
  lst_map :: "svr_id \<Rightarrow> tstmp"
  cl_view :: view_txid \<comment> \<open>history variable\<close>
  cl_clock :: tstmp

definition view_txid_init :: view_txid where
  "view_txid_init \<equiv> (\<lambda>k. {T0})"

\<comment> \<open>Global State\<close>
record 'v state = 
  cls :: "cl_id \<Rightarrow> 'v client"
  svrs :: "svr_id \<Rightarrow> 'v server"
  commit_order :: "key \<Rightarrow> txid list" \<comment> \<open>history variable - not used for the algorithm itself\<close>
  (* inv: all txids in the list have committed/prepared versions for that key *)

subsubsection \<open>Functions\<close>

\<comment> \<open>Translator functions\<close>
abbreviation get_txn_cl :: "'v state \<Rightarrow> cl_id \<Rightarrow> txid0" where
  "get_txn_cl s cl \<equiv> Tn_cl (txn_sn (cls s cl)) cl"

abbreviation get_wtxn_cl :: "'v state \<Rightarrow> cl_id \<Rightarrow> txid" where
  "get_wtxn_cl s cl \<equiv> Tn (get_txn_cl s cl)"

fun get_cl_wtxn :: "txid \<Rightarrow> cl_id" where
  "get_cl_wtxn T0 = undefined" |
  "get_cl_wtxn (Tn (Tn_cl sn cl)) = cl"

fun get_sn_wtxn :: "txid \<Rightarrow> sqn" where
  "get_sn_wtxn T0 = undefined" |
  "get_sn_wtxn (Tn (Tn_cl sn cl)) = sn"

fun get_val_ver :: "'v ver_state \<Rightarrow> 'v" where
  "get_val_ver No_Ver = undefined" |
  "get_val_ver (Prep _ v) = v" |
  "get_val_ver (Commit _ v _) = v"

fun get_ts_ver :: "'v ver_state \<Rightarrow> tstmp" where
  "get_ts_ver No_Ver = undefined" |
  "get_ts_ver (Prep ts _) = ts" |
  "get_ts_ver (Commit cts _ _) = cts"

fun get_rs_ver :: "'v ver_state \<Rightarrow> txid0 set" where
  "get_rs_ver No_Ver = undefined" |
  "get_rs_ver (Prep _ _) = {}" |
  "get_rs_ver (Commit _ _ rs) = rs"


\<comment> \<open>Reading functions\<close>

\<comment> \<open>returns greatest commit timestamp (cts) less than read timestamp (rts)\<close>
definition committed_at where
  "committed_at wts t cts \<equiv> \<exists>v rs. wts t = Commit cts v rs"

definition at_cts :: "'v state_wtxn \<Rightarrow> tstmp \<Rightarrow> tstmp" where
  "at_cts wts rts \<equiv> GREATEST cts. cts \<le> rts \<and> (\<exists>t. committed_at wts t cts)"

\<comment> \<open>(Probably redundant) returns the version read at read timestamp (highest cts less than ts)\<close>
definition at :: "'v state_wtxn \<Rightarrow> tstmp \<Rightarrow> txid" where
  "at wts rts \<equiv> SOME t. committed_at wts t (at_cts wts rts)"

abbreviation has_newer_own_write :: "'v state_wtxn \<Rightarrow> tstmp \<Rightarrow> cl_id \<Rightarrow> bool" where
  "has_newer_own_write wts cts cl \<equiv> \<exists>t. get_cl_wtxn t = cl \<and> committed_at wts t cts"

definition newest_own_write :: "'v state_wtxn \<Rightarrow> tstmp \<Rightarrow> cl_id \<rightharpoonup> txid" where
  "newest_own_write wts ts cl \<equiv>
    (if (\<exists>cts. has_newer_own_write wts cts cl \<and> cts \<ge> ts)
     then Some (SOME t. \<exists>v rs. wts t = Commit (GREATEST cts. has_newer_own_write wts cts cl \<and> cts \<ge> ts) v rs)
     else None)"

definition read_at :: "'v state_wtxn \<Rightarrow> tstmp \<Rightarrow> cl_id \<Rightarrow> txid" where
  "read_at wts ts cl \<equiv> let t = at wts ts in
    (case newest_own_write wts (get_ts_ver (wts t)) cl of
      None \<Rightarrow> t |
      Some t' \<Rightarrow> t')"


\<comment> \<open>Helper functions\<close>

definition add_to_readerset :: "'v state_wtxn \<Rightarrow> txid0 \<Rightarrow> txid \<Rightarrow> 'v state_wtxn" where
  "add_to_readerset wts t t_wr \<equiv> (case wts t_wr of
    Commit cts v rs \<Rightarrow> wts (t_wr := Commit cts v (insert t rs)) |
    _ \<Rightarrow> wts)"

definition view_txid_vid :: "'v state \<Rightarrow> view_txid \<Rightarrow> view" where
  "view_txid_vid s u \<equiv> (\<lambda>k. (inv ((!) (commit_order s k))) ` (u k))"

definition view_txid_vid' :: "'v state \<Rightarrow> view_txid \<Rightarrow> view" where
  "view_txid_vid' s u \<equiv> (\<lambda>k. List.map_project (\<lambda>tid. if tid \<in> set (commit_order s k)
    then Some (SOME i. i < length (commit_order s k) \<and> (commit_order s k) ! i = tid) else None) (u k))"

(* inv: showing all elements of view exist in commit_order *)
(* inv: commit_order distinct *)

definition get_view :: "'v state \<Rightarrow> cl_id \<Rightarrow> view_txid" where
  "get_view s cl \<equiv> (\<lambda>k. {t. \<exists>cts v rs. wtxn_state (svrs s k) t = Commit cts v rs \<and>
    (cts \<le> gst (cls s cl) \<or> get_cl_wtxn t = cl)})"

definition pending_wtxns where
  "pending_wtxns s k \<equiv> {prep_t. \<exists>t v. wtxn_state (svrs s k) t = Prep prep_t v}"


subsubsection \<open>Events\<close>

datatype 'v ev =
  RInvoke cl_id "key set" | Read cl_id key 'v txid | RDone cl_id "key \<rightharpoonup> ('v \<times> txid)" sqn view |
  WInvoke cl_id "key \<rightharpoonup> 'v" | WCommit cl_id "key \<rightharpoonup> 'v" tstmp sqn view | WDone cl_id |
  RegR svr_id txid0 'v txid tstmp | PrepW svr_id txid 'v tstmp | CommitW svr_id txid | Skip2

definition other_insts_unchanged where
  "other_insts_unchanged e s s' \<equiv> \<forall>e'. e' \<noteq> e \<longrightarrow> s' e' = s e'"

definition cls_svr_k'_unchanged where
  "cls_svr_k'_unchanged k s s' \<equiv> cls s' = cls s \<and> other_insts_unchanged k (svrs s) (svrs s')"

definition svrs_cls_cl'_unchanged where
  "svrs_cls_cl'_unchanged cl s s' \<equiv> svrs s' = svrs s \<and> other_insts_unchanged cl (cls s) (cls s')"

lemmas svr_unchanged_defs = cls_svr_k'_unchanged_def other_insts_unchanged_def
lemmas cl_unchanged_defs = svrs_cls_cl'_unchanged_def other_insts_unchanged_def
lemmas unchanged_defs = svr_unchanged_defs svrs_cls_cl'_unchanged_def

definition tid_match :: "'v state \<Rightarrow> txid0 \<Rightarrow> bool" where
  "tid_match s t \<equiv> txn_sn (cls s (get_cl_txn t)) = get_sn_txn t"

definition wtid_match :: "'v state \<Rightarrow> txid \<Rightarrow> bool" where
  "wtid_match s t \<equiv> txn_sn (cls s (get_cl_wtxn t)) = get_sn_wtxn t"

\<comment> \<open>Clint Events\<close>
definition read_invoke :: "cl_id \<Rightarrow> key set \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read_invoke cl keys s s' \<equiv>
    keys \<noteq> {} \<and>
    txn_state (cls s cl) = Idle \<and>
    txn_state (cls s' cl) = RtxnInProg keys (Map.empty) \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = max (gst (cls s cl)) (Min (range (lst_map (cls s cl)))) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    cl_clock (cls s' cl) = Suc (cl_clock (cls s cl)) \<and>
    svrs_cls_cl'_unchanged cl s s' \<and>
    commit_order s' = commit_order s"

definition read :: "cl_id \<Rightarrow> key \<Rightarrow> 'v \<Rightarrow> txid \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read cl k v t s s' \<equiv> (\<exists>keys vals.
    txn_state (cls s cl) = RtxnInProg keys vals \<and> k \<in> keys \<and> vals k = None \<and>
    txn_state (cls s' cl) = RtxnInProg keys (vals (k \<mapsto> (v, t)))) \<and>
    (\<exists>cts rs. wtxn_state (svrs s k) t = Commit cts v rs \<and> get_txn_cl s cl \<in> rs) \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = (lst_map (cls s cl)) (k := lst (svrs s k)) \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    cl_clock (cls s' cl) = Suc (max (cl_clock (cls s cl)) (clock (svrs s k))) \<and>
    svrs_cls_cl'_unchanged cl s s' \<and>
    commit_order s' = commit_order s"

definition read_done :: "cl_id \<Rightarrow> (key \<rightharpoonup> ('v \<times> txid)) \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read_done cl kvt_map sn u'' s s' \<equiv>
    sn = txn_sn (cls s cl) \<and>
    u'' = view_txid_vid s (get_view s cl) \<and>
    txn_state (cls s cl) = RtxnInProg (dom kvt_map) kvt_map \<and>
    txn_state (cls s' cl) = Idle \<and>
    txn_sn (cls s' cl) = Suc (txn_sn (cls s cl)) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    cl_view (cls s' cl) = get_view s cl \<and>
    cl_clock (cls s' cl) = Suc (cl_clock (cls s cl)) \<and>
    svrs_cls_cl'_unchanged cl s s' \<and>
    (\<forall>k \<in> dom kvt_map. commit_order s' k = commit_order s k @ [get_wtxn_cl s cl]) \<and>
    (\<forall>k. k \<notin> dom kvt_map \<longrightarrow> commit_order s' k = commit_order s k)"

definition write_invoke :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "write_invoke cl kv_map s s' \<equiv> 
    kv_map \<noteq> Map.empty \<and>
    txn_state (cls s cl) = Idle \<and>
    txn_state (cls s' cl) = WtxnPrep kv_map \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    cl_clock (cls s' cl) = Suc (cl_clock (cls s cl)) \<and>
    svrs_cls_cl'_unchanged cl s s' \<and>
    commit_order s' = commit_order s"

definition write_commit :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> tstmp \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "write_commit cl kv_map commit_t sn u'' s s' \<equiv>
    sn = txn_sn (cls s cl) \<and>
    u'' = view_txid_vid s (get_view s cl) \<and>
    txn_state (cls s cl) = WtxnPrep kv_map \<and>
    (\<forall>k \<in> dom kv_map.
      (\<exists>v prep_t. wtxn_state (svrs s k) (get_wtxn_cl s cl) = Prep prep_t v)) \<and>
    commit_t = Max {prep_t. (\<exists>k \<in> dom kv_map. \<exists>v.
      wtxn_state (svrs s k) (get_wtxn_cl s cl) = Prep prep_t v)} \<and>
    txn_state (cls s' cl) = WtxnCommit commit_t kv_map \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    cl_view (cls s' cl) = (\<lambda>k. if kv_map k = None then get_view s cl k else insert (get_wtxn_cl s cl) (get_view s cl k)) \<and>
    cl_clock (cls s' cl) = Suc (max (cl_clock (cls s cl)) commit_t) \<and> \<comment> \<open>Why not max of all involved server clocks\<close>
    svrs_cls_cl'_unchanged cl s s' \<and>
    (\<forall>k \<in> dom kv_map. commit_order s' k = commit_order s k @ [get_wtxn_cl s cl]) \<and>
    (\<forall>k. k \<notin> dom kv_map \<longrightarrow> commit_order s' k = commit_order s k)"

definition write_done :: "cl_id \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "write_done cl s s' \<equiv> 
    (\<exists>kv_map.
      (\<exists>commit_t. txn_state (cls s cl) = WtxnCommit commit_t kv_map \<and>
        (\<forall>k\<in>dom kv_map. \<exists>v rs. wtxn_state (svrs s k) (get_wtxn_cl s cl) = Commit commit_t v rs)) \<and>
      (\<forall>k \<in> dom kv_map. lst_map (cls s' cl) k = lst (svrs s k)) \<and>
      (\<forall>k. k \<notin> dom kv_map \<longrightarrow> lst_map (cls s' cl) k = lst_map (cls s cl) k) \<and>
      cl_clock (cls s' cl) = Suc (max (cl_clock (cls s cl)) (Max {clock (svrs s k) | k. k \<in> dom kv_map}))) \<and>
    txn_state (cls s' cl) = Idle \<and>
    txn_sn (cls s' cl) = Suc (txn_sn (cls s cl)) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    svrs_cls_cl'_unchanged cl s s' \<and>
    commit_order s' = commit_order s"

\<comment> \<open>Server Events\<close>
definition register_read :: "svr_id \<Rightarrow> txid0 \<Rightarrow> 'v \<Rightarrow> txid \<Rightarrow> tstmp \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "register_read svr t v t_wr gst_ts s s' \<equiv>
    tid_match s t \<and>
    (\<exists>keys kvt_map.
      txn_state (cls s (get_cl_txn t)) = RtxnInProg keys kvt_map \<and> svr \<in> keys \<and> kvt_map svr = None) \<and>
    t_wr = read_at (wtxn_state (svrs s svr)) gst_ts (get_cl_txn t) \<and>
    v = get_val_ver (wtxn_state (svrs s svr) t_wr) \<and>
    gst_ts = gst (cls s (get_cl_txn t)) \<and>
    wtxn_state (svrs s' svr) = add_to_readerset (wtxn_state (svrs s svr)) t t_wr \<and>
    clock (svrs s' svr) = Suc (max (clock (svrs s svr)) (cl_clock (cls s (get_cl_txn t)))) \<and>
    lst (svrs s' svr) = lst (svrs s svr) \<and>
    cls_svr_k'_unchanged svr s s' \<and>
    commit_order s' = commit_order s"

definition prepare_write :: "svr_id \<Rightarrow> txid \<Rightarrow> 'v \<Rightarrow> tstmp \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "prepare_write svr t v gst_ts s s' \<equiv>
    wtid_match s t \<and>
    (\<exists>kv_map.
      txn_state (cls s (get_cl_wtxn t)) = WtxnPrep kv_map \<and> svr \<in> dom kv_map \<and> kv_map svr = Some v) \<and>
    gst_ts = gst (cls s (get_cl_wtxn t)) \<and>
    wtxn_state (svrs s svr) t = No_Ver \<and>
    wtxn_state (svrs s' svr) = (wtxn_state (svrs s svr)) (t := Prep (clock (svrs s svr)) v) \<and>
    clock (svrs s' svr) = Suc (max (clock (svrs s svr)) (cl_clock (cls s (get_cl_wtxn t)))) \<and>
    lst (svrs s' svr) = lst (svrs s svr) \<and>
    cls_svr_k'_unchanged svr s s' \<and>
    commit_order s' = commit_order s"

definition commit_write :: "svr_id \<Rightarrow> txid \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "commit_write svr t s s' \<equiv>
    wtid_match s t \<and>
    (\<exists>commit_t. (\<exists>kv_map. svr \<in> dom kv_map \<and>
      txn_state (cls s (get_cl_wtxn t)) = WtxnCommit commit_t kv_map) \<and>
      (\<exists>prep_t v. wtxn_state (svrs s svr) t = Prep prep_t v \<and>
        wtxn_state (svrs s' svr) = (wtxn_state (svrs s svr)) (t := Commit commit_t v {}))) \<and>
    clock (svrs s' svr) = Suc (max (clock (svrs s svr)) (cl_clock (cls s (get_cl_wtxn t)))) \<and>
    lst (svrs s' svr) =
      (if pending_wtxns s' svr = {} then clock (svrs s svr) else Min (pending_wtxns s' svr)) \<and>
    cls_svr_k'_unchanged svr s s' \<and>
    commit_order s' = commit_order s"

subsubsection \<open>The Event System\<close>

definition state_init :: "'v state" where
  "state_init \<equiv> \<lparr> 
    cls = (\<lambda>cl. \<lparr> txn_state = Idle,
                  txn_sn = 0,
                  gst = 0,
                  lst_map = (\<lambda>svr. 0),
                  cl_view = view_txid_init,
                  cl_clock = 0 \<rparr>),
    svrs = (\<lambda>svr. \<lparr> wtxn_state = (\<lambda>t. No_Ver) (T0 := Commit 0 undefined {}),
                    clock = 0,
                    lst = 0 \<rparr>),
    commit_order = (\<lambda>k. [T0])
  \<rparr>"

fun state_trans :: "'v state \<Rightarrow> 'v ev \<Rightarrow> 'v state \<Rightarrow> bool" where
  "state_trans s (RInvoke cl keys)          s' \<longleftrightarrow> read_invoke cl keys s s'" |
  "state_trans s (Read cl k v t)            s' \<longleftrightarrow> read cl k v t s s'" |
  "state_trans s (RDone cl kvt_map sn u'')  s' \<longleftrightarrow> read_done cl kvt_map sn u'' s s'" |
  "state_trans s (WInvoke cl kv_map)        s' \<longleftrightarrow> write_invoke cl kv_map s s'" |
  "state_trans s (WCommit cl kv_map cts sn u'')  s' \<longleftrightarrow> write_commit cl kv_map cts sn u'' s s'" |
  "state_trans s (WDone cl)                 s' \<longleftrightarrow> write_done cl s s'" |
  "state_trans s (RegR svr t v i gts)       s' \<longleftrightarrow> register_read svr t v i gts s s'" |
  "state_trans s (PrepW svr t v gts)        s' \<longleftrightarrow> prepare_write svr t v gts s s'" |
  "state_trans s (CommitW svr t)            s' \<longleftrightarrow> commit_write svr t s s'" |
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


subsubsection \<open>Simulation function\<close>

definition kvs_of_s :: "'v state \<Rightarrow> 'v kv_store" where
  "kvs_of_s s \<equiv>
    (\<lambda>k. map
      (\<lambda>t. case wtxn_state (svrs s k) t of
        Prep ts v \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = {}\<rparr> |
        Commit cts v rs \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = rs\<rparr>)
      (commit_order s k))"

definition views_of_s :: "'v state \<Rightarrow> (cl_id \<Rightarrow> view)" where
  "views_of_s s = (\<lambda>cl. view_txid_vid s (cl_view (cls s cl)))"

definition sim :: "'v state \<Rightarrow> 'v config" where         
  "sim s = (kvs_of_s s, views_of_s s)"

lemmas sim_defs = sim_def kvs_of_s_def views_of_s_def

\<comment> \<open>Mediator function\<close>
fun med :: "'v ev \<Rightarrow> 'v label" where
  "med (RDone cl kvt_map sn u'') = ET cl sn u'' (\<lambda>k op. case op of R \<Rightarrow> map_option fst (kvt_map k) | W \<Rightarrow> None)" |
  "med (WCommit cl kv_map _ sn u'') = ET cl sn u'' (\<lambda>k op. case op of R \<Rightarrow> None | W \<Rightarrow> kv_map k)" |
  "med _ = ETSkip"

end