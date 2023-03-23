section \<open>Modified Eiger Port Protocol Satisfying CCv (Causal+)\<close>

theory CCv_Eiger_Port_plus
  imports Execution_Tests "HOL-Library.Multiset"
begin

subsection \<open>Event system & Refinement from ET_ES to tps\<close>

subsubsection \<open>State\<close>

type_synonym svr_id = key
type_synonym tstmp = nat

\<comment> \<open>Server State\<close>
datatype 'v ver_state = Prep tstmp 'v | Commit tstmp 'v "txid0 set"
type_synonym 'v state_wtxn = "txid \<rightharpoonup> 'v ver_state"
record 'v server =
  wtxn_state :: "'v state_wtxn"
  clock :: tstmp
  lst :: tstmp

\<comment> \<open>Client State\<close>
datatype 'v state_txn =
  Idle | RtxnInProg "key set" "key \<rightharpoonup> ('v \<times> txid)" | WtxnPrep "key \<rightharpoonup> 'v" | WtxnCommit tstmp "key \<rightharpoonup> 'v"

type_synonym view_txid = "key \<Rightarrow> txid set"

record 'v client =
  txn_state :: "'v state_txn"
  txn_sn :: sqn
  gst :: tstmp
  lst_map :: "svr_id \<Rightarrow> tstmp"
  cl_view :: view_txid
  cl_clock :: tstmp

definition view_txid_init :: view_txid where
  "view_txid_init \<equiv> (\<lambda>k. {T0})"

\<comment> \<open>Global State\<close>
record 'v state = 
  cls :: "cl_id \<Rightarrow> 'v client"
  svrs :: "svr_id \<Rightarrow> 'v server"
  commit_order :: "key \<Rightarrow> txid list" \<comment> \<open>history variable - not used for the algorithm itself\<close>
  (* inv: all txids in the list have committed versions for that key *)

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
  "get_val_ver (Prep _ v) = v" |
  "get_val_ver (Commit _ v _) = v"

fun get_ts_ver :: "'v ver_state \<Rightarrow> tstmp" where
  "get_ts_ver (Prep ts _) = ts" |
  "get_ts_ver (Commit cts _ _) = cts"

fun get_rs_ver :: "'v ver_state \<Rightarrow> txid0 set" where
  "get_rs_ver (Prep _ _) = {}" |
  "get_rs_ver (Commit _ _ rs) = rs"


\<comment> \<open>Reading functions\<close>

\<comment> \<open>returns greatest commit timestamp (cts) less than read timestamp (rts)\<close>
definition at_cts :: "'v state_wtxn \<Rightarrow> tstmp \<Rightarrow> txid \<Rightarrow> tstmp" where
  "at_cts wtxn_s rts t \<equiv> GREATEST cts. (\<exists>v rs. wtxn_s t = Some (Commit cts v rs)) \<and> cts \<le> rts"

\<comment> \<open>(Probably redundant) returns the version read at read timestamp (highest cts less than ts)\<close>
definition at :: "'v state_wtxn \<Rightarrow> tstmp \<Rightarrow> txid" where
  "at wtxn_s rts \<equiv> (SOME t. \<exists>v rs. wtxn_s t = Some (Commit (at_cts wtxn_s rts t) v rs))"

abbreviation has_newer_own_write :: "'v state_wtxn \<Rightarrow> tstmp \<Rightarrow> tstmp \<Rightarrow> txid \<Rightarrow> bool" where
  "has_newer_own_write wtxn_s cts ts t \<equiv> (\<exists>v rs. wtxn_s t = Some (Commit cts v rs)) \<and> cts \<ge> ts"

definition newest_own_write :: "'v state_wtxn \<Rightarrow> tstmp \<Rightarrow> cl_id \<rightharpoonup> txid" where
  "newest_own_write wtxn_s ts cl \<equiv>
    (if \<exists>t cts. get_cl_wtxn t = cl \<and> has_newer_own_write wtxn_s cts ts t
     then Some (SOME t. \<exists>v rs. wtxn_s t = Some (Commit (GREATEST cts. has_newer_own_write wtxn_s cts ts t) v rs))
     else None)"

definition read_at :: "'v state_wtxn \<Rightarrow> tstmp \<Rightarrow> cl_id \<Rightarrow> txid" where
  "read_at wtxn_s ts cl \<equiv> let t = at wtxn_s ts in
    (case newest_own_write wtxn_s (get_ts_ver (the (wtxn_s t))) cl of
      None \<Rightarrow> t |
      Some t' \<Rightarrow> t')"


\<comment> \<open>Helper functions\<close>

definition add_to_readerset :: "'v state_wtxn \<Rightarrow> txid0 \<Rightarrow> txid \<Rightarrow> 'v state_wtxn" where
  "add_to_readerset wtxn_s t t_wr \<equiv> (case wtxn_s t_wr of
    Some (Commit cts v rs) \<Rightarrow> wtxn_s (t_wr \<mapsto> Commit cts v (insert t rs)) |
    _ \<Rightarrow> wtxn_s)"

abbreviation view_txid_vid :: "'v state \<Rightarrow> view_txid \<Rightarrow> view" where
  "view_txid_vid s u \<equiv> (\<lambda>k. (inv ((!) (commit_order s k))) ` (u k))"

abbreviation view_txid_vid' :: "'v state \<Rightarrow> view_txid \<Rightarrow> view" where
  "view_txid_vid' s u \<equiv> (\<lambda>k. List.map_project (\<lambda>tid. if tid \<in> set (commit_order s k)
    then Some (SOME i. (commit_order s k) ! i = tid) else None) (u k))"

(* inv: showing all elements of view exist in commit_order *)

definition get_view where
  "get_view s cl \<equiv> (\<lambda>k. {t. \<exists>cts v rs. wtxn_state (svrs s k) t = Some (Commit cts v rs) \<and>
    (cts \<le> gst (cls s cl) \<or> get_cl_wtxn t = cl)})"

definition pending_wtxns where
  "pending_wtxns s k \<equiv> {prep_t. \<exists>t v. wtxn_state (svrs s k) t = Some (Prep prep_t v)}"

\<comment> \<open>Lemmas about the functions\<close>

lemma add_to_readerset_dom: "dom (add_to_readerset wtxn_s t t') = dom wtxn_s"
  by (auto simp add: add_to_readerset_def split: option.split ver_state.split)

lemma add_to_readerset_none_inv:
  "add_to_readerset wtxn_s t t' t'' = None \<longleftrightarrow> wtxn_s t'' = None"
  apply (rule iffI; auto simp add: add_to_readerset_def split: option.split ver_state.split)
  apply (cases "wtxn_s t'"; simp)
  subgoal for a by (cases a; cases "t'' = t'"; simp).

lemma add_to_readerset_prep_inv:
  "add_to_readerset wtxn_s t t' t'' = Some (Prep ts v) \<longleftrightarrow> wtxn_s t'' = Some (Prep ts v)"
  apply (rule iffI; auto simp add: add_to_readerset_def; cases "wtxn_s t'"; auto)
  apply (smt (z3) get_val_ver.cases map_upd_Some_unfold ver_state.distinct(1) ver_state.simps(5,6))
  by (smt (verit) get_val_ver.cases map_upd_Some_unfold ver_state.simps(5) ver_state.simps(6))

lemma finite_pending_wtxns_rtxn:
  assumes "wtxn_state (svrs s' k) = add_to_readerset (wtxn_state (svrs s k)) t' t"
    and "finite (pending_wtxns s svr)"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
  shows "finite (pending_wtxns s' svr)"
  using assms apply (auto simp add: add_to_readerset_def finite_nat_set_iff_bounded_le pending_wtxns_def)
  by (metis (full_types) add_to_readerset_prep_inv assms(1))

lemma finite_pending_wtxns_adding: 
  assumes "wtxn_state (svrs s' k) = wtxn_state (svrs s k) (t \<mapsto> Prep prep_t v)"
    and "finite (pending_wtxns s svr)"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
  shows "finite (pending_wtxns s' svr)"
  using assms apply (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_def)
  by (metis (no_types, opaque_lifting) dual_order.trans fun_upd_other nat_le_linear not_Some_eq
      option.inject ver_state.inject(1))

lemma finite_pending_wtxns_removing: 
  assumes "wtxn_state (svrs s' k) = wtxn_state (svrs s k) (t \<mapsto> Commit cts v rs)"
    and "finite (pending_wtxns s svr)"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
  shows "finite (pending_wtxns s' svr)"
  using assms apply (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_def)
  by (metis fun_upd_apply option.inject ver_state.distinct(1))

lemma pending_wtxns_adding_ub:
  assumes "wtxn_state (svrs s' k) = wtxn_state (svrs s k) (t \<mapsto> Prep clk v)"
    and "\<forall>ts \<in> pending_wtxns s k. ts \<le> clk"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
  shows "\<forall>ts \<in> pending_wtxns s' k. ts \<le> clk"
  using assms by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_def)

lemma pending_wtxns_removing_ub:
  assumes "wtxn_state (svrs s' k) = wtxn_state (svrs s k) (t \<mapsto> Commit cts v rs)"
    and "\<forall>ts \<in> pending_wtxns s k. ts \<le> clk"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
  shows "\<forall>ts \<in> pending_wtxns s' k. ts \<le> clk"
  using assms by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_def)

lemma pending_wtxns_rtxn:
  assumes "wtxn_state (svrs s' k) = add_to_readerset (wtxn_state (svrs s k)) t' t"
    and "\<forall>clk v. wtxn_state (svrs s k) t \<noteq> Some (Prep clk v)"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
  shows "pending_wtxns s' k = pending_wtxns s k"
  using assms apply (auto simp add: pending_wtxns_def)
  by (meson add_to_readerset_prep_inv)+

lemma pending_wtxns_adding:
  assumes "wtxn_state (svrs s' k) = wtxn_state (svrs s k) (t \<mapsto> Prep clk v)"
    and "\<forall>clk v. wtxn_state (svrs s k) t \<noteq> Some (Prep clk v)"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
  shows "pending_wtxns s' k = insert clk (pending_wtxns s k)"
  using assms apply (auto simp add: pending_wtxns_def)
  by metis

lemma pending_wtxns_removing:
  assumes "wtxn_state (svrs s k) t = Some (Prep clk v)"
    and "wtxn_state (svrs s' k) = wtxn_state (svrs s k) (t \<mapsto> Commit cts v rs)"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
  shows "pending_wtxns s' k = pending_wtxns s k \<or> pending_wtxns s' k = Set.remove clk (pending_wtxns s k)"
  using assms apply (auto simp add: pending_wtxns_def)
  by (metis get_ts_ver.simps(1) option.inject)+

lemma pending_wtxns_empty:
  "pending_wtxns s k = {} \<longleftrightarrow> (\<forall>t. \<exists>cts v rs. wtxn_state (svrs s k) t \<in> {None, Some (Commit cts v rs)})"
  apply (auto simp add: pending_wtxns_def)
   apply (metis get_val_ver.cases option.exhaust)
   by (metis option.distinct(1) option.inject ver_state.distinct(1))

lemma pending_wtxns_non_empty:
  assumes "wtxn_state (svrs s k) t \<noteq> None"
    and "\<forall>cts v rs. wtxn_state (svrs s k) t \<noteq> Some (Commit cts v rs)"
  shows "pending_wtxns s k \<noteq> {}"
  using assms apply (auto simp add: pending_wtxns_def)
  by (metis get_val_ver.cases)

subsubsection \<open>Events\<close>

datatype 'v ev =
  RInvoke cl_id "key set" | Read cl_id key 'v txid | RDone cl_id "key \<rightharpoonup> ('v \<times> txid)" sqn view |
  WInvoke cl_id "key \<rightharpoonup> 'v" | WCommit cl_id "key \<rightharpoonup> 'v" tstmp sqn view | WDone cl_id |
  RegR svr_id txid0 'v txid tstmp | PrepW svr_id txid 'v tstmp | CommitW svr_id txid | Skip2

definition other_insts_unchanged where
  "other_insts_unchanged e s s' \<equiv> \<forall>e'. e' \<noteq> e \<longrightarrow> s' e' = s e'"

definition cls_svr_k'_t'_unchanged where
  "cls_svr_k'_t'_unchanged k s s' \<equiv> cls s' = cls s \<and> other_insts_unchanged k (svrs s) (svrs s')"

definition svrs_cls_cl'_unchanged where
  "svrs_cls_cl'_unchanged cl s s' \<equiv> svrs s' = svrs s \<and> other_insts_unchanged cl (cls s) (cls s')"

lemmas svr_unchanged_defs = cls_svr_k'_t'_unchanged_def other_insts_unchanged_def
lemmas cl_unchanged_defs = svrs_cls_cl'_unchanged_def other_insts_unchanged_def
lemmas unchanged_defs = svr_unchanged_defs svrs_cls_cl'_unchanged_def

definition tid_match :: "'v state \<Rightarrow> txid \<Rightarrow> bool" where
  "tid_match s t \<equiv> txn_sn (cls s (get_cl_wtxn t)) = get_sn_wtxn t"

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
    (\<exists>cts rs. wtxn_state (svrs s k) t = Some (Commit cts v rs) \<and> get_txn_cl s cl \<in> rs) \<and>
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
    cl_view (cls s' cl) = get_view s' cl \<and>
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
      (\<exists>v prep_t. wtxn_state (svrs s k) (get_wtxn_cl s cl) = Some (Prep prep_t v))) \<and>
    commit_t = Max {prep_t. (\<exists>k \<in> dom kv_map. \<exists>v.
      wtxn_state (svrs s k) (get_wtxn_cl s cl) = Some (Prep prep_t v))} \<and>
    txn_state (cls s' cl) = WtxnCommit commit_t kv_map \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    cl_view (cls s' cl) = get_view s' cl \<and>
    cl_clock (cls s' cl) = Suc (max (cl_clock (cls s cl)) commit_t) \<and> \<comment> \<open>Why not max of all involved server clocks\<close>
    svrs_cls_cl'_unchanged cl s s' \<and>
    (\<forall>k \<in> dom kv_map. commit_order s' k = commit_order s k @ [get_wtxn_cl s cl]) \<and>
    (\<forall>k. k \<notin> dom kv_map \<longrightarrow> commit_order s' k = commit_order s k)"

definition write_done :: "cl_id \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "write_done cl s s' \<equiv> 
    (\<exists>kv_map.
      (\<exists>commit_t. txn_state (cls s cl) = WtxnCommit commit_t kv_map \<and>
        (\<forall>k\<in>dom kv_map. \<exists>v rs. wtxn_state (svrs s k) (get_wtxn_cl s cl) = Some (Commit commit_t v rs))) \<and>
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
    tid_match s (Tn t) \<and>
    (\<exists>keys kvt_map.
      txn_state (cls s (get_cl_txn t)) = RtxnInProg keys kvt_map \<and> svr \<in> keys \<and> kvt_map svr = None) \<and>
    t_wr = read_at (wtxn_state (svrs s svr)) gst_ts (get_cl_txn t) \<and>
    v = get_val_ver (the (wtxn_state (svrs s svr) t_wr)) \<and>
    gst_ts = gst (cls s (get_cl_txn t)) \<and>
    wtxn_state (svrs s' svr) = add_to_readerset (wtxn_state (svrs s svr)) t t_wr \<and>
    clock (svrs s' svr) = Suc (max (clock (svrs s svr)) (cl_clock (cls s (get_cl_txn t)))) \<and>
    lst (svrs s' svr) = lst (svrs s svr) \<and>
    cls_svr_k'_t'_unchanged svr s s' \<and>
    commit_order s' = commit_order s"

definition prepare_write :: "svr_id \<Rightarrow> txid \<Rightarrow> 'v \<Rightarrow> tstmp \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "prepare_write svr t v gst_ts s s' \<equiv>
    tid_match s t \<and>
    (\<exists>kv_map.
      txn_state (cls s (get_cl_wtxn t)) = WtxnPrep kv_map \<and> svr \<in> dom kv_map \<and> kv_map svr = Some v) \<and>
    gst_ts = gst (cls s (get_cl_wtxn t)) \<and>
    wtxn_state (svrs s svr) t = None \<and>
    wtxn_state (svrs s' svr) = wtxn_state (svrs s svr) (t \<mapsto> Prep (clock (svrs s svr)) v) \<and>
    clock (svrs s' svr) = Suc (max (clock (svrs s svr)) (cl_clock (cls s (get_cl_wtxn t)))) \<and>
    lst (svrs s' svr) = lst (svrs s svr) \<and>
    cls_svr_k'_t'_unchanged svr s s' \<and>
    commit_order s' = commit_order s"

definition commit_write :: "svr_id \<Rightarrow> txid \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "commit_write svr t s s' \<equiv>
    tid_match s t \<and>
    (\<exists>commit_t. (\<exists>kv_map. svr \<in> dom kv_map \<and>
      txn_state (cls s (get_cl_wtxn t)) = WtxnCommit commit_t kv_map) \<and>
      (\<exists>prep_t v. wtxn_state (svrs s svr) t = Some (Prep prep_t v) \<and>
        wtxn_state (svrs s' svr) = wtxn_state (svrs s svr) (t \<mapsto> Commit commit_t v {}))) \<and>
    clock (svrs s' svr) = Suc (max (clock (svrs s svr)) (cl_clock (cls s (get_cl_wtxn t)))) \<and>
    lst (svrs s' svr) =
      (if pending_wtxns s' svr = {} then clock (svrs s svr) else Min (pending_wtxns s' svr)) \<and>
    cls_svr_k'_t'_unchanged svr s s' \<and>
    commit_order s' = commit_order s"

subsubsection \<open>The Event System\<close>

definition state_init :: "'v state" where
  "state_init \<equiv> \<lparr> 
    cls = (\<lambda>cl. \<lparr> txn_state = Idle,
                  txn_sn = 0,
                  gst = 0,
                  lst_map = (\<lambda>svr. 0),
                  cl_view = (\<lambda>k. {}),
                  cl_clock = 0 \<rparr>),
    svrs = (\<lambda>svr. \<lparr> wtxn_state = Map.empty (T0 \<mapsto> Commit 0 undefined {}),
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
  "kvs_of_s s \<equiv> (\<lambda>k. map (\<lambda>t. case wtxn_state (svrs s k) t of
    Some (Commit cts v rs) \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = rs\<rparr>) (commit_order s k))"

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


subsection \<open>Invariants and lemmas\<close>

\<comment> \<open>lemmas for unchanged elements in svrs\<close>

lemma eq_for_all_k: 
  assumes "f (svrs s' k) = f (svrs s k)"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> svrs s' k' = svrs s k'"
  shows "\<forall>k. f (svrs s' k) = f (svrs s k)"
  apply (auto simp add: fun_eq_iff) using assms
  subgoal for k' by (cases "k' = k"; simp).

lemma eq_for_all_k_t: 
  assumes "f (svrs s' k) t = f (svrs s k) t"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> svrs s' k' = svrs s k'"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> f (svrs s' k) t' = f (svrs s k) t'"
  shows "\<forall>k. f (svrs s' k) = f (svrs s k)"
  apply (auto simp add: fun_eq_iff) using assms
  subgoal for k' t' by (cases "k' = k"; cases "t' = t"; simp).

lemma eq_for_all_cl:
  assumes "f (cls s' cl) = f (cls s cl)"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "\<forall>cl. f (cls s' cl) = f (cls s cl)"
  apply (auto simp add: fun_eq_iff) using assms
  subgoal for cl' by (cases "cl' = cl"; simp).

subsection \<open>monotonic lemmas and inequality of timestamps invariants\<close>

lemma clock_monotonic:
  assumes "state_trans s e s'"
  shows "clock (svrs s' svr) \<ge> clock (svrs s svr)"
  using assms
proof (induction e)
  case (RegR k t)
  then show ?case apply (auto simp add: register_read_def svr_unchanged_defs)
    by (cases "k = svr"; simp)
next
  case (PrepW k t)
  then show ?case apply (auto simp add: prepare_write_def svr_unchanged_defs)
    by (cases "k = svr"; simp)
next
  case (CommitW k t)
  then show ?case apply (auto simp add: commit_write_def svr_unchanged_defs)
    by (metis le_SucI max.cobounded1 max_def)
qed (auto simp add: tps_trans_defs cl_unchanged_defs dest!:eq_for_all_k)


lemma cl_clock_monotonic:
  assumes "state_trans s e s'"
  shows "cl_clock (cls s' cl) \<ge> cl_clock (cls s cl)"
  using assms
proof (induction e)
  case (RInvoke x1 x2)
  then show ?case apply (auto simp add: read_invoke_def cl_unchanged_defs)
    by (metis Suc_n_not_le_n nat_le_linear)
next
  case (Read x1 x2 x3 x4)
  then show ?case apply (auto simp add: read_def cl_unchanged_defs)
    by (metis Suc_n_not_le_n max.coboundedI1 nat_le_linear)
next
  case (RDone x1 x2 x3 x4)
  then show ?case apply (auto simp add: read_done_def cl_unchanged_defs)
    by (metis Suc_n_not_le_n nat_le_linear)
next
  case (WInvoke x1 x2)
  then show ?case apply (auto simp add: write_invoke_def cl_unchanged_defs)
    by (metis Suc_n_not_le_n nat_le_linear)
next
  case (WCommit x1 x2 x3 x4 x5)
  then show ?case apply (auto simp add: write_commit_def cl_unchanged_defs)
    by (metis (no_types, lifting) le_SucI max.absorb_iff2 max_def)
next
  case (WDone x)
  then show ?case apply (auto simp add: write_done_def cl_unchanged_defs)
    by (metis (lifting) le_SucI max.cobounded1 max_def_raw)
qed (auto simp add: tps_trans_defs svr_unchanged_defs dest!:eq_for_all_k)


definition PendingWtxnsUB where
  "PendingWtxnsUB s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns s svr. ts \<le> clock (svrs s svr))"

lemmas PendingWtxnsUBI = PendingWtxnsUB_def[THEN iffD2, rule_format]
lemmas PendingWtxnsUBE[elim] = PendingWtxnsUB_def[THEN iffD1, elim_format, rule_format]

lemma reach_PendingWtxnsUB [simp, dest]: "reach tps s \<Longrightarrow> PendingWtxnsUB s svr"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    apply (auto simp add: PendingWtxnsUB_def tps_defs tid_match_def pending_wtxns_def)
    by (metis option.distinct(1) option.inject ver_state.distinct(1))
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: PendingWtxnsUB_def tps_trans_defs svr_unchanged_defs pending_wtxns_def)
      by (metis (no_types, lifting) add_to_readerset_prep_inv le_Suc_eq max.coboundedI1)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: PendingWtxnsUB_def tps_trans_defs svr_unchanged_defs pending_wtxns_def ran_def)
      by (smt (z3) le_Suc_eq map_upd_Some_unfold max.coboundedI1 nat_le_linear ver_state.inject(1))
  next
    case (CommitW x1 x2)
    then show ?case
      apply (auto simp add: PendingWtxnsUB_def tps_trans_defs svr_unchanged_defs pending_wtxns_def ran_def)
      by (smt (z3) less_Suc_eq_le less_or_eq_imp_le map_upd_Some_unfold max.coboundedI1 ver_state.distinct(1))
  qed (auto simp add: PendingWtxnsUB_def tps_trans_defs cl_unchanged_defs pending_wtxns_def)
qed

definition FinitePendingInv where
  "FinitePendingInv s svr \<longleftrightarrow> finite (pending_wtxns s svr)"

lemmas FinitePendingInvI = FinitePendingInv_def[THEN iffD2, rule_format]
lemmas FinitePendingInvE[elim] = FinitePendingInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_finitepending [simp, dest]: "reach tps s \<Longrightarrow> FinitePendingInv s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FinitePendingInv_def tps_defs pending_wtxns_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x71 x72 x73 x74 x75)
    then show ?case
      by (auto simp add: tps_trans_defs svr_unchanged_defs FinitePendingInv_def pending_wtxns_def
          dest!: finite_pending_wtxns_rtxn)
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case
      by (auto simp add: tps_trans_defs svr_unchanged_defs FinitePendingInv_def
          dest!: finite_pending_wtxns_adding)
  next
    case (CommitW x91 x92)
    then show ?case
      by (auto simp add: tps_trans_defs svr_unchanged_defs FinitePendingInv_def
          dest!: finite_pending_wtxns_removing)
  qed (auto simp add: tps_trans_defs cl_unchanged_defs FinitePendingInv_def pending_wtxns_def)
qed

definition ClockLstInv where
  "ClockLstInv s \<longleftrightarrow> (\<forall>svr. lst (svrs s svr) \<le> clock (svrs s svr))"

lemmas ClockLstInvI = ClockLstInv_def[THEN iffD2, rule_format]
lemmas ClockLstInvE[elim] = ClockLstInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_clocklstinv [simp, dest]: "reach tps s \<Longrightarrow> ClockLstInv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: ClockLstInv_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x71 x72 x73 x74 x75)
    then show ?case apply (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs)
      by (metis le_Suc_eq max.coboundedI1)
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case apply (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs)
      by (metis (no_types, lifting) clock_monotonic dual_order.trans reach_trans.hyps(1) tps_trans)
  next
    case (CommitW x91 x92)
    then show ?case apply (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs)
      apply (cases "pending_wtxns s' x91 = {}")
      apply (metis clock_monotonic reach_trans.hyps(1) tps_trans)
    proof -
      fix svr
      assume a: "pending_wtxns s' x91 \<noteq> {}"
      hence fin: "finite (pending_wtxns s' x91)" using CommitW
        apply (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs)
        by (metis (mono_tags) FinitePendingInv_def reach.reach_trans reach_finitepending
            reach_trans.hyps(1) reach_trans.hyps(2))
      hence clk_ub: "\<forall>ts \<in> pending_wtxns s' x91. ts \<le> clock (svrs s x91)" using CommitW
        by (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs dest!: pending_wtxns_removing_ub)
      hence "Min (pending_wtxns s' x91) \<le> clock (svrs s x91)" using a fin CommitW
        by (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs)
      then show "lst (svrs s' svr) \<le> clock (svrs s' svr)" using CommitW
        by (cases "svr = x91"; auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs)
    qed
  qed (auto simp add: ClockLstInv_def tps_trans_defs cl_unchanged_defs)
qed

definition PendingWtxnsLB where
  "PendingWtxnsLB s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns s svr. lst (svrs s svr) \<le> ts)"

lemmas PendingWtxnsLBI = PendingWtxnsLB_def[THEN iffD2, rule_format]
lemmas PendingWtxnsLBE[elim] = PendingWtxnsLB_def[THEN iffD1, elim_format, rule_format]

lemma reach_PendingWtxnsLB [simp, dest]: "reach tps s \<Longrightarrow> PendingWtxnsLB s svr"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: PendingWtxnsLB_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case
    apply (auto simp add: PendingWtxnsLB_def tps_trans_defs svr_unchanged_defs pending_wtxns_def)
      by (metis add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case
    apply (auto simp add: PendingWtxnsLB_def tps_trans_defs svr_unchanged_defs pending_wtxns_def)
      by (metis (no_types) ClockLstInv_def fun_upd_other fun_upd_same get_ts_ver.simps(1)
          option.sel reach_clocklstinv)
  next
    case (CommitW x1 x2)
    then show ?case
    apply (auto simp add: PendingWtxnsLB_def commit_write_def svr_unchanged_defs pending_wtxns_def)
    apply (cases "pending_wtxns s' x1 = {}")
      apply (metis option.distinct(1) option.inject pending_wtxns_non_empty ver_state.distinct(1))
      apply (cases "svr = x1"; auto)
      apply (metis option.sel ver_state.distinct(1))
      subgoal for x kv_map y glts prep_t commit_t t apply (cases "t = x2"; auto)
      proof -
        fix t ts v
        assume a: "wtxn_state (svrs s x1) t = Some (Prep ts v)" and b: "t \<noteq> x2"
        hence fin: "finite (pending_wtxns s' x1)" using CommitW
          apply (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs)
          by (metis (mono_tags) FinitePendingInv_def reach.reach_trans reach_finitepending
              reach_trans.hyps(1) reach_trans.hyps(2))
        then show "Min (pending_wtxns s' x1) \<le> ts" using a b CommitW
          apply (auto simp add: PendingWtxnsLB_def tps_trans_defs svr_unchanged_defs
              pending_wtxns_def split del: if_split)
          by (smt (z3) Min.coboundedI mem_Collect_eq)
      qed.
  qed (auto simp add: PendingWtxnsLB_def tps_trans_defs cl_unchanged_defs pending_wtxns_def)
qed

lemma Min_insert_larger:
  assumes "a \<noteq> {}" and "b \<noteq> {}"
    and "finite a"
    and "b = insert x a"
    and "\<forall>y \<in> a. y \<le> x"
  shows "Min a \<le> Min b"
  using assms
  by simp

lemma min_pending_wtxns_monotonic:
  assumes "state_trans s e s'"
    and "pending_wtxns s k \<noteq> {}"
    and "pending_wtxns s' k \<noteq> {}"
    and "PendingWtxnsUB s k" and "FinitePendingInv s k"
  shows "Min (pending_wtxns s k) \<le> Min (pending_wtxns s' k)"
  using assms
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case
    apply (auto simp add: tps_trans_defs svr_unchanged_defs pending_wtxns_def)
      by (smt (z3) Collect_cong add_to_readerset_prep_inv nat_le_linear)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (auto simp add: prepare_write_def svr_unchanged_defs PendingWtxnsUB_def
          FinitePendingInv_def)
      using pending_wtxns_adding [of s' x1 s]
        Min_insert_larger[of "pending_wtxns s x1" "pending_wtxns s' x1" "clock (svrs s x1)"]
      by (cases "k = x1"; auto simp add: pending_wtxns_def)
  next
    case (CommitW x1 x2)
    then show ?case apply (auto simp add: commit_write_def svr_unchanged_defs pending_wtxns_empty 
          FinitePendingInv_def)
      apply (cases "k = x1") subgoal for t ta y ya commit_t kv_map prep_t v
      by (smt (verit) Min.coboundedI Min_in assms(3) finite_pending_wtxns_removing member_remove pending_wtxns_removing)
      by (simp add: pending_wtxns_def)
  qed (auto simp add: tps_trans_defs unchanged_defs pending_wtxns_def dest!: eq_for_all_k)

lemma lst_monotonic:
  assumes "state_trans s e s'"
    and "ClockLstInv s" and "FinitePendingInv s svr"
    and "PendingWtxnsLB s svr" and "PendingWtxnsUB s svr"
  shows "lst (svrs s' svr) \<ge> lst (svrs s svr)"
  using assms
  proof (induction e)
    case (CommitW k t)
    then show ?case
      apply (auto simp add: commit_write_def svr_unchanged_defs ClockLstInv_def PendingWtxnsLB_def
          FinitePendingInv_def)
    apply (cases "svr = k"; simp)
    apply (cases "pending_wtxns s k = {}"; cases "pending_wtxns s' k = {}"; simp)
      apply (metis option.discI option.sel pending_wtxns_non_empty ver_state.distinct(1))
      by (meson FinitePendingInvI Min.boundedI assms(1) le_trans min_pending_wtxns_monotonic)
  qed (auto simp add: tps_trans_defs unchanged_defs dest!:eq_for_all_k)

lemma gst_monotonic:
  assumes "state_trans s e s'"
  shows "gst (cls s' cl) \<ge> gst (cls s cl)"
  using assms
proof (induction e)
  case (RInvoke x1 x2)
  then show ?case apply (auto simp add: read_invoke_def cl_unchanged_defs)
    by (metis dual_order.refl max.cobounded1)
qed (auto simp add: tps_trans_defs unchanged_defs dest!:eq_for_all_cl)

\<comment> \<open>Invariants about kvs, global ts and init version v0\<close>

definition KVSNonEmp where
  "KVSNonEmp s \<longleftrightarrow> (\<forall>k. wtxn_state (svrs s k) \<noteq> Map.empty)"

lemmas KVSNonEmpI = KVSNonEmp_def[THEN iffD2, rule_format]
lemmas KVSNonEmpE[elim] = KVSNonEmp_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_non_emp [simp, intro]: "reach tps s \<Longrightarrow> KVSNonEmp s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: KVSNonEmp_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: KVSNonEmp_def tps_trans_defs svr_unchanged_defs)
      by (metis add_to_readerset_dom domIff)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: KVSNonEmp_def tps_trans_defs svr_unchanged_defs)
      by (metis map_upd_nonempty)
  next
    case (CommitW x1 x2)
    then show ?case
      apply (auto simp add: KVSNonEmp_def tps_trans_defs svr_unchanged_defs)
      by (metis map_upd_nonempty)
  qed (auto simp add: KVSNonEmp_def tps_trans_defs cl_unchanged_defs)
qed


definition CommitOrderNonEmp where
  "CommitOrderNonEmp s k \<longleftrightarrow> commit_order s k \<noteq> []"

lemmas CommitOrderNonEmpI = CommitOrderNonEmp_def[THEN iffD2, rule_format]
lemmas CommitOrderNonEmpE[elim] = CommitOrderNonEmp_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_non_emp [simp, intro]: "reach tps s \<Longrightarrow> CommitOrderNonEmp s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: CommitOrderNonEmp_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: CommitOrderNonEmp_def tps_trans_defs)
      by (metis append_is_Nil_conv)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: CommitOrderNonEmp_def tps_trans_defs)
      by (metis append_is_Nil_conv)
  qed (auto simp add: CommitOrderNonEmp_def tps_trans_defs)
qed


definition KVSSNonEmp where
  "KVSSNonEmp s \<longleftrightarrow> (\<forall>k. kvs_of_s s k \<noteq> [])"

lemmas KVSSNonEmpI = KVSSNonEmp_def[THEN iffD2, rule_format]
lemmas KVSSNonEmpE[elim] = KVSSNonEmp_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_s_non_emp [simp, intro]: "reach tps s \<Longrightarrow> KVSSNonEmp s"
  using reach_commit_order_non_emp
  by (auto simp add: KVSSNonEmp_def kvs_of_s_def)


\<comment> \<open>Invariant about server and client state relations and (future and past) transactions ids\<close>

definition FutureTIDInv where
  "FutureTIDInv s cl \<longleftrightarrow> (\<forall>n k. n > txn_sn (cls s cl) \<longrightarrow> wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = None)"

lemmas FutureTIDInvI = FutureTIDInv_def[THEN iffD2, rule_format]
lemmas FutureTIDInvE[elim] = FutureTIDInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidfuturekm [simp, dest]: "reach tps s \<Longrightarrow> FutureTIDInv s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FutureTIDInv_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x11 x12)
    then show ?case
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def)
      by (metis not_None_eq)
  next
    case (Read x21 x22 x23 x24)
    then show ?case
      by (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def, metis)
  next
    case (RDone x31 x32 x33 x34)
    then show ?case
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def)
      by (metis Suc_lessD)
  next
    case (WInvoke x41 x42)
    then show ?case
      by (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def, metis)
  next
    case (WCommit x51 x52 x53 x54 x55)
    then show ?case
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def)
      by (metis (lifting))
  next
    case (WDone x6)
    then show ?case  using reach_trans
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def)
      by (metis Suc_lessD)
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?case
      apply (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def FutureTIDInv_def)
      by (metis add_to_readerset_none_inv)
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case
      apply (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def FutureTIDInv_def)
      by (metis fun_upd_apply get_cl_wtxn.simps(2) get_sn_wtxn.simps(2) nat_neq_iff)
  next
    case (CommitW x91 x92)
    then show ?case  using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def FutureTIDInv_def)
      by (metis fun_upd_apply option.discI)
  qed simp
qed


definition IdleReadInv where
  "IdleReadInv s \<longleftrightarrow> (\<forall>cl k keys kvm. txn_state (cls s cl) \<in> {Idle, RtxnInProg keys kvm}
    \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) = None)"

lemmas IdleReadInvI = IdleReadInv_def[THEN iffD2, rule_format]
lemmas IdleReadInvE[elim] = IdleReadInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_idle_read_inv [simp, dest]: "reach tps s \<Longrightarrow> IdleReadInv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: IdleReadInv_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs cl_unchanged_defs)
      by metis
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs cl_unchanged_defs)
      by metis
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs cl_unchanged_defs)
      by (metis (opaque_lifting) FutureTIDInv_def lessI reach_tidfuturekm)
  next
    case (WInvoke x1 x2)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs cl_unchanged_defs)
      by metis
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs cl_unchanged_defs)
      by (metis (opaque_lifting) state_txn.distinct(5) state_txn.distinct(9))
  next
    case (WDone x)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs cl_unchanged_defs)
      by (metis (full_types) FutureTIDInv_def lessI reach_tidfuturekm)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs svr_unchanged_defs)
      by (metis add_to_readerset_none_inv)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs svr_unchanged_defs)
      by (metis fun_upd_other get_cl_wtxn.simps(2) state_txn.distinct(3) state_txn.distinct(7))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs svr_unchanged_defs)
      by (smt (verit) fun_upd_apply option.discI)
  qed simp
qed

definition WriteTxnIdleSvr where
  "WriteTxnIdleSvr s \<longleftrightarrow>
    (\<forall>cl k cts kv_map. txn_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map}
        \<and> kv_map k = None \<longrightarrow> wtxn_state (svrs s k) (Tn (get_txn_cl s cl)) = None)"

lemmas WriteTxnIdleSvrI = WriteTxnIdleSvr_def[THEN iffD2, rule_format]
lemmas WriteTxnIdleSvrE[elim] = WriteTxnIdleSvr_def[THEN iffD1, elim_format, rule_format]

lemma reach_write_txn_idle_svr [simp, dest]: "reach tps s \<Longrightarrow> WriteTxnIdleSvr s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: WriteTxnIdleSvr_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: WriteTxnIdleSvr_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(7) state_txn.distinct(9))
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: WriteTxnIdleSvr_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(7) state_txn.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: WriteTxnIdleSvr_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) state_txn.distinct(3) state_txn.distinct(5))
  next
    case (WInvoke x1 x2)
    then show ?case apply (auto simp add: WriteTxnIdleSvr_def tps_trans_defs cl_unchanged_defs)
      apply (metis IdleReadInv_def insertI1 reach_idle_read_inv reach_trans.hyps(2))
      by (metis state_txn.distinct(11))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: WriteTxnIdleSvr_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) state_txn.distinct(11) state_txn.inject(3))
  next
    case (WDone x)
    then show ?case apply (simp add: WriteTxnIdleSvr_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) state_txn.distinct(3) state_txn.distinct(5))
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: WriteTxnIdleSvr_def tps_trans_defs svr_unchanged_defs)
      by (metis add_to_readerset_none_inv)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: WriteTxnIdleSvr_def tps_trans_defs svr_unchanged_defs)
      by (smt (z3) domIff fun_upd_other get_cl_wtxn.simps(2) state_txn.distinct(11) state_txn.inject(2))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: WriteTxnIdleSvr_def tps_trans_defs svr_unchanged_defs)
      by (smt (z3) fun_upd_other option.distinct(1))
  qed simp
qed

definition PastTIDInv where
  "PastTIDInv s cl \<longleftrightarrow> (\<forall>k. \<forall>n < txn_sn (cls s cl).
   wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = None \<or>
   (\<exists>cts v rs. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Some (Commit cts v rs)))"

lemmas PastTIDInvI = PastTIDInv_def[THEN iffD2, rule_format]
lemmas PastTIDInvE[elim] = PastTIDInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidpastkm [simp, dest]: "reach tps s \<Longrightarrow> PastTIDInv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: PastTIDInv_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x11 x12)
    then show ?case
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def)
      by (metis option.discI option.inject)
  next
    case (Read x21 x22 x23)
    then show ?case
      by (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def, metis)
  next
    case (RDone x31 x32 x33 x34)
    then show ?case
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def)
      by (smt IdleReadInv_def insertI1 insert_commute not_less_less_Suc_eq reach_idle_read_inv reach_trans.hyps(2))
  next
    case (WInvoke x41 x42)
    then show ?case
      by (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def, metis)
  next
    case (WCommit x51 x52 x53 x54 x55)
    then show ?case
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def)
      by (metis (lifting))
  next
    case (WDone x6)
    then show ?case
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def)
      apply (cases "cl = x6"; auto)
      subgoal for n
        apply (cases "n = txn_sn (cls s x6)", simp_all)
        subgoal using FutureTIDInv_def[of s x6]
          sorry sorry
      by meson
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?case
      apply (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def PastTIDInv_def) sorry
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case
      apply (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def PastTIDInv_def) sorry
  next
    case (CommitW x91 x92)
    then show ?case
      apply (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def PastTIDInv_def) sorry
  qed simp
qed

lemma other_sn_idle:  
  assumes "FutureTIDInv s cl" and "PastTIDInv s cl"
    and "get_cl_txn t = cl" and "get_sn_txn t \<noteq> txn_sn (cls s cl)"
  shows "\<And>k. \<exists>cts v rs. wtxn_state (svrs s k) (Tn t) \<in> {None, Some (Commit cts v rs)}"
  using assms
  apply (auto simp add: FutureTIDInv_def PastTIDInv_def)
  apply (cases "get_sn_txn t > txn_sn (cls s cl)")
  apply (metis get_cl_txn.elims get_sn_txn.simps)
  by (metis get_cl_txn.elims get_sn_txn.simps linorder_cases)

definition PrepInv where
  "PrepInv s \<longleftrightarrow> (\<forall>cl k kvm. \<exists>prep_t v. txn_state (cls s cl) = WtxnPrep kvm
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> wtxn_state (svrs s k) (Tn (get_txn_cl s cl)) \<in> {None, Some (Prep prep_t v)}) \<and>
    (k \<notin> dom kvm \<longrightarrow> wtxn_state (svrs s k) (Tn (get_txn_cl s cl)) = None))"

lemmas PrepInvI = PrepInv_def[THEN iffD2, rule_format]
lemmas PrepInvE[elim] = PrepInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_prep_inv [simp, dest]: "reach tps s \<Longrightarrow> PrepInv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: PrepInv_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(7))
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(7))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) state_txn.distinct(3))
  next
    case (WInvoke x1 x2)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs cl_unchanged_defs)
      by (metis IdleReadInv_def insertI1 reach_idle_read_inv)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) state_txn.distinct(11))
  next
    case (WDone x)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) state_txn.distinct(3))
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs svr_unchanged_defs)
      by (smt (verit) add_to_readerset_dom add_to_readerset_prep_inv domIff)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs svr_unchanged_defs)
      by (smt (verit) fun_upd_apply get_cl_txn.simps state_txn.inject(2) txid.inject)
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs svr_unchanged_defs)
      by (smt (verit) fun_upd_apply get_cl_txn.simps state_txn.distinct(11) txid.inject)
  qed simp
qed

(* lemma defs fixed up to here! *)

definition CommitInv where
  "CommitInv s \<longleftrightarrow> (\<forall>cl k gts cts kvm. \<exists>prep_t. txn_state (cls s cl) = WtxnCommit gts cts kvm
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> wtxn_state (svrs s k) (get_txn_cl s cl) \<in> {Prep prep_t, Commit}) \<and>
    (k \<notin> dom kvm \<longrightarrow> wtxn_state (svrs s k) (get_txn_cl s cl) = Ready))"

lemmas CommitInvI = CommitInv_def[THEN iffD2, rule_format]
lemmas CommitInvE[elim] = CommitInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_inv [simp, dest]: "reach tps s \<Longrightarrow> CommitInv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: CommitInv_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(9))
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) state_txn.distinct(5))
  next
    case (WInvoke x1 x2)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(11))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs cl_unchanged_defs)
      by (smt (verit) PrepInv_def reach_prep_inv state_txn.inject(3))
  next
    case (WDone x)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs cl_unchanged_defs)
      by (smt (verit, ccfv_SIG) state_txn.distinct(5))
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case by (simp add: CommitInv_def tps_trans_defs svr_unchanged_defs, metis)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs svr_unchanged_defs)
      by (metis get_cl_txn.simps state_txn.distinct(11))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs svr_unchanged_defs)
      by (metis (no_types, lifting) state_wtxn.distinct(1))
  qed simp
qed


definition FutureTidRdDS where
  "FutureTidRdDS s cl \<longleftrightarrow> (\<forall>n k. \<forall>ver \<in> set (DS (svrs s k)). n > txn_sn (cls s cl) \<longrightarrow> Tn_cl n cl \<notin> v_readerset ver)"

lemmas FutureTidRdDSI = FutureTidRdDS_def[THEN iffD2, rule_format]
lemmas FutureTidRdDSE[elim] = FutureTidRdDS_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidfuture_rd_ds [simp, dest]: "reach tps s \<Longrightarrow> FutureTidRdDS s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FutureTidRdDS_def tps_defs tid_match_def DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case by (simp add: FutureTidRdDS_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x1 x2 x3 x4)
    then show ?case by (simp add: FutureTidRdDS_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: FutureTidRdDS_def tps_trans_defs cl_unchanged_defs)
      by (metis Suc_lessD)
  next
    case (WInvoke x1 x2)
    then show ?case by (simp add: FutureTidRdDS_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case by (simp add: FutureTidRdDS_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WDone x)
    then show ?case apply (simp add: FutureTidRdDS_def tps_trans_defs cl_unchanged_defs)
      by (metis (opaque_lifting) Suc_lessD)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: FutureTidRdDS_def tps_trans_defs svr_unchanged_defs tid_match_def) sorry
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: FutureTidRdDS_def tps_trans_defs svr_unchanged_defs)
      using append_image[of v_readerset "DS (svrs s x1)" "\<lparr>v_value = x3, v_writer = Tn x2,
        v_readerset = {}, v_ts = clock (svrs s x1), v_glts = 0, v_is_pending = True\<rparr>"] sorry
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: FutureTidRdDS_def tps_trans_defs svr_unchanged_defs) sorry
  qed simp
qed

definition FutureTidWrDS where
  "FutureTidWrDS s cl \<longleftrightarrow> (\<forall>n k. n > txn_sn (cls s cl) \<longrightarrow> Tn (Tn_cl n cl) \<notin> v_writer ` set (DS (svrs s k)))"

lemmas FutureTidWrDSI = FutureTidWrDS_def[THEN iffD2, rule_format]
lemmas FutureTidWrDSE[elim] = FutureTidWrDS_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidfuture_wr_ds [simp, dest]: "reach tps s \<Longrightarrow> FutureTidWrDS s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FutureTidWrDS_def tps_defs tid_match_def DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x11 x12)
    then show ?case by (simp add: FutureTidWrDS_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x21 x22 x23)
    then show ?case by (simp add: FutureTidWrDS_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (RDone x31 x32 x33 x34)
    then show ?case apply (simp add: FutureTidWrDS_def tps_trans_defs cl_unchanged_defs)
      by (metis Suc_lessD)
  next
    case (WInvoke x41 x42)
    then show ?case by (simp add: FutureTidWrDS_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x51 x52 x53 x54 x55)
    then show ?case by (simp add: FutureTidWrDS_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WDone x6)
    then show ?case apply (simp add: FutureTidWrDS_def tps_trans_defs cl_unchanged_defs)
      by (metis Suc_lessD)
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?case apply (simp add: FutureTidWrDS_def tps_trans_defs svr_unchanged_defs)
      by (metis add_to_readerset_v_writer_img)
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case apply (simp add: FutureTidWrDS_def tps_trans_defs svr_unchanged_defs tid_match_def)
      by (metis (no_types, lifting) append_image get_cl_txn.simps get_sn_txn.simps insertE nat_neq_iff
          txid.inject version.select_convs(2))
  next
    case (CommitW x91 x92)
    then show ?case apply (simp add: FutureTidWrDS_def tps_trans_defs svr_unchanged_defs)
      by (metis commit_in_vl_v_writer_img)
  qed simp
qed

definition VerWrLCurrT where
  "VerWrLCurrT s cl \<longleftrightarrow> (\<forall>n k. \<forall>ver \<in> set (DS (svrs s k)).
   v_writer ver = Tn (Tn_cl n cl) \<longrightarrow> n \<le> txn_sn (cls s cl))"

lemmas VerWrLCurrTI = VerWrLCurrT_def[THEN iffD2, rule_format]
lemmas VerWrLCurrTE[elim] = VerWrLCurrT_def[THEN iffD1, elim_format, rule_format]

lemma reach_ver_wr_L_currT [simp, dest]: "reach tps s \<Longrightarrow> VerWrLCurrT s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: VerWrLCurrT_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case by (simp add: VerWrLCurrT_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x1 x2 x3 x4)
    then show ?case by (simp add: VerWrLCurrT_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: VerWrLCurrT_def tps_trans_defs cl_unchanged_defs)
      by (metis le_Suc_eq)
  next
    case (WInvoke x1 x2)
    then show ?case by (simp add: VerWrLCurrT_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case by (simp add: VerWrLCurrT_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WDone x)
    then show ?case apply (simp add: VerWrLCurrT_def tps_trans_defs cl_unchanged_defs)
      by (metis (mono_tags, lifting) nat_le_linear not_less_eq_eq)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: VerWrLCurrT_def tps_trans_defs svr_unchanged_defs)
    by (metis add_to_readerset_v_writer_img FutureTidWrDS_def linorder_le_less_linear not_in_image
        reach_tidfuture_wr_ds)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (auto simp add: VerWrLCurrT_def tps_trans_defs svr_unchanged_defs)
    subgoal for n kvm k apply (cases "k = x1"; simp)
    apply (metis get_cl_txn.simps get_sn_txn.simps order_class.order_eq_iff tid_match_def
            txid.inject version.select_convs(2)) by blast.
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: VerWrLCurrT_def tps_trans_defs svr_unchanged_defs)
      by (metis commit_in_vl_v_writer_img FutureTidWrDS_def linorder_le_less_linear not_in_image
        reach_tidfuture_wr_ds)
  qed simp
qed

lemma not_in_append: "ver \<in> set(vl @ [v]) \<and> ver \<noteq> v \<Longrightarrow> ver \<in> set vl"
  by auto

definition VerWrLCurrT2 where
  "VerWrLCurrT2 s cl \<longleftrightarrow> (\<forall>n k. \<forall>ver \<in> set (DS (svrs s k)). v_writer ver = Tn (Tn_cl n cl) \<and>
    (\<exists>keys kvm. txn_state (cls s cl) \<in> {Idle, RtxnInProg keys kvm}) \<longrightarrow> n < txn_sn (cls s cl))"

lemmas VerWrLCurrT2I = VerWrLCurrT2_def[THEN iffD2, rule_format]
lemmas VerWrLCurrT2E[elim] = VerWrLCurrT2_def[THEN iffD1, elim_format, rule_format]

lemma reach_ver_wr_L_currT2 [simp, dest]: "reach tps s \<Longrightarrow> VerWrLCurrT2 s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: VerWrLCurrT2_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case by (simp add: VerWrLCurrT2_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x1 x2 x3 x4)
    then show ?case by (simp add: VerWrLCurrT2_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: VerWrLCurrT2_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) less_SucI)
  next
    case (WInvoke x1 x2)
    then show ?case by (simp add: VerWrLCurrT2_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: VerWrLCurrT2_def tps_trans_defs cl_unchanged_defs)
    by (metis (lifting) state_txn.distinct(5) state_txn.distinct(9))
  next
    case (WDone x)
    then show ?case apply (simp add: VerWrLCurrT2_def tps_trans_defs cl_unchanged_defs)
    by (metis (lifting) VerWrLCurrT_def less_Suc_eq nat_less_le reach_ver_wr_L_currT)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: VerWrLCurrT2_def tps_trans_defs svr_unchanged_defs)
      by (metis add_to_readerset_length add_to_readerset_v_writer in_set_conv_nth)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: VerWrLCurrT2_def tps_trans_defs svr_unchanged_defs)
      by (metis get_cl_txn.simps not_in_append state_txn.distinct(3) state_txn.distinct(7)
          txid.inject version.select_convs(2))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: VerWrLCurrT2_def tps_trans_defs svr_unchanged_defs)
        by (smt commit_in_vl_v_writer_img image_iff)
  qed simp
qed

definition VerWrLCurrT3 where
  "VerWrLCurrT3 s k \<longleftrightarrow> (\<forall>n cl. \<forall>ver \<in> set (DS (svrs s k)). v_writer ver = Tn (Tn_cl n cl) \<and>
    wtxn_state (svrs s k) (get_txn_cl s cl) = Ready \<longrightarrow> n < txn_sn (cls s cl))"

lemmas VerWrLCurrT3I = VerWrLCurrT3_def[THEN iffD2, rule_format]
lemmas VerWrLCurrT3E[elim] = VerWrLCurrT3_def[THEN iffD1, elim_format, rule_format]

lemma reach_ver_wr_L_currT3 [simp, dest]: "reach tps s \<Longrightarrow> VerWrLCurrT3 s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: VerWrLCurrT3_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case by (simp add: VerWrLCurrT3_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x1 x2 x3 x4)
    then show ?case by (simp add: VerWrLCurrT3_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: VerWrLCurrT3_def tps_trans_defs cl_unchanged_defs)
      by (metis (no_types, lifting) VerWrLCurrT2_def insertCI less_Suc_eq reach_ver_wr_L_currT2)
  next
    case (WInvoke x1 x2)
    then show ?case by (simp add: VerWrLCurrT3_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: VerWrLCurrT3_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting))
  next
    case (WDone x)
    then show ?case apply (simp add: VerWrLCurrT3_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) VerWrLCurrT_def nat_less_le not_less_eq_eq reach.reach_trans reach_trans.hyps(1)
          reach_ver_wr_L_currT)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: VerWrLCurrT3_def tps_trans_defs svr_unchanged_defs)
      by (metis add_to_readerset_length add_to_readerset_v_writer in_set_conv_nth)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: VerWrLCurrT3_def tps_trans_defs svr_unchanged_defs)
      by (smt (verit, best) get_cl_txn.simps get_sn_txn.simps not_in_append state_wtxn.distinct(1)
          tid_match_def txid.inject version.select_convs(2))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: VerWrLCurrT3_def tps_trans_defs svr_unchanged_defs)
      by (smt (verit) state_wtxn.distinct(3) commit_in_vl_v_writer_img image_iff)
  qed simp
qed

definition SvrVerWrTIDDistinct where
  "SvrVerWrTIDDistinct s k \<longleftrightarrow> distinct (map v_writer (DS (svrs s k)))"

lemmas SvrVerWrTIDDistinctI = SvrVerWrTIDDistinct_def[THEN iffD2, rule_format]
lemmas SvrVerWrTIDDistinctE[elim] = SvrVerWrTIDDistinct_def[THEN iffD1, elim_format, rule_format]

lemma reach_svr_ver_wr_tid_unique[simp, dest]: "reach tps s \<Longrightarrow> SvrVerWrTIDDistinct s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: SvrVerWrTIDDistinct_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: SvrVerWrTIDDistinct_def tps_trans_defs svr_unchanged_defs)
      by (metis add_to_readerset_v_writer_map)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: SvrVerWrTIDDistinct_def tps_trans_defs svr_unchanged_defs tid_match_def)
      apply (cases "k = x1"; auto)
      using VerWrLCurrT3_def[of s x1] apply simp
      by (metis get_cl_txn.elims get_sn_txn.simps less_irrefl_nat)
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: SvrVerWrTIDDistinct_def tps_trans_defs svr_unchanged_defs)
      by (metis commit_in_vl_v_writer_multiset mset_eq_imp_distinct_iff mset_map)
  qed (auto simp add: SvrVerWrTIDDistinct_def tps_trans_defs cl_unchanged_defs)
qed

definition PastTIDNotPending where
  "PastTIDNotPending s cl \<longleftrightarrow> (\<forall>n k. \<forall>ver \<in> set (DS (svrs s k)).
   v_writer ver = Tn (Tn_cl n cl) \<and> n < txn_sn (cls s cl) \<longrightarrow> \<not>v_is_pending ver)"

lemmas PastTIDNotPendingI = PastTIDNotPending_def[THEN iffD2, rule_format]
lemmas PastTIDNotPendingE[elim] = PastTIDNotPending_def[THEN iffD1, elim_format, rule_format]

lemma reach_past_tid_notp [simp, dest]: "reach tps s \<Longrightarrow> PastTIDNotPending s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: PastTIDNotPending_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case by (simp add: PastTIDNotPending_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x1 x2 x3 x4)
    then show ?case by (simp add: PastTIDNotPending_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: PastTIDNotPending_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) VerWrLCurrT2_def insertCI reach_ver_wr_L_currT2)
  next
    case (WInvoke x1 x2)
    then show ?case by (simp add: PastTIDNotPending_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case by (simp add: PastTIDNotPending_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WDone x)
    then show ?case apply (simp add: PastTIDNotPending_def tps_trans_defs cl_unchanged_defs)
      apply (cases "cl = x", simp add: less_Suc_eq_le)
      subgoal sorry
      by metis
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: PastTIDNotPending_def tps_trans_defs svr_unchanged_defs)
      by (metis add_to_readerset_length add_to_readerset_v_is_pending add_to_readerset_v_writer
          in_set_conv_nth)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: PastTIDNotPending_def tps_trans_defs svr_unchanged_defs)
      by (smt get_cl_txn.simps get_sn_txn.simps nat_neq_iff not_in_append tid_match_def txid.inject
          version.select_convs(2))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: PastTIDNotPending_def tps_trans_defs svr_unchanged_defs) sorry
  qed simp
qed


abbreviation not_committing_ev where
  "not_committing_ev e \<equiv> \<forall>cl kvt_map kv_map cts sn u. e \<noteq> RDone cl kvt_map sn u \<and> e \<noteq> WCommit cl kv_map cts sn u"


definition FreshReadTxnInv where
  "FreshReadTxnInv s cl k \<longleftrightarrow> (txn_state (cls s cl) = Idle \<longrightarrow>
  (\<forall>i < length (DS (svrs s k)). get_txn_cl s cl \<notin> v_readerset (DS (svrs s k) ! i)))"

lemmas FreshReadTxnInvI = FreshReadTxnInv_def[THEN iffD2, rule_format]
lemmas FreshReadTxnInvE[elim] = FreshReadTxnInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_freshrdtxn [simp, dest]: "reach tps s \<Longrightarrow> FreshReadTxnInv s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FreshReadTxnInv_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x11 x12)
    then show ?case by (simp add: FreshReadTxnInv_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x21 x22 x23)
    then show ?case apply (simp add: FreshReadTxnInv_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(1))
  next
    case (RDone x31 x32 x33 x34)
    then show ?case apply (simp add: FreshReadTxnInv_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) FutureTidRdDS_def lessI nth_mem reach_tidfuture_rd_ds)
  next
    case (WInvoke x41 x42)
    then show ?case by (simp add: FreshReadTxnInv_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x51 x52 x53 x54 x55)
    then show ?case apply (simp add: FreshReadTxnInv_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) state_txn.distinct(5))
  next
    case (WDone x6)
    then show ?case apply (simp add: FreshReadTxnInv_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) FutureTidRdDS_def lessI nth_mem reach_tidfuture_rd_ds)
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?case apply (simp add: FreshReadTxnInv_def tps_trans_defs svr_unchanged_defs tid_match_def)
      apply (cases "k = x71"; cases "cl = get_cl_txn x72"; auto) sorry
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case sorry
  next
    case (CommitW x91 x92)
    then show ?case sorry
  qed simp
qed

definition FreshWriteTxnInv where
  "FreshWriteTxnInv s cl \<longleftrightarrow> (\<forall>keys kvt_map k. txn_state (cls s cl) \<in> {Idle, RtxnInProg keys kvt_map} \<longrightarrow>
    Tn (get_txn_cl s cl) \<notin> v_writer ` set (DS (svrs s k)))"

lemmas FreshWriteTxnInvI = FreshWriteTxnInv_def[THEN iffD2, rule_format]
lemmas FreshWriteTxnInvE[elim] = FreshWriteTxnInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_freshwrtxn [simp, dest]: "reach tps s \<Longrightarrow> FreshWriteTxnInv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FreshWriteTxnInv_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case by (simp add: tps_trans_defs FreshWriteTxnInv_def cl_unchanged_defs, metis)
  next
    case (Read x1 x2 x3 x4)
    then show ?case by (simp add: tps_trans_defs FreshWriteTxnInv_def cl_unchanged_defs, metis)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: tps_trans_defs FreshWriteTxnInv_def cl_unchanged_defs)
      by (metis (lifting) FutureTidWrDS_def lessI reach_tidfuture_wr_ds)
  next
    case (WInvoke x1 x2)
    then show ?case by (simp add: tps_trans_defs FreshWriteTxnInv_def cl_unchanged_defs, metis)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: tps_trans_defs FreshWriteTxnInv_def cl_unchanged_defs)
      by (metis (no_types, lifting) state_txn.distinct(5) state_txn.distinct(9))
  next
    case (WDone x)
    then show ?case apply (simp add: tps_trans_defs FreshWriteTxnInv_def cl_unchanged_defs)
      by (metis (lifting) FutureTidWrDS_def lessI reach_tidfuture_wr_ds)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: tps_trans_defs FreshWriteTxnInv_def svr_unchanged_defs)
      by (metis add_to_readerset_v_writer_img)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: tps_trans_defs FreshWriteTxnInv_def svr_unchanged_defs)
      by (metis (no_types, lifting) append_image get_cl_txn.simps insert_iff state_txn.distinct(3)
          state_txn.distinct(7) txid.inject version.select_convs(2))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: tps_trans_defs FreshWriteTxnInv_def svr_unchanged_defs)
      by (metis commit_in_vl_v_writer_img)
  qed simp
qed

lemma bla:
  assumes "x \<notin> a"
  shows "a - insert x b = a - b"
  using assms
  by simp

abbreviation invariant_list_kvs where
  "invariant_list_kvs s \<equiv> \<forall>cl k. FutureTIDInv s cl \<and> PastTIDInv s cl \<and> KVSNonEmp s \<and>
    KVSNotAllPending s k \<and> FreshReadTxnInv s cl k"

lemma kvs_of_s_inv:
  assumes "state_trans s e s'"
    and "invariant_list_kvs s"
    and "not_committing_ev e"
  shows "kvs_of_s s' = kvs_of_s s"
  using assms
  proof (induction e)
    case (RInvoke x1 x2)
    then have "get_ver_committed_rd s' = get_ver_committed_rd s"
      using pending_rtxn_added[of s x1 s'] bla[where x="get_txn_cl s x1" and b="Collect (pending_rtxn s)"]
      apply (auto simp add: tps_trans_defs get_ver_committed_rd_def cl_unchanged_defs FreshReadTxnInv_def get_vl_pre_committed_readersets) sorry
    then show ?case using RInvoke reach_trans pending_wtxn_cl_ev_inv[of s x1 s']
      apply (auto simp add: tps_trans_defs kvs_of_s_def cl_unchanged_defs get_vl_pre_committed_readersets) sorry
  next
    case (Read x1 x2 x3 x4)
    then show ?case sorry
  next
    case (WInvoke x1 x2)
    then show ?case sorry
  next
    case (WDone x)
    then show ?case sorry
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case sorry
  next
    case (CommitW x1 x2)
    then show ?case sorry
  qed auto

lemma writers_inv_not_commit_write:
  assumes "state_trans s e s'"
    and "\<And>cl kv_map cts sn u. \<not>write_commit cl kv_map cts sn u s s'"
  shows "v_writer ` set (get_vl_pre_committed s' (DS (svrs s' svr))) =
  v_writer ` set (get_vl_pre_committed s (DS (svrs s svr)))"
  using assms
proof (induction e)
  case (RInvoke x1 x2)
  then show ?case using pending_wtxn_cl_ev_inv[of s x1 s']
    by (simp add: tps_trans_defs get_vl_pre_committed_writers cl_unchanged_defs)
next
  case (Read x1 x2 x3 x4)
  then show ?case using pending_wtxn_cl_ev_inv[of s x1 s']
    apply (simp add: tps_trans_defs get_vl_pre_committed_writers cl_unchanged_defs)
    by (metis state_txn.distinct(7))
next
  case (RDone x1 x2 x3 x4)
  then show ?case using pending_wtxn_cl_ev_inv[of s x1 s']
    by (simp add: tps_trans_defs get_vl_pre_committed_writers cl_unchanged_defs)
next
  case (WInvoke x1 x2)                    
  then show ?case using pending_wtxn_cl_ev_inv[of s x1 s']
    apply (simp add: tps_trans_defs get_vl_pre_committed_writers cl_unchanged_defs) sorry
next
  case (WDone x)
  then show ?case using pending_wtxn_cl_ev_inv[of s x s']
    apply (simp add: tps_trans_defs get_vl_pre_committed_writers cl_unchanged_defs)
    by (metis state_txn.distinct(11))
next
  case (RegR x1 x2 x3 x4 x5)
  then show ?case using pending_wtxn_svr_ev_inv[of s' s]
    apply (simp add: tps_trans_defs get_vl_pre_committed_writers svr_unchanged_defs) sorry
next
  case (PrepW x1 x2 x3 x4)
  then show ?case using pending_wtxn_svr_ev_inv[of s' s]
    apply (simp add: tps_trans_defs get_vl_pre_committed_writers svr_unchanged_defs) sorry
next
  case (CommitW x1 x2)
  then show ?case using pending_wtxn_svr_ev_inv[of s' s]
    apply (simp add: tps_trans_defs get_vl_pre_committed_writers cl_unchanged_defs) sorry
qed auto


definition NoPendingInView where
  "NoPendingInView s \<longleftrightarrow> (\<forall>cl k. cl_view (cls s cl) k \<subseteq> v_writer ` set (get_vl_pre_committed s (DS (svrs s k))))"

lemmas NoPendingInViewI = NoPendingInView_def[THEN iffD2, rule_format]
lemmas NoPendingInViewE[elim] = NoPendingInView_def[THEN iffD1, elim_format, rule_format]

lemma reach_no_pending_in_view [simp, dest]: "reach tps s \<Longrightarrow> NoPendingInView s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    apply (auto simp add: NoPendingInView_def tps_defs view_txid_init_def commit_all_in_vl_writers)
    by (simp add: get_state_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x11 x12)
    then show ?case
      apply (auto simp add: NoPendingInView_def tps_trans_defs get_vl_pre_committed_writers
          cl_unchanged_defs pending_wtxn_cl_ev_inv[of s x11 s'] dest!:eq_for_all_cl) by blast
  next
    case (Read x21 x22 x23)
    then show ?case
      apply (auto simp add: NoPendingInView_def tps_trans_defs get_vl_pre_committed_writers
          cl_unchanged_defs pending_wtxn_cl_ev_inv[of s x21 s'] dest!:eq_for_all_cl) by blast
  next
    case (RDone x31 x32 x33 x34)
    then show ?case 
      apply (auto simp add: NoPendingInView_def tps_trans_defs get_vl_pre_committed_writers
          cl_unchanged_defs pending_wtxn_cl_ev_inv[of s x31 s']) sorry
  next
    case (WInvoke x41 x42)
    then show ?case
      apply (auto simp add: NoPendingInView_def tps_trans_defs get_vl_pre_committed_writers
          cl_unchanged_defs dest!:eq_for_all_cl) sorry
  next
    case (WCommit x51 x52 x53 x54 x55)
    then show ?case 
      apply (auto simp add: NoPendingInView_def tps_trans_defs get_vl_pre_committed_writers
          cl_unchanged_defs) sorry
  next
    case (WDone x6)
    then show ?case
      apply (auto simp add: NoPendingInView_def tps_trans_defs get_vl_pre_committed_writers
          cl_unchanged_defs pending_wtxn_cl_ev_inv[of s x6 s'] dest!:eq_for_all_cl) by blast
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?case 
      apply (auto simp add: NoPendingInView_def tps_trans_defs get_vl_pre_committed_writers
          svr_unchanged_defs pending_wtxn_svr_ev_inv[of s' s]) sorry
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case sorry
  next
    case (CommitW x91 x92)
    then show ?case sorry
  qed simp
qed

lemma in_view_index_not_none:
  assumes "x \<in> cl_view (cls s cl) k"
    and "NoPendingInView s"
  shows "x \<in> dom (get_indices_map (kvs_of_s s k))"
  using assms apply (auto simp add: kvs_of_s_def dom_indices_map get_indices_map_def)
  by blast

lemma map_extend_subset:
  assumes "k \<notin> dom m1"
    and "m2 = [k \<mapsto> v] ++ m1"
  shows "m1 \<subseteq>\<^sub>m m2"
  using assms
  by (simp add: map_le_def map_add_dom_app_simps(1))

lemma prefix_update_get_indices_map:
  shows "indices_map (vl1 @ [ver]) i = [v_writer ver \<mapsto> (i + length vl1)] ++ indices_map vl1 i"
  apply (induction vl1 i rule: indices_map.induct) subgoal by simp
  by (simp only: append_Cons indices_map.simps(2) map_add_upd length_Cons add_Suc_shift)

lemma prefix_subset_indices_map:
  assumes "v_writer ver \<notin> v_writer ` set vl1"
  shows "indices_map vl1 i \<subseteq>\<^sub>m indices_map (vl1 @ [ver]) i"
  using assms
  by (metis map_extend_subset dom_indices_map prefix_update_get_indices_map)

lemma read_commit_indices_map_grows:
  assumes "read_done cl kvt_map sn u s s'"
  shows "get_indices_map (kvs_of_s s k) \<subseteq>\<^sub>m get_indices_map (kvs_of_s s' k)"
  using assms
  apply (induction "kvs_of_s s k"; simp add: read_done_def dom_indices_map get_indices_map_def)
  apply (simp add: kvs_of_s_def) sorry

definition OnlyPendingVer where
  "OnlyPendingVer s cl k \<longleftrightarrow>
  (\<forall>t. \<forall>ver \<in> set (DS (svrs s k)). v_is_pending ver \<and> is_txn_writer t ver \<longrightarrow> t = Tn (get_txn_cl s cl))"

lemmas OnlyPendingVerI = OnlyPendingVer_def[THEN iffD2, rule_format]
lemmas OnlyPendingVerE[elim] = OnlyPendingVer_def[THEN iffD1, elim_format, rule_format]

lemma reach_only_pending_ver [simp, dest]: "reach tps s \<Longrightarrow> OnlyPendingVer s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: OnlyPendingVer_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case by (simp add: OnlyPendingVer_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x1 x2 x3 x4)
    then show ?case by (simp add: OnlyPendingVer_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: OnlyPendingVer_def tps_trans_defs cl_unchanged_defs)
      apply (cases "x1 = cl"; simp add: is_txn_writer_def)
      by (smt (z3) FreshWriteTxnInv_def insertI1 insert_commute insert_image reach_freshwrtxn reach_trans.hyps(2))
  next
    case (WInvoke x1 x2)
    then show ?case by (simp add: OnlyPendingVer_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case by (simp add: OnlyPendingVer_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WDone x)
    then show ?case apply (auto simp add: OnlyPendingVer_def tps_trans_defs cl_unchanged_defs)
      apply (cases "x = cl") subgoal sorry
      by metis 
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case sorry
  next
    case (CommitW x1 x2)
    then show ?case sorry
  qed simp
qed

definition CurrentVerPending where
  "CurrentVerPending s cl k \<longleftrightarrow>
    (\<forall>kvm keys ver kvtm. txn_state (cls s cl) \<in> {Idle, WtxnPrep kvm, RtxnInProg keys kvtm} \<and> 
    find (is_txn_writer (Tn (get_txn_cl s cl))) (DS (svrs s k)) = Some ver \<longrightarrow> v_is_pending ver)"

lemmas CurrentVerPendingI = CurrentVerPending_def[THEN iffD2, rule_format]
lemmas CurrentVerPendingE[elim] = CurrentVerPending_def[THEN iffD1, elim_format, rule_format]

lemma reach_curr_ver_pending [simp, dest]: "reach tps s \<Longrightarrow> CurrentVerPending s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: CurrentVerPending_def tps_defs DS_vl_init_def ep_version_init_def is_txn_writer_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case by (simp add: CurrentVerPending_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x1 x2 x3 x4)
    then show ?case by (simp add: CurrentVerPending_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: CurrentVerPending_def tps_trans_defs cl_unchanged_defs)
      by (metis (mono_tags, opaque_lifting) FutureTidWrDS_def find_Some_in_set image_iff
          is_txn_writer_def lessI reach_tidfuture_wr_ds)
  next
    case (WInvoke x1 x2)
    then show ?case by (simp add: CurrentVerPending_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: CurrentVerPending_def tps_trans_defs cl_unchanged_defs)
      by (metis (mono_tags))
  next
    case (WDone x)
    then show ?case apply (simp add: CurrentVerPending_def tps_trans_defs cl_unchanged_defs)
      by (metis (mono_tags) find_Some_in_set VerWrLCurrT_def Suc_n_not_le_n is_txn_writer_def
          reach_ver_wr_L_currT)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: CurrentVerPending_def tps_trans_defs svr_unchanged_defs)
      by (metis add_to_readerset_find_None add_to_readerset_find_is_pending option.exhaust)+
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: CurrentVerPending_def tps_trans_defs svr_unchanged_defs)
      by (cases "x1 = k"; auto simp add: find_append split: option.split)
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: CurrentVerPending_def tps_trans_defs svr_unchanged_defs)
      apply (cases "get_txn_cl s cl = x2"; cases "x1 = k"; auto del: disjE)
      using commit_in_vl_find_another[of "Tn (get_txn_cl s cl)" "Tn x2" "DS (svrs s k)"] by auto
  qed simp
qed

lemma filter_non_existing:
  assumes "x \<notin> set vl"
    and "P x" and "\<not>Q x"
    and "\<And>y. y \<noteq> x \<longrightarrow> P y = Q y"
  shows "filter P vl = filter Q vl"
  using assms
  by (metis filter_cong)

lemma filter_existing:
  assumes "x \<in> set vl"
    and "P x" and "\<not>Q x"
    and "\<And>y. y \<noteq> x \<longrightarrow> P y = Q y"
  shows "filter P vl = filter Q vl @ [x]"
  using assms oops
  
lemma write_commit_not_add_to_ready:
  assumes "find (is_txn_writer (Tn (get_txn_cl s cl))) (DS (svrs s k)) = None"
    and "txn_sn (cls s' cl) = txn_sn (cls s cl)"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "get_vl_ready_to_commit_wr s' (DS (svrs s' k)) = get_vl_ready_to_commit_wr s (DS (svrs s k))"
  using assms eq_for_all_cl[of txn_sn s' cl s]
  apply (simp add: cl_unchanged_defs get_vl_ready_to_commit_wr_def pending_wtxn_def is_txn_writer_def
      split: txid.split txid0.split)
  by (smt (verit) filter_cong find_None_iff)
  

lemma write_commit_adds_one_to_ready:
  assumes "find (is_txn_writer (Tn (get_txn_cl s cl))) (DS (svrs s k)) = Some ver"
    and "txn_state (cls s cl) = WtxnPrep kv_map"
    and "txn_state (cls s' cl) = WtxnCommit (global_time s) cts kv_map"
    and "txn_sn (cls s' cl) = txn_sn (cls s cl)"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "\<exists>ver \<in> set (DS (svrs s' k)). get_vl_ready_to_commit_wr s' (DS (svrs s' k)) =
                                      get_vl_ready_to_commit_wr s (DS (svrs s k)) @ [ver]"
  using assms eq_for_all_cl[of txn_sn s' cl s]
  apply (simp add: cl_unchanged_defs get_vl_ready_to_commit_wr_def pending_wtxn_def
      split: txid.split txid0.split)
  apply (rule bexI [where x=ver])
    subgoal sorry
    by (meson find_Some_in_set)


lemma get_glts_ready_to_commit_inv:
  assumes "PastTIDNotPending s cl" and "VerWrLCurrT s cl"
    and "ver \<in> set (get_vl_ready_to_commit_wr s (DS (svrs s k)))"
    and "find (is_txn_writer (Tn (get_txn_cl s cl))) (DS (svrs s k)) = None"
    and "txn_state (cls s cl) = WtxnPrep kv_map"
    and "txn_state (cls s' cl) = WtxnCommit (global_time s) cts kv_map"
    and "txn_sn (cls s' cl) = txn_sn (cls s cl)"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "get_glts s' ver = get_glts s ver"
  using assms
  apply (auto simp add: get_glts_def get_state_defs cl_unchanged_defs split: txid.split txid0.split)
  subgoal for n cl' apply (cases "cl' = cl"; simp add: is_txn_writer_def)
    by (smt (verit) PastTIDNotPending_def VerWrLCurrT_def find_None_iff order_le_imp_less_or_eq).

lemma write_commit_indices_map_grows:
  assumes "write_commit cl kv_map cts sn u s s'"
  shows "get_indices_map (kvs_of_s s k) \<subseteq>\<^sub>m get_indices_map (kvs_of_s s' k)"
  using assms
  apply (simp add: write_commit_def dom_indices_map get_indices_map_def)
  apply (simp add: kvs_of_s_def get_vl_pre_committed_def svrs_cls_cl'_unchanged_def)
  apply (cases "find (is_txn_writer (Tn (get_txn_cl s cl))) (DS (svrs s k))")
  subgoal apply (auto dest!: write_commit_not_add_to_ready)
    apply (induction s "get_vl_committed_wr (DS (svrs s k))" "get_vl_ready_to_commit_wr s (DS (svrs s k))"
        arbitrary: k s' rule: commit_all_in_vl.induct; auto) sorry
  apply (auto dest!: write_commit_adds_one_to_ready simp add:commit_all_in_vl_append)
  using prefix_subset_indices_map sorry

lemma kvs_readers_sqns_other_cl_inv:
  assumes "FutureTIDInv s cl" and "PastTIDInv s cl" and "KVSNonEmp s"
    and "txn_state (cls s cl) = RtxnInProg keys kvm"
    and "txn_state (cls s' cl) = Idle"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
    and "cl' \<noteq> cl"
  shows "kvs_readers_sqns (kvs_of_s s') cl' = kvs_readers_sqns (kvs_of_s s) cl'"
  using assms sorry

lemma vl_writers_sqns_other_cl_inv:
  assumes "KVSNonEmp s"
  shows "\<And>cl. vl_writers_sqns (map (epv_to_ver o get_ver_committed_rd s') (get_vl_pre_committed s' vl)) cl =
              vl_writers_sqns vl cl'"
  using assms
  apply (auto simp add: vl_writers_sqns_def vl_writers_def) sorry

lemma read_done_kvs_writers_sqns_inv:
  assumes "FutureTIDInv s cl" and "PastTIDInv s cl" and "KVSNonEmp s"
    and "txn_state (cls s cl) = RtxnInProg keys kvm"
    and "txn_state (cls s' cl) = Idle"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "\<And>cl. kvs_writers_sqns (kvs_of_s s') cl = kvs_writers_sqns (kvs_of_s s) cl"
  using assms
  apply (simp add: kvs_writers_sqns_def kvs_of_s_def)
  by (metis vl_writers_sqns_other_cl_inv)

lemma read_done_get_sqns_other_cl_inv:
  assumes "FutureTIDInv s cl" and "PastTIDInv s cl" and "KVSNonEmp s"
    and "txn_state (cls s cl) = RtxnInProg keys kvm"
    and "txn_state (cls s' cl) = Idle"
    and "svrs_cls_cl'_unchanged cl s s'"
    and "cl' \<noteq> cl"
  shows "get_sqns (kvs_of_s s') cl' = get_sqns (kvs_of_s s) cl'"
  using assms by (auto simp add: get_sqns_def read_done_kvs_writers_sqns_inv
      kvs_readers_sqns_other_cl_inv cl_unchanged_defs)
                              

definition SqnInv_nc where
  "SqnInv_nc s cl \<longleftrightarrow> (\<forall>gts cts kvm.
    (txn_state (cls s cl) \<noteq> WtxnCommit gts cts kvm \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m < txn_sn (cls s cl))))"

lemmas SqnInv_ncI = SqnInv_nc_def[THEN iffD2, rule_format]
lemmas SqnInv_ncE[elim] = SqnInv_nc_def[THEN iffD1, elim_format, rule_format]

lemma reach_sql_inv_nc [simp, intro]:
  assumes "reach tps s"
  shows "SqnInv_nc s cl"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    apply (auto simp add: SqnInv_nc_def tps_defs kvs_of_s_def get_sqns_old_def kvs_txids_def
        get_state_defs full_view_def DS_vl_init_def ep_version_init_def)
    apply (auto simp add: kvs_writers_def vl_writers_def)
    by (auto simp add: kvs_readers_def vl_readers_def)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: SqnInv_nc_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(5))
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: SqnInv_nc_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: SqnInv_nc_def tps_trans_defs)
       apply (metis (lifting) state_txn.distinct(9) cl_unchanged_defs)
      apply (cases "cl = x1", simp)
      subgoal sorry
      by (smt (verit) other_insts_unchanged_def reach_kvs_non_emp reach_tidfuturekm reach_tidpastkm
          svrs_cls_cl'_unchanged_def read_done_get_sqns_other_cl_inv)
  next
    case (WInvoke x1 x2)
    then show ?case apply (simp add: SqnInv_nc_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(5))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: SqnInv_nc_def tps_trans_defs cl_unchanged_defs) sorry
  next
    case (WDone x)
    then show ?case apply (simp add: SqnInv_nc_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) less_SucI nat.discI state_txn.inject(3))
  qed (auto simp add: SqnInv_nc_def tps_trans_defs svr_unchanged_defs)
qed

definition SqnInv_c where
  "SqnInv_c s cl \<longleftrightarrow> (\<forall>gts cts kvm.
    (txn_state (cls s cl) = WtxnCommit gts cts kvm \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m \<le> txn_sn (cls s cl))))"

lemmas SqnInv_cI = SqnInv_c_def[THEN iffD2, rule_format]
lemmas SqnInv_cE[elim] = SqnInv_c_def[THEN iffD1, elim_format, rule_format]

lemma reach_sql_inv_c [simp, intro]:
  assumes "reach tps s"
    and "KVSNonEmp s"
  shows "SqnInv_c s cl"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: SqnInv_c_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: SqnInv_c_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(9))
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: SqnInv_c_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: SqnInv_c_def tps_trans_defs cl_unchanged_defs)
      apply (metis state_txn.distinct(5))
      by (metis SqnInv_nc_def nat.distinct(1) nless_le reach.reach_trans reach_sql_inv_nc
          reach_trans.hyps(1) state_txn.inject(3))
  next
    case (WInvoke x1 x2)
    then show ?case apply (simp add: SqnInv_c_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(11))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: SqnInv_c_def tps_trans_defs cl_unchanged_defs)
      by (metis SqnInv_nc_def leD nat_le_linear reach.reach_trans reach_sql_inv_nc
          reach_trans.hyps(1) state_txn.inject(3))
  next
    case (WDone x)
    then show ?case apply (simp add: SqnInv_c_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(5))
  qed (auto simp add: SqnInv_c_def tps_trans_defs svr_unchanged_defs)
qed

lemma t_is_fresh:
  assumes "SqnInv_c s cl" and "SqnInv_nc s cl"
    and "txn_state (cls s cl) \<in> {WtxnPrep kv_map, RtxnInProg keys kvt_map}"
  shows "get_txn_cl s cl \<in> next_txids (kvs_of_s s) cl"
  using assms by (auto simp add: kvs_of_s_def next_txids_def)

\<comment> \<open>CanCommit\<close>

definition RO_WO_Inv where
  "RO_WO_Inv s \<longleftrightarrow> (kvs_writers (\<lambda>k. DS (svrs s k)) \<inter> Tn ` kvs_readers (\<lambda>k. DS (svrs s k)) = {})"

lemmas RO_WO_InvI = RO_WO_Inv_def[THEN iffD2, rule_format]
lemmas RO_WO_InvE[elim] = RO_WO_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_ro_wo_inv [simp, dest]: "reach tps s \<Longrightarrow> RO_WO_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: RO_WO_Inv_def tps_defs DS_vl_init_def ep_version_init_def txid_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: RO_WO_Inv_def tps_trans_defs svr_unchanged_defs)
     using add_to_readerset_v_writer_img[of ] apply (simp add: txid_defs) sorry \<comment> \<open>Continue here!\<close>
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case sorry
  next
    case (CommitW x1 x2)
    then show ?case sorry
  qed (auto simp add: RO_WO_Inv_def tps_trans_defs cl_unchanged_defs)
qed

lemma "kvs_txids (kvs_of_s gs) - kvs_writers (kvs_of_s gs) = Tn ` kvs_readers (kvs_of_s gs)"
  apply (simp add: kvs_of_s_def) sorry

definition canCommit_rd_Inv where
  "canCommit_rd_Inv s cl \<longleftrightarrow> (\<forall>kvt_map. txn_state (cls s cl) = RtxnInProg (dom kvt_map) kvt_map  \<longrightarrow>
    ET_CC.canCommit (kvs_of_s s) (view_txid_vid s (curr_rd_view s cl kvt_map))
      (\<lambda>k. case_op_type (map_option fst (kvt_map k)) None))"

lemmas canCommit_rd_InvI = canCommit_rd_Inv_def[THEN iffD2, rule_format]
lemmas canCommit_rd_InvE[elim] = canCommit_rd_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_canCommit_rd_inv [simp, dest]: "reach tps s \<Longrightarrow> canCommit_rd_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: canCommit_rd_Inv_def tps_defs DS_vl_init_def ep_version_init_def txid_defs)
next
  case (reach_trans s e s')
  then show ?case
  using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case
      apply (simp add: canCommit_rd_Inv_def tps_trans_defs cl_unchanged_defs curr_rd_view_def)
      apply (cases "cl = x1"; simp) by presburger
  next
    case (Read x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: canCommit_rd_Inv_def tps_trans_defs cl_unchanged_defs curr_rd_view_def 
                  dest!: eq_for_all_cl)
      apply (cases "cl = x1"; simp) subgoal sorry by presburger
  next
    case (RDone x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: canCommit_rd_Inv_def tps_trans_defs cl_unchanged_defs curr_rd_view_def
                  dest!: eq_for_all_cl)
      apply (cases "cl = x1"; simp add: ET_CC.canCommit_def closed_def R_CC_def R_onK_def) sorry
  next
    case (WInvoke x1 x2)
    then show ?case
      apply (simp add: canCommit_rd_Inv_def tps_trans_defs cl_unchanged_defs curr_rd_view_def)
      apply (cases "cl = x1"; simp) by presburger
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: canCommit_rd_Inv_def tps_trans_defs cl_unchanged_defs curr_rd_view_def 
                  dest!: eq_for_all_cl)
      apply (cases "cl = x1"; simp) sorry
  next
    case (WDone x)
    then show ?case
      apply (simp add: canCommit_rd_Inv_def tps_trans_defs cl_unchanged_defs curr_rd_view_def)
      apply (cases "cl = x"; simp) by presburger
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case
      apply (simp add: canCommit_rd_Inv_def tps_trans_defs svr_unchanged_defs curr_rd_view_def)
      by presburger
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case
      apply (simp add: canCommit_rd_Inv_def tps_trans_defs svr_unchanged_defs curr_rd_view_def)
      by presburger
  next
    case (CommitW x1 x2)
    then show ?case
      apply (simp add: canCommit_rd_Inv_def tps_trans_defs svr_unchanged_defs curr_rd_view_def)
      by presburger
  qed simp
qed

subsection\<open>View invariants\<close>

lemma cl_view_inv:
  assumes "state_trans s e s'"
    and "not_committing_ev e"
  shows "cl_view (cls s' cl) = cl_view (cls s cl)"
  using assms
  by (induction e) (auto simp add: tps_trans_defs unchanged_defs views_of_s_def dest!:eq_for_all_cl)

lemma views_of_s_inv:
  assumes "state_trans s e s'"
    and "invariant_list_kvs s"
    and "not_committing_ev e"
  shows "views_of_s s' cl = views_of_s s cl"
  using assms using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case by simp
  qed (auto simp add: tps_trans_defs unchanged_defs views_of_s_def dest!:eq_for_all_cl)

lemma read_commit_views_of_s_other_cl_inv:
  assumes "read_done cl kv_map sn u s s'"
    and "NoPendingInView s"
    and "cl' \<noteq> cl"
  shows "views_of_s s' cl' = views_of_s s cl'"
  using assms
  apply (auto simp add: read_done_def svrs_cls_cl'_unchanged_def views_of_s_def image_def split: option.split)
  apply (rule ext) subgoal for k using read_commit_indices_map_grows [where s=s and s'=s' and k=k]
    unfolding map_le_def
    by (smt (z3) Collect_cong assms(1) domIff in_view_index_not_none other_insts_unchanged_def).

lemma write_commit_views_of_s_other_cl_inv:
  assumes "write_commit cl kv_map cts sn u s s'"
    and "NoPendingInView s"
    and "cl' \<noteq> cl"
  shows "views_of_s s' cl' = views_of_s s cl'"
  using assms
  apply (auto simp add: write_commit_def svrs_cls_cl'_unchanged_def views_of_s_def image_def split: option.split)
  apply (rule ext) subgoal for k using write_commit_indices_map_grows [where s=s and s'=s' and k=k]
    unfolding map_le_def
    by (smt (z3) Collect_cong assms(1) domIff in_view_index_not_none other_insts_unchanged_def).

abbreviation invariant_list where
  "invariant_list s \<equiv> (\<forall>cl. invariant_list_kvs s \<and> NoPendingInView s \<and> SqnInv_c s cl \<and> SqnInv_nc s cl \<and>
    canCommit_rd_Inv s cl)"

subsection \<open>Refinement Proof\<close>

lemma tps_refines_et_es: "tps \<sqsubseteq>\<^sub>med ET_CC.ET_ES"
proof (intro simulate_ES_fun_with_invariant[where I="\<lambda>s. invariant_list s"])
  fix gs0 :: "'v state"
  assume p: "init tps gs0"
  then show "init ET_CC.ET_ES (sim gs0)"
  by (auto simp add: ET_CC.ET_ES_defs tps_defs sim_defs DS_vl_init_def ep_version_init_def get_state_defs
    get_indices_map_def kvs_init_def v_list_init_def version_init_def view_txid_init_def)
next
  fix gs a and gs' :: "'v state"
  assume p: "tps: gs\<midarrow>a\<rightarrow> gs'" and inv: "invariant_list gs"
  then show "ET_CC.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  using kvs_of_s_inv[of gs a gs'] views_of_s_inv[of gs a gs']
  proof (induction a)
    case (RDone cl kvt_map sn u'')
    then show ?case using p apply simp
      apply (auto simp add: read_done_def cl_unchanged_defs sim_def)
      apply (rule exI [where x="views_of_s gs' cl"]) apply auto
      subgoal apply (auto simp add: ET_CC.ET_cl_txn_def t_is_fresh KVSSNonEmp_def canCommit_rd_Inv_def)
        subgoal apply (simp add: view_wellformed_def views_of_s_def) sorry
        subgoal sorry
        subgoal apply (auto simp add: vShift_MR_RYW_def vShift_MR_def vShift_RYW_def) sorry
        sorry
        subgoal apply (rule ext)
          subgoal for cl' apply (cases "cl' = cl"; simp)
          using read_commit_views_of_s_other_cl_inv [where s=gs and s'=gs' and cl=cl and cl'=cl']
          by (metis RDone.prems(1) state_trans.simps(3) tps_trans).
      subgoal apply (auto simp add: fp_property_def view_snapshot_def)
        subgoal for k y apply (simp add: last_version_def kvs_of_s_def get_state_defs)
          apply (cases "k \<in> dom kvt_map") sorry
        done
      done
  next
    case (WCommit cl kv_map cts sn u'')
    then show ?case using p apply simp
      apply (auto simp add: write_commit_def cl_unchanged_defs sim_def fp_property_def)
      apply (rule exI [where x="views_of_s gs' cl"]) apply auto
        subgoal apply (auto simp add: ET_CC.ET_cl_txn_def t_is_fresh) sorry
        subgoal apply (rule ext)
          subgoal for cl' apply (cases "cl' = cl"; simp)
          using write_commit_views_of_s_other_cl_inv [where s=gs and s'=gs' and cl=cl and cl'=cl']
          by (metis WCommit.prems(1) state_trans.simps(5) tps_trans).
      done
  qed (auto simp add: sim_defs get_state_defs image_iff)
qed simp

end