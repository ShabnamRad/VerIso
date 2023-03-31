section \<open>Eiger Port Plus Protocol Satisfying CCv (Causal+) - Proofs and lemmas\<close>

theory CCv_Eiger_Port_plus_proof
  imports CCv_Eiger_Port_plus
begin

section \<open>Lemmas about the functions\<close>


subsection \<open>wts_dom lemmas\<close>

lemma wts_dom_eq_empty_conv [simp]: "wts_dom wts = {} \<longleftrightarrow> wts = wts_emp"
  by (auto simp: wts_dom_def)

lemma wts_domI1: "wts t = Prep ts v \<Longrightarrow> t \<in> wts_dom wts"
  by (simp add: wts_dom_def)

lemma wts_domI2: "wts t = Commit cts v rs \<Longrightarrow> t \<in> wts_dom wts"
  by (simp add: wts_dom_def)

lemma wts_domD: "t \<in> wts_dom wts \<Longrightarrow> (\<exists>ts v. wts t = Prep ts v) \<or> (\<exists>cts v rs. wts t = Commit cts v rs)"
  by (cases "wts t") (auto simp add: wts_dom_def)

lemma wts_domIff [iff, simp del, code_unfold]: "t \<in> wts_dom wts \<longleftrightarrow> wts t \<noteq> No_Ver"
  by (simp add: wts_dom_def)

lemma wts_dom_fun_upd [simp]:
  "wts_dom(wts(t := x)) = (if x = No_Ver then wts_dom wts - {t} else insert t (wts_dom wts))"
  by (auto simp: wts_dom_def)

lemma wts_dom_if:
  "wts_dom (\<lambda>x. if P x then f x else g x) = wts_dom f \<inter> {x. P x} \<union> wts_dom g \<inter> {x. \<not> P x}"
  by (auto split: if_splits)

lemma wts_dom_minus:
  "wts t = No_Ver \<Longrightarrow> wts_dom wts - insert t A = wts_dom wts - A"
  unfolding wts_dom_def by simp

lemma insert_prep_wts_dom:
  "wts t = Prep ts v \<Longrightarrow> insert t (wts_dom wts) = wts_dom wts"
  unfolding wts_dom_def by auto

lemma insert_commit_wts_dom:
  "wts t = Commit cts v rs \<Longrightarrow> insert t (wts_dom wts) = wts_dom wts"
  unfolding wts_dom_def by auto


subsection \<open>wts_rsran lemmas\<close>

lemma wts_vranI1: "wts t = Commit cts v rs \<Longrightarrow> v \<in> wts_vran wts"
  apply (simp add: wts_vran_def) by blast

lemma wts_vranI2: "wts t = Prep ts v \<Longrightarrow> v \<in> wts_vran wts"
  apply (simp add: wts_vran_def) by blast

lemma wts_vran_empty [simp]: "wts_vran wts_emp = {}"
  by (auto simp: wts_vran_def)

lemma wts_vran_map_upd [simp]:  "wts t = No_Ver \<Longrightarrow>
  wts_vran (wts (t := Commit cts v rs)) = insert v (wts_vran wts)"
  apply (auto simp add: wts_vran_def)
  apply (metis ver_state.distinct(1))
  by (metis ver_state.distinct(3))

lemma finite_wts_vran:
  assumes "finite (wts_dom wts)"
  shows "finite (wts_vran wts)"
proof -
  have "wts_vran wts = (\<lambda>t. get_val_ver (wts t)) ` wts_dom wts"
    unfolding wts_vran_def
    by (smt (verit) Collect_cong Setcompr_eq_image get_val_ver.simps wts_domD wts_domI1 wts_domI2)
  from this \<open>finite (wts_dom wts)\<close> show ?thesis by auto
qed
      
      
subsection \<open>wts_rsran lemmas\<close>

lemma wts_rsranI1: "wts t = Commit cts v rs \<Longrightarrow> rs \<in> wts_rsran wts"
  apply (simp add: wts_rsran_def) by blast

lemma wts_rsranI2: "wts t = Prep ts v \<Longrightarrow> {} \<in> wts_rsran wts"
  apply (simp add: wts_rsran_def) by blast

lemma wts_rsran_empty [simp]: "wts_rsran wts_emp = {}"
  by (auto simp: wts_rsran_def)

lemma wts_rsran_map_upd1 [simp]:  "wts t = No_Ver \<Longrightarrow>
  wts_rsran (wts (t := Prep ts v)) = insert {} (wts_rsran wts)"
  apply (auto simp add: wts_rsran_def)
  by (metis ver_state.distinct(3))

lemma wts_rsran_map_upd2 [simp]:  "wts t = No_Ver \<Longrightarrow>
  wts_rsran (wts (t := Commit cts v rs)) = insert rs (wts_rsran wts)"
  apply (auto simp add: wts_rsran_def)
  apply (metis ver_state.distinct(1))
  by (metis ver_state.distinct(3))

lemma finite_wts_rsran:
  assumes "finite (wts_dom wts)"
  shows "finite (wts_rsran wts)"
proof -
  have "wts_rsran wts = (\<lambda>t. get_rs_ver (wts t)) ` wts_dom wts"
    unfolding wts_rsran_def
    by (smt (verit) Collect_cong Setcompr_eq_image get_rs_ver.simps wts_domD wts_domI1 wts_domI2)
  from this \<open>finite (wts_dom wts)\<close> show ?thesis by auto
qed


subsection \<open>Translator functions lemmas\<close>

lemma "\<forall>rts wts. \<exists>t. committed_at wts t (at_cts wts rts)" sorry

lemma "get_ts_ver (wts (at wts rts)) = at_cts wts rts" apply (simp add: at_def) sorry


subsection \<open>Helper functions lemmas\<close>

lemma add_to_readerset_wts_dom: "wts_dom (add_to_readerset wts t t') = wts_dom wts"
  by (auto simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_no_ver_inv:
  "add_to_readerset wts t t' t'' = No_Ver \<longleftrightarrow> wts t'' = No_Ver"
  by (simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_prep_inv:
  "add_to_readerset wts t t' t'' = Prep ts v \<longleftrightarrow> wts t'' = Prep ts v"
  by (simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_commit:
  "add_to_readerset wts t t' t'' = Commit cts v rs \<Longrightarrow> \<exists>rs'. wts t'' = Commit cts v rs'"
  apply (simp add: add_to_readerset_def)
  by (cases "wts t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_commit_subset:
  "add_to_readerset wts t t' t'' = Commit cts v rs \<Longrightarrow> \<exists>rs'. wts t'' = Commit cts v rs' \<and> rs' \<subseteq> rs"
  apply (simp add: add_to_readerset_def)
  by (cases "wts t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_commit':
  "wts t'' = Commit cts v rs' \<Longrightarrow> \<exists>rs. add_to_readerset wts t t' t'' = Commit cts v rs"
  apply (simp add: add_to_readerset_def)
  by (cases "wts t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_commit'_subset:
  "wts t'' = Commit cts v rs' \<Longrightarrow> \<exists>rs. add_to_readerset wts t t' t'' = Commit cts v rs \<and> rs' \<subseteq> rs"
  apply (simp add: add_to_readerset_def)
  by (cases "wts t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_upd:
  assumes "wts' = add_to_readerset wts t t_wr"
    and "t' \<noteq> t_wr"
  shows "wts' t' = wts t'"
  using assms
  by (simp add: add_to_readerset_def split: ver_state.split)


lemma finite_pending_wtxns_rtxn:
  assumes "wtxn_state (svrs s' k) = add_to_readerset (wtxn_state (svrs s k)) t' t"
    and "finite (pending_wtxns s svr)"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
  shows "finite (pending_wtxns s' svr)"
  using assms apply (auto simp add: add_to_readerset_def finite_nat_set_iff_bounded_le pending_wtxns_def)
  by (metis (full_types) add_to_readerset_prep_inv assms(1))

lemma finite_pending_wtxns_adding: 
  assumes "wtxn_state (svrs s' k) = (wtxn_state (svrs s k)) (t := Prep prep_t v)"
    and "finite (pending_wtxns s svr)"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
  shows "finite (pending_wtxns s' svr)"
  using assms apply (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_def)
  by (metis (full_types) dual_order.trans fun_upd_def linorder_le_cases ver_state.inject(1))

lemma finite_pending_wtxns_removing: 
  assumes "wtxn_state (svrs s' k) = (wtxn_state (svrs s k)) (t := Commit cts v rs)"
    and "finite (pending_wtxns s svr)"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
  shows "finite (pending_wtxns s' svr)"
  using assms apply (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_def)
  by (metis fun_upd_def ver_state.distinct(5))

lemma pending_wtxns_adding_ub:
  assumes "wtxn_state (svrs s' k) = (wtxn_state (svrs s k)) (t := Prep clk v)"
    and "\<forall>ts \<in> pending_wtxns s k. ts \<le> clk"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
  shows "\<forall>ts \<in> pending_wtxns s' k. ts \<le> clk"
  using assms by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_def)

lemma pending_wtxns_removing_ub:
  assumes "wtxn_state (svrs s' k) = (wtxn_state (svrs s k)) (t := Commit cts v rs)"
    and "\<forall>ts \<in> pending_wtxns s k. ts \<le> clk"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
  shows "\<forall>ts \<in> pending_wtxns s' k. ts \<le> clk"
  using assms by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_def)

lemma pending_wtxns_rtxn:
  assumes "wtxn_state (svrs s' k) = add_to_readerset (wtxn_state (svrs s k)) t' t"
    and "\<forall>clk v. wtxn_state (svrs s k) t \<noteq> Prep clk v"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
  shows "pending_wtxns s' k = pending_wtxns s k"
  using assms apply (auto simp add: pending_wtxns_def)
  by (meson add_to_readerset_prep_inv)+

lemma pending_wtxns_adding:
  assumes "wtxn_state (svrs s' k) = (wtxn_state (svrs s k)) (t := Prep clk v)"
    and "\<forall>clk v. wtxn_state (svrs s k) t \<noteq> Prep clk v"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
  shows "pending_wtxns s' k = insert clk (pending_wtxns s k)"
  using assms apply (auto simp add: pending_wtxns_def)
  by metis

lemma pending_wtxns_removing:
  assumes "wtxn_state (svrs s k) t = Prep clk v"
    and "wtxn_state (svrs s' k) = (wtxn_state (svrs s k)) (t := Commit cts v rs)"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
  shows "pending_wtxns s' k = pending_wtxns s k \<or> pending_wtxns s' k = Set.remove clk (pending_wtxns s k)"
  using assms apply (auto simp add: pending_wtxns_def)
  apply (metis ver_state.inject(1))
  by (metis get_ts_ver.simps(2))

lemma pending_wtxns_empty:
  "pending_wtxns s k = {} \<longleftrightarrow> (\<forall>t. \<exists>cts v rs. wtxn_state (svrs s k) t \<in> {No_Ver, Commit cts v rs})"
  apply (auto simp add: pending_wtxns_def)
  apply (metis get_rs_ver.elims)
  by (metis ver_state.distinct(1) ver_state.distinct(5))

lemma pending_wtxns_non_empty:
  assumes "wtxn_state (svrs s k) t \<noteq> No_Ver"
    and "\<forall>cts v rs. wtxn_state (svrs s k) t \<noteq> Commit cts v rs"
  shows "pending_wtxns s k \<noteq> {}"
  using assms apply (auto simp add: pending_wtxns_def)
  by (metis get_val_ver.cases)


lemma get_view_add_to_readerset_inv:
  assumes "wtxn_state (svrs s' k) = add_to_readerset (wtxn_state (svrs s k)) t t_wr"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> svrs s' k' = svrs s k'"
    and "gst (cls s' cl) = gst (cls s cl)"
  shows "get_view s' cl = get_view s cl"
  apply (simp add: get_view_def add_to_readerset_def)
  apply (rule ext, auto del: disjE)
  apply (metis add_to_readerset_commit assms)
  by (metis add_to_readerset_commit' assms)

lemma get_view_wprep_inv:
  assumes "wtxn_state (svrs s' k) = (wtxn_state (svrs s k)) (t := Prep clk v)"
    and "wtxn_state (svrs s k) t = No_Ver"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> svrs s' k' = svrs s k'"
    and "gst (cls s' cl) = gst (cls s cl)"
  shows "get_view s' cl = get_view s cl"
  using assms
  apply (simp add: get_view_def add_to_readerset_def)
  apply (rule ext, auto del: disjE)
  apply (metis fun_upd_other fun_upd_same ver_state.distinct(5))
  by (metis fun_upd_other ver_state.distinct(3))

lemma get_view_wcommit_inv:
  assumes "wtxn_state (svrs s' k) = (wtxn_state (svrs s k)) (t := Commit cts v {})"
    and "wtxn_state (svrs s k) t = Prep ts v"
    and "txn_state (cls s (get_cl_wtxn t)) = WtxnCommit cts kv_map"
    and "get_cl_wtxn t \<noteq> cl"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> svrs s' k' = svrs s k'"
    and "gst (cls s' cl) = gst (cls s cl)"
  shows "get_view s' cl = get_view s cl"
  using assms
  apply (simp add: get_view_def add_to_readerset_def)
  apply (rule ext, auto del: disjE)
  subgoal for k' apply (cases "k' = k"; simp split: if_split_asm) oops
  (* show cts > rts *)


subsection  \<open>Extra: general lemmas\<close>

lemma find_Some_in_set:
  "find P vl = Some ver \<Longrightarrow> ver \<in> set vl \<and> P ver"
  apply (simp add: find_Some_iff)
  by (meson nth_mem)

lemma find_append:
  "find P (vl1 @ vl2) = (case find P vl1 of None \<Rightarrow> find P vl2 | Some ver \<Rightarrow> Some ver)"
  by (induction vl1; simp)

lemma append_image: "f ` set (vl @ [a]) = insert (f a) (f ` set vl)"
  by simp


section \<open>Invariants and lemmas\<close>


subsection \<open>lemmas for unchanged elements in svrs\<close>

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
    apply (auto simp add: PendingWtxnsUB_def tps_defs wtid_match_def pending_wtxns_def)
    by (metis ver_state.distinct(1) ver_state.distinct(5))
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
      by (smt (z3) clock_monotonic fun_upd_apply le_trans reach_trans.hyps(1) tps_trans ver_state.inject(1))
  next
    case (CommitW x1 x2)
    then show ?case
      apply (auto simp add: PendingWtxnsUB_def tps_trans_defs svr_unchanged_defs pending_wtxns_def ran_def)
      by (smt (z3) fun_upd_other fun_upd_same max.coboundedI1 plus_1_eq_Suc trans_le_add2 ver_state.distinct(5))
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
  by (auto simp add: ClockLstInv_def tps_defs wtid_match_def)
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
  by (auto simp add: PendingWtxnsLB_def tps_defs wtid_match_def)
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
      by (metis ClockLstInv_def fun_upd_apply reach_clocklstinv ver_state.inject(1))
  next
    case (CommitW x1 x2)
    then show ?case
    apply (auto simp add: PendingWtxnsLB_def commit_write_def svr_unchanged_defs pending_wtxns_def)
    apply (cases "pending_wtxns s' x1 = {}")
      apply (metis pending_wtxns_non_empty ver_state.distinct(1) ver_state.distinct(5))
      apply (cases "svr = x1"; auto)
      apply (metis ver_state.distinct(5))
      subgoal for x kv_map y glts prep_t commit_t t apply (cases "t = x2"; auto)
      proof -
        fix t ts v
        assume a: "wtxn_state (svrs s x1) t = Prep ts v" and b: "t \<noteq> x2"
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
      apply (cases "k = x1") subgoal for t ta commit_t kv_map prep_t v y
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
      apply (metis pending_wtxns_non_empty ver_state.distinct(1) ver_state.distinct(5))
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


definition GstLtPts where
  "GstLtPts s cl \<longleftrightarrow> (\<forall>k prep_t v. 
      wtxn_state (svrs s k) (get_wtxn_cl s cl) = Prep prep_t v \<longrightarrow> gst (cls s cl) < prep_t)"
                                                           
lemmas GstLtPtsI = GstLtPts_def[THEN iffD2, rule_format]
lemmas GstLtPtsE[elim] = GstLtPts_def[THEN iffD1, elim_format, rule_format]

lemma reach_GstLtPts [simp, dest]: "reach tps s \<Longrightarrow> GstLtPts s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: GstLtPts_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case sorry
qed


definition GstLtCts where
  "GstLtCts s cl \<longleftrightarrow> (\<forall>cts kv_map. txn_state (cls s cl) = WtxnCommit cts kv_map \<longrightarrow> gst (cls s cl) < cts)"
                                                           
lemmas GstLtCtsI = GstLtCts_def[THEN iffD2, rule_format]
lemmas GstLtCtsE[elim] = GstLtCts_def[THEN iffD1, elim_format, rule_format]

lemma reach_GstLtCts [simp, dest]: "reach tps s \<Longrightarrow> GstLtCts s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: GstLtCts_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: GstLtCts_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(9))
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: GstLtCts_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: GstLtCts_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(5))
  next
    case (WInvoke x1 x2)
    then show ?case apply (simp add: GstLtCts_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(11))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: GstLtCts_def tps_trans_defs cl_unchanged_defs)
      apply (cases "cl = x1"; simp) sorry
  next
    case (WDone x)
    then show ?case apply (simp add: GstLtCts_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(5))
  qed (simp_all add: GstLtCts_def tps_trans_defs svr_unchanged_defs)
qed


subsection \<open>Invariants about kvs, global ts and init version v0\<close>

definition KVSNonEmp where
  "KVSNonEmp s \<longleftrightarrow> (\<forall>k. wtxn_state (svrs s k) \<noteq> wts_emp)"

lemmas KVSNonEmpI = KVSNonEmp_def[THEN iffD2, rule_format]
lemmas KVSNonEmpE[elim] = KVSNonEmp_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_non_emp [simp, intro]: "reach tps s \<Longrightarrow> KVSNonEmp s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    apply (auto simp add: KVSNonEmp_def tps_defs)
    by (metis fun_upd_apply ver_state.distinct(3))
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: KVSNonEmp_def tps_trans_defs svr_unchanged_defs)
      by (metis add_to_readerset_wts_dom wts_domIff)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: KVSNonEmp_def tps_trans_defs svr_unchanged_defs)
      by (metis fun_upd_same ver_state.distinct(1))
  next
    case (CommitW x1 x2)
    then show ?case
      apply (auto simp add: KVSNonEmp_def tps_trans_defs svr_unchanged_defs)
      by (metis fun_upd_same ver_state.distinct(3))
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


subsection \<open>Invariant about server and client state relations and (future and past) transactions ids\<close>

definition FutureTIDInv where
  "FutureTIDInv s cl \<longleftrightarrow> (\<forall>n k. n > txn_sn (cls s cl) \<longrightarrow> wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver)"

lemmas FutureTIDInvI = FutureTIDInv_def[THEN iffD2, rule_format]
lemmas FutureTIDInvE[elim] = FutureTIDInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidfuturekm [simp, dest]: "reach tps s \<Longrightarrow> FutureTIDInv s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FutureTIDInv_def tps_defs wtid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x11 x12)
    then show ?case
      by (auto simp add: tps_trans_defs cl_unchanged_defs wtid_match_def FutureTIDInv_def, metis)
  next
    case (Read x21 x22 x23 x24)
    then show ?case
      by (auto simp add: tps_trans_defs cl_unchanged_defs wtid_match_def FutureTIDInv_def, metis)
  next
    case (RDone x31 x32 x33 x34)
    then show ?case
      apply (auto simp add: tps_trans_defs cl_unchanged_defs wtid_match_def FutureTIDInv_def)
      by (metis Suc_lessD)
  next
    case (WInvoke x41 x42)
    then show ?case
      by (auto simp add: tps_trans_defs cl_unchanged_defs wtid_match_def FutureTIDInv_def, metis)
  next
    case (WCommit x51 x52 x53 x54 x55)
    then show ?case
      apply (auto simp add: tps_trans_defs cl_unchanged_defs wtid_match_def FutureTIDInv_def)
      by (metis (lifting))
  next
    case (WDone x6)
    then show ?case  using reach_trans
      apply (auto simp add: tps_trans_defs cl_unchanged_defs wtid_match_def FutureTIDInv_def)
      by (metis Suc_lessD)
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?case
      apply (auto simp add: tps_trans_defs svr_unchanged_defs wtid_match_def FutureTIDInv_def)
      by (metis add_to_readerset_no_ver_inv)
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case
      apply (auto simp add: tps_trans_defs svr_unchanged_defs wtid_match_def FutureTIDInv_def)
      by (metis fun_upd_apply get_cl_wtxn.simps(2) get_sn_wtxn.simps(2) nat_neq_iff)
  next
    case (CommitW x91 x92)
    then show ?case  using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs wtid_match_def FutureTIDInv_def)
      by (metis insert_prep_wts_dom ver_state.distinct(3) wts_domIff wts_dom_fun_upd)
  qed simp
qed


definition IdleReadInv where
  "IdleReadInv s \<longleftrightarrow> (\<forall>cl k keys kvm. txn_state (cls s cl) \<in> {Idle, RtxnInProg keys kvm}
    \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) = No_Ver)"

lemmas IdleReadInvI = IdleReadInv_def[THEN iffD2, rule_format]
lemmas IdleReadInvE[elim] = IdleReadInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_idle_read_inv [simp, dest]: "reach tps s \<Longrightarrow> IdleReadInv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: IdleReadInv_def tps_defs wtid_match_def)
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
      by (metis add_to_readerset_no_ver_inv)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs svr_unchanged_defs)
      by (metis fun_upd_other get_cl_wtxn.simps(2) state_txn.distinct(3) state_txn.distinct(7))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs svr_unchanged_defs)
      by (metis (full_types) fun_upd_apply ver_state.distinct(1))
  qed simp
qed

definition WriteTxnIdleSvr where
  "WriteTxnIdleSvr s \<longleftrightarrow>
    (\<forall>cl k cts kv_map. txn_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map}
        \<and> kv_map k = None \<longrightarrow> wtxn_state (svrs s k) (Tn (get_txn_cl s cl)) = No_Ver)"

lemmas WriteTxnIdleSvrI = WriteTxnIdleSvr_def[THEN iffD2, rule_format]
lemmas WriteTxnIdleSvrE[elim] = WriteTxnIdleSvr_def[THEN iffD1, elim_format, rule_format]

lemma reach_write_txn_idle_svr [simp, dest]: "reach tps s \<Longrightarrow> WriteTxnIdleSvr s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: WriteTxnIdleSvr_def tps_defs wtid_match_def)
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
      by (metis add_to_readerset_no_ver_inv)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: WriteTxnIdleSvr_def tps_trans_defs svr_unchanged_defs)
      by (smt (z3) domIff fun_upd_other get_cl_wtxn.simps(2) state_txn.distinct(11) state_txn.inject(2))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: WriteTxnIdleSvr_def tps_trans_defs svr_unchanged_defs)
      by (smt (verit) fun_upd_apply ver_state.distinct(1))
  qed simp
qed

definition PastTIDInv where
  "PastTIDInv s cl \<longleftrightarrow> (\<forall>k. \<forall>n < txn_sn (cls s cl).
   wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver \<or>
   (\<exists>cts v rs. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts v rs))"

lemmas PastTIDInvI = PastTIDInv_def[THEN iffD2, rule_format]
lemmas PastTIDInvE[elim] = PastTIDInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidpastkm [simp, dest]: "reach tps s \<Longrightarrow> PastTIDInv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: PastTIDInv_def tps_defs wtid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x11 x12)
    then show ?case
      by (auto simp add: tps_trans_defs cl_unchanged_defs PastTIDInv_def, metis)
  next
    case (Read x21 x22 x23)
    then show ?case
      by (auto simp add: tps_trans_defs cl_unchanged_defs PastTIDInv_def, metis)
  next
    case (RDone x31 x32 x33 x34)
    then show ?case
      apply (auto simp add: tps_trans_defs cl_unchanged_defs PastTIDInv_def)
      by (smt IdleReadInv_def insertI1 insert_commute not_less_less_Suc_eq reach_idle_read_inv reach_trans.hyps(2))
  next
    case (WInvoke x41 x42)
    then show ?case
      by (auto simp add: tps_trans_defs cl_unchanged_defs PastTIDInv_def, metis)
  next
    case (WCommit x51 x52 x53 x54 x55)
    then show ?case
      apply (auto simp add: tps_trans_defs cl_unchanged_defs PastTIDInv_def)
      by (metis (lifting))
  next
    case (WDone x6)
    then show ?case
      apply (auto simp add: tps_trans_defs cl_unchanged_defs PastTIDInv_def)
      subgoal for k n kv_map commit_t apply (cases "k \<in> dom kv_map")
        apply (metis (no_types, lifting) less_antisym)
        by (metis (lifting) WriteTxnIdleSvr_def domIff insertCI less_antisym reach_write_txn_idle_svr).
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?case
      apply (auto simp add: tps_trans_defs svr_unchanged_defs PastTIDInv_def)
      by (metis add_to_readerset_commit' add_to_readerset_no_ver_inv)
  next                            
    case (PrepW x81 x82 x83 x84)
    then show ?case
      apply (auto simp add: tps_trans_defs svr_unchanged_defs wtid_match_def PastTIDInv_def)
      by (metis fun_upd_other get_cl_wtxn.simps(2) get_sn_wtxn.simps(2) max.strict_order_iff)
  next
    case (CommitW x91 x92)
    then show ?case
      apply (auto simp add: tps_trans_defs svr_unchanged_defs PastTIDInv_def)
      by (metis fun_upd_other fun_upd_same)
  qed simp
qed

lemma other_sn_idle:  
  assumes "FutureTIDInv s cl" and "PastTIDInv s cl"
    and "get_cl_txn t = cl" and "get_sn_txn t \<noteq> txn_sn (cls s cl)"
  shows "\<And>k. \<exists>cts v rs. wtxn_state (svrs s k) (Tn t) \<in> {No_Ver, Commit cts v rs}"
  using assms
  apply (auto simp add: FutureTIDInv_def PastTIDInv_def)
  apply (cases "get_sn_txn t > txn_sn (cls s cl)")
  apply (metis get_cl_txn.elims get_sn_txn.simps)
  by (metis get_cl_txn.elims get_sn_txn.simps linorder_cases)

definition PrepInv where
  "PrepInv s \<longleftrightarrow> (\<forall>cl k kvm. \<exists>prep_t v. txn_state (cls s cl) = WtxnPrep kvm
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> wtxn_state (svrs s k) (Tn (get_txn_cl s cl)) \<in> {No_Ver, Prep prep_t v}) \<and>
    (k \<notin> dom kvm \<longrightarrow> wtxn_state (svrs s k) (Tn (get_txn_cl s cl)) = No_Ver))"

lemmas PrepInvI = PrepInv_def[THEN iffD2, rule_format]
lemmas PrepInvE[elim] = PrepInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_prep_inv [simp, dest]: "reach tps s \<Longrightarrow> PrepInv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: PrepInv_def tps_defs)
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
      by (smt (verit) add_to_readerset_wts_dom add_to_readerset_prep_inv wts_domIff)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs svr_unchanged_defs)
      by (smt (verit) fun_upd_other fun_upd_same get_cl_wtxn.simps(2) state_txn.inject(2))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs svr_unchanged_defs)
      by (smt (verit) fun_upd_apply get_cl_wtxn.simps(2) state_txn.distinct(11))
  qed simp
qed

definition CommitInv where
  "CommitInv s \<longleftrightarrow> (\<forall>cl k cts kvm. \<exists>prep_t v rs. txn_state (cls s cl) = WtxnCommit cts kvm
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) \<in> {Prep prep_t v, Commit cts v rs}) \<and>
    (k \<notin> dom kvm \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) = No_Ver))"

lemmas CommitInvI = CommitInv_def[THEN iffD2, rule_format]
lemmas CommitInvE[elim] = CommitInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_inv [simp, dest]: "reach tps s \<Longrightarrow> CommitInv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: CommitInv_def tps_defs wtid_match_def)
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
    then show ?case apply (simp add: CommitInv_def tps_trans_defs svr_unchanged_defs)
      by (smt add_to_readerset_commit add_to_readerset_no_ver_inv add_to_readerset_prep_inv
          get_val_ver.cases ver_state.inject(2))
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs svr_unchanged_defs)
      by (smt (verit) fun_upd_other get_cl_wtxn.simps(2) state_txn.distinct(11))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs svr_unchanged_defs)
      by (smt (verit) fun_upd_apply get_cl_wtxn.simps(2) state_txn.inject(3))
  qed simp
qed


definition FutureTidRdDS where
  "FutureTidRdDS s cl \<longleftrightarrow> (\<forall>n k t cts v rs.  n > txn_sn (cls s cl) \<and>
    wtxn_state (svrs s k) t = Commit cts v rs \<longrightarrow> Tn_cl n cl \<notin> rs)"

lemmas FutureTidRdDSI = FutureTidRdDS_def[THEN iffD2, rule_format]
lemmas FutureTidRdDSE[elim] = FutureTidRdDS_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidfuture_rd_ds [simp, dest]: "reach tps s \<Longrightarrow> FutureTidRdDS s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  apply (auto simp add: FutureTidRdDS_def tps_defs)
    by (metis empty_iff ver_state.distinct(3) ver_state.inject(2))
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
      by (metis fun_upd_apply ver_state.distinct(5))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: FutureTidRdDS_def tps_trans_defs svr_unchanged_defs)
      by (metis empty_iff fun_upd_other fun_upd_same ver_state.inject(2))
  qed simp
qed

definition FutureTidWrDS where
  "FutureTidWrDS s cl \<longleftrightarrow> (\<forall>n k. n > txn_sn (cls s cl) \<longrightarrow> Tn (Tn_cl n cl) \<notin> wts_dom (wtxn_state (svrs s k)))"

lemmas FutureTidWrDSI = FutureTidWrDS_def[THEN iffD2, rule_format]
lemmas FutureTidWrDSE[elim] = FutureTidWrDS_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidfuture_wr_ds [simp, dest]: "reach tps s \<Longrightarrow> FutureTidWrDS s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FutureTidWrDS_def tps_defs)
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
      by (metis add_to_readerset_wts_dom)
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case apply (simp add: FutureTidWrDS_def tps_trans_defs svr_unchanged_defs wtid_match_def)
      by (metis get_cl_wtxn.simps(2) get_sn_wtxn.simps(2) insertE nat_neq_iff wts_domI1 wts_domIff wts_dom_fun_upd)
  next
    case (CommitW x91 x92)
    then show ?case apply (simp add: FutureTidWrDS_def tps_trans_defs svr_unchanged_defs)
      by (metis insert_prep_wts_dom ver_state.distinct(3) wts_dom_fun_upd)
  qed simp
qed

(*
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
    apply (metis get_cl_txn.simps get_sn_txn.simps order_class.order_eq_iff wtid_match_def
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
          wtid_match_def txid.inject version.select_convs(2))
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
    then show ?case apply (simp add: SvrVerWrTIDDistinct_def tps_trans_defs svr_unchanged_defs wtid_match_def)
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
      by (smt get_cl_txn.simps get_sn_txn.simps nat_neq_iff not_in_append wtid_match_def txid.inject
          version.select_convs(2))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: PastTIDNotPending_def tps_trans_defs svr_unchanged_defs) sorry
  qed simp
qed*)


abbreviation not_committing_ev where
  "not_committing_ev e \<equiv> \<forall>cl kvt_map kv_map cts sn u. e \<noteq> RDone cl kvt_map sn u \<and> e \<noteq> WCommit cl kv_map cts sn u"


definition FreshReadTxnInv where
  "FreshReadTxnInv s cl k \<longleftrightarrow> (\<forall>t cts v rs. txn_state (cls s cl) = Idle \<and>
    wtxn_state (svrs s k) t = Commit cts v rs \<longrightarrow> get_txn_cl s cl \<notin> rs)"

lemmas FreshReadTxnInvI = FreshReadTxnInv_def[THEN iffD2, rule_format]
lemmas FreshReadTxnInvE[elim] = FreshReadTxnInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_freshrdtxn [simp, dest]: "reach tps s \<Longrightarrow> FreshReadTxnInv s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  apply (auto simp add: FreshReadTxnInv_def tps_defs)
    by (metis ex_in_conv get_rs_ver.simps(3) ver_state.distinct(3))
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
      by (metis (lifting) FutureTidRdDS_def lessI reach_tidfuture_rd_ds)
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
      by (metis (lifting) FutureTidRdDS_def lessI reach_tidfuture_rd_ds)
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?case apply (simp add: FreshReadTxnInv_def tps_trans_defs svr_unchanged_defs wtid_match_def)
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
    Tn (get_txn_cl s cl) \<notin> wts_dom (wtxn_state (svrs s k)))"

lemmas FreshWriteTxnInvI = FreshWriteTxnInv_def[THEN iffD2, rule_format]
lemmas FreshWriteTxnInvE[elim] = FreshWriteTxnInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_freshwrtxn [simp, dest]: "reach tps s \<Longrightarrow> FreshWriteTxnInv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FreshWriteTxnInv_def tps_defs)
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
      by (metis add_to_readerset_wts_dom)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: tps_trans_defs FreshWriteTxnInv_def svr_unchanged_defs)
      by (metis get_cl_wtxn.simps(2) insertE state_txn.distinct(3) state_txn.distinct(7)
          ver_state.distinct(1) wts_dom_fun_upd)
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: tps_trans_defs FreshWriteTxnInv_def svr_unchanged_defs)
      by (metis insert_prep_wts_dom ver_state.distinct(3) wts_dom_fun_upd)
  qed simp
qed

(*
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
      kvs_readers_sqns_other_cl_inv cl_unchanged_defs)*)

lemma bla:
  assumes "x \<notin> a"
  shows "a - insert x b = a - b"
  using assms
  by simp

abbreviation invariant_list_kvs where
  "invariant_list_kvs s \<equiv> \<forall>cl k. FutureTIDInv s cl \<and> PastTIDInv s cl \<and> KVSNonEmp s \<and>
   \<comment> \<open> KVSNotAllPending s k \<and>\<close> FreshReadTxnInv s cl k"

lemma kvs_of_s_inv:
  assumes "state_trans s e s'"
    and "invariant_list_kvs s"
    and "not_committing_ev e"
  shows "kvs_of_s s' = kvs_of_s s"
  sorry

definition SqnInv_nc where
  "SqnInv_nc s cl \<longleftrightarrow> (\<forall>cts kvm.
    (txn_state (cls s cl) \<noteq> WtxnCommit cts kvm \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m < txn_sn (cls s cl))))"

lemmas SqnInv_ncI = SqnInv_nc_def[THEN iffD2, rule_format]
lemmas SqnInv_ncE[elim] = SqnInv_nc_def[THEN iffD1, elim_format, rule_format]

lemma reach_sql_inv_nc [simp, intro]:
  assumes "reach tps s"
  shows "SqnInv_nc s cl"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    apply (auto simp add: SqnInv_nc_def tps_defs kvs_of_s_def get_sqns_old_def kvs_txids_def)
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
       apply (metis (lifting) state_txn.distinct(9) cl_unchanged_defs) sorry
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
  "SqnInv_c s cl \<longleftrightarrow> (\<forall>cts kvm.
    (txn_state (cls s cl) = WtxnCommit cts kvm \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m \<le> txn_sn (cls s cl))))"

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


subsection \<open>CanCommit\<close>

subsubsection \<open>visTx' and closed' lemmas\<close>

lemma visTx_visTx': "visTx (kvs_of_s s) (view_txid_vid s u) = visTx' u"
  apply (simp add: view_txid_vid_def visTx_def visTx'_def) sorry

lemma closed_closed': "closed (kvs_of_s s) (view_txid_vid s u) r = closed' (kvs_of_s s) u r"
  by (simp add: closed_def closed'_def visTx_visTx')

lemma visTx'_subset_writers: "visTx' (get_view s cl) \<subseteq> kvs_writers (kvs_of_s s)" sorry

lemma get_view_closed:
  "ET_CC.canCommit (kvs_of_s s) (view_txid_vid s (get_view s cl)) F"
  apply (auto simp add: ET_CC.canCommit_def closed_closed' closed'_def)
   apply (metis DiffD2 read_only_Txs_def subsetD visTx'_subset_writers)
  subgoal for t' t apply (simp add: R_CC_def) sorry.
  

subsubsection \<open>Invariants for canCommit\<close>

definition RO_WO_Inv where
  "RO_WO_Inv s \<longleftrightarrow> (\<Union>k. wts_dom (wtxn_state (svrs s k))) \<inter> Tn ` (\<Union>k. \<Union>(wts_rsran (wtxn_state (svrs s k)))) = {}"

lemmas RO_WO_InvI = RO_WO_Inv_def[THEN iffD2, rule_format]
lemmas RO_WO_InvE[elim] = RO_WO_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_ro_wo_inv [simp, dest]: "reach tps s \<Longrightarrow> RO_WO_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: RO_WO_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: RO_WO_Inv_def tps_trans_defs svr_unchanged_defs) sorry
     (*using add_to_readerset_v_writer_img[of ] apply (simp add: txid_defs) sorry \<comment> \<open>Continue here!\<close>*)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case sorry
  next
    case (CommitW x1 x2)
    then show ?case sorry
  qed (auto simp add: RO_WO_Inv_def tps_trans_defs cl_unchanged_defs)
qed

lemma "kvs_writers (kvs_of_s s) \<subseteq> (\<Union>k. wts_dom (wtxn_state (svrs s k)))"
  oops

lemma "kvs_readers (kvs_of_s s) \<subseteq> (\<Union>k. \<Union>(wts_rsran (wtxn_state (svrs s k))))"
  oops

lemma "kvs_txids (kvs_of_s gs) - kvs_writers (kvs_of_s gs) = Tn ` kvs_readers (kvs_of_s gs)"
  apply (simp add: kvs_of_s_def) sorry \<comment> \<open>turn into invariant\<close>

definition canCommit_rd_Inv where
  "canCommit_rd_Inv s cl \<longleftrightarrow> (\<forall>kvt_map. txn_state (cls s cl) = RtxnInProg (dom kvt_map) kvt_map  \<longrightarrow>
    ET_CC.canCommit (kvs_of_s s) (view_txid_vid s (get_view s cl))
      (\<lambda>k. case_op_type (map_option kvs (kvt_map k)) None))"

lemmas canCommit_rd_InvI = canCommit_rd_Inv_def[THEN iffD2, rule_format]
lemmas canCommit_rd_InvE[elim] = canCommit_rd_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_canCommit_rd_inv [simp, dest]: "reach tps s \<Longrightarrow> canCommit_rd_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: canCommit_rd_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case
      apply (simp add: canCommit_rd_Inv_def tps_trans_defs cl_unchanged_defs)
      by (cases "cl = x1"; simp add: get_view_def view_txid_vid_def)
  next
    case (Read x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: canCommit_rd_Inv_def tps_trans_defs cl_unchanged_defs dest!: eq_for_all_cl)
      apply (cases "cl = x1"; simp add: get_view_def view_txid_vid_def) sorry
  next
    case (RDone x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: canCommit_rd_Inv_def tps_trans_defs cl_unchanged_defs dest!: eq_for_all_cl)
      apply (cases "cl = x1"; simp add: ET_CC.canCommit_def closed_def R_CC_def R_onK_def) sorry
  next
    case (WInvoke x1 x2)
    then show ?case
      apply (simp add: canCommit_rd_Inv_def tps_trans_defs cl_unchanged_defs)
      by (cases "cl = x1"; simp add: get_view_def view_txid_vid_def)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: canCommit_rd_Inv_def tps_trans_defs cl_unchanged_defs dest!: eq_for_all_cl)
      apply (cases "cl = x1"; simp) sorry
  next
    case (WDone x)
    then show ?case
      apply (simp add: canCommit_rd_Inv_def tps_trans_defs cl_unchanged_defs)
      by (cases "cl = x"; simp add: get_view_def view_txid_vid_def)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case
      by (auto simp add: canCommit_rd_Inv_def tps_trans_defs svr_unchanged_defs view_txid_vid_def
          get_view_add_to_readerset_inv)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case
      by (auto simp add: canCommit_rd_Inv_def tps_trans_defs svr_unchanged_defs view_txid_vid_def
        get_view_wprep_inv)
  next
    case (CommitW x1 x2)
    then show ?case
      apply (simp add: canCommit_rd_Inv_def tps_trans_defs svr_unchanged_defs)
      apply (cases "get_cl_wtxn x2 = cl"; auto) sorry (* Continue here!*)
  qed simp
qed


subsection \<open>View invariants\<close>

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
  case (RInvoke x1 x2)
  then show ?case sorry
next
  case (Read x1 x2 x3 x4)
  then show ?case sorry
next
  case (RDone x1 x2 x3 x4)
  then show ?case sorry
next
  case (WInvoke x1 x2)
  then show ?case sorry
next
  case (WCommit x1 x2 x3 x4 x5)
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
qed simp

lemma read_commit_views_of_s_other_cl_inv:
  assumes "read_done cl kv_map sn u s s'"
    and "cl' \<noteq> cl"
  shows "views_of_s s' cl' = views_of_s s cl'"
  using assms
  apply (auto simp add: read_done_def cl_unchanged_defs views_of_s_def view_txid_vid_def)
  apply (rule ext) subgoal for k apply(cases "k \<in> dom kv_map"; simp add: image_def)
    apply (auto intro: Collect_eqI)
    subgoal for y x apply (rule bexI[where x=x]) sorry
    subgoal for y x apply (rule bexI[where x=x]) sorry
    done
  done

lemma write_commit_views_of_s_other_cl_inv:
  assumes "write_commit cl kv_map cts sn u s s'"
    and "cl' \<noteq> cl"
  shows "views_of_s s' cl' = views_of_s s cl'"
  using assms
  apply (auto simp add: write_commit_def cl_unchanged_defs views_of_s_def view_txid_vid_def)
  apply (rule ext) subgoal for k apply(cases "k \<in> dom kv_map"; simp add: image_def)
    apply (auto intro: Collect_eqI)
    subgoal for y x apply (rule bexI[where x=x]) sorry
    subgoal for y x apply (rule bexI[where x=x]) sorry
    done
  done

lemma inv_T0: "inv ((!) [T0]) T0 = 0" apply (rule inv_f_eq) sorry

abbreviation invariant_list where
  "invariant_list s \<equiv> (\<forall>cl. invariant_list_kvs s \<and> SqnInv_c s cl \<and> SqnInv_nc s cl)" \<comment> \<open>\<and> canCommit_rd_Inv s cl)\<close>


section \<open>Refinement Proof\<close>

lemma tps_refines_et_es: "tps \<sqsubseteq>\<^sub>med ET_CC.ET_ES"
proof (intro simulate_ES_fun_with_invariant[where I="\<lambda>s. invariant_list s"])
  fix gs0 :: "'v state"
  assume p: "init tps gs0"
  then show "init ET_CC.ET_ES (sim gs0)"
    by (auto simp add: ET_CC.ET_ES_defs tps_defs sim_defs kvs_init_def v_list_init_def version_init_def
        view_txid_init_def view_txid_vid_def inv_T0)
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
      subgoal apply (auto simp add: ET_CC.ET_cl_txn_def t_is_fresh KVSSNonEmp_def)
        subgoal apply (simp add: view_wellformed_def views_of_s_def) sorry
        subgoal sorry
        subgoal (*canCommit_rd_Inv_def*) sorry \<comment> \<open>show get_view always returns a closed u? for any t the SO, WR tstmp is less\<close>
        subgoal apply (auto simp add: vShift_MR_RYW_def vShift_MR_def vShift_RYW_def) sorry
        sorry
        subgoal apply (rule ext)
          subgoal for cl' apply (cases "cl' = cl"; simp)
          using read_commit_views_of_s_other_cl_inv [where s=gs and s'=gs' and cl=cl and cl'=cl']
          by (metis RDone.prems(1) state_trans.simps(3) tps_trans).
      subgoal apply (auto simp add: fp_property_def view_snapshot_def)
        subgoal for k y apply (simp add: last_version_def kvs_of_s_def)
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
  qed (auto simp add: sim_def)
qed simp

end
