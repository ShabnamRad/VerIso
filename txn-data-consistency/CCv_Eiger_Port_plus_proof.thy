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
  have "wts_vran wts = (\<lambda>t. get_val (wts t)) ` wts_dom wts"
    unfolding wts_vran_def
    by (smt (verit) Collect_cong Setcompr_eq_image ver_state.sel wts_domD wts_domI1 wts_domI2)
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

lemma "get_ts (wts (at wts rts)) = at_cts wts rts" apply (simp add: at_def committed_at_def) sorry


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

lemma ran_map_upd_None_finite:
  "finite (ran m) \<Longrightarrow> finite (ran (m (a := None)))"
  apply (simp add: ran_def)
  by (smt (verit) Collect_mono_iff rev_finite_subset)

lemma pending_wtxns_ts_empty:
  "pending_wtxns_ts (wtxn_state (svrs s k)) = {} \<longleftrightarrow>
    (\<forall>t. \<exists>cts v rs. wtxn_state (svrs s k) t \<in> {No_Ver, Commit cts v rs})"
  apply (auto simp add: pending_wtxns_ts_def)
  apply (metis get_rs_ver.elims)
  by (metis ver_state.distinct(1) ver_state.distinct(5))

lemma pending_wtxns_ts_non_empty:
  assumes "wtxn_state (svrs s k) t \<noteq> No_Ver"
    and "\<forall>cts v rs. wtxn_state (svrs s k) t \<noteq> Commit cts v rs"
  shows "pending_wtxns_ts (wtxn_state (svrs s k)) \<noteq> {}"
  using assms apply (auto simp add: pending_wtxns_ts_def)
  by (meson get_rs_ver.elims)

lemma finite_pending_wtxns_rtxn:
  assumes "finite (pending_wtxns_ts (wtxn_state (svrs s k)))"
  shows "finite (pending_wtxns_ts (add_to_readerset (wtxn_state (svrs s k)) t' t))"
  using assms
  by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def add_to_readerset_prep_inv)

lemma finite_pending_wtxns_adding:
  assumes "finite (pending_wtxns_ts (wtxn_state (svrs s k)))"
  shows "finite (pending_wtxns_ts ((wtxn_state (svrs s k)) (t := Prep prep_t v)))"
  using assms
  apply (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def)
  by (metis dual_order.trans linorder_le_cases)

lemma finite_pending_wtxns_removing: 
  assumes "finite (pending_wtxns_ts (wtxn_state (svrs s k)))"
  shows "finite (pending_wtxns_ts ((wtxn_state (svrs s k)) (t := Commit cts v rs)))"
  using assms
  by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def)

lemma pending_wtxns_adding_ub:
  assumes "\<forall>ts \<in> pending_wtxns_ts (wtxn_state (svrs s k)). ts \<le> clk"
  shows "\<forall>ts \<in> pending_wtxns_ts ((wtxn_state (svrs s k)) (t := Prep clk v)). ts \<le> clk"
  using assms by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def)

lemma pending_wtxns_removing_ub:
  assumes "\<forall>ts \<in> pending_wtxns_ts (wtxn_state (svrs s k)). ts \<le> clk"
  shows "\<forall>ts \<in> pending_wtxns_ts ((wtxn_state (svrs s k)) (t := Commit cts v rs)). ts \<le> clk"
  using assms by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def)

lemma pending_wtxns_rtxn:
  "pending_wtxns_ts (add_to_readerset (wtxn_state (svrs s k)) t' t) =
   pending_wtxns_ts (wtxn_state (svrs s k))"
  by (auto simp add: pending_wtxns_ts_def add_to_readerset_prep_inv)

lemma pending_wtxns_adding:
  assumes "\<forall>clk v. wtxn_state (svrs s k) t \<noteq> Prep clk v"
  shows "pending_wtxns_ts ((wtxn_state (svrs s k)) (t := Prep clk v)) =
         insert clk (pending_wtxns_ts (wtxn_state (svrs s k)))"
  using assms apply (auto simp add: pending_wtxns_ts_def)
  by metis

lemma pending_wtxns_removing:
  assumes "wtxn_state (svrs s k) t = Prep clk v"
  shows "pending_wtxns_ts ((wtxn_state (svrs s k)) (t := Commit cts v rs)) =
          pending_wtxns_ts (wtxn_state (svrs s k)) \<or>
         pending_wtxns_ts ((wtxn_state (svrs s k)) (t := Commit cts v rs)) =
          Set.remove clk (pending_wtxns_ts (wtxn_state (svrs s k)))"
  using assms apply (auto simp add: pending_wtxns_ts_def)
  by (metis ver_state.inject(1))+

lemma other_prep_t_inv:
  assumes "wtxn_state (svrs s k) t = Prep prep_t v"
    and "t \<noteq> t'"
  shows "prep_t \<in> pending_wtxns_ts ((wtxn_state (svrs s k))(t' := b))"
  using assms
  by (auto simp add: pending_wtxns_ts_def)


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

lemma view_of_prefix:
  assumes "\<And>k. prefix (corder k) (corder' k)"
    and "\<And>k. distinct (corder' k)"
    and "\<And>k. u k \<subseteq> set (corder k)"
  shows "view_of corder u = view_of corder' u"
  unfolding view_of_def
proof (rule ext, rule Collect_eqI, rule iffI)
  fix k pos
  assume *: "\<exists>tid\<in>u k. tid \<in> set (corder k) \<and> pos = (THE i. i < length (corder k) \<and> corder k ! i = tid)"
  show "\<exists>tid\<in>u k. tid \<in> set (corder' k) \<and> pos = (THE i. i < length (corder' k) \<and> corder' k ! i = tid)"
  proof -
    from assms(1) obtain zs where p: "corder k @ zs = corder' k" using prefixE by metis
    from * obtain tid where **: "tid \<in> u k" "tid \<in> set (corder k)"
      "pos = (THE i. i < length (corder k) \<and> corder k ! i = tid)" by blast
    from \<open>tid \<in> set (corder k)\<close> obtain i where the_i:"i < length (corder k) \<and> corder k ! i = tid"
      by (meson in_set_conv_nth)
    with p ** have the1: "(THE i. i < length (corder k) \<and> corder k ! i = tid) = i"
      using assms(2) distinct_Ex1[of "corder k" tid]
      by (metis (mono_tags, lifting) distinct_append[of "corder k" zs] the_equality)
    from ** have tid_in_corder': "tid \<in> set (corder' k)" using assms(1) set_mono_prefix by blast
    then obtain i' where the_i':"i' < length (corder' k) \<and> corder' k ! i' = tid"
      by (meson in_set_conv_nth)
    with p tid_in_corder' have the2: "(THE i. i < length (corder' k) \<and> corder' k ! i = tid) = i'"
      using assms(2) distinct_Ex1[of "corder' k" tid] by (simp add: the1_equality)
    from p the_i the_i' have "i = i'" using assms(1,2)[of k]
      by (metis distinct_conv_nth nth_append order_less_le_trans prefix_length_le)
    with ** have "pos = (THE i. i < length (corder' k) \<and> corder' k ! i = tid)"
      using the1 the2 by presburger
    then show ?thesis using ** tid_in_corder' by auto
  qed
next
  fix k pos
  assume *: "\<exists>tid\<in>u k. tid \<in> set (corder' k) \<and> pos = (THE i. i < length (corder' k) \<and> corder' k ! i = tid)"
  show "\<exists>tid\<in>u k. tid \<in> set (corder k) \<and> pos = (THE i. i < length (corder k) \<and> corder k ! i = tid)"
  proof -
    from assms(1) obtain zs where p: "corder k @ zs = corder' k" using prefixE by metis
    from * obtain tid where **: "tid \<in> u k" "tid \<in> set (corder' k)"
      "pos = (THE i. i < length (corder' k) \<and> corder' k ! i = tid)" by blast
    from \<open>tid \<in> set (corder' k)\<close> obtain i' where the_i':"i' < length (corder' k) \<and> corder' k ! i' = tid"
      by (meson in_set_conv_nth)
    with p ** have the2: "(THE i. i < length (corder' k) \<and> corder' k ! i = tid) = i'"
      using assms(2) distinct_Ex1[of "corder' k" tid]
      by (metis (mono_tags, lifting) the_equality)
    from ** have tid_in_corder: "tid \<in> set (corder k)" using assms(3) by blast
    then obtain i where the_i:"i < length (corder k) \<and> corder k ! i = tid"
      by (meson in_set_conv_nth)
    with p tid_in_corder have the1: "(THE i. i < length (corder k) \<and> corder k ! i = tid) = i" using assms(2)
      distinct_Ex1[of "corder k" tid] distinct_append[of "corder k" zs]
      by (metis (mono_tags, lifting) the_equality)
    from p the_i the_i' have "i = i'" using assms(1,2)[of k]
      by (metis distinct_conv_nth nth_append order_less_le_trans prefix_length_le)
    with ** have "pos = (THE i. i < length (corder k) \<and> corder k ! i = tid)"
      using the1 the2 by presburger
    then show ?thesis using ** tid_in_corder by auto
  qed
qed


subsection \<open>Simulation realtion lemmas\<close>

lemma kvs_of_s_init:
  "kvs_of_s (state_init) = (\<lambda>k. [\<lparr>v_value = undefined, v_writer = T0, v_readerset = {}\<rparr>])"
  by (simp add: kvs_of_s_def tps_defs)


subsection  \<open>Extra: general lemmas\<close>

lemma find_Some_in_set:
  "find P vl = Some ver \<Longrightarrow> ver \<in> set vl \<and> P ver"
  apply (simp add: find_Some_iff)
  by (meson nth_mem)

lemma find_append:
  "find P (vl1 @ vl2) = (case find P vl1 of None \<Rightarrow> find P vl2 | Some ver \<Rightarrow> Some ver)"
  by (induction vl1; simp)

lemma Min_insert_larger:
  assumes "a \<noteq> {}" and "b \<noteq> {}"
    and "finite a"
    and "b = insert x a"
    and "\<forall>y \<in> a. y \<le> x"
  shows "Min a \<le> Min b"
  using assms
  by simp

lemma Min_remove:
  assumes "b \<noteq> {}"
    and "finite a"
    and "b = Set.remove x a"
  shows "Min a \<le> Min b"
  using assms
  by (simp add: remove_def)

lemma fold_pending_wtxns_fun_upd:
  "pending_wtxns_ts (\<lambda>a. if a = t then b else m a) =
   pending_wtxns_ts (m (t := b))"
  by (simp add: fun_upd_def)

lemma not_less_eq: "\<not>((a :: nat) < b) \<Longrightarrow> a \<noteq> b \<Longrightarrow> a > b" by simp


section \<open>Invariants and lemmas\<close>

subsection \<open>monotonic lemmas and inequality of timestamps invariants\<close>

lemma clock_monotonic:
  "state_trans s e s' \<Longrightarrow> clock (svrs s' svr) \<ge> clock (svrs s svr)"
  by (induction e) (auto simp add: tps_trans_defs)


lemma cl_clock_monotonic:
  "state_trans s e s' \<Longrightarrow> cl_clock (cls s' cl) \<ge> cl_clock (cls s cl)"
  by (induction e) (auto simp add: tps_trans_defs)


definition Pend_Wt_UB where
  "Pend_Wt_UB s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns_ts (wtxn_state (svrs s svr)). ts \<le> clock (svrs s svr))"

lemmas Pend_Wt_UBI = Pend_Wt_UB_def[THEN iffD2, rule_format]
lemmas Pend_Wt_UBE[elim] = Pend_Wt_UB_def[THEN iffD1, elim_format, rule_format]

lemma reach_pend_wt_ub [simp, dest]: "reach tps s \<Longrightarrow> Pend_Wt_UB s svr"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Pend_Wt_UB_def tps_defs pending_wtxns_ts_def split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: Pend_Wt_UB_def tps_trans_defs pending_wtxns_ts_def)
      by (meson add_to_readerset_prep_inv le_SucI le_trans max.cobounded1)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: Pend_Wt_UB_def tps_trans_defs pending_wtxns_ts_def)
      by (meson le_Suc_eq max.coboundedI1)
  next
    case (CommitW x1 x2)
    then show ?case
      apply (auto simp add: Pend_Wt_UB_def tps_trans_defs pending_wtxns_ts_def split: if_split_asm)
      by (meson le_Suc_eq max.coboundedI1 notin_set_remove1)
  qed (auto simp add: Pend_Wt_UB_def tps_trans_defs)
qed


definition Finite_Pend_Inv where
  "Finite_Pend_Inv s svr \<longleftrightarrow> finite (pending_wtxns_ts (wtxn_state (svrs s svr)))"

lemmas Finite_Pend_InvI = Finite_Pend_Inv_def[THEN iffD2, rule_format]
lemmas Finite_Pend_InvE[elim] = Finite_Pend_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_finitepending [simp, dest]: "reach tps s \<Longrightarrow> Finite_Pend_Inv s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Finite_Pend_Inv_def tps_defs pending_wtxns_ts_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x71 x72 x73 x74 x75)
    then show ?case
      by (auto simp add: Finite_Pend_Inv_def tps_trans_defs finite_pending_wtxns_rtxn)
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case
      by (auto simp add: Finite_Pend_Inv_def tps_trans_defs finite_pending_wtxns_adding)
  next
    case (CommitW x91 x92)
    then show ?case
      by (auto simp add: Finite_Pend_Inv_def tps_trans_defs finite_pending_wtxns_removing)
  qed (auto simp add: Finite_Pend_Inv_def tps_trans_defs)
qed


definition Clk_Lst_Inv where
  "Clk_Lst_Inv s \<longleftrightarrow> (\<forall>svr. lst (svrs s svr) \<le> clock (svrs s svr))"

lemmas Clk_Lst_InvI = Clk_Lst_Inv_def[THEN iffD2, rule_format]
lemmas Clk_Lst_InvE[elim] = Clk_Lst_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_clock_lst_inv [simp, dest]: "reach tps s \<Longrightarrow> Clk_Lst_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Clk_Lst_Inv_def tps_defs wtid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x71 x72 x73 x74 x75)
    then show ?case apply (auto simp add: Clk_Lst_Inv_def tps_trans_defs)
      by (metis le_Suc_eq max.coboundedI1)
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case apply (auto simp add: Clk_Lst_Inv_def tps_trans_defs)
      using le_SucI le_max_iff_disj by blast
  next
    case (CommitW x91 x92)
    then show ?case
      apply (auto simp add: Clk_Lst_Inv_def tps_trans_defs split: if_split_asm, linarith)
      by (metis (no_types, opaque_lifting) Finite_Pend_Inv_def Min_le_iff Pend_Wt_UB_def emptyE
          finite_pending_wtxns_removing le_SucI max.coboundedI2 max.commute pending_wtxns_removing_ub
          reach_finitepending reach_pend_wt_ub)
  qed (auto simp add: Clk_Lst_Inv_def tps_trans_defs)
qed

definition Pend_Wt_LB where
  "Pend_Wt_LB s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns_ts (wtxn_state (svrs s svr)). lst (svrs s svr) \<le> ts)"

lemmas Pend_Wt_LBI = Pend_Wt_LB_def[THEN iffD2, rule_format]
lemmas Pend_Wt_LBE[elim] = Pend_Wt_LB_def[THEN iffD1, elim_format, rule_format]

lemma reach_pend_wt_lb [simp, dest]: "reach tps s \<Longrightarrow> Pend_Wt_LB s svr"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Pend_Wt_LB_def tps_defs )
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case by (auto simp add: Pend_Wt_LB_def tps_trans_defs pending_wtxns_rtxn)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case by (auto simp add: Pend_Wt_LB_def tps_trans_defs pending_wtxns_adding)
  next
    case (CommitW x1 x2)
    then show ?case apply (auto simp add: Pend_Wt_LB_def tps_trans_defs split: if_split_asm)
      by (meson Finite_Pend_Inv_def Min_le finite_pending_wtxns_removing reach_finitepending)
  qed(auto simp add: Pend_Wt_LB_def tps_trans_defs)
qed

lemma min_pending_wtxns_monotonic:
  assumes "state_trans s e s'"
    and "pending_wtxns_ts (wtxn_state (svrs s k)) \<noteq> {}"
    and "pending_wtxns_ts (wtxn_state (svrs s' k)) \<noteq> {}"
    and "Pend_Wt_UB s k" and "Finite_Pend_Inv s k"
  shows "Min (pending_wtxns_ts (wtxn_state (svrs s k))) \<le>
         Min (pending_wtxns_ts (wtxn_state (svrs s' k)))"
  using assms
proof (induction e)
  case (RegR x1 x2 x3 x4 x5)
  then show ?case
  apply (auto simp add: tps_trans_defs pending_wtxns_ts_def)
    by (smt (z3) Collect_cong add_to_readerset_prep_inv nat_le_linear)
next
  case (PrepW x1 x2 x3 x4)
  then show ?case apply (auto simp add: prepare_write_def Pend_Wt_UB_def Finite_Pend_Inv_def)
    using Min_insert_larger[of "pending_wtxns_ts (wtxn_state (svrs s x1))"
        "pending_wtxns_ts (wtxn_state (svrs s' x1))" "clock (svrs s x1)"]
      pending_wtxns_adding [of s x1]
    by (cases "k = x1"; auto simp add: pending_wtxns_ts_def)
next
  case (CommitW x1 x2)
  then show ?case
    apply (auto simp add: commit_write_def Finite_Pend_Inv_def fold_pending_wtxns_fun_upd)
    by (metis Min.coboundedI Min_in Min_remove empty_iff pending_wtxns_removing)
  qed (auto simp add: tps_trans_defs pending_wtxns_ts_def)


lemma lst_monotonic:
  assumes "state_trans s e s'"
    and "Clk_Lst_Inv s" and "Finite_Pend_Inv s svr"
    and "Pend_Wt_LB s svr"
  shows "lst (svrs s' svr) \<ge> lst (svrs s svr)"
  using assms
  proof (induction e)
    case (CommitW k t)
    then show ?case
      apply (auto simp add: commit_write_def Clk_Lst_Inv_def Finite_Pend_Inv_def Pend_Wt_LB_def 
                  split: if_split_asm)
      by (metis Min_in empty_iff finite_pending_wtxns_removing member_remove pending_wtxns_removing)
  qed (auto simp add: tps_trans_defs)

lemma gst_monotonic:
  assumes "state_trans s e s'"
  shows "gst (cls s' cl) \<ge> gst (cls s cl)"
  using assms
  by (induction e) (auto simp add: tps_trans_defs)

definition Pend_Wt_Inv where
  "Pend_Wt_Inv s k \<longleftrightarrow> (\<forall>prep_t. prep_t \<in> pending_wtxns_ts (wtxn_state (svrs s k))
    \<longleftrightarrow> (\<exists>t v. wtxn_state (svrs s k) t = Prep prep_t v))"
                                                           
lemmas Pend_Wt_InvI = Pend_Wt_Inv_def[THEN iffD2, rule_format]
lemmas Pend_Wt_InvE[elim] = Pend_Wt_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_pend_wt_inv [simp, dest]: "reach tps s \<Longrightarrow> Pend_Wt_Inv s cl"
  by (auto simp add: Pend_Wt_Inv_def tps_def pending_wtxns_ts_def)

definition Lst_Lt_Pts where
  "Lst_Lt_Pts s k \<longleftrightarrow> (\<forall>t prep_t v. wtxn_state (svrs s k) t = Prep prep_t v \<longrightarrow> lst (svrs s k) \<le> prep_t)"
                                                           
lemmas Lst_Lt_PtsI = Lst_Lt_Pts_def[THEN iffD2, rule_format]
lemmas Lst_Lt_PtsE[elim] = Lst_Lt_Pts_def[THEN iffD1, elim_format, rule_format]

lemma reach_lst_lt_pts [simp, dest]: "reach tps s \<Longrightarrow> Lst_Lt_Pts s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Lst_Lt_Pts_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
  case (RegR x1 x2 x3 x4 x5)
  then show ?case apply (auto simp add: Lst_Lt_Pts_def tps_trans_defs)
    by (meson add_to_readerset_prep_inv)
  next
    case (CommitW x1 x2)
    then show ?case apply (auto simp add: Lst_Lt_Pts_def tps_trans_defs)
      apply (metis emptyE other_prep_t_inv ver_state.distinct(5))
      by (metis Finite_Pend_Inv_def Min.coboundedI finite_pending_wtxns_removing other_prep_t_inv
          reach_finitepending ver_state.distinct(5))
  qed(auto simp add: Lst_Lt_Pts_def tps_trans_defs)
qed


definition Gst_Lt_Pts where
  "Gst_Lt_Pts s cl \<longleftrightarrow> (\<forall>k prep_t v. 
      wtxn_state (svrs s k) (get_wtxn_cl s cl) = Prep prep_t v \<longrightarrow> gst (cls s cl) < prep_t)"
                                                           
lemmas Gst_Lt_PtsI = Gst_Lt_Pts_def[THEN iffD2, rule_format]
lemmas Gst_Lt_PtsE[elim] = Gst_Lt_Pts_def[THEN iffD1, elim_format, rule_format]

lemma reach_Gst_Lt_Pts [simp, dest]: "reach tps s \<Longrightarrow> Gst_Lt_Pts s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Gst_Lt_Pts_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case sorry
qed


definition Gst_lt_Cts where
  "Gst_lt_Cts s cl \<longleftrightarrow> (\<forall>cts kv_map. txn_state (cls s cl) = WtxnCommit cts kv_map \<longrightarrow> gst (cls s cl) < cts)"
                                                           
lemmas Gst_lt_CtsI = Gst_lt_Cts_def[THEN iffD2, rule_format]
lemmas Gst_lt_CtsE[elim] = Gst_lt_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_gst_lt_cts [simp, dest]: "reach tps s \<Longrightarrow> Gst_lt_Cts s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Gst_lt_Cts_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Gst_lt_Cts_def tps_trans_defs)
      apply (cases "cl = x1"; simp) sorry
  qed (auto simp add: Gst_lt_Cts_def tps_trans_defs)
qed


subsection \<open>Invariants about kvs, global ts and init version v0\<close>

definition Kvs_Not_Emp where
  "Kvs_Not_Emp s \<longleftrightarrow> (\<forall>k. wtxn_state (svrs s k) \<noteq> wts_emp)"

lemmas Kvs_Not_EmpI = Kvs_Not_Emp_def[THEN iffD2, rule_format]
lemmas Kvs_Not_EmpE[elim] = Kvs_Not_Emp_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_not_emp [simp, dest]: "reach tps s \<Longrightarrow> Kvs_Not_Emp s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    apply (auto simp add: Kvs_Not_Emp_def tps_defs)
    by (metis fun_upd_apply ver_state.distinct(3))
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: Kvs_Not_Emp_def tps_trans_defs)
      by (metis add_to_readerset_wts_dom wts_domIff)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: Kvs_Not_Emp_def tps_trans_defs)
      by (metis fun_upd_same ver_state.distinct(1))
  next
    case (CommitW x1 x2)
    then show ?case
      apply (auto simp add: Kvs_Not_Emp_def tps_trans_defs)
      by (metis fun_upd_same ver_state.distinct(3))
  qed (auto simp add: Kvs_Not_Emp_def tps_trans_defs)
qed


definition Commit_Order_Not_Emp where
  "Commit_Order_Not_Emp s k \<longleftrightarrow> commit_order s k \<noteq> []"

lemmas Commit_Order_Not_EmpI = Commit_Order_Not_Emp_def[THEN iffD2, rule_format]
lemmas Commit_Order_Not_EmpE[elim] = Commit_Order_Not_Emp_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_not_emp [simp, dest]: "reach tps s \<Longrightarrow> Commit_Order_Not_Emp s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Commit_Order_Not_Emp_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Commit_Order_Not_Emp_def tps_trans_defs)
qed


definition KvsOfS_Not_Emp where
  "KvsOfS_Not_Emp s \<longleftrightarrow> (\<forall>k. kvs_of_s s k \<noteq> [])"

lemmas KvsOfS_Not_EmpI = KvsOfS_Not_Emp_def[THEN iffD2, rule_format]
lemmas KvsOfS_Not_EmpE[elim] = KvsOfS_Not_Emp_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_of_s_not_emp [simp, dest]: "reach tps s \<Longrightarrow> KvsOfS_Not_Emp s"
  using reach_commit_order_not_emp
  by (auto simp add: KvsOfS_Not_Emp_def kvs_of_s_def)


definition Init_Ver_Inv where
  "Init_Ver_Inv s k \<longleftrightarrow> (\<exists>rs. wtxn_state (svrs s k) T0 = Commit 0 undefined rs)"

lemmas Init_Ver_InvI = Init_Ver_Inv_def[THEN iffD2, rule_format]
lemmas Init_Ver_InvE[elim] = Init_Ver_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_init_ver_inv [simp, intro]: "reach tps s \<Longrightarrow> Init_Ver_Inv s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Init_Ver_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Init_Ver_Inv_def tps_trans_defs)
      by (meson add_to_readerset_commit')
  qed (auto simp add: Init_Ver_Inv_def tps_trans_defs)
qed


subsection \<open>Invariant about server and client state relations and (future and past) transactions ids\<close>

definition FTid_Inv where
  "FTid_Inv s cl \<longleftrightarrow> (\<forall>n k. n > txn_sn (cls s cl) \<longrightarrow> wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver)"

lemmas FTid_InvI = FTid_Inv_def[THEN iffD2, rule_format]
lemmas FTid_InvE[elim] = FTid_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_ftid_inv [simp, dest]: "reach tps s \<Longrightarrow> FTid_Inv s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FTid_Inv_def tps_defs wtid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x71 x72 x73 x74 x75)
    then show ?case
      apply (auto simp add: tps_trans_defs wtid_match_def FTid_Inv_def)
      by (metis add_to_readerset_no_ver_inv)
  qed (auto simp add: tps_trans_defs wtid_match_def FTid_Inv_def)
qed


definition Idle_Read_Inv where
  "Idle_Read_Inv s \<longleftrightarrow> (\<forall>cl k keys kvm. txn_state (cls s cl) \<in> {Idle, RtxnInProg keys kvm}
    \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) = No_Ver)"

lemmas Idle_Read_InvI = Idle_Read_Inv_def[THEN iffD2, rule_format]
lemmas Idle_Read_InvE[elim] = Idle_Read_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_idle_read_inv [simp, dest]: "reach tps s \<Longrightarrow> Idle_Read_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Idle_Read_Inv_def tps_defs wtid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Idle_Read_Inv_def tps_trans_defs)
      by (metis add_to_readerset_no_ver_inv)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: Idle_Read_Inv_def tps_trans_defs)
      by (metis get_cl_wtxn.simps(2) state_txn.distinct(3) state_txn.distinct(7))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: Idle_Read_Inv_def tps_trans_defs)
      by force
  qed (auto simp add: Idle_Read_Inv_def tps_trans_defs)
qed

definition Wr_Svr_Idle where
  "Wr_Svr_Idle s \<longleftrightarrow>
    (\<forall>cl k cts kv_map. txn_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map}
        \<and> kv_map k = None \<longrightarrow> wtxn_state (svrs s k) (Tn (get_txn_cl s cl)) = No_Ver)"

lemmas Wr_Svr_IdleI = Wr_Svr_Idle_def[THEN iffD2, rule_format]
lemmas Wr_Svr_IdleE[elim] = Wr_Svr_Idle_def[THEN iffD1, elim_format, rule_format]

lemma reach_wr_svr_idle [simp, dest]: "reach tps s \<Longrightarrow> Wr_Svr_Idle s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Wr_Svr_Idle_def tps_defs wtid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Wr_Svr_Idle_def tps_trans_defs)
      by (metis add_to_readerset_no_ver_inv)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: Wr_Svr_Idle_def tps_trans_defs)
      by (smt (z3) domIff get_cl_wtxn.simps(2) state_txn.distinct(11) state_txn.inject(2))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: Wr_Svr_Idle_def tps_trans_defs)
      by force
  qed (auto simp add: Wr_Svr_Idle_def tps_trans_defs, blast?)
qed

definition PTid_Inv where
  "PTid_Inv s cl \<longleftrightarrow> (\<forall>k. \<forall>n < txn_sn (cls s cl).
   wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver \<or>
   (\<exists>cts v rs. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts v rs))"

lemmas PTid_InvI = PTid_Inv_def[THEN iffD2, rule_format]
lemmas PTid_InvE[elim] = PTid_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_ptid_inv [simp, dest]: "reach tps s \<Longrightarrow> PTid_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: PTid_Inv_def tps_defs wtid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RDone x31 x32 x33 x34)
    then show ?case
      apply (auto simp add: tps_trans_defs PTid_Inv_def)
      by (smt Idle_Read_Inv_def insertI1 insert_commute not_less_less_Suc_eq reach_idle_read_inv reach_trans.hyps(2))
  next
    case (WDone x6)
    then show ?case
      apply (auto simp add: tps_trans_defs PTid_Inv_def)
      subgoal for kv_map commit_t k apply (cases "k \<in> dom kv_map")
        apply (metis (no_types, lifting) less_antisym)
        by (metis (lifting) Wr_Svr_Idle_def domIff insertCI less_antisym reach_wr_svr_idle).
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?case
      apply (auto simp add: tps_trans_defs PTid_Inv_def)
      by (metis add_to_readerset_commit' add_to_readerset_no_ver_inv)
  next                            
    case (CommitW x91 x92)
    then show ?case
      apply (auto simp add: tps_trans_defs PTid_Inv_def)
      by blast
  qed (auto simp add: tps_trans_defs PTid_Inv_def wtid_match_def)
qed

lemma other_sn_idle:  
  assumes "FTid_Inv s cl" and "PTid_Inv s cl"
    and "get_cl_txn t = cl" and "get_sn_txn t \<noteq> txn_sn (cls s cl)"
  shows "\<And>k. \<exists>cts v rs. wtxn_state (svrs s k) (Tn t) \<in> {No_Ver, Commit cts v rs}"
  using assms
  apply (auto simp add: FTid_Inv_def PTid_Inv_def)
  apply (cases "get_sn_txn t > txn_sn (cls s cl)")
  apply (metis txid0.collapse)
  by (metis txid0.collapse linorder_cases)

definition Prep_Inv where
  "Prep_Inv s \<longleftrightarrow> (\<forall>cl k kvm. \<exists>prep_t v. txn_state (cls s cl) = WtxnPrep kvm
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> wtxn_state (svrs s k) (Tn (get_txn_cl s cl)) \<in> {No_Ver, Prep prep_t v}) \<and>
    (k \<notin> dom kvm \<longrightarrow> wtxn_state (svrs s k) (Tn (get_txn_cl s cl)) = No_Ver))"

lemmas Prep_InvI = Prep_Inv_def[THEN iffD2, rule_format]
lemmas Prep_InvE[elim] = Prep_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_prep_inv [simp, dest]: "reach tps s \<Longrightarrow> Prep_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Prep_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (WInvoke x1 x2)
    then show ?case by (simp add: Prep_Inv_def tps_trans_defs, blast)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Prep_Inv_def tps_trans_defs)
      by (smt (verit) add_to_readerset_wts_dom add_to_readerset_prep_inv wts_domIff)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: Prep_Inv_def tps_trans_defs)
      by (smt (verit) fun_upd_other fun_upd_same get_cl_wtxn.simps(2) state_txn.inject(2))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: Prep_Inv_def tps_trans_defs)
      using get_cl_wtxn.simps(2) state_txn.distinct(11) state_txn.simps(19) by force
  qed (auto simp add: Prep_Inv_def tps_trans_defs)
qed

definition Commit_Inv where
  "Commit_Inv s \<longleftrightarrow> (\<forall>cl k cts kvm. \<exists>prep_t v rs. txn_state (cls s cl) = WtxnCommit cts kvm
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) \<in> {Prep prep_t v, Commit cts v rs}) \<and>
    (k \<notin> dom kvm \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) = No_Ver))"

lemmas Commit_InvI = Commit_Inv_def[THEN iffD2, rule_format]
lemmas Commit_InvE[elim] = Commit_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_inv [simp, dest]: "reach tps s \<Longrightarrow> Commit_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Commit_Inv_def tps_defs wtid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case by (simp add: Commit_Inv_def tps_trans_defs, blast)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Commit_Inv_def tps_trans_defs)
      by (smt add_to_readerset_commit add_to_readerset_no_ver_inv add_to_readerset_prep_inv
          ver_state.exhaust ver_state.inject(2))
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: Commit_Inv_def tps_trans_defs)
      by (smt (verit) fun_upd_other get_cl_wtxn.simps(2) state_txn.distinct(11))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: Commit_Inv_def tps_trans_defs)
      using fun_upd_same get_cl_wtxn.simps(2) state_txn.simps(19) ver_state.distinct(1)
        ver_state.simps(10) by force
  qed (auto simp add: Commit_Inv_def tps_trans_defs)
qed


definition FTid_notin_rs where
  "FTid_notin_rs s cl \<longleftrightarrow> (\<forall>n k t cts v rs.  n > txn_sn (cls s cl) \<and>
    wtxn_state (svrs s k) t = Commit cts v rs \<longrightarrow> Tn_cl n cl \<notin> rs)"

lemmas FTid_notin_rsI = FTid_notin_rs_def[THEN iffD2, rule_format]
lemmas FTid_notin_rsE[elim] = FTid_notin_rs_def[THEN iffD1, elim_format, rule_format]

lemma reach_ftid_notin_rs [simp, dest]: "reach tps s \<Longrightarrow> FTid_notin_rs s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  apply (auto simp add: FTid_notin_rs_def tps_defs)
    by (metis empty_iff ver_state.distinct(3) ver_state.inject(2))
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: FTid_notin_rs_def tps_trans_defs tid_match_def) sorry
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: FTid_notin_rs_def tps_trans_defs)
      by (metis)
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: FTid_notin_rs_def tps_trans_defs)
      by (smt empty_iff fun_upd_other fun_upd_same state_txn.simps(19) ver_state.inject(2)
          ver_state.simps(10))
  qed (auto simp add: FTid_notin_rs_def tps_trans_defs)
qed

definition FTid_not_wr where
  "FTid_not_wr s cl \<longleftrightarrow> (\<forall>n k. n > txn_sn (cls s cl) \<longrightarrow> Tn (Tn_cl n cl) \<notin> wts_dom (wtxn_state (svrs s k)))"

lemmas FTid_not_wrI = FTid_not_wr_def[THEN iffD2, rule_format]
lemmas FTid_not_wrE[elim] = FTid_not_wr_def[THEN iffD1, elim_format, rule_format]

lemma reach_ftid_not_wr [simp, dest]: "reach tps s \<Longrightarrow> FTid_not_wr s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FTid_not_wr_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RDone x31 x32 x33 x34)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (metis Suc_lessD)
  next
    case (WDone x6)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (metis Suc_lessD)
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (metis add_to_readerset_wts_dom)
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs wtid_match_def)
      by (metis get_cl_wtxn.simps(2) get_sn_wtxn.simps(2) nat_neq_iff)
  next
    case (CommitW x91 x92)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (smt (z3) fun_upd_other state_txn.simps(19) ver_state.distinct(1) ver_state.simps(10) wts_domIff)
  qed (auto simp add: FTid_not_wr_def tps_trans_defs)
qed


abbreviation not_committing_ev where
  "not_committing_ev e \<equiv> \<forall>cl kvt_map kv_map cts sn u. e \<noteq> RDone cl kvt_map sn u \<and> e \<noteq> WCommit cl kv_map cts sn u"


definition Fresh_rd_notin_rs where
  "Fresh_rd_notin_rs s cl k \<longleftrightarrow> (\<forall>t cts v rs. txn_state (cls s cl) = Idle \<and>
    wtxn_state (svrs s k) t = Commit cts v rs \<longrightarrow> get_txn_cl s cl \<notin> rs)"

lemmas Fresh_rd_notin_rsI = Fresh_rd_notin_rs_def[THEN iffD2, rule_format]
lemmas Fresh_rd_notin_rsE[elim] = Fresh_rd_notin_rs_def[THEN iffD1, elim_format, rule_format]

lemma reach_fresh_rd_notin_rs [simp, dest]: "reach tps s \<Longrightarrow> Fresh_rd_notin_rs s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  apply (auto simp add: Fresh_rd_notin_rs_def tps_defs)
    by (metis ex_in_conv get_rs_ver.simps(3) ver_state.distinct(3))
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RDone x31 x32 x33 x34)
    then show ?case by (simp add: Fresh_rd_notin_rs_def tps_trans_defs, blast)
  next
    case (WDone x6)
    then show ?case by (simp add: Fresh_rd_notin_rs_def tps_trans_defs, blast)
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?case apply (simp add: Fresh_rd_notin_rs_def tps_trans_defs wtid_match_def)
      apply (cases "k = x71"; cases "cl = get_cl_txn x72"; auto) sorry
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case sorry
  next
    case (CommitW x91 x92)
    then show ?case sorry
  qed (auto simp add: Fresh_rd_notin_rs_def tps_trans_defs)
qed

definition Fresh_wr_notin_Wts_dom where
  "Fresh_wr_notin_Wts_dom s cl \<longleftrightarrow> (\<forall>keys kvt_map k. txn_state (cls s cl) \<in> {Idle, RtxnInProg keys kvt_map} \<longrightarrow>
    Tn (get_txn_cl s cl) \<notin> wts_dom (wtxn_state (svrs s k)))"

lemmas Fresh_wr_notin_Wts_domI = Fresh_wr_notin_Wts_dom_def[THEN iffD2, rule_format]
lemmas Fresh_wr_notin_Wts_domE[elim] = Fresh_wr_notin_Wts_dom_def[THEN iffD1, elim_format, rule_format]

lemma reach_fresh_wr_notin_wts_dom [simp, dest]: "reach tps s \<Longrightarrow> Fresh_wr_notin_Wts_dom s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Fresh_wr_notin_Wts_dom_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case by (simp add: tps_trans_defs Fresh_wr_notin_Wts_dom_def, blast)
  next
    case (WDone x)
    then show ?case by (simp add: tps_trans_defs Fresh_wr_notin_Wts_dom_def, blast)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: tps_trans_defs Fresh_wr_notin_Wts_dom_def)
      by (metis add_to_readerset_wts_dom)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: tps_trans_defs Fresh_wr_notin_Wts_dom_def)
      by (metis get_cl_wtxn.simps(2) state_txn.distinct(3) state_txn.distinct(7))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: tps_trans_defs Fresh_wr_notin_Wts_dom_def)
      by (smt (verit) fun_upd_other state_txn.simps(19) ver_state.simps(10) wts_domI1 wts_domIff)
  qed (auto simp add: tps_trans_defs Fresh_wr_notin_Wts_dom_def)
qed

abbreviation invariant_list_kvs where
  "invariant_list_kvs s \<equiv> \<forall>cl k. FTid_Inv s cl \<and> PTid_Inv s cl \<and> Kvs_Not_Emp s \<and>
   \<comment> \<open> KVS_Not_All_Pending s k \<and>\<close> Fresh_rd_notin_rs s cl k"

lemma kvs_of_s_inv:
  assumes "state_trans s e s'"
    and "invariant_list_kvs s"
    and "not_committing_ev e"
  shows "kvs_of_s s' = kvs_of_s s"
  using assms
proof (induction e)
  case (WDone x)
  then show ?case apply (auto simp add: kvs_of_s_def tps_trans_defs )
    apply (rule ext) apply (auto intro: list.map_cong0 split: ver_state.split) sorry
next
  case (RegR x1 x2 x3 x4 x5)
  then show ?case sorry
next
  case (PrepW x1 x2 x3 x4)
  then show ?case sorry
next
  case (CommitW x1 x2)
  then show ?case sorry
qed (auto simp add: kvs_of_s_def tps_trans_defs split: ver_state.split)

definition Sqn_Inv_nc where
  "Sqn_Inv_nc s cl \<longleftrightarrow> (\<forall>cts kvm.
    (txn_state (cls s cl) \<noteq> WtxnCommit cts kvm \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m < txn_sn (cls s cl))))"

lemmas Sqn_Inv_ncI = Sqn_Inv_nc_def[THEN iffD2, rule_format]
lemmas Sqn_Inv_ncE[elim] = Sqn_Inv_nc_def[THEN iffD1, elim_format, rule_format]

lemma reach_sql_inv_nc [simp, dest]: "reach tps s \<Longrightarrow> Sqn_Inv_nc s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Sqn_Inv_nc_def tps_def kvs_of_s_init get_sqns_old_def txid_defs)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: Sqn_Inv_nc_def)
      apply (metis (full_types) gt_ex state_txn.inject(3)) sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Sqn_Inv_nc_def tps_trans_defs) sorry
  next
    case (WDone x)
    then show ?case apply (simp add: Sqn_Inv_nc_def tps_trans_defs)
      by (metis Gst_lt_Cts_def less_Suc_eq less_irrefl_nat reach_gst_lt_cts)
  qed (auto simp add: Sqn_Inv_nc_def tps_trans_defs)
qed

definition Sqn_Inv_c where
  "Sqn_Inv_c s cl \<longleftrightarrow> (\<forall>cts kvm.
    (txn_state (cls s cl) = WtxnCommit cts kvm \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m \<le> txn_sn (cls s cl))))"

lemmas Sqn_Inv_cI = Sqn_Inv_c_def[THEN iffD2, rule_format]
lemmas Sqn_Inv_cE[elim] = Sqn_Inv_c_def[THEN iffD1, elim_format, rule_format]

lemma reach_sql_inv_c [simp, dest]: "reach tps s \<Longrightarrow> Sqn_Inv_c s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Sqn_Inv_c_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: Sqn_Inv_c_def)
      by (metis (full_types) Sqn_Inv_nc_def gt_ex nless_le reach.reach_trans reach_sql_inv_nc
          reach_trans.hyps(1) state_txn.inject(3))+
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Sqn_Inv_c_def)
      by (metis Sqn_Inv_nc_def less_or_eq_imp_le reach.reach_trans reach_sql_inv_nc
          reach_trans.hyps(1) state_txn.inject(3))
  qed (auto simp add: Sqn_Inv_c_def tps_trans_defs)
qed

lemma t_is_fresh:
  assumes "Sqn_Inv_c s cl" and "Sqn_Inv_nc s cl"
    and "txn_state (cls s cl) \<in> {WtxnPrep kv_map, RtxnInProg keys kvt_map}"
  shows "get_txn_cl s cl \<in> next_txids (kvs_of_s s) cl"
  using assms by (auto simp add: kvs_of_s_def next_txids_def)


subsection \<open>Invariants about commit order\<close>

definition Commit_Order_Tid where
  "Commit_Order_Tid s cl \<longleftrightarrow> (case txn_state (cls s cl) of
    WtxnCommit cts kv_map \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (commit_order s k) \<longrightarrow> n \<le> txn_sn (cls s cl))
  | _ \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (commit_order s k) \<longrightarrow> n < txn_sn (cls s cl)))"

lemmas Commit_Order_TidI = Commit_Order_Tid_def[THEN iffD2, rule_format]
lemmas Commit_Order_TidE[elim] = Commit_Order_Tid_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_tid[simp, dest]: "reach tps s \<Longrightarrow> Commit_Order_Tid s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Commit_Order_Tid_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: Commit_Order_Tid_def tps_trans_defs split: state_txn.split_asm)
      using less_SucI less_Suc_eq_le by blast+
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Commit_Order_Tid_def tps_trans_defs split: state_txn.split_asm)
      apply (metis state_txn.distinct(3))
      apply (metis state_txn.distinct(7))
      apply (meson less_or_eq_imp_le)
      by blast
  next
    case (WDone x)
    then show ?case apply (simp add: Commit_Order_Tid_def tps_trans_defs split: state_txn.split_asm)
      apply (meson less_SucI)+
      by (meson linorder_le_less_linear not_less_eq_eq)
  qed (auto simp add: Commit_Order_Tid_def tps_trans_defs split: state_txn.split_asm)
qed

definition Commit_Order_Distinct where
  "Commit_Order_Distinct s k \<longleftrightarrow> distinct (commit_order s k)"

lemmas Commit_Order_DistinctI = Commit_Order_Distinct_def[THEN iffD2, rule_format]
lemmas Commit_Order_DistinctE[elim] = Commit_Order_Distinct_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_distinct [simp, dest]: "reach tps s \<Longrightarrow> Commit_Order_Distinct s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Commit_Order_Distinct_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Commit_Order_Distinct_def tps_trans_defs)
      using Commit_Order_Tid_def
      by (metis (no_types, lifting) less_not_refl reach_commit_order_tid state_txn.simps(18))
  qed (simp_all add: Commit_Order_Distinct_def tps_trans_defs)
qed

definition Commit_Order_Sound where
  "Commit_Order_Sound s k \<longleftrightarrow> (\<forall>n cl. Tn (Tn_cl n cl) \<in> set (commit_order s k) \<longrightarrow>
    (\<exists>cts v rs. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts v rs) \<or> 
    ((\<exists>ts v. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Prep ts v) \<and> 
     (\<exists>cts kv_map. txn_state (cls s cl) = WtxnCommit cts kv_map \<and> 
      txn_sn (cls s cl) = n \<and> k \<in> dom kv_map)))"

lemmas Commit_Order_SoundI = Commit_Order_Sound_def[THEN iffD2, rule_format]
lemmas Commit_Order_SoundE[elim] = Commit_Order_Sound_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_sound [simp, dest]: "reach tps s \<Longrightarrow> Commit_Order_Sound s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Commit_Order_Sound_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: Commit_Order_Sound_def tps_trans_defs)
      by (metis state_txn.distinct(5))
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: Commit_Order_Sound_def tps_trans_defs)
      by (metis state_txn.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: Commit_Order_Sound_def tps_trans_defs)
      by (metis state_txn.distinct(9))
  next
    case (WInvoke x1 x2)
    then show ?case apply (simp add: Commit_Order_Sound_def tps_trans_defs)
      by (metis state_txn.distinct(5))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Commit_Order_Sound_def tps_trans_defs)
      by (metis (no_types, lifting) domIff option.discI state_txn.distinct(11))
  next
    case (WDone x)
    then show ?case apply (simp add: Commit_Order_Sound_def tps_trans_defs)
      by (metis (no_types, lifting) state_txn.inject(3))
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Commit_Order_Sound_def tps_trans_defs)
      by (metis add_to_readerset_commit' add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: Commit_Order_Sound_def tps_trans_defs)
      by (metis ver_state.distinct(3))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: Commit_Order_Sound_def tps_trans_defs)
      by (smt (z3) fun_upd_apply state_txn.simps(19) ver_state.simps(10))
  qed (auto simp add: Commit_Order_Sound_def tps_trans_defs)
qed

definition Commit_Order_Complete where
  "Commit_Order_Complete s k \<longleftrightarrow> (\<forall>n cl.
    (\<exists>cts v rs. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts v rs) \<or> 
    ((\<exists>ts v. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Prep ts v) \<and> 
     (\<exists>cts kv_map. txn_state (cls s cl) = WtxnCommit cts kv_map \<and> 
      txn_sn (cls s cl) = n \<and> k \<in> dom kv_map)) \<longrightarrow>
    Tn (Tn_cl n cl) \<in> set (commit_order s k))"

lemmas Commit_Order_CompleteI = Commit_Order_Complete_def[THEN iffD2, rule_format]
lemmas Commit_Order_CompleteE[elim] = Commit_Order_Complete_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_complete [simp, dest]: "reach tps s \<Longrightarrow> Commit_Order_Complete s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Commit_Order_Complete_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: Commit_Order_Complete_def tps_trans_defs)
      by (metis state_txn.distinct(9) state_txn.simps(17))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Commit_Order_Complete_def tps_trans_defs)
      by (metis (no_types, lifting) domIff)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Commit_Order_Complete_def tps_trans_defs)
      by (smt (verit) add_to_readerset_commit add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: Commit_Order_Complete_def tps_trans_defs)
      by (metis get_cl_wtxn.simps(2) state_txn.distinct(11))
  next
    case (CommitW x1 x2)
    then show ?case apply (auto simp add: Commit_Order_Complete_def tps_trans_defs)
      apply (metis domI get_cl_wtxn.simps(2) get_sn_wtxn.simps(2) wtid_match_def)
      by (metis domI)
  qed (simp_all add: Commit_Order_Complete_def tps_trans_defs)
qed

definition Commit_Order_Superset_View where
  "Commit_Order_Superset_View s k \<longleftrightarrow> (\<forall>cl. (cl_view (cls s cl)) k \<subseteq> set (commit_order s k))"

lemmas Commit_Order_Superset_ViewI = Commit_Order_Superset_View_def[THEN iffD2, rule_format]
lemmas Commit_Order_Superset_ViewE[elim] = Commit_Order_Superset_View_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_superset_view [simp, dest]: "reach tps s \<Longrightarrow> Commit_Order_Superset_View s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Commit_Order_Superset_View_def tps_defs view_txid_init_def)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: Commit_Order_Superset_View_def tps_trans_defs get_view_def)
      using Commit_Order_Complete_def[of s k] apply auto sorry \<comment> \<open>Continue here\<close>
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case sorry
  qed (simp_all add: Commit_Order_Superset_View_def tps_trans_defs)
qed

definition Commit_Order_len where
  "Commit_Order_len s k \<longleftrightarrow> length (commit_order s k) = length (kvs_of_s s k)"

lemmas Commit_Order_lenI = Commit_Order_len_def[THEN iffD2, rule_format]
lemmas Commit_Order_lenE[elim] = Commit_Order_len_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_len [simp, dest]: "reach tps s \<Longrightarrow> Commit_Order_len s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Commit_Order_len_def tps_def kvs_of_s_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: Commit_Order_len_def tps_trans_defs)
      by (smt (verit, ccfv_SIG) RInvoke.prems(1) ev.distinct(3,7) kvs_of_s_inv reach_fresh_rd_notin_rs
          reach_kvs_not_emp reach_ftid_inv reach_ptid_inv tps_trans)
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
qed


subsection \<open>view wellformed\<close>

definition Get_view_Wellformed where
  "Get_view_Wellformed s cl \<longleftrightarrow> (view_wellformed (kvs_of_s s) (view_of (commit_order s) (get_view s cl)))"

lemmas Get_view_WellformedI = Get_view_Wellformed_def[THEN iffD2, rule_format]
lemmas Get_view_WellformedE[elim] = Get_view_Wellformed_def[THEN iffD1, elim_format, rule_format]

lemma reach_get_view_wellformed [simp, dest]: "reach tps s \<Longrightarrow> Get_view_Wellformed s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Get_view_Wellformed_def tps_defs view_of_def get_view_def kvs_of_s_def
        view_wellformed_defs full_view_def, auto)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: Get_view_Wellformed_def tps_trans_defs view_of_def
          get_view_def view_wellformed_def full_view_def) sorry
  next
    case (RDone x1 x2 x3 x4)
    then show ?case sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Get_view_Wellformed_def tps_trans_defs get_view_def)
      using add_to_readerset_commit_subset sorry
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case sorry
  next
    case (CommitW x1 x2)
    then show ?case sorry
  qed (auto simp add: Get_view_Wellformed_def tps_trans_defs get_view_def)
qed


subsection \<open>CanCommit\<close>

lemmas canCommit_defs = ET_CC.canCommit_def closed_def R_CC_def R_onK_def

lemma "kvs_writers (kvs_of_s gs) \<inter> Tn ` kvs_readers (kvs_of_s gs) = {}" sorry

lemma "read_only_Txs (kvs_of_s gs) = Tn ` kvs_readers (kvs_of_s gs)"
  apply (simp add: kvs_of_s_def) sorry \<comment> \<open>turn into invariant\<close>

subsubsection \<open>visTx' and closed' lemmas\<close>

lemma visTx_visTx': "visTx (kvs_of_s s) (view_of (commit_order s) u) = visTx' u"
  apply (simp add: view_of_def visTx_def visTx'_def) sorry

lemma closed_closed': "closed (kvs_of_s s) (view_of (commit_order s) u) r = closed' (kvs_of_s s) u r"
  by (simp add: closed_def closed'_def visTx_visTx')

lemma visTx'_subset_writers: "visTx' (get_view s cl) \<subseteq> kvs_writers (kvs_of_s s)" sorry

definition Get_view_Closed where
  "Get_view_Closed s cl \<longleftrightarrow> (\<forall>F. ET_CC.canCommit (kvs_of_s s) (view_of (commit_order s) (get_view s cl)) F)"

lemmas Get_view_ClosedI = Get_view_Closed_def[THEN iffD2, rule_format]
lemmas Get_view_ClosedE[elim] = Get_view_Closed_def[THEN iffD1, elim_format, rule_format]

lemma reach_get_view_closed [simp, dest]: "reach tps s \<Longrightarrow> Get_view_Closed s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case (* inv : show view is wellformed *)
    apply (auto simp add: Get_view_Closed_def tps_defs canCommit_defs view_of_def
        get_view_def txid_defs split: if_split_asm) sorry
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s'] sorry
  (*apply (auto simp add: ET_CC.canCommit_def closed_closed' closed'_def)
   apply (metis DiffD2 read_only_Txs_def subsetD visTx'_subset_writers)
  thm rtrancl.simps
  subgoal for t' t apply (simp add: R_CC_def) sorry.*)
qed
  

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
    then show ?case apply (auto simp add: RO_WO_Inv_def tps_trans_defs) sorry
     (*using add_to_readerset_v_writer_img[of ] apply (simp add: txid_defs) sorry \<comment> \<open>Continue here!\<close>*)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case sorry
  next
    case (CommitW x1 x2)
    then show ?case sorry
  qed (auto simp add: RO_WO_Inv_def tps_trans_defs)
qed

lemma "kvs_writers (kvs_of_s s) \<subseteq> (\<Union>k. wts_dom (wtxn_state (svrs s k)))"
  oops

lemma "kvs_readers (kvs_of_s s) \<subseteq> (\<Union>k. \<Union>(wts_rsran (wtxn_state (svrs s k))))"
  oops

definition canCommit_rd_Inv where
  "canCommit_rd_Inv s cl \<longleftrightarrow> (\<forall>kvt_map. txn_state (cls s cl) = RtxnInProg (dom kvt_map) kvt_map  \<longrightarrow>
    ET_CC.canCommit (kvs_of_s s) (view_of (commit_order s) (get_view s cl))
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
      apply (simp add: canCommit_rd_Inv_def tps_trans_defs)
      by (cases "cl = x1"; simp add: get_view_def view_of_def)
  next
    case (Read x1 x2 x3 x4)
    then show ?case
      apply (simp add: canCommit_rd_Inv_def tps_trans_defs)
      apply (cases "cl = x1"; simp add: get_view_def view_of_def) sorry
  next
    case (RDone x1 x2 x3 x4)
    then show ?case
      apply (simp add: canCommit_rd_Inv_def tps_trans_defs)
      apply (cases "cl = x1"; simp add: ET_CC.canCommit_def closed_def R_CC_def R_onK_def) sorry
  next
    case (WInvoke x1 x2)
    then show ?case
      apply (simp add: canCommit_rd_Inv_def tps_trans_defs)
      by (cases "cl = x1"; simp add: get_view_def view_of_def)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case
      apply (simp add: canCommit_rd_Inv_def tps_trans_defs)
      apply (cases "cl = x1"; simp) sorry
  next
    case (WDone x)
    then show ?case
      apply (simp add: canCommit_rd_Inv_def tps_trans_defs)
      by (cases "cl = x"; simp add: get_view_def view_of_def)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: canCommit_rd_Inv_def tps_trans_defs view_of_def
          get_view_add_to_readerset_inv) sorry
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: canCommit_rd_Inv_def tps_trans_defs view_of_def
        get_view_wprep_inv) sorry
  next
    case (CommitW x1 x2)
    then show ?case
      apply (simp add: canCommit_rd_Inv_def tps_trans_defs)
      apply (cases "get_cl_wtxn x2 = cl"; auto) sorry
  qed simp
qed


subsection \<open>View invariants\<close>

lemma cl_view_inv:
  assumes "state_trans s e s'"
    and "not_committing_ev e"
  shows "cl_view (cls s' cl) = cl_view (cls s cl)"
  using assms
  by (induction e) (auto simp add: tps_trans_defs views_of_s_def)

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
  by (auto simp add: read_done_def views_of_s_def )
  (*apply (rule ext) apply (simp split: if_split_asm)
  apply (rule impI, rule Collect_eqI, rule iffI)
  
    subgoal for k x apply (rule bexI[where x=x]) sorry
    done
  done*)

lemma write_commit_views_of_s_other_cl_inv:
  assumes "write_commit cl kv_map cts sn u s s'"
    and "cl' \<noteq> cl"
  shows "views_of_s s' cl' = views_of_s s cl'"
  using assms
  apply (auto simp add: write_commit_def views_of_s_def view_of_def)
  apply (rule ext) subgoal for k apply(cases "k \<in> dom kv_map"; simp add: image_def)
    (*apply (auto intro: Collect_eqI)
    subgoal for y x apply (rule bexI[where x=x]) sorry
    subgoal for y x apply (rule bexI[where x=x]) sorry
    done
  done*) sorry.

lemma the_T0: "(THE i. i = 0 \<and> [T0] ! i = T0) = 0" by auto

abbreviation invariant_list where
  "invariant_list s \<equiv> (\<forall>cl. invariant_list_kvs s \<and> Sqn_Inv_c s cl \<and> Sqn_Inv_nc s cl \<and> Get_view_Closed s cl)"


section \<open>Refinement Proof\<close>

lemma tps_refines_et_es: "tps \<sqsubseteq>\<^sub>med ET_CC.ET_ES"
proof (intro simulate_ES_fun_with_invariant[where I="\<lambda>s. invariant_list s"])
  fix gs0 :: "'v state"
  assume p: "init tps gs0"
  then show "init ET_CC.ET_ES (sim gs0)"
    by (auto simp add: ET_CC.ET_ES_defs tps_defs sim_defs kvs_init_def v_list_init_def version_init_def
        view_txid_init_def view_of_def the_T0)
next
  fix gs a and gs' :: "'v state"
  assume p: "tps: gs\<midarrow>a\<rightarrow> gs'" and inv: "invariant_list gs"
  then show "ET_CC.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  using kvs_of_s_inv[of gs a gs'] views_of_s_inv[of gs a gs']
  proof (induction a)
    case (RDone cl kvt_map sn u'')
    then show ?case
    apply (auto simp add: read_done_def sim_def intro!: exI [where x="views_of_s gs' cl"])
    subgoal apply (auto simp add: ET_CC.ET_cl_txn_def t_is_fresh KvsOfS_Not_Emp_def Get_view_Closed_def)
      subgoal apply (simp add: view_wellformed_def views_of_s_def) sorry
      subgoal sorry
      subgoal apply (auto simp add: vShift_MR_RYW_def vShift_MR_def vShift_RYW_def) sorry
      sorry
      subgoal apply (rule ext)
        subgoal for cl' apply (cases "cl' = cl"; simp)
        using read_commit_views_of_s_other_cl_inv [where s=gs and s'=gs' and cl=cl and cl'=cl']
        by (metis RDone.prems(1) state_trans.simps(3) tps_trans).
    subgoal apply (auto simp add: fp_property_def view_snapshot_def)
      subgoal for k y apply (simp add: last_version_def kvs_of_s_def)
        apply (cases "k \<in> dom kvt_map") sorry
      done.
  next
    case (WCommit cl kv_map cts sn u'')
    then show ?case 
    apply (auto simp add: write_commit_def sim_def fp_property_def intro!: exI [where x="views_of_s gs' cl"])
    subgoal apply (auto simp add: ET_CC.ET_cl_txn_def t_is_fresh Get_view_Closed_def) sorry
    subgoal apply (rule ext)
      subgoal for cl' apply (cases "cl' = cl"; simp)
      using write_commit_views_of_s_other_cl_inv [where s=gs and s'=gs' and cl=cl and cl'=cl']
      by (metis (no_types, lifting) WCommit.prems(1) state_trans.simps(5) tps_trans).
    done
  qed (auto simp add: sim_def)
qed simp

end
