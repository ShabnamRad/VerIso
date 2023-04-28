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

lemma get_view_inv:
  assumes "state_trans s e s'"
    and "\<forall>cl keys. e \<noteq> RInvoke cl keys" and "\<forall>k t. e \<noteq> CommitW k t"
  shows "get_view s' cl = get_view s cl"
  using assms
proof (induction e)
  case (RegR x1 x2 x3 x4 x5)
  then show ?case apply (auto simp add: tps_trans_defs get_view_def)
    apply (rule ext, auto del: disjE split: if_split_asm)
    apply (metis add_to_readerset_commit)
    by (meson add_to_readerset_commit')
next
  case (PrepW x1 x2 x3 x4)
  then show ?case apply (auto simp add: tps_trans_defs get_view_def)
    by (rule ext, auto)
qed (auto simp add: tps_trans_defs get_view_def)


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

lemma Min_monotonic:
  assumes "\<And>k. f s k \<le> f s' k"
    and "finite (range (f s))" and "finite (range (f s'))"
  shows "Min (range (f s)) \<le> Min (range (f s'))"
  using assms
  using Min_le_iff empty_is_image empty_not_UNIV rangeI by fastforce

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

definition Lst_map_le_Lst where
  "Lst_map_le_Lst s cl k \<longleftrightarrow> (lst_map (cls s cl) k \<le> lst (svrs s k))"
                                                           
lemmas Lst_map_le_LstI = Lst_map_le_Lst_def[THEN iffD2, rule_format]
lemmas Lst_map_le_LstE[elim] = Lst_map_le_Lst_def[THEN iffD1, elim_format, rule_format]

lemma reach_lst_map_le_lst [simp, dest]: "reach tps s \<Longrightarrow> Lst_map_le_Lst s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Lst_map_le_Lst_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (CommitW x1 x2)
    then show ?case using lst_monotonic[of s "CommitW x1 x2" s' x1]
      by (auto simp add: Lst_map_le_Lst_def tps_trans_defs)
  qed (auto simp add: Lst_map_le_Lst_def tps_trans_defs)
qed

lemma lst_map_monotonic:
  assumes "state_trans s e s'"
    and "Lst_map_le_Lst s cl k"
  shows "lst_map (cls s cl) k \<le> lst_map (cls s' cl) k"
  using assms
  by (induction e) (auto simp add: tps_trans_defs)

definition Finite_Dom_Kv_map where
  "Finite_Dom_Kv_map s cl \<longleftrightarrow>
    (\<forall>kv_map cts. txn_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map} \<longrightarrow>
      finite (dom (kv_map)))"
                                                           
lemmas Finite_Dom_Kv_mapI = Finite_Dom_Kv_map_def[THEN iffD2, rule_format]
lemmas Finite_Dom_Kv_mapE[elim] = Finite_Dom_Kv_map_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_finite_dom_kv_map [simp, dest]: "reach tps s \<Longrightarrow> Finite_Dom_Kv_map s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Finite_Dom_Kv_map_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Finite_Dom_Kv_map_def tps_trans_defs)
qed

definition Finite_Lst_map_Ran where
  "Finite_Lst_map_Ran s cl \<longleftrightarrow> finite (range (lst_map (cls s cl)))"
                                                           
lemmas Finite_Lst_map_RanI = Finite_Lst_map_Ran_def[THEN iffD2, rule_format]
lemmas Finite_Lst_map_RanE[elim] = Finite_Lst_map_Ran_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_finite_lst_map_ran [simp, dest]: "reach tps s \<Longrightarrow> Finite_Lst_map_Ran s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Finite_Lst_map_Ran_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: Finite_Lst_map_Ran_def tps_trans_defs)
      by (meson image_mono rev_finite_subset subset_UNIV)
  next
    case (WDone x)
    then show ?case apply (auto simp add: Finite_Lst_map_Ran_def tps_trans_defs)
       apply (meson image_mono rev_finite_subset subset_UNIV)
        using Finite_Dom_Kv_map_def[of s x] by (simp add: image_def dom_def)
  qed (auto simp add: Finite_Lst_map_Ran_def tps_trans_defs)
qed

lemma lst_map_min_monotonic:
  assumes "state_trans s e s'"
    and "\<And>k. Lst_map_le_Lst s cl k"
    and "Finite_Lst_map_Ran s cl"
    and "Finite_Lst_map_Ran s' cl"
  shows "Min (range (lst_map (cls s cl))) \<le> Min (range (lst_map (cls s' cl)))"
  using assms lst_map_monotonic[of s]
  apply (auto simp add: Finite_Lst_map_Ran_def)
  by (meson Min.coboundedI dual_order.trans rangeI)

definition Gst_le_Lst_map where
  "Gst_le_Lst_map s cl \<longleftrightarrow> (gst (cls s cl) \<le> Min (range (lst_map (cls s cl))))"
                                                           
lemmas Gst_le_Lst_mapI = Gst_le_Lst_map_def[THEN iffD2, rule_format]
lemmas Gst_le_Lst_mapE[elim] = Gst_le_Lst_map_def[THEN iffD1, elim_format, rule_format]

lemma reach_gst_le_lst_map [simp, dest]: "reach tps s \<Longrightarrow> Gst_le_Lst_map s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Gst_le_Lst_map_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Read x1 x2 x3 x4)
    then show ?case using lst_map_min_monotonic[of s "Read x1 x2 x3 x4" s' x1]
      apply (simp add: Gst_le_Lst_map_def tps_trans_defs)
      by (smt (z3) Read.prems(1) le_trans reach.reach_trans reach_finite_lst_map_ran)
  next
    case (WDone x)
    then show ?case using lst_map_min_monotonic[of s "WDone x" s' x]
      apply (simp add: Gst_le_Lst_map_def tps_trans_defs)
      by (smt (z3) WDone.prems(1) le_trans reach.reach_trans reach_finite_lst_map_ran)
  qed (auto simp add: Gst_le_Lst_map_def tps_trans_defs)
qed

lemma gst_monotonic:
  assumes "state_trans s e s'"
    and "Gst_le_Lst_map s cl"
  shows "gst (cls s' cl) \<ge> gst (cls s cl)"
  using assms unfolding Gst_le_Lst_map_def
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
  "Gst_lt_Cts s cl \<longleftrightarrow> (\<forall>cl' cts kv_map. txn_state (cls s cl') = WtxnCommit cts kv_map
    \<longrightarrow> gst (cls s cl) < cts)"
                                                           
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
    case (RInvoke x1 x2)
    then show ?case apply (auto simp add: Gst_lt_Cts_def tps_trans_defs) sorry
  next
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


definition Commit_Order_T0 where
  "Commit_Order_T0 s k \<longleftrightarrow> T0 \<in> set (commit_order s k)"

lemmas Commit_Order_T0I = Commit_Order_T0_def[THEN iffD2, rule_format]
lemmas Commit_Order_T0E[elim] = Commit_Order_T0_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_t0 [simp, dest]: "reach tps s \<Longrightarrow> Commit_Order_T0 s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Commit_Order_T0_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Commit_Order_T0_def tps_trans_defs)
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

definition Ex_Cts_le_Rts where
  "Ex_Cts_le_Rts s k \<longleftrightarrow> (\<forall>rts. \<exists>cts. readable_cts (wtxn_state (svrs s k)) rts cts)"

lemmas Ex_Cts_le_RtsI = Ex_Cts_le_Rts_def[THEN iffD2, rule_format]
lemmas Ex_Cts_le_RtsE[elim] = Ex_Cts_le_Rts_def[THEN iffD1, elim_format, rule_format]

lemma reach_ex_cts_le_rts [simp, dest]: "reach tps s \<Longrightarrow> Ex_Cts_le_Rts s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Ex_Cts_le_Rts_def tps_defs readable_cts_def committed_at_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Ex_Cts_le_Rts_def tps_trans_defs readable_cts_def committed_at_def)
      by (meson add_to_readerset_commit')
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: Ex_Cts_le_Rts_def tps_trans_defs readable_cts_def committed_at_def)
      by (metis ver_state.distinct(3))
  next
    case (CommitW x1 x2)
    then show ?case apply (auto simp add: Ex_Cts_le_Rts_def tps_trans_defs readable_cts_def committed_at_def)
      by (metis ver_state.distinct(5))
  qed (simp_all add: Ex_Cts_le_Rts_def tps_trans_defs)
qed

definition Readable_at_cts where
  "Readable_at_cts s k \<longleftrightarrow>
    (\<forall>rts. readable_cts (wtxn_state (svrs s k)) rts (at_cts (wtxn_state (svrs s k)) rts))"

lemmas Readable_at_ctsI = Readable_at_cts_def[THEN iffD2, rule_format]
lemmas Readable_at_ctsE[elim] = Readable_at_cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_readable_at_cts [simp, dest]: "reach tps s \<Longrightarrow> Readable_at_cts s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case apply (auto simp add: Readable_at_cts_def tps_def at_cts_def)
    using Ex_Cts_le_Rts_def GreatestI_ex_nat
    by (smt (verit) local.reach_init reach.reach_init reach_ex_cts_le_rts readable_cts_def)
next
  case (reach_trans s e s')
  then show ?case 
    apply (auto simp add: Readable_at_cts_def at_cts_def)
    subgoal for rts using Ex_Cts_le_Rts_def
      GreatestI_ex_nat[of "readable_cts (wtxn_state (svrs s' k)) rts"]
      reach_ex_cts_le_rts readable_cts_def reach_trans.hyps(1) by blast.
qed

definition at_cts_Committed where
  "at_cts_Committed s k \<longleftrightarrow>
    (\<forall>rts. \<exists>t. committed_at (wtxn_state (svrs s k)) t (at_cts (wtxn_state (svrs s k)) rts))"

lemmas at_cts_CommittedI = at_cts_Committed_def[THEN iffD2, rule_format]
lemmas at_cts_CommittedE[elim] = at_cts_Committed_def[THEN iffD1, elim_format, rule_format]

lemma reach_at_cts_committed [simp, dest]: "reach tps s \<Longrightarrow> at_cts_Committed s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case apply (auto simp add: at_cts_Committed_def tps_def)
    using Readable_at_cts_def reach_readable_at_cts readable_cts_def local.reach_init by blast
next
  case (reach_trans s e s')
  then show ?case 
    apply (auto simp add: at_cts_Committed_def)
    using Readable_at_cts_def reach_readable_at_cts[of s' k] readable_cts_def
      reach_trans.hyps(1) reach_trans.hyps(2) by blast
qed

definition at_Committed where
  "at_Committed s k \<longleftrightarrow>
    (\<forall>rts. \<exists>cts. committed_at (wtxn_state (svrs s k)) (at (wtxn_state (svrs s k)) rts) cts)"

lemmas at_CommittedI = at_Committed_def[THEN iffD2, rule_format]
lemmas at_CommittedE[elim] = at_Committed_def[THEN iffD1, elim_format, rule_format]

lemma reach_at_committed [simp, dest]: "reach tps s \<Longrightarrow> at_Committed s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case apply (auto simp add: at_Committed_def tps_def at_def)
    using at_cts_Committed_def reach_at_cts_committed local.reach_init reach.reach_init
    by (smt (verit) tfl_some)
next
  case (reach_trans s e s')
  then show ?case apply (auto simp add: at_Committed_def at_def)
    using at_cts_Committed_def reach_at_cts_committed[of s' k] reach.reach_trans
    by (metis reach_trans.hyps(1) some_eq_imp)
qed

definition newest_own_write_Committed where
  "newest_own_write_Committed s k \<longleftrightarrow>
    (\<forall>cts' cl t. newest_own_write (wtxn_state (svrs s k)) cts' cl = Some t \<longrightarrow>
      (\<exists>cts. committed_at (wtxn_state (svrs s k)) t cts))"

lemmas newest_own_write_CommittedI = newest_own_write_Committed_def[THEN iffD2, rule_format]
lemmas newest_own_write_CommittedE[elim] = newest_own_write_Committed_def[THEN iffD1, elim_format, rule_format]

lemma reach_newest_own_write_committed [simp, dest]: "reach tps s \<Longrightarrow> newest_own_write_Committed s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case apply (auto simp add: newest_own_write_Committed_def tps_def newest_own_write_def)
    using at_Committed_def reach_at_committed local.reach_init reach.reach_init sorry
next
  case (reach_trans s e s')
  then show ?case sorry
qed


definition Rtxn_rts_le_Gst where
  "Rtxn_rts_le_Gst s cl \<longleftrightarrow> (\<forall>n ts. rtxn_rts (cls s cl) n = Some ts \<longrightarrow> ts \<le> gst (cls s cl))"

lemmas Rtxn_rts_le_GstI = Rtxn_rts_le_Gst_def[THEN iffD2, rule_format]
lemmas Rtxn_rts_le_GstE[elim] = Rtxn_rts_le_Gst_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_wtxn_st [simp, dest]: "reach tps s \<Longrightarrow> Rtxn_rts_le_Gst s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rtxn_rts_le_Gst_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: Rtxn_rts_le_Gst_def read_invoke_def)
      by (meson Gst_le_Lst_map_def dual_order.trans reach_gst_le_lst_map)
  qed (auto simp add: Rtxn_rts_le_Gst_def tps_trans_defs)
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
     (\<exists>cts kv_map. txn_state (cls s cl) = WtxnCommit cts kv_map \<and> txn_sn (cls s cl) = n)) \<longrightarrow>
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
      by (metis (no_types, lifting) Prep_Inv_def domIff reach_prep_inv ver_state.distinct(1))
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
      apply (metis get_cl_wtxn.simps(2) get_sn_wtxn.simps(2) wtid_match_def)
      by metis
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
      apply (rule subsetI) subgoal for x apply (cases x)
        apply blast using Commit_Order_Complete_def[of s k]
        by (smt mem_Collect_eq reach_commit_order_complete txid0.exhaust).
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Commit_Order_Superset_View_def tps_trans_defs get_view_def)
      apply (cases "x2 k", simp_all)
      apply (rule subsetI) subgoal for x apply (cases x, blast)
        by (smt mem_Collect_eq Commit_Order_Complete_def reach_commit_order_complete txid0.exhaust)
      apply (rule allI) subgoal for _ cl apply (cases "cl = x1", simp)
        apply (rule subsetI) subgoal for x apply (cases x, blast)
          by (smt list.set_intros(2) list.simps(15) mem_Collect_eq Commit_Order_Complete_def
              reach_commit_order_complete txid0.exhaust)
        by blast.
  qed (simp_all add: Commit_Order_Superset_View_def tps_trans_defs)
qed

definition Commit_Order_Superset_Get_View where
  "Commit_Order_Superset_Get_View s k \<longleftrightarrow> (\<forall>cl. (get_view s cl) k \<subseteq> set (commit_order s k))"

lemmas Commit_Order_Superset_Get_ViewI = Commit_Order_Superset_Get_View_def[THEN iffD2, rule_format]
lemmas Commit_Order_Superset_Get_ViewE[elim] = Commit_Order_Superset_Get_View_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_superset_get_view [simp, dest]:
  "reach tps s \<Longrightarrow> Commit_Order_Superset_Get_View s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Commit_Order_Superset_Get_View_def tps_defs get_view_def split:if_split_asm)
next
  case (reach_trans s e s')
  then show ?case using get_view_inv[of s e s']
  proof (induction e)
    case (CommitW x1 x2)
    then show ?case
      apply (simp add: Commit_Order_Superset_Get_View_def tps_trans_defs get_view_def)
      apply (rule, rule, rule) subgoal for cl x apply (auto; cases "x = x2"; simp_all)
        using Gst_lt_Cts_def linorder_not_less reach_gst_lt_cts apply blast
          apply blast apply (cases x, blast)
        subgoal for cts v rs kv_map prep_t y x2a apply (cases x2a)
          using Commit_Order_Complete_def[of s x1]
          by (metis (no_types, lifting) get_cl_wtxn.simps(2) get_sn_wtxn.simps(2)
              reach_commit_order_complete wtid_match_def)
        by blast.
  qed (simp_all add: Commit_Order_Superset_Get_View_def tps_trans_defs get_view_def, (blast+)?)
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

(*lemma kvs_of_s_view_atomic:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. NoLockFpInv s k"
    and "SqnInv s cl" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
  shows "view_atomic (kvs_of_gs s') (\<lambda>k. full_view (kvs_of_gs s k))"
  using assms
  apply (auto simp add: kvs_of_gs_def km_tm_cl'_unchanged_def view_atomic_def)
  subgoal for k k' i i'
    apply (auto elim!: allE[where x=k'])
    apply (auto simp add: update_kv_all_tm_commit_no_lock_inv read_only_update')
     apply (metis full_view_same_length update_kv_reads_all_txn_length)
    apply (cases "i' \<in> full_view (update_kv_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t)))
      (km_status (kms s k')) (km_key_fp (kms s k')) (km_vl (kms s k')))"; simp)
    using new_version_index[of s cl k' s' i'] apply (auto simp add: writer_update_before)
     apply (simp add: new_writer the_wr_tI)
    using tm_commit_writer_update_kv_all[of s cl k s'] apply simp
    using update_kv_all_txn_v_writer_inv[of i
        "update_kv_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
          (km_key_fp (kms s k)) (km_vl (kms s k))"] assms(3, 5, 6, 11)
    apply (auto elim!: allE[where x=k])
    apply (simp_all add: update_kv_all_tm_commit_no_lock_inv)
    by (metis t_is_fresh fresh_txid_v_writer kvs_of_gs_def)+
  done

lemma reach_kvs_expands [simp, dest]:
  assumes "reach tps s" and "state_trans s e s'"
    and "\<And>cl. TIDFutureKm s cl" and "\<And>cl. TIDPastKm s cl"
    and "KVS_Non_Emp s"
  shows "kvs_of_s s \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s kvs_of_s s'"
  using assms kvs_of_s_inv[of s e s'] apply (cases "not_committing_ev e"; auto)
  using kvs_of_s_view_atomic[of s]
  apply (auto simp add: tps_trans_defs kvs_expands_def vlist_order_def)
  apply (meson kvs_of_gs_commit_length_increasing)
  by (simp add: kvs_of_gs_version_order)*)

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
  then show ?case using kvs_of_s_inv[of s e s'] get_view_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: Get_view_Wellformed_def tps_trans_defs view_of_def
          get_view_def view_wellformed_def full_view_def) sorry
  next
    case (RDone x1 x2 x3 x4)
    then show ?case 
      apply (simp add: Get_view_Wellformed_def tps_trans_defs)
      apply (cases "cl = x1", simp_all) sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    hence "\<And>k. prefix (commit_order s k) (commit_order s' k)" by (simp add: write_commit_def)
    hence "view_of (commit_order s') (get_view s cl) = view_of (commit_order s) (get_view s cl)"
      using WCommit view_of_prefix[of "commit_order s" "commit_order s'" "get_view s cl"]
        Commit_Order_Distinct_def[of s'] Commit_Order_Superset_Get_View_def[of s]
      by (metis reach.reach_trans reach_commit_order_distinct reach_commit_order_superset_get_view)
    hence "view_of (commit_order s') (get_view s' cl) = view_of (commit_order s) (get_view s cl)"
      using WCommit by (auto simp add: write_commit_def get_view_def)
    then show ?case using WCommit
      apply (simp add: Get_view_Wellformed_def tps_trans_defs) sorry
  next
    case (CommitW x1 x2)
    then show ?case sorry
  qed (auto simp add: Get_view_Wellformed_def tps_trans_defs)
qed

lemma visTx_in_kvs_of_s_writers[simp, dest]:
  "reach tps s \<Longrightarrow>
   visTx (kvs_of_s s) ((view_of (commit_order s) (get_view s cl))) \<subseteq> kvs_writers (kvs_of_s s)"
  apply (rule visTx_in_kvs_writers, rule view_wellformed_range)
  by auto


subsection \<open>CanCommit\<close>

lemmas canCommit_defs = ET_CC.canCommit_def closed_def R_CC_def R_onK_def

lemma "kvs_writers (kvs_of_s gs) \<inter> Tn ` kvs_readers (kvs_of_s gs) = {}" sorry

lemma "read_only_Txs (kvs_of_s gs) = Tn ` kvs_readers (kvs_of_s gs)"
  apply (simp add: kvs_of_s_def) sorry \<comment> \<open>turn into invariant\<close>

lemma the_T0: "(THE i. i = 0 \<and> [T0] ! i = T0) = 0" by auto

lemma visTx_visTx': "visTx (kvs_of_s s) (view_of (commit_order s) u) = visTx' u"
  apply (simp add: view_of_def visTx_def visTx'_def) sorry

lemma closed_closed': "closed (kvs_of_s s) (view_of (commit_order s) u) r = closed' (kvs_of_s s) u r"
  by (simp add: closed_def closed'_def visTx_visTx')

lemma visTx'_subset_writers: "visTx' (get_view s cl) \<subseteq> kvs_writers (kvs_of_s s)" sorry

lemma "kvs_writers (kvs_of_s s) \<subseteq> (\<Union>k. wts_dom (wtxn_state (svrs s k)))"
  oops

lemma "kvs_readers (kvs_of_s s) \<subseteq> (\<Union>k. \<Union>(wts_rsran (wtxn_state (svrs s k))))"
  oops

abbreviation RO_le_gst :: "'v state \<Rightarrow> cl_id \<Rightarrow> txid set" where
  "RO_le_gst s cl \<equiv> {t \<in> read_only_Txs (kvs_of_s s). \<exists>sn cl'. t = Tn (Tn_cl sn cl')
    \<and> the (rtxn_rts (cls s cl') sn) \<le> gst (cls s cl)}"


definition Get_view_Closed where
  "Get_view_Closed s cl \<longleftrightarrow> (\<forall>F. ET_CC.canCommit (kvs_of_s s) (view_of (commit_order s) (get_view s cl)) F)"

lemmas Get_view_ClosedI = Get_view_Closed_def[THEN iffD2, rule_format]
lemmas Get_view_ClosedE[elim] = Get_view_Closed_def[THEN iffD1, elim_format, rule_format]

lemma reach_get_view_closed [simp, dest]: "reach tps s \<Longrightarrow> Get_view_Closed s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case apply (auto simp add: Get_view_Closed_def tps_def canCommit_defs)
     apply (metis DiffD2 read_only_Txs_def subsetD visTx'_subset_writers visTx_visTx')
    apply (rotate_tac -1) subgoal for x x' by (induction rule: rtrancl.induct,
     auto simp add: SO_def SO0_def WR_def state_init_def kvs_of_s_def visTx_def view_of_def the_T0).
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s'] get_view_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2)
    { fix x x'
      assume "(x, x') \<in> (SO \<union> \<Union> (range (WR (kvs_of_s s))))\<^sup>*"
      and "x' \<in> visTx (kvs_of_s s) (view_of (commit_order s) (get_view s' cl)) \<union> RO_le_gst s cl"
      and "txn_state (cls s x1) = Idle"
      then have "x \<in> visTx (kvs_of_s s) (view_of (commit_order s) (get_view s' cl)) \<union> RO_le_gst s cl"
        apply (induction rule: rtrancl.induct, simp_all) sorry
     }
    then show ?case apply (auto simp add: Get_view_Closed_def canCommit_defs)
      apply (metis DiffD2 read_only_Txs_def subsetD visTx'_subset_writers visTx_visTx')
      using RInvoke by (auto simp add: tps_trans_defs)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (CommitW x1 x2)
    then show ?case sorry
  qed (auto simp add: Get_view_Closed_def tps_trans_defs)
qed


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

subsection \<open>View Shift\<close>

lemma read_commit_added_txid:
  assumes "read_done cl kv_map sn u s s'"
    and "Tn (Tn_cl sn' cl) \<in> (kvs_txids (kvs_of_s s') - kvs_txids (kvs_of_s s))"
  shows "sn' = sn"
  using assms
  apply (auto simp add: read_done_def kvs_of_s_def txid_defs split: ver_state.split) sorry
  

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
  using kvs_of_s_inv[of gs a gs'] views_of_s_inv[of gs a gs'] get_view_inv[of gs a gs'] (*needed?*)
  proof (induction a)
    case (RDone cl kvt_map sn u'')
    then show ?case
    apply (auto simp add: read_done_def sim_def intro!: exI [where x="views_of_s gs' cl"])
    subgoal apply (auto simp add: ET_CC.ET_cl_txn_def t_is_fresh KvsOfS_Not_Emp_def Get_view_Closed_def)
      subgoal apply (simp add: view_wellformed_def views_of_s_def) sorry
      subgoal sorry                                                                    
      subgoal apply (auto simp add: vShift_MR_RYW_def vShift_MR_def vShift_RYW_def views_of_s_def) sorry
      sorry
      subgoal by (rule ext, simp add: read_done_def views_of_s_def)
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
