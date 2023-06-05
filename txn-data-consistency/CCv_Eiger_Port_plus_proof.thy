section \<open>Eiger Port Plus Protocol Satisfying CCv (Causal+) - Proofs and lemmas\<close>

theory CCv_Eiger_Port_plus_proof
  imports CCv_Eiger_Port_plus
begin

section \<open>Lemmas about the functions\<close>


subsection \<open>wtxns_dom lemmas\<close>

lemma wtxns_dom_eq_empty_conv [simp]: "wtxns_dom wtxns = {} \<longleftrightarrow> wtxns = wtxns_emp"
  by (auto simp: wtxns_dom_def)

lemma wtxns_domI1: "wtxns t = Prep ts v \<Longrightarrow> t \<in> wtxns_dom wtxns"
  by (simp add: wtxns_dom_def)

lemma wtxns_domI2: "wtxns t = Commit cts v rs deps \<Longrightarrow> t \<in> wtxns_dom wtxns"
  by (simp add: wtxns_dom_def)

lemma wtxns_domD: "t \<in> wtxns_dom wtxns \<Longrightarrow> (\<exists>ts v. wtxns t = Prep ts v) \<or> (\<exists>cts v rs deps. wtxns t = Commit cts v rs deps)"
  by (cases "wtxns t") (auto simp add: wtxns_dom_def)

lemma wtxns_domIff [iff, simp del, code_unfold]: "t \<in> wtxns_dom wtxns \<longleftrightarrow> wtxns t \<noteq> No_Ver"
  by (simp add: wtxns_dom_def)

lemma wtxns_dom_fun_upd [simp]:
  "wtxns_dom(wtxns(t := x)) = (if x = No_Ver then wtxns_dom wtxns - {t} else insert t (wtxns_dom wtxns))"
  by (auto simp: wtxns_dom_def)

lemma wtxns_dom_if:
  "wtxns_dom (\<lambda>x. if P x then f x else g x) = wtxns_dom f \<inter> {x. P x} \<union> wtxns_dom g \<inter> {x. \<not> P x}"
  by (auto split: if_splits)

lemma wtxns_dom_minus:
  "wtxns t = No_Ver \<Longrightarrow> wtxns_dom wtxns - insert t A = wtxns_dom wtxns - A"
  unfolding wtxns_dom_def by simp

lemma insert_prep_wtxns_dom:
  "wtxns t = Prep ts v \<Longrightarrow> insert t (wtxns_dom wtxns) = wtxns_dom wtxns"
  unfolding wtxns_dom_def by auto

lemma insert_commit_wtxns_dom:
  "wtxns t = Commit cts v rs deps \<Longrightarrow> insert t (wtxns_dom wtxns) = wtxns_dom wtxns"
  unfolding wtxns_dom_def by auto


subsection \<open>wtxns_vran lemmas\<close>

lemma wtxns_vranI1: "wtxns t = Commit cts v rs deps \<Longrightarrow> v \<in> wtxns_vran wtxns"
  apply (simp add: wtxns_vran_def)
  by (metis ver_state.sel(4) wtxns_domI2)

lemma wtxns_vranI2: "wtxns t = Prep ts v \<Longrightarrow> v \<in> wtxns_vran wtxns"
  apply (simp add: wtxns_vran_def)
  by (metis ver_state.sel(3) wtxns_domI1)

lemma wtxns_vran_empty [simp]: "wtxns_vran wtxns_emp = {}"
  by (auto simp: wtxns_vran_def)

lemma wtxns_vran_map_upd [simp]:  "wtxns t = No_Ver \<Longrightarrow>
  wtxns_vran (wtxns (t := Commit cts v rs deps)) = insert v (wtxns_vran wtxns)"
  by (auto simp add: wtxns_vran_def)

lemma finite_wtxns_vran:
  assumes "finite (wtxns_dom wtxns)"
  shows "finite (wtxns_vran wtxns)"
proof -
  have "wtxns_vran wtxns = (\<lambda>t. get_val (wtxns t)) ` wtxns_dom wtxns"
    unfolding wtxns_vran_def
    by (smt (verit) Collect_cong Setcompr_eq_image ver_state.sel wtxns_domD wtxns_domI1 wtxns_domI2)
  with \<open>finite (wtxns_dom wtxns)\<close> show ?thesis by auto
qed
      
      
subsection \<open>wtxns_rsran lemmas\<close>

lemma wtxns_rsranI: "wtxns t = Commit cts v rs deps \<Longrightarrow> rs \<subseteq> wtxns_rsran wtxns"
  apply (simp add: wtxns_rsran_def)
  by (metis (mono_tags, lifting) Sup_upper get_rs.simps(3) mem_Collect_eq wtxns_domI2)

lemma wtxns_rsran_empty [simp]: "wtxns_rsran wtxns_emp = {}"
  by (auto simp: wtxns_rsran_def)

lemma wtxns_rsran_map_upd1 [simp]:  "wtxns t = No_Ver \<Longrightarrow>
  wtxns_rsran (wtxns (t := Prep ts v)) = wtxns_rsran wtxns"
  by (auto simp add: wtxns_rsran_def)

lemma wtxns_rsran_map_upd2 [simp]:  "wtxns t = No_Ver \<Longrightarrow>
  wtxns_rsran (wtxns (t := Commit cts v rs deps)) = rs \<union> (wtxns_rsran wtxns)"
  by (auto simp add: wtxns_rsran_def)

lemma wtxns_rsran_map_upd3 [simp]:  "is_prepared (wtxns t) \<Longrightarrow>
  wtxns_rsran (wtxns (t := Commit cts v rs deps)) = rs \<union> (wtxns_rsran wtxns)"
  apply (auto simp add: wtxns_rsran_def)
  by (metis empty_iff get_rs.simps(2) is_prepared.elims(2) wtxns_domIff)

lemma wtxns_rsran_map_upd4 [simp]:  "wtxns t_wr = Commit cts v rs deps \<Longrightarrow>
  wtxns_rsran (wtxns (t_wr := Commit cts v (insert t rs) deps)) = insert t (wtxns_rsran wtxns)"
  apply (auto simp add: wtxns_rsran_def)
  apply (metis get_rs.simps(3) wtxns_domI2)
  by (metis get_rs.simps(3) insertI2 wtxns_domIff)

subsection \<open>Helper functions lemmas\<close>

lemma arg_max_exI:
  fixes f :: "'a \<Rightarrow> 'b :: linorder"
  assumes "finite {y. \<exists>x. P x \<and> y = f x}" and "P t"
  shows "\<exists>x. is_arg_max f P x"
proof -
  obtain x where "P x" "Max {y. \<exists>x. P x \<and> y = f x} = f x"
    using Max_in assms by auto
  then show ?thesis apply (simp add: is_arg_max_def)
    by (smt Max_ge assms(1) leD mem_Collect_eq)
qed

lemma P_is_arg_max: "is_arg_max f P x \<Longrightarrow> P x"
  by (simp add: is_arg_max_def)

lemma P_arg_max:
  "\<exists>x. is_arg_max f P x \<Longrightarrow> P (arg_max f P)"
  apply (rule P_is_arg_max[of f])
  apply (simp add: arg_max_def)
  by (simp add: someI_ex)

lemma P_Q_arg_max:
  "\<exists>x. is_arg_max f (\<lambda>x. P x \<and> Q x) x \<Longrightarrow> P (arg_max f (\<lambda>x. P x \<and> Q x))"
  using P_arg_max[of f "\<lambda>x. P x \<and> Q x"] by auto

lemma add_to_readerset_wtxns_dom:
  "wtxns_dom (add_to_readerset wtxns t t') = wtxns_dom wtxns"
  by (auto simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_wtxns_rsran:
  assumes "is_committed (wtxns t_wr)" (* later use read_at_is_committed to fulfill this *)
  shows "wtxns_rsran (add_to_readerset wtxns t t_wr) = insert t (wtxns_rsran (wtxns))"
  using assms
  by (auto simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_no_ver_inv:
  "add_to_readerset wtxns t t' t'' = No_Ver \<longleftrightarrow> wtxns t'' = No_Ver"
  by (simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_prep_inv:
  "add_to_readerset wtxns t t' t'' = Prep ts v \<longleftrightarrow> wtxns t'' = Prep ts v"
  by (simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_commit:
  "add_to_readerset wtxns t t' t'' = Commit cts v rs deps \<Longrightarrow>
    \<exists>rs'. wtxns t'' = Commit cts v rs' deps"
  apply (simp add: add_to_readerset_def)
  by (cases "wtxns t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_commit_subset:
  "add_to_readerset wtxns t t' t'' = Commit cts v rs deps \<Longrightarrow>
    \<exists>rs'. wtxns t'' = Commit cts v rs' deps \<and> rs' \<subseteq> rs"
  apply (simp add: add_to_readerset_def)
  by (cases "wtxns t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_commit':
  "wtxns t'' = Commit cts v rs' deps \<Longrightarrow>
    \<exists>rs. add_to_readerset wtxns t t' t'' = Commit cts v rs deps"
  apply (simp add: add_to_readerset_def)
  by (cases "wtxns t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_commit'_subset:
  "wtxns t'' = Commit cts v rs' deps \<Longrightarrow>
    \<exists>rs. add_to_readerset wtxns t t' t'' = Commit cts v rs deps \<and> rs' \<subseteq> rs"
  apply (simp add: add_to_readerset_def)
  by (cases "wtxns t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_upd:
  assumes "wtxns' = add_to_readerset wtxns t t_wr"
    and "t' \<noteq> t_wr"
  shows "wtxns' t' = wtxns t'"
  using assms
  by (simp add: add_to_readerset_def split: ver_state.split)

lemma ran_map_upd_None_finite:
  "finite (ran m) \<Longrightarrow> finite (ran (m (a := None)))"
  apply (simp add: ran_def)
  by (smt (verit) Collect_mono_iff rev_finite_subset)

lemma pending_wtxns_ts_empty:
  "pending_wtxns_ts (wtxn_state (svrs s k)) = {} \<longleftrightarrow>
    (\<forall>t. \<exists>cts v rs deps. wtxn_state (svrs s k) t \<in> {No_Ver, Commit cts v rs deps})"
  apply (auto simp add: pending_wtxns_ts_def)
  apply (metis get_rs.elims)
  by (metis ver_state.distinct(1) ver_state.distinct(5))

lemma pending_wtxns_ts_non_empty:
  assumes "wtxn_state (svrs s k) t \<noteq> No_Ver"
    and "\<forall>cts v rs deps. wtxn_state (svrs s k) t \<noteq> Commit cts v rs deps"
  shows "pending_wtxns_ts (wtxn_state (svrs s k)) \<noteq> {}"
  using assms apply (auto simp add: pending_wtxns_ts_def)
  by (meson get_rs.elims)

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
  shows "finite (pending_wtxns_ts ((wtxn_state (svrs s k)) (t := Commit cts v rs deps)))"
  using assms
  by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def)

lemma pending_wtxns_adding_ub:
  assumes "\<forall>ts \<in> pending_wtxns_ts (wtxn_state (svrs s k)). ts \<le> clk"
  shows "\<forall>ts \<in> pending_wtxns_ts ((wtxn_state (svrs s k)) (t := Prep clk v)). ts \<le> clk"
  using assms by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def)

lemma pending_wtxns_removing_ub:
  assumes "\<forall>ts \<in> pending_wtxns_ts (wtxn_state (svrs s k)). ts \<le> clk"
  shows "\<forall>ts \<in> pending_wtxns_ts ((wtxn_state (svrs s k)) (t := Commit cts v rs deps)). ts \<le> clk"
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
  shows "pending_wtxns_ts ((wtxn_state (svrs s k)) (t := Commit cts v rs deps)) =
          pending_wtxns_ts (wtxn_state (svrs s k)) \<or>
         pending_wtxns_ts ((wtxn_state (svrs s k)) (t := Commit cts v rs deps)) =
          Set.remove clk (pending_wtxns_ts (wtxn_state (svrs s k)))"
  using assms apply (auto simp add: pending_wtxns_ts_def)
  by (metis ver_state.inject(1))+

lemma other_prep_t_inv:
  assumes "wtxn_state (svrs s k) t = Prep prep_t v"
    and "t \<noteq> t'"
  shows "prep_t \<in> pending_wtxns_ts ((wtxn_state (svrs s k))(t' := b))"
  using assms
  by (auto simp add: pending_wtxns_ts_def)

lemma view_of_prefix:
  assumes "\<And>k. prefix (corder k) (corder' k)"
    and "\<And>k. distinct (corder' k)"
    and "\<And>k. u `` {k} \<subseteq> set (corder k)"
  shows "view_of corder u = view_of corder' u"
  unfolding view_of_def
proof (rule ext, rule Collect_eqI, rule iffI)
  fix k pos
  assume *: "\<exists>t. pos = (THE i. i < length (corder k) \<and> corder k ! i = t) \<and> (k, t) \<in> u \<and> t \<in> set (corder k)"
  show "\<exists>t. pos = (THE i. i < length (corder' k) \<and> corder' k ! i = t) \<and> (k, t) \<in> u \<and> t \<in> set (corder' k)"
  proof -
    from assms(1) obtain zs where p: "corder k @ zs = corder' k" using prefixE by metis
    from * obtain tid where **: "(k, tid) \<in> u" "tid \<in> set (corder k)"
      "pos = (THE i. i < length (corder k) \<and> corder k ! i = tid)" by blast
    from \<open>tid \<in> set (corder k)\<close> obtain i
      where the_i: "i < length (corder k) \<and> corder k ! i = tid" by (meson in_set_conv_nth)
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
  assume *: "\<exists>t. pos = (THE i. i < length (corder' k) \<and> corder' k ! i = t) \<and> (k, t) \<in> u \<and> t \<in> set (corder' k)"
  show "\<exists>t. pos = (THE i. i < length (corder k) \<and> corder k ! i = t) \<and> (k, t) \<in> u \<and> t \<in> set (corder k)"
  proof -
    from assms(1) obtain zs where p: "corder k @ zs = corder' k" using prefixE by metis
    from * obtain tid where **: "(k, tid) \<in> u" "tid \<in> set (corder' k)"
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

lemma get_ctx_step:
  assumes "txn_state (cls s cl) = RtxnInProg keys kvt_map"
    and "kvt_map k = None"
    and "txn_state (cls s' cl) = RtxnInProg keys (kvt_map (k \<mapsto> (v, t)))"
    and "wtxn_state (svrs s k) t = Commit cts v rs deps"
    and "\<And>k t. wtxn_state (svrs s' k) t = wtxn_state (svrs s k) t"
  shows "get_ctx s' (kvt_map (k \<mapsto> (v, t))) = get_ctx s kvt_map \<union> (insert (k, t) deps)"
  using assms
  apply (auto simp add: get_ctx_def)
  apply blast
  apply blast
  apply blast
  apply blast
  apply (metis insertI1 not_None_eq)
  by (metis insertCI not_None_eq)

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

lemma reach_pend_wt_ub [simp]: "reach tps s \<Longrightarrow> Pend_Wt_UB s svr"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Pend_Wt_UB_def tps_defs pending_wtxns_ts_def split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: Pend_Wt_UB_def tps_trans_defs pending_wtxns_ts_def)
      by (meson add_to_readerset_prep_inv le_SucI le_trans max.cobounded1)
  next
    case (PrepW x1 x2 x3)
    then show ?case
      apply (auto simp add: Pend_Wt_UB_def tps_trans_defs pending_wtxns_ts_def)
      by (meson le_Suc_eq max.coboundedI1)
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: Pend_Wt_UB_def tps_trans_defs pending_wtxns_ts_def split: if_split_asm)
      by (meson le_Suc_eq max.coboundedI1 notin_set_remove1)
  qed (auto simp add: Pend_Wt_UB_def tps_trans_defs)
qed


definition Finite_Pend_Inv where
  "Finite_Pend_Inv s svr \<longleftrightarrow> finite (pending_wtxns_ts (wtxn_state (svrs s svr)))"

lemmas Finite_Pend_InvI = Finite_Pend_Inv_def[THEN iffD2, rule_format]
lemmas Finite_Pend_InvE[elim] = Finite_Pend_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_finitepending [simp]: "reach tps s \<Longrightarrow> Finite_Pend_Inv s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Finite_Pend_Inv_def tps_defs pending_wtxns_ts_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x71 x72 x73 x74)
    then show ?case
      by (auto simp add: Finite_Pend_Inv_def tps_trans_defs finite_pending_wtxns_rtxn)
  next
    case (PrepW x81 x82 x83)
    then show ?case
      by (auto simp add: Finite_Pend_Inv_def tps_trans_defs finite_pending_wtxns_adding)
  next
    case (CommitW x91 x92)
    then show ?case
      by (auto simp add: Finite_Pend_Inv_def tps_trans_defs finite_pending_wtxns_removing)
  qed (auto simp add: Finite_Pend_Inv_def tps_trans_defs)
qed


definition Clk_le_Lst where
  "Clk_le_Lst s k \<longleftrightarrow> lst (svrs s k) \<le> clock (svrs s k)"

lemmas Clk_le_LstI = Clk_le_Lst_def[THEN iffD2, rule_format]
lemmas Clk_le_LstE[elim] = Clk_le_Lst_def[THEN iffD1, elim_format, rule_format]

lemma reach_clock_lst_inv [simp, dest]: "reach tps s \<Longrightarrow> Clk_le_Lst s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Clk_le_Lst_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (CommitW x91 x92 x93 x94)
    then show ?case
      apply (auto simp add: Clk_le_Lst_def tps_trans_defs split: if_split_asm)
      by (metis (no_types, opaque_lifting) Finite_Pend_Inv_def Min_le_iff Pend_Wt_UB_def emptyE
          finite_pending_wtxns_removing le_SucI le_max_iff_disj pending_wtxns_removing_ub
          reach_finitepending reach_pend_wt_ub)
  qed (auto simp add: Clk_le_Lst_def tps_trans_defs)
qed

definition Pend_Wt_LB where
  "Pend_Wt_LB s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns_ts (wtxn_state (svrs s svr)). lst (svrs s svr) \<le> ts)"

lemmas Pend_Wt_LBI = Pend_Wt_LB_def[THEN iffD2, rule_format]
lemmas Pend_Wt_LBE[elim] = Pend_Wt_LB_def[THEN iffD1, elim_format, rule_format]

lemma reach_pend_wt_lb [simp]: "reach tps s \<Longrightarrow> Pend_Wt_LB s svr"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Pend_Wt_LB_def tps_defs )
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4)
    then show ?case by (auto simp add: Pend_Wt_LB_def tps_trans_defs pending_wtxns_rtxn)
  next
    case (PrepW x1 x2 x3)
    then show ?case by (auto simp add: Pend_Wt_LB_def tps_trans_defs pending_wtxns_adding)
  next
    case (CommitW x1 x2 x3 x4 x5)
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
  case (RegR x1 x2 x3 x4)
  then show ?case
  apply (auto simp add: tps_trans_defs pending_wtxns_ts_def)
    by (smt (z3) Collect_cong add_to_readerset_prep_inv nat_le_linear)
next
  case (PrepW x1 x2 x3)
  then show ?case apply (auto simp add: prepare_write_def Pend_Wt_UB_def Finite_Pend_Inv_def)
    using Min_insert_larger[of "pending_wtxns_ts (wtxn_state (svrs s x1))"
        "pending_wtxns_ts (wtxn_state (svrs s' x1))" "clock (svrs s x1)"]
      pending_wtxns_adding [of s x1]
    by (cases "k = x1"; auto simp add: pending_wtxns_ts_def)
next
  case (CommitW x1 x2 x3 x4 x5)
  then show ?case
    apply (auto simp add: commit_write_def Finite_Pend_Inv_def fold_pending_wtxns_fun_upd)
    by (metis Min.coboundedI Min_in Min_remove empty_iff pending_wtxns_removing is_prepared.elims(2)
        ver_state.sel(3))
  qed (auto simp add: tps_trans_defs pending_wtxns_ts_def)


lemma lst_monotonic:
  assumes "state_trans s e s'"
    and "Clk_le_Lst s svr" and "Finite_Pend_Inv s svr"
    and "Pend_Wt_LB s svr"
  shows "lst (svrs s' svr) \<ge> lst (svrs s svr)"
  using assms
  proof (induction e)
    case (CommitW k t)
    then show ?case
      apply (auto simp add: commit_write_def Clk_le_Lst_def Finite_Pend_Inv_def Pend_Wt_LB_def 
                  split: if_split_asm)
      by (metis Min_in empty_iff finite_pending_wtxns_removing member_remove pending_wtxns_removing
          is_prepared.elims(2) ver_state.sel(3))
  qed (auto simp add: tps_trans_defs)

definition Lst_map_le_Lst where
  "Lst_map_le_Lst s cl k \<longleftrightarrow> (lst_map (cls s cl) k \<le> lst (svrs s k))"
                                                           
lemmas Lst_map_le_LstI = Lst_map_le_Lst_def[THEN iffD2, rule_format]
lemmas Lst_map_le_LstE[elim] = Lst_map_le_Lst_def[THEN iffD1, elim_format, rule_format]

lemma reach_lst_map_le_lst [simp]: "reach tps s \<Longrightarrow> Lst_map_le_Lst s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Lst_map_le_Lst_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case using lst_monotonic[of s "CommitW x1 x2 x3 x4 x5" s' x1]
      apply (auto simp add: Lst_map_le_Lst_def tps_trans_defs)
      by (smt (z3) all_not_in_conv le_trans)
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
    (\<forall>kv_map cts deps. txn_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map deps} \<longrightarrow>
      finite (dom (kv_map)))"
                                                           
lemmas Finite_Dom_Kv_mapI = Finite_Dom_Kv_map_def[THEN iffD2, rule_format]
lemmas Finite_Dom_Kv_mapE[elim] = Finite_Dom_Kv_map_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_finite_dom_kv_map [simp]: "reach tps s \<Longrightarrow> Finite_Dom_Kv_map s cl"
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
         
lemma reach_finite_lst_map_ran [simp]: "reach tps s \<Longrightarrow> Finite_Lst_map_Ran s cl"
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
    case (WDone x1 x2)
    then show ?case apply (auto simp add: Finite_Lst_map_Ran_def tps_trans_defs)
       apply (meson image_mono rev_finite_subset subset_UNIV)
        using Finite_Dom_Kv_map_def[of s x1] by (simp add: image_def dom_def)
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

definition Gst_le_Min_Lst_map where
  "Gst_le_Min_Lst_map s cl \<longleftrightarrow> (gst (cls s cl) \<le> Min (range (lst_map (cls s cl))))"
                                                           
lemmas Gst_le_Min_Lst_mapI = Gst_le_Min_Lst_map_def[THEN iffD2, rule_format]
lemmas Gst_le_Min_Lst_mapE[elim] = Gst_le_Min_Lst_map_def[THEN iffD1, elim_format, rule_format]

lemma reach_gst_le_min_lst_map [simp]: "reach tps s \<Longrightarrow> Gst_le_Min_Lst_map s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Gst_le_Min_Lst_map_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Read x1 x2 x3 x4)
    then show ?case using lst_map_min_monotonic[of s "Read x1 x2 x3 x4" s' x1]
      apply (simp add: Gst_le_Min_Lst_map_def tps_trans_defs)
      by (smt (z3) Read.prems(1) le_trans reach.reach_trans reach_finite_lst_map_ran)
  next
    case (WDone x1 x2)
    then show ?case using lst_map_min_monotonic[of s "WDone x1 x2" s' x1]
      apply (simp add: Gst_le_Min_Lst_map_def tps_trans_defs)
      by (smt (z3) WDone.prems(1) le_trans reach.reach_trans reach_finite_lst_map_ran)
  qed (auto simp add: Gst_le_Min_Lst_map_def tps_trans_defs)
qed

lemma gst_monotonic:
  assumes "state_trans s e s'"
    and "Gst_le_Min_Lst_map s cl"
  shows "gst (cls s' cl) \<ge> gst (cls s cl)"
  using assms unfolding Gst_le_Min_Lst_map_def
  by (induction e) (auto simp add: tps_trans_defs)

definition Gst_le_Lst_map where
  "Gst_le_Lst_map s cl k \<longleftrightarrow> (gst (cls s cl) \<le> lst_map (cls s cl) k)"
                                                           
lemmas Gst_le_Lst_mapI = Gst_le_Lst_map_def[THEN iffD2, rule_format]
lemmas Gst_le_Lst_mapE[elim] = Gst_le_Lst_map_def[THEN iffD1, elim_format, rule_format]

lemma reach_gst_le_lst [simp]: "reach tps s \<Longrightarrow> Gst_le_Lst_map s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Gst_le_Lst_map_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: Gst_le_Lst_map_def tps_trans_defs)
      by (meson Finite_Lst_map_Ran_def Min_le rangeI reach_finite_lst_map_ran)
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: Gst_le_Lst_map_def tps_trans_defs)
      by (meson Lst_map_le_Lst_def le_trans reach_lst_map_le_lst)
  next
    case (WDone x1 x2)
    then show ?case apply (simp add: Gst_le_Lst_map_def tps_trans_defs)
      by (meson Lst_map_le_Lst_def le_trans reach_lst_map_le_lst)
  qed (auto simp add: Gst_le_Lst_map_def tps_trans_defs)
qed

definition Pend_Wt_Inv where
  "Pend_Wt_Inv s k \<longleftrightarrow> (\<forall>prep_t. prep_t \<in> pending_wtxns_ts (wtxn_state (svrs s k))
    \<longleftrightarrow> (\<exists>t v. wtxn_state (svrs s k) t = Prep prep_t v))"
                                                           
lemmas Pend_Wt_InvI = Pend_Wt_Inv_def[THEN iffD2, rule_format]
lemmas Pend_Wt_InvE[elim] = Pend_Wt_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_pend_wt_inv [simp]: "reach tps s \<Longrightarrow> Pend_Wt_Inv s cl"
  by (auto simp add: Pend_Wt_Inv_def tps_def pending_wtxns_ts_def)

definition Lst_Lt_Pts where
  "Lst_Lt_Pts s k \<longleftrightarrow> (\<forall>t prep_t v. wtxn_state (svrs s k) t = Prep prep_t v \<longrightarrow> lst (svrs s k) \<le> prep_t)"
                                                           
lemmas Lst_Lt_PtsI = Lst_Lt_Pts_def[THEN iffD2, rule_format]
lemmas Lst_Lt_PtsE[elim] = Lst_Lt_Pts_def[THEN iffD1, elim_format, rule_format]

lemma reach_lst_lt_pts [simp]: "reach tps s \<Longrightarrow> Lst_Lt_Pts s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Lst_Lt_Pts_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
  case (RegR x1 x2 x3 x4)
  then show ?case apply (auto simp add: Lst_Lt_Pts_def tps_trans_defs)
    by (meson add_to_readerset_prep_inv)
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Lst_Lt_Pts_def tps_trans_defs)
      apply (metis emptyE other_prep_t_inv)
      by (metis Finite_Pend_Inv_def Min.coboundedI finite_pending_wtxns_removing other_prep_t_inv
          reach_finitepending)
  qed(auto simp add: Lst_Lt_Pts_def tps_trans_defs)
qed

definition Finite_Wtxns_Dom where
  "Finite_Wtxns_Dom s k \<longleftrightarrow> finite (wtxns_dom (wtxn_state (svrs s k)))"

lemmas Finite_Wtxns_DomI = Finite_Wtxns_Dom_def[THEN iffD2, rule_format]
lemmas Finite_Wtxns_DomE[elim] = Finite_Wtxns_Dom_def[THEN iffD1, elim_format, rule_format]

lemma reach_finite_wtxns_dom [simp]: "reach tps s \<Longrightarrow> Finite_Wtxns_Dom s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case apply (auto simp add: Finite_Wtxns_Dom_def tps_defs)
    by (metis finite.emptyI wtxns_dom_eq_empty_conv)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4)
    then show ?case
      by (auto simp add: Finite_Wtxns_Dom_def tps_trans_defs add_to_readerset_def
               split: ver_state.split)
  qed (auto simp add: Finite_Wtxns_Dom_def tps_trans_defs)
qed

definition Finite_Wtxns_rsran where
  "Finite_Wtxns_rsran s k \<longleftrightarrow> finite (wtxns_rsran (wtxn_state (svrs s k)))"

lemmas Finite_Wtxns_rsranI = Finite_Wtxns_rsran_def[THEN iffD2, rule_format]
lemmas Finite_Wtxns_rsranE[elim] = Finite_Wtxns_rsran_def[THEN iffD1, elim_format, rule_format]

lemma reach_finite_wtxns_rsran [simp]: "reach tps s \<Longrightarrow> Finite_Wtxns_rsran s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Finite_Wtxns_rsran_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4)
    then show ?case
      by (auto simp add: Finite_Wtxns_rsran_def tps_trans_defs add_to_readerset_def
               split: ver_state.split)
  qed (auto simp add: Finite_Wtxns_rsran_def tps_trans_defs)
qed


subsection \<open>Invariants about kvs, global ts and init version v0\<close>

definition Kvs_Not_Emp where
  "Kvs_Not_Emp s \<longleftrightarrow> (\<forall>k. wtxn_state (svrs s k) \<noteq> wtxns_emp)"

lemmas Kvs_Not_EmpI = Kvs_Not_Emp_def[THEN iffD2, rule_format]
lemmas Kvs_Not_EmpE[elim] = Kvs_Not_Emp_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_not_emp [simp]: "reach tps s \<Longrightarrow> Kvs_Not_Emp s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    apply (auto simp add: Kvs_Not_Emp_def tps_defs)
    by (metis fun_upd_apply ver_state.distinct(3))
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: Kvs_Not_Emp_def tps_trans_defs)
      by (metis add_to_readerset_wtxns_dom wtxns_domIff)
  next
    case (PrepW x1 x2 x3)
    then show ?case
      apply (auto simp add: Kvs_Not_Emp_def tps_trans_defs)
      by (metis fun_upd_same ver_state.distinct(1))
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: Kvs_Not_Emp_def tps_trans_defs)
      by (metis fun_upd_same ver_state.distinct(3))
  qed (auto simp add: Kvs_Not_Emp_def tps_trans_defs)
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

lemma reach_kvs_of_s_not_emp [simp]: "reach tps s \<Longrightarrow> KvsOfS_Not_Emp s"
  apply (auto simp add: KvsOfS_Not_Emp_def Commit_Order_T0_def kvs_of_s_def)
  by (smt (verit) Commit_Order_T0_def empty_iff empty_set reach_commit_order_t0)


definition Init_Ver_Inv where
  "Init_Ver_Inv s k \<longleftrightarrow> (\<exists>rs. wtxn_state (svrs s k) T0 = Commit 0 undefined rs {})"

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
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Init_Ver_Inv_def tps_trans_defs)
      by (meson add_to_readerset_commit')
  qed (auto simp add: Init_Ver_Inv_def tps_trans_defs)
qed


subsection \<open>Invariant about server and client state relations and (future and past) transactions ids\<close>

\<comment> \<open>Value of rtxn_rts for current and future transaction ids\<close>
definition CFTid_Rtxn_Inv where
  "CFTid_Rtxn_Inv s cl \<longleftrightarrow> (\<forall>n. n \<ge> txn_sn (cls s cl) \<longrightarrow> rtxn_rts s (Tn_cl n cl) = None)"

lemmas CFTid_Rtxn_InvI = CFTid_Rtxn_Inv_def[THEN iffD2, rule_format]
lemmas CFTid_Rtxn_InvE[elim] = CFTid_Rtxn_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_cftid_rtxn_inv [simp]: "reach tps s \<Longrightarrow> CFTid_Rtxn_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: CFTid_Rtxn_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case by (induction e) (auto simp add: CFTid_Rtxn_Inv_def tps_trans_defs)
qed

\<comment> \<open>Value of wtxn_state for future transaction ids\<close>
definition FTid_Wtxn_Inv where
  "FTid_Wtxn_Inv s cl \<longleftrightarrow> (\<forall>n k. n > txn_sn (cls s cl) \<longrightarrow> wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver)"

lemmas FTid_Wtxn_InvI = FTid_Wtxn_Inv_def[THEN iffD2, rule_format]
lemmas FTid_Wtxn_InvE[elim] = FTid_Wtxn_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_ftid_wtxn_inv [simp, dest]: "reach tps s \<Longrightarrow> FTid_Wtxn_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FTid_Wtxn_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x71 x72 x73 x74)
    then show ?case
      apply (auto simp add: tps_trans_defs FTid_Wtxn_Inv_def)
      by (metis add_to_readerset_no_ver_inv)
  qed (auto simp add: tps_trans_defs FTid_Wtxn_Inv_def)
qed

\<comment> \<open>Next 4 invariants: txn_state + txn_sn \<longrightarrow> wtxn_state\<close>
definition Cl_Rtxn_Inv where
  "Cl_Rtxn_Inv s cl \<longleftrightarrow> (\<forall>k keys kvm. txn_state (cls s cl) \<in> {Idle, RtxnInProg keys kvm}
    \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) = No_Ver)"

lemmas Cl_Rtxn_InvI = Cl_Rtxn_Inv_def[THEN iffD2, rule_format]
lemmas Cl_Rtxn_InvE[elim] = Cl_Rtxn_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_rtxn_inv [simp, dest]: "reach tps s \<Longrightarrow> Cl_Rtxn_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Cl_Rtxn_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Cl_Rtxn_Inv_def tps_trans_defs)
      by (metis add_to_readerset_no_ver_inv)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Cl_Rtxn_Inv_def tps_trans_defs)
      by (metis get_cl_wtxn.simps(2) state_txn.distinct(3) state_txn.distinct(7))
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Cl_Rtxn_Inv_def tps_trans_defs)
      by force
  qed (auto simp add: Cl_Rtxn_Inv_def tps_trans_defs)
qed

definition Cl_Wtxn_Idle_Svr where
  "Cl_Wtxn_Idle_Svr s \<longleftrightarrow>
    (\<forall>cl k cts kv_map deps. txn_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map deps}
        \<and> kv_map k = None \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) = No_Ver)"

lemmas Cl_Wtxn_Idle_SvrI = Cl_Wtxn_Idle_Svr_def[THEN iffD2, rule_format]
lemmas Cl_Wtxn_Idle_SvrE[elim] = Cl_Wtxn_Idle_Svr_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_wtxn_idle_svr [simp]: "reach tps s \<Longrightarrow> Cl_Wtxn_Idle_Svr s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Cl_Wtxn_Idle_Svr_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Cl_Wtxn_Idle_Svr_def tps_trans_defs)
      by (metis add_to_readerset_no_ver_inv)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Cl_Wtxn_Idle_Svr_def tps_trans_defs)
      by (smt (z3) domIff get_cl_wtxn.simps(2) state_txn.distinct(11) state_txn.inject(2))
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Cl_Wtxn_Idle_Svr_def tps_trans_defs)
      by force
  qed (auto simp add: Cl_Wtxn_Idle_Svr_def tps_trans_defs, blast?)
qed

definition Cl_Prep_Inv where
  "Cl_Prep_Inv s \<longleftrightarrow> (\<forall>cl k kvm. \<exists>prep_t v. txn_state (cls s cl) = WtxnPrep kvm
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) \<in> {No_Ver, Prep prep_t v}) \<and>
    (k \<notin> dom kvm \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) = No_Ver))"

lemmas Cl_Prep_InvI = Cl_Prep_Inv_def[THEN iffD2, rule_format]
lemmas Cl_Prep_InvE[elim] = Cl_Prep_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_prep_inv [simp]: "reach tps s \<Longrightarrow> Cl_Prep_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Cl_Prep_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (WInvoke x1 x2)
    then show ?case by (simp add: Cl_Prep_Inv_def tps_trans_defs, blast)
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Cl_Prep_Inv_def tps_trans_defs)
      by (smt (verit) add_to_readerset_wtxns_dom add_to_readerset_prep_inv wtxns_domIff)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Cl_Prep_Inv_def tps_trans_defs)
      by (metis domI get_cl_wtxn.simps(2) state_txn.inject(2))
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Cl_Prep_Inv_def tps_trans_defs)
      using get_cl_wtxn.simps(2) state_txn.distinct(11) state_txn.simps(19) by force
  qed (auto simp add: Cl_Prep_Inv_def tps_trans_defs)
qed

definition Cl_Commit_Inv where
  "Cl_Commit_Inv s \<longleftrightarrow> (\<forall>cl k cts kvm. \<exists>prep_t v rs deps. txn_state (cls s cl) = WtxnCommit cts kvm deps
    \<longrightarrow> (kvm k = Some v \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) \<in> {Prep prep_t v, Commit cts v rs deps}) \<and>
    (kvm k = None \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) = No_Ver))"

lemmas Cl_Commit_InvI = Cl_Commit_Inv_def[THEN iffD2, rule_format]
lemmas Cl_Commit_InvE[elim] = Cl_Commit_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_commit_inv [simp]: "reach tps s \<Longrightarrow> Cl_Commit_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Cl_Commit_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Cl_Commit_Inv_def tps_trans_defs)
      by blast
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Cl_Commit_Inv_def tps_trans_defs)
      by (smt add_to_readerset_commit add_to_readerset_no_ver_inv add_to_readerset_prep_inv
          ver_state.exhaust ver_state.inject(2))
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Cl_Commit_Inv_def tps_trans_defs)
      by (smt (verit) fun_upd_other get_cl_wtxn.simps(2) state_txn.distinct(11))
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Cl_Commit_Inv_def tps_trans_defs)
      using fun_upd_same get_cl_wtxn.simps(2) state_txn.simps(19) ver_state.distinct(1)
        ver_state.simps(10) by force
  qed (auto simp add: Cl_Commit_Inv_def tps_trans_defs)
qed

\<comment> \<open>Next 2 invariants: wtxn_state \<longrightarrow> txn_state\<close>
definition Svr_Prep_Inv where
  "Svr_Prep_Inv s \<longleftrightarrow> (\<forall>k t ts v. wtxn_state (svrs s k) t = Prep ts v  \<and> is_curr_wt s t \<longrightarrow>
    (\<exists>cts kv_map deps.
      txn_state (cls s (get_cl_wtxn t)) \<in> {WtxnPrep  kv_map, WtxnCommit cts kv_map deps} \<and>
      k \<in> dom kv_map))"

lemmas Svr_Prep_InvI = Svr_Prep_Inv_def[THEN iffD2, rule_format]
lemmas Svr_Prep_InvE[elim] = Svr_Prep_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_svr_prep_inv [simp]: "reach tps s \<Longrightarrow> Svr_Prep_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Svr_Prep_Inv_def tps_defs split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis state_txn.distinct(3) state_txn.distinct(5))
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis state_txn.distinct(7) state_txn.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis FTid_Wtxn_Inv_def get_cl_wtxn.simps(2) get_sn_wtxn.cases get_sn_wtxn.simps(2)
          lessI reach_ftid_wtxn_inv ver_state.distinct(1))
  next
    case (WInvoke x1 x2)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis state_txn.distinct(3) state_txn.distinct(5))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis (lifting) state_txn.distinct(11) state_txn.inject(2))
  next
    case (WDone x1 x2)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis (lifting) FTid_Wtxn_Inv_def get_cl_wtxn.elims get_sn_wtxn.simps(2) lessI
          reach_ftid_wtxn_inv reach_trans.hyps(2) ver_state.distinct(1))
  next
    case (RegR x1 x2 x3 x4)
    then show ?case by (simp add: Svr_Prep_Inv_def tps_trans_defs add_to_readerset_prep_inv)
  qed (auto simp add: Svr_Prep_Inv_def tps_trans_defs)
qed


definition Svr_Commit_Inv where
  "Svr_Commit_Inv s \<longleftrightarrow> (\<forall>k t cts v rs deps. 
    wtxn_state (svrs s k) t = Commit cts v rs deps \<and> is_curr_wt s t \<longrightarrow> 
      (\<exists>kv_map. txn_state (cls s (get_cl_wtxn t)) = WtxnCommit cts kv_map deps \<and> k \<in> dom kv_map))"

lemmas Svr_Commit_InvI = Svr_Commit_Inv_def[THEN iffD2, rule_format]
lemmas Svr_Commit_InvE[elim] = Svr_Commit_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_svr_commit_inv [simp]: "reach tps s \<Longrightarrow> Svr_Commit_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Svr_Commit_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis state_txn.distinct(5))
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis state_txn.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis FTid_Wtxn_Inv_def get_cl_wtxn.elims get_sn_wtxn.simps(2) lessI
          reach_ftid_wtxn_inv ver_state.distinct(3))
  next
    case (WInvoke x1 x2)
    then show ?case apply (simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis state_txn.distinct(5))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis (lifting) state_txn.distinct(11))
  next
    case (WDone x1 x2)
    then show ?case apply (auto simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis (lifting) FTid_Wtxn_Inv_def get_cl_wtxn.elims get_sn_wtxn.simps(2)
          lessI reach_ftid_wtxn_inv ver_state.distinct(3))
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (auto simp add: Svr_Commit_Inv_def tps_trans_defs)
    by (metis add_to_readerset_commit)
  qed (auto simp add: Svr_Commit_Inv_def tps_trans_defs)
qed


\<comment> \<open>Values of wtxn_state and rtxn_rts for past transaction ids\<close>
definition PTid_Inv where
  "PTid_Inv s cl \<longleftrightarrow> (\<forall>k. \<forall>n < txn_sn (cls s cl).
   (wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver) \<or>
   (rtxn_rts s (Tn_cl n cl) = None \<and> (\<exists>cts v rs deps. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts v rs deps)))"

lemmas PTid_InvI = PTid_Inv_def[THEN iffD2, rule_format]
lemmas PTid_InvE[elim] = PTid_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_ptid_inv [simp]: "reach tps s \<Longrightarrow> PTid_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: PTid_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RDone x31 x32 x33 x34)
    then show ?case
      apply (auto simp add: tps_trans_defs PTid_Inv_def)
      apply blast
      by (metis not_less_less_Suc_eq)+
  next
    case (WDone x61 x62)
    then show ?case
      apply (auto simp add: tps_trans_defs PTid_Inv_def)
      subgoal for _ _ _ n apply (cases "n = txn_sn (cls s x61)")
        apply (metis CFTid_Rtxn_Inv_def eq_imp_le reach_cftid_rtxn_inv)
        by (metis less_SucE)
      subgoal for _ _ k apply (cases "x62 k = None")
        apply (metis (lifting) Cl_Wtxn_Idle_Svr_def insertCI less_antisym reach_cl_wtxn_idle_svr)
        by (metis (no_types, lifting) domIff less_antisym)
      done
  next
    case (RegR x71 x72 x73 x74)
    then show ?case
      apply (auto simp add: tps_trans_defs PTid_Inv_def)
      apply (metis add_to_readerset_no_ver_inv)
      by (metis add_to_readerset_commit' add_to_readerset_no_ver_inv)
  qed (auto simp add: tps_trans_defs PTid_Inv_def)
qed

lemma other_sn_idle:  
  assumes "FTid_Wtxn_Inv s cl" and "PTid_Inv s cl"
    and "get_cl_txn t = cl" and "get_sn_txn t \<noteq> txn_sn (cls s cl)"
  shows "\<And>k. \<exists>cts v rs deps. wtxn_state (svrs s k) (Tn t) \<in> {No_Ver, Commit cts v rs deps}"
  using assms
  apply (auto simp add: FTid_Wtxn_Inv_def PTid_Inv_def)
  apply (cases "get_sn_txn t > txn_sn (cls s cl)")
  apply (metis txid0.collapse)
  by (metis txid0.collapse linorder_cases)

definition Rtxn_Wtxn_No_Ver where
  "Rtxn_Wtxn_No_Ver s cl \<longleftrightarrow>
    (\<forall>n ts. rtxn_rts s (Tn_cl n cl) = Some ts \<longrightarrow> (\<forall>k. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver))"

lemmas Rtxn_Wtxn_No_VerI = Rtxn_Wtxn_No_Ver_def[THEN iffD2, rule_format]
lemmas Rtxn_Wtxn_No_VerE[elim] = Rtxn_Wtxn_No_Ver_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_wtxn_no_ver [simp]: "reach tps s \<Longrightarrow> Rtxn_Wtxn_No_Ver s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rtxn_Wtxn_No_Ver_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: Rtxn_Wtxn_No_Ver_def tps_trans_defs)
      using Cl_Rtxn_Inv_def by blast
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Rtxn_Wtxn_No_Ver_def tps_trans_defs)
      by (meson add_to_readerset_no_ver_inv)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (auto simp add: Rtxn_Wtxn_No_Ver_def tps_trans_defs)
      by (metis CFTid_Rtxn_Inv_def get_sn_wtxn.simps(2) le_refl reach_cftid_rtxn_inv)
  qed (auto simp add: Rtxn_Wtxn_No_Ver_def tps_trans_defs)
qed

definition Wtxn_Rtxn_None where
  "Wtxn_Rtxn_None s k \<longleftrightarrow>
    (\<forall>cl n ts v cts rs deps. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) \<in> {Prep ts v, Commit cts v rs deps}
       \<longrightarrow> rtxn_rts s (Tn_cl n cl) = None)"

lemmas Wtxn_Rtxn_NoneI = Wtxn_Rtxn_None_def[THEN iffD2, rule_format]
lemmas Wtxn_Rtxn_NoneE[elim] = Wtxn_Rtxn_None_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_rtxn_none [simp]: "reach tps s \<Longrightarrow> Wtxn_Rtxn_None s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Wtxn_Rtxn_None_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case using Cl_Rtxn_Inv_def[of s]
  proof (induction e)
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Wtxn_Rtxn_None_def tps_trans_defs)
      by (meson add_to_readerset_commit_subset add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Wtxn_Rtxn_None_def tps_trans_defs)
      by (metis CFTid_Rtxn_Inv_def get_cl_wtxn.simps(2) get_sn_wtxn.simps(2) le_refl
          reach_cftid_rtxn_inv)
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Wtxn_Rtxn_None_def tps_trans_defs)
      by (meson is_prepared.elims(2))
  qed (auto simp add: Wtxn_Rtxn_None_def tps_trans_defs)
qed

definition WtxnCommit_Wtxn_Cts where
  "WtxnCommit_Wtxn_Cts s cl \<longleftrightarrow> (\<forall>cts kv_map deps. txn_state (cls s cl) = WtxnCommit cts kv_map deps
    \<longrightarrow> wtxn_cts s (get_wtxn_cl s cl) = Some cts)"

lemmas WtxnCommit_Wtxn_CtsI = WtxnCommit_Wtxn_Cts_def[THEN iffD2, rule_format]
lemmas WtxnCommit_Wtxn_CtsE[elim] = WtxnCommit_Wtxn_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxncommit_wtxn_cts [simp, intro]: "reach tps s \<Longrightarrow> WtxnCommit_Wtxn_Cts s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: WtxnCommit_Wtxn_Cts_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: WtxnCommit_Wtxn_Cts_def tps_trans_defs)
qed

definition Wtxn_State_Cts where
  "Wtxn_State_Cts s k \<longleftrightarrow>
    (\<forall>t cts v rs deps ts kv_map. (wtxn_state (svrs s k) t = Commit cts v rs deps) \<or> 
      (wtxn_state (svrs s k) t = Prep ts v \<and> is_curr_wt s t \<and>
       txn_state (cls s (get_cl_wtxn t)) = WtxnCommit cts kv_map deps)
      \<longrightarrow> wtxn_cts s t = Some cts)"

lemmas Wtxn_State_CtsI = Wtxn_State_Cts_def[THEN iffD2, rule_format]
lemmas Wtxn_State_CtsE[elim] = Wtxn_State_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_state_cts [simp]: "reach tps s \<Longrightarrow> Wtxn_State_Cts s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Wtxn_State_Cts_def tps_defs split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Wtxn_State_Cts_def tps_trans_defs domI)
    apply (metis (no_types, lifting) Cl_Prep_Inv_def is_prepared.simps(3) reach_cl_prep_inv ver_state.distinct(3))
    subgoal for t apply (cases t, metis)
      by (metis get_cl_wtxn.simps(2) get_sn_wtxn.simps(2) txid0.exhaust).
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Wtxn_State_Cts_def tps_trans_defs domI)
      by (meson add_to_readerset_commit add_to_readerset_prep_inv)
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Wtxn_State_Cts_def tps_trans_defs domI)
      by (meson domI is_prepared.elims(2))
  qed (auto simp add: Wtxn_State_Cts_def tps_trans_defs domI)
qed

definition FTid_notin_rs where
  "FTid_notin_rs s cl \<longleftrightarrow> (\<forall>k n t cts v rs deps. n > txn_sn (cls s cl) \<and>
    wtxn_state (svrs s k) t = Commit cts v rs deps \<longrightarrow> Tn_cl n cl \<notin> rs)"

lemmas FTid_notin_rsI = FTid_notin_rs_def[THEN iffD2, rule_format]
lemmas FTid_notin_rsE[elim] = FTid_notin_rs_def[THEN iffD1, elim_format, rule_format]

lemma reach_ftid_notin_rs [simp, dest]: "reach tps s \<Longrightarrow> FTid_notin_rs s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: FTid_notin_rs_def tps_defs split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: FTid_notin_rs_def tps_trans_defs)
      by (meson Suc_lessD)
  next
    case (WDone x1 x2)
    then show ?case apply (simp add: FTid_notin_rs_def tps_trans_defs)
      by (meson Suc_lessD)
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: FTid_notin_rs_def tps_trans_defs add_to_readerset_def
          split: ver_state.split)
      by (smt (verit) less_irrefl_nat txid0.sel(1) txid0.sel(2))
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: FTid_notin_rs_def tps_trans_defs)
      by (metis)
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: FTid_notin_rs_def tps_trans_defs)
      by (smt empty_iff fun_upd_other fun_upd_same state_txn.simps(19) ver_state.inject(2)
          ver_state.simps(10))
  qed (auto simp add: FTid_notin_rs_def tps_trans_defs)
qed

definition FTid_not_wr where
  "FTid_not_wr s cl \<longleftrightarrow> (\<forall>n k. n > txn_sn (cls s cl) \<longrightarrow> Tn (Tn_cl n cl) \<notin> wtxns_dom (wtxn_state (svrs s k)))"

lemmas FTid_not_wrI = FTid_not_wr_def[THEN iffD2, rule_format]
lemmas FTid_not_wrE[elim] = FTid_not_wr_def[THEN iffD1, elim_format, rule_format]

lemma reach_ftid_not_wr [simp]: "reach tps s \<Longrightarrow> FTid_not_wr s cl"
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
    case (WDone x61 x62)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (metis Suc_lessD)
  next
    case (RegR x71 x72 x73 x74)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (metis add_to_readerset_wtxns_dom)
  next
    case (PrepW x81 x82 x83)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (metis get_cl_wtxn.simps(2) get_sn_wtxn.simps(2) nat_neq_iff)
  next
    case (CommitW x91 x92)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (metis get_cl_wtxn.simps(2) get_sn_wtxn.simps(2) order_less_irrefl)
  qed (auto simp add: FTid_not_wr_def tps_trans_defs)
qed

definition Fresh_wr_notin_rs where
  "Fresh_wr_notin_rs s k \<longleftrightarrow> (\<forall>t t' cts kv_map deps cts' v' rs' deps'.
    txn_state (cls s (get_cl_txn t')) \<in> {Idle, WtxnPrep kv_map, WtxnCommit cts kv_map deps} \<and>
    get_sn_txn t' \<ge> txn_sn (cls s (get_cl_txn t')) \<and>
    wtxn_state (svrs s k) t = Commit cts' v' rs' deps' \<longrightarrow> t' \<notin> rs')"

lemmas Fresh_wr_notin_rsI = Fresh_wr_notin_rs_def[THEN iffD2, rule_format]
lemmas Fresh_wr_notin_rsE[elim] = Fresh_wr_notin_rs_def[THEN iffD1, elim_format, rule_format]

lemma reach_fresh_wr_notin_rs [simp]: "reach tps s \<Longrightarrow> Fresh_wr_notin_rs s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Fresh_wr_notin_rs_def tps_defs split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: Fresh_wr_notin_rs_def tps_trans_defs)
      apply (metis FTid_notin_rs_def Suc_le_eq reach_ftid_notin_rs txid0.exhaust_sel)
      by blast+
  next
    case (WDone x1 x2)
    then show ?case apply (simp add: Fresh_wr_notin_rs_def tps_trans_defs )
      by (meson Suc_leD)
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (auto simp add: Fresh_wr_notin_rs_def tps_trans_defs add_to_readerset_def
          split: ver_state.split)
      by blast+
  qed (simp_all add: Fresh_wr_notin_rs_def tps_trans_defs split: state_txn.split, (blast+)?)
qed

definition Fresh_wr_notin_Wts_dom where
  "Fresh_wr_notin_Wts_dom s cl \<longleftrightarrow> (\<forall>keys kv_map k. txn_state (cls s cl) \<in> {Idle, RtxnInProg keys kv_map} \<longrightarrow>
    Tn (get_txn_cl s cl) \<notin> wtxns_dom (wtxn_state (svrs s k)))"

lemmas Fresh_wr_notin_Wts_domI = Fresh_wr_notin_Wts_dom_def[THEN iffD2, rule_format]
lemmas Fresh_wr_notin_Wts_domE[elim] = Fresh_wr_notin_Wts_dom_def[THEN iffD1, elim_format, rule_format]

lemma reach_fresh_wr_notin_wtxns_dom [simp]: "reach tps s \<Longrightarrow> Fresh_wr_notin_Wts_dom s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Fresh_wr_notin_Wts_dom_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: tps_trans_defs Fresh_wr_notin_Wts_dom_def)
      by (metis add_to_readerset_wtxns_dom)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: tps_trans_defs Fresh_wr_notin_Wts_dom_def)
      by (metis get_cl_wtxn.simps(2) state_txn.distinct(3) state_txn.distinct(7))
  qed (auto simp add: tps_trans_defs Fresh_wr_notin_Wts_dom_def)
qed

definition Rtxn_rts_le_Gst where
  "Rtxn_rts_le_Gst s cl \<longleftrightarrow> (\<forall>n ts. rtxn_rts s (Tn_cl n cl) = Some ts \<longrightarrow> ts \<le> gst (cls s cl))"

lemmas Rtxn_rts_le_GstI = Rtxn_rts_le_Gst_def[THEN iffD2, rule_format]
lemmas Rtxn_rts_le_GstE[elim] = Rtxn_rts_le_Gst_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_rts_le_gst [simp]: "reach tps s \<Longrightarrow> Rtxn_rts_le_Gst s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rtxn_rts_le_Gst_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: Rtxn_rts_le_Gst_def read_invoke_def)
      by (meson Gst_le_Min_Lst_map_def dual_order.trans reach_gst_le_min_lst_map)
  qed (auto simp add: Rtxn_rts_le_Gst_def tps_trans_defs)
qed

subsection \<open>Gst, Cts, Pts relations\<close>

definition Gst_le_Pts where
  "Gst_le_Pts s cl \<longleftrightarrow> (\<forall>k prep_t v. 
      wtxn_state (svrs s k) (get_wtxn_cl s cl) = Prep prep_t v \<longrightarrow> gst (cls s cl) \<le> prep_t)"
                                                           
lemmas Gst_le_PtsI = Gst_le_Pts_def[THEN iffD2, rule_format]
lemmas Gst_le_PtsE[elim] = Gst_le_Pts_def[THEN iffD1, elim_format, rule_format]

lemma reach_gst_le_pts [simp]: "reach tps s \<Longrightarrow> Gst_le_Pts s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Gst_le_Pts_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: Gst_le_Pts_def tps_trans_defs)
      by (metis Cl_Rtxn_Inv_def insert_iff reach_cl_rtxn_inv ver_state.distinct(1))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: Gst_le_Pts_def tps_trans_defs)
      by (meson FTid_not_wr_def lessI reach_ftid_not_wr wtxns_domI1)
  next
    case (WDone x1 x2)
    then show ?case apply (simp add: Gst_le_Pts_def tps_trans_defs)
      by (meson FTid_not_wr_def less_Suc_eq reach_ftid_not_wr wtxns_domI1)
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Gst_le_Pts_def tps_trans_defs)
      by (meson add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (auto simp add: Gst_le_Pts_def tps_trans_defs)
      using Gst_le_Lst_map_def[of s cl x1] Lst_map_le_Lst_def Clk_le_Lst_def
      by (metis dual_order.trans reach_clock_lst_inv reach_gst_le_lst reach_lst_map_le_lst)
  qed (auto simp add: Gst_le_Pts_def tps_trans_defs)
qed

definition Gst_Lt_Cts where
  "Gst_Lt_Cts s cl \<longleftrightarrow> (\<forall>k cts v rs deps. 
      wtxn_state (svrs s k) (get_wtxn_cl s cl) = Commit cts v rs deps \<longrightarrow> gst (cls s cl) < cts)"
                                                           
lemmas Gst_Lt_CtsI = Gst_Lt_Cts_def[THEN iffD2, rule_format]
lemmas Gst_Lt_CtsE[elim] = Gst_Lt_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_gst_lt_cts [simp]: "reach tps s \<Longrightarrow> Gst_Lt_Cts s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Gst_Lt_Cts_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: Gst_Lt_Cts_def tps_trans_defs) sorry
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: Gst_Lt_Cts_def tps_trans_defs)
      by (metis FTid_Wtxn_Inv_def lessI reach_ftid_wtxn_inv ver_state.distinct(3))
  next
    case (WDone x1 x2)
    then show ?case apply (simp add: Gst_Lt_Cts_def tps_trans_defs)
      by (meson FTid_not_wr_def less_Suc_eq reach_ftid_not_wr wtxns_domI2)
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Gst_Lt_Cts_def tps_trans_defs)
      by (meson add_to_readerset_commit)
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Gst_Lt_Cts_def tps_trans_defs) sorry
  qed (auto simp add: Gst_Lt_Cts_def tps_trans_defs)
qed


definition Gst_Lt_Cl_Cts where
  "Gst_Lt_Cl_Cts s cl \<longleftrightarrow> (\<forall>cl' cts kv_map deps. txn_state (cls s cl') = WtxnCommit cts kv_map deps
    \<longrightarrow> gst (cls s cl) < cts)"
                                                           
lemmas Gst_Lt_Cl_CtsI = Gst_Lt_Cl_Cts_def[THEN iffD2, rule_format]
lemmas Gst_Lt_Cl_CtsE[elim] = Gst_Lt_Cl_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_gst_lt_cl_cts [simp]: "reach tps s \<Longrightarrow> Gst_Lt_Cl_Cts s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Gst_Lt_Cl_Cts_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (auto simp add: Gst_Lt_Cl_Cts_def tps_trans_defs) sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Gst_Lt_Cl_Cts_def tps_trans_defs)
      apply (cases "cl = x1"; simp) sorry
  qed (auto simp add: Gst_Lt_Cl_Cts_def tps_trans_defs, (blast+)?)
qed

subsection \<open>Invariants about commit order\<close>

abbreviation is_committed_in_abs where
  "is_committed_in_abs s k t \<equiv> 
    is_committed (wtxn_state (svrs s k) t)  \<or> 
    (is_prepared (wtxn_state (svrs s k) t) \<and> \<comment> \<open>is_curr_wt s t \<and>\<close>
     (\<exists>cts kv_map deps. txn_state (cls s (get_cl_wtxn t)) = WtxnCommit cts kv_map deps))"

definition Commit_Order_Tid where
  "Commit_Order_Tid s cl \<longleftrightarrow> (case txn_state (cls s cl) of
    WtxnCommit cts kv_map deps \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (commit_order s k) \<longrightarrow> n \<le> txn_sn (cls s cl))
  | _ \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (commit_order s k) \<longrightarrow> n < txn_sn (cls s cl)))"

lemmas Commit_Order_TidI = Commit_Order_Tid_def[THEN iffD2, rule_format]
lemmas Commit_Order_TidE[elim] = Commit_Order_Tid_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_tid[simp]: "reach tps s \<Longrightarrow> Commit_Order_Tid s cl"
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
    case (WDone x1 x2)
    then show ?case apply (simp add: Commit_Order_Tid_def tps_trans_defs split: state_txn.split_asm)
      apply (meson less_SucI)+
      by (meson linorder_le_less_linear not_less_eq_eq)
  qed (auto simp add: Commit_Order_Tid_def tps_trans_defs split: state_txn.split_asm)
qed

definition Commit_Order_Distinct where
  "Commit_Order_Distinct s k \<longleftrightarrow> distinct (commit_order s k)"

lemmas Commit_Order_DistinctI = Commit_Order_Distinct_def[THEN iffD2, rule_format]
lemmas Commit_Order_DistinctE[elim] = Commit_Order_Distinct_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_distinct [simp]: "reach tps s \<Longrightarrow> Commit_Order_Distinct s k"
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
    (\<exists>cts v rs deps. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts v rs deps) \<or> 
    ((\<exists>ts v. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Prep ts v) \<and> 
     (\<exists>cts kv_map deps. txn_state (cls s cl) = WtxnCommit cts kv_map deps \<and> 
      txn_sn (cls s cl) = n \<and> k \<in> dom kv_map)))"

lemmas Commit_Order_SoundI = Commit_Order_Sound_def[THEN iffD2, rule_format]
lemmas Commit_Order_SoundE[elim] = Commit_Order_Sound_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_sound [simp]: "reach tps s \<Longrightarrow> Commit_Order_Sound s k"
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
      by (smt (verit) domIff is_prepared.elims(2) option.discI state_txn.distinct(11))
  next
    case (WDone x1 x2)
    then show ?case apply (simp add: Commit_Order_Sound_def tps_trans_defs)
      by (metis (no_types, lifting) state_txn.inject(3))
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Commit_Order_Sound_def tps_trans_defs)
      by (metis add_to_readerset_commit' add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Commit_Order_Sound_def tps_trans_defs)
      by (metis ver_state.distinct(3))
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Commit_Order_Sound_def tps_trans_defs)
      by (smt (z3) fun_upd_apply state_txn.simps(19) ver_state.simps(10))
  qed (auto simp add: Commit_Order_Sound_def tps_trans_defs)
qed

definition Commit_Order_Sound' where
  "Commit_Order_Sound' s k \<longleftrightarrow> (\<forall>t \<in> set (commit_order s k). wtxn_state (svrs s k) t \<noteq> No_Ver)"

lemmas Commit_Order_Sound'I = Commit_Order_Sound'_def[THEN iffD2, rule_format]
lemmas Commit_Order_Sound'E[elim] = Commit_Order_Sound'_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_sound' [simp]: "reach tps s \<Longrightarrow> Commit_Order_Sound' s k"
  apply (simp add: Commit_Order_Sound'_def)
  apply rule subgoal for t apply (cases t)
     apply (metis Init_Ver_Inv_def reach_init_ver_inv ver_state.distinct(3))
    using Commit_Order_Sound_def
    by (metis reach_commit_order_sound txid0.exhaust ver_state.distinct(1) ver_state.distinct(3)).

definition Commit_Order_Sound'' where
  "Commit_Order_Sound'' s k \<longleftrightarrow> (\<forall>t \<in> set (commit_order s k). \<exists>cts. wtxn_cts s t = Some cts)"

lemmas Commit_Order_Sound''I = Commit_Order_Sound''_def[THEN iffD2, rule_format]
lemmas Commit_Order_Sound''E[elim] = Commit_Order_Sound''_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_sound'' [simp]: "reach tps s \<Longrightarrow> Commit_Order_Sound'' s k"
  apply (simp add: Commit_Order_Sound''_def)
  apply rule subgoal for t apply (cases t)
    using Init_Ver_Inv_def Wtxn_State_Cts_def[of s k] reach_wtxn_state_cts apply blast
    by (metis Commit_Order_Sound_def Wtxn_State_Cts_def WtxnCommit_Wtxn_Cts_def
        reach_commit_order_sound reach_wtxn_state_cts reach_wtxncommit_wtxn_cts txid0.exhaust).

definition Commit_Order_Complete where
  "Commit_Order_Complete s k \<longleftrightarrow> (\<forall>n cl.
    (\<exists>cts v rs deps. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts v rs deps) \<or> 
    ((\<exists>ts v. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Prep ts v) \<and> 
     (\<exists>cts kv_map deps. txn_state (cls s cl) = WtxnCommit cts kv_map deps \<and> txn_sn (cls s cl) = n)) \<longrightarrow>
    Tn (Tn_cl n cl) \<in> set (commit_order s k))"

lemmas Commit_Order_CompleteI = Commit_Order_Complete_def[THEN iffD2, rule_format]
lemmas Commit_Order_CompleteE[elim] = Commit_Order_Complete_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_complete [simp]: "reach tps s \<Longrightarrow> Commit_Order_Complete s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Commit_Order_Complete_def tps_defs split: if_split_asm)
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
      by (metis (no_types, lifting) Cl_Prep_Inv_def domIff reach_cl_prep_inv ver_state.distinct(1))
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Commit_Order_Complete_def tps_trans_defs)
      by (smt (verit) add_to_readerset_commit add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Commit_Order_Complete_def tps_trans_defs)
      by (metis get_cl_wtxn.simps(2) state_txn.distinct(11))
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Commit_Order_Complete_def tps_trans_defs)
      by (metis (no_types, opaque_lifting) is_prepared.elims(2))
  qed (simp_all add: Commit_Order_Complete_def tps_trans_defs)
qed

definition Commit_Order_Sorted where
  "Commit_Order_Sorted s k \<longleftrightarrow> (\<forall>i < length (commit_order s k). \<forall>i' < length (commit_order s k).
    i < i' \<longrightarrow> the (wtxn_cts s (commit_order s k ! i)) \<le> the (wtxn_cts s (commit_order s k ! i')))"

lemmas Commit_Order_SortedI = Commit_Order_Sorted_def[THEN iffD2, rule_format]
lemmas Commit_Order_SortedE[elim] = Commit_Order_Sorted_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_sorted [simp]: "reach tps s \<Longrightarrow> Commit_Order_Sorted s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Commit_Order_Sorted_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Commit_Order_Sorted_def tps_trans_defs)
      (*apply (cases "x2 k", auto)*) sorry
  qed (auto simp add: Commit_Order_Sorted_def tps_trans_defs)
qed


subsection \<open>kvs_of_s preserved through non-commit\<close>

abbreviation invariant_list_kvs where
  "invariant_list_kvs s \<equiv> \<forall>k. Commit_Order_Sound' s k \<and>  Fresh_wr_notin_rs s k"

abbreviation not_committing_ev where
  "not_committing_ev e \<equiv> \<forall>cl kvt_map kv_map cts sn u. e \<noteq> RDone cl kvt_map sn u \<and>
    e \<noteq> WCommit cl kv_map cts sn u"

lemma kvs_of_s_inv:
  assumes "state_trans s e s'"
    and "invariant_list_kvs s"
    and "not_committing_ev e"
  shows "kvs_of_s s' = kvs_of_s s"
  using assms
proof (induction e)
  case (WDone cl kv_map)    \<comment> \<open>write transaction already in abstract state, now just added to svr\<close>
  then show ?case 
    apply (auto simp add: tps_trans_defs)
    apply (auto simp add: kvs_of_s_def tps_trans_defs)
    apply (intro ext)
    apply (auto split: ver_state.split)
    subgoal for cts ctx k t cts' v' rs' ctx' t'
      apply (thin_tac "X = Y" for X Y)
      apply (cases "get_sn_txn t' = txn_sn (cls s (get_cl_txn t'))", auto)
      using Fresh_wr_notin_rs_def[of s]
      by (metis dual_order.refl insertCI).
next
  case (RegR svr t t_wr gst_ts)
  then show ?case       \<comment> \<open>extends readerset; ok since committed reads remain the same\<close>
    by (auto 3 3 simp add: kvs_of_s_def tps_trans_defs add_to_readerset_def split: ver_state.split)
next
  case (PrepW svr t v)  \<comment> \<open>goes to Prep state; not yet added to abstract state (client not committed)\<close>
  then show ?case 
    apply (auto simp add: kvs_of_s_def tps_trans_defs split: ver_state.split)
    apply (intro ext)
    by (auto split: ver_state.split)
next
  case (CommitW svr t v cts deps)   \<comment> \<open>goes to Commit state; ok: no change\<close>
  then show ?case  
    by (fastforce simp add: kvs_of_s_def tps_trans_defs split: ver_state.split)
qed (auto simp add: kvs_of_s_def tps_trans_defs split: ver_state.split)


subsection \<open>Transaction ID Freshness\<close>

definition Sqn_Inv_nc where
  "Sqn_Inv_nc s cl \<longleftrightarrow> (\<forall>cts kvm deps. txn_state (cls s cl) \<noteq> WtxnCommit cts kvm deps
     \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m < txn_sn (cls s cl)))"

lemmas Sqn_Inv_ncI = Sqn_Inv_nc_def[THEN iffD2, rule_format]
lemmas Sqn_Inv_ncE[elim] = Sqn_Inv_nc_def[THEN iffD1, elim_format, rule_format]

lemma reach_sql_inv_nc [simp]: "reach tps s \<Longrightarrow> Sqn_Inv_nc s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Sqn_Inv_nc_def tps_def kvs_of_s_init get_sqns_old_def txid_defs)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    hence sqn_added: "get_sqns (kvs_of_s s') x1 = get_sqns (kvs_of_s s) x1 \<union> {txn_sn (cls s x1)}" sorry
    from RDone have "cl \<noteq> x1 \<longrightarrow> get_sqns (kvs_of_s s') cl = get_sqns (kvs_of_s s) cl"
      apply (simp add: read_done_def) sorry
    then show ?case using RDone sqn_added by (auto simp add: Sqn_Inv_nc_def tps_trans_defs)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Sqn_Inv_nc_def tps_trans_defs) sorry
  next
    case (WDone x1 x2)
    then show ?case apply (simp add: Sqn_Inv_nc_def tps_trans_defs)
      by (metis less_Suc_eq state_txn.inject(3))
  qed (auto simp add: Sqn_Inv_nc_def tps_trans_defs)
qed

definition Sqn_Inv_c where
  "Sqn_Inv_c s cl \<longleftrightarrow> (\<forall>cts kvm deps. txn_state (cls s cl) = WtxnCommit cts kvm deps
     \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m \<le> txn_sn (cls s cl)))"

lemmas Sqn_Inv_cI = Sqn_Inv_c_def[THEN iffD2, rule_format]
lemmas Sqn_Inv_cE[elim] = Sqn_Inv_c_def[THEN iffD1, elim_format, rule_format]

lemma reach_sql_inv_c [simp]: "reach tps s \<Longrightarrow> Sqn_Inv_c s cl"
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

subsection \<open>At functions point to committed versions\<close>

lemma at_is_committed:
  assumes "Init_Ver_Inv s k"
  shows "is_committed ((wtxn_state (svrs s k)) (at (wtxn_state (svrs s k)) rts))"
proof -
  let ?P = "\<lambda>t. is_committed (wtxn_state (svrs s k) t) \<and> get_ts (wtxn_state (svrs s k) t) \<le> rts"
    and ?f = "get_ts o (wtxn_state (svrs s k))"
  have fin: "finite {y. \<exists>x. ?P x \<and> y = ?f x}"
    using finite_nat_set_iff_bounded_le by auto
  have "?P T0" using assms(1) by auto
  then show ?thesis apply (auto simp add: at_def ver_committed_before_def)
    by (smt arg_max_exI[of ?P ?f] P_arg_max fin)
qed

lemma newest_own_write_is_committed:
  assumes "Finite_Wtxns_Dom s k"and "newest_own_write (wtxn_state (svrs s k)) ts cl = Some t"
  shows "is_committed (wtxn_state (svrs s k) t)"
proof -
  let ?P = "\<lambda>t. is_committed (wtxn_state (svrs s k) t)"
    and ?Q = "\<lambda>t. ts \<le> get_ts (wtxn_state (svrs s k) t) \<and> get_cl_wtxn t = cl"
    and ?PQ = "\<lambda>t. is_committed (wtxn_state (svrs s k) t) \<and> ts \<le> get_ts (wtxn_state (svrs s k) t)
      \<and> get_cl_wtxn t = cl"
    and ?f = "get_ts o (wtxn_state (svrs s k))"
  obtain tw where P_tw: "?PQ tw" using assms
    by (auto simp add: newest_own_write_def ver_committed_after_def split: if_split_asm)
  have "finite {x. ?P x}" using assms(1) Finite_Wtxns_Dom_def
    by (smt (verit) wtxns_dom_def Collect_mono is_committed.simps(2) rev_finite_subset)
  hence fin: "finite {y. \<exists>x. ?PQ x \<and> y = ?f x}" by auto
  show ?thesis using assms P_Q_arg_max[of ?f ?P ?Q] arg_max_exI[OF fin P_tw]
    by (auto simp add: newest_own_write_def ver_committed_after_def split: if_split_asm)
qed

lemma read_at_is_committed:
  assumes "Init_Ver_Inv s k" and "Finite_Wtxns_Dom s k"
  shows "is_committed (wtxn_state (svrs s k) (read_at (wtxn_state (svrs s k)) rts cl))"
  using assms
  by (simp add: read_at_def Let_def at_is_committed newest_own_write_is_committed split: option.split)

definition Kvt_map_t_Committed where (* needed? *)
  "Kvt_map_t_Committed s cl \<longleftrightarrow> (\<forall>keys kvt_map k v t. txn_state (cls s cl) = RtxnInProg keys kvt_map
    \<and> kvt_map k = Some (v, t) \<longrightarrow> is_committed (wtxn_state (svrs s k) t))"
                                                           
lemmas Kvt_map_t_CommittedI = Kvt_map_t_Committed_def[THEN iffD2, rule_format]
lemmas Kvt_map_t_CommittedE[elim] = Kvt_map_t_Committed_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvt_map_t_committed [simp]: "reach tps s \<Longrightarrow> Kvt_map_t_Committed s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Kvt_map_t_Committed_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: Kvt_map_t_Committed_def tps_trans_defs)
      by force
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Kvt_map_t_Committed_def tps_trans_defs)
      by (metis add_to_readerset_commit' is_committed.elims(1) is_committed.simps(1))
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Kvt_map_t_Committed_def tps_trans_defs)
      by (metis is_committed.simps(2))
  qed (auto simp add: Kvt_map_t_Committed_def tps_trans_defs)
qed


subsection \<open>Timestamp relations\<close>

definition Disjoint_RW where
  "Disjoint_RW s \<longleftrightarrow> ((\<Union>k. wtxns_dom (wtxn_state (svrs s k))) \<inter> Tn ` (\<Union>k. wtxns_rsran (wtxn_state (svrs s k))) = {})"

lemmas Disjoint_RWI = Disjoint_RW_def[THEN iffD2, rule_format]
lemmas Disjoint_RWE[elim] = Disjoint_RW_def[THEN iffD1, elim_format, rule_format]

lemma reach_disjoint_rw [simp]: "reach tps s \<Longrightarrow> Disjoint_RW s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Disjoint_RW_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4)
    hence "\<And>k. wtxns_dom (wtxn_state (svrs s' k)) = wtxns_dom (wtxn_state (svrs s k))"
      by (simp add: tps_trans_defs add_to_readerset_wtxns_dom)
    hence "\<And>k. wtxns_rsran (wtxn_state (svrs s' k)) =
      (if k = x1
       then insert x2 (wtxns_rsran (wtxn_state (svrs s k)))
       else wtxns_rsran (wtxn_state (svrs s k)))" using RegR
      by (simp add: tps_trans_defs add_to_readerset_wtxns_rsran read_at_is_committed)
    then show ?case using RegR apply (simp add: Disjoint_RW_def)
      using Fresh_wr_notin_Wts_dom_def[of s "get_cl_txn x2"] sorry
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (auto simp add: Disjoint_RW_def tps_trans_defs) sorry
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case sorry
  qed (auto simp add: Disjoint_RW_def tps_trans_defs)
qed

definition Disjoint_RW' where
  "Disjoint_RW' s \<longleftrightarrow> (kvs_writers (kvs_of_s s) \<inter> Tn ` kvs_readers (kvs_of_s s) = {})"

lemmas Disjoint_RW'I = Disjoint_RW'_def[THEN iffD2, rule_format]
lemmas Disjoint_RW'E[elim] = Disjoint_RW'_def[THEN iffD1, elim_format, rule_format]

lemma reach_disjoint_rw' [simp]: "reach tps s \<Longrightarrow> Disjoint_RW' s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case apply (auto simp add: Disjoint_RW'_def tps_def txid_defs)
    by (metis empty_set kvs_of_s_init list.simps(15) singletonD txid.distinct(1) version.select_convs(2))
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RDone cl kvt_map sn u'')
    then show ?case apply (auto simp add: Disjoint_RW'_def tps_trans_defs txid_defs kvs_of_s_def
          split: ver_state.split_asm)
      apply (metis Commit_Order_Sound'_def reach_commit_order_sound')
      apply (metis Commit_Order_Sound'_def reach_commit_order_sound')
      apply (metis Commit_Order_Sound'_def reach_commit_order_sound')
        apply (metis Commit_Order_Sound'_def reach_commit_order_sound')
      subgoal for xa xb apply (cases xb)
        by (smt (verit) Commit_Order_Sound_def[of s xa] less_irrefl_nat reach_commit_order_sound
          reach_trans.hyps(2) state_txn.distinct(9) txid0.sel(1) txid0.sel(2) ver_state.distinct(5))
      subgoal for xa xb apply (cases xb)
        using Fresh_wr_notin_rs_def[of s] Commit_Order_Sound_def[of s xa]
      (*
          xd \<in> set (commit_order s xc);
          Tn xb \<in> set (commit_order s xa);
          wtxn_state (svrs s xc) xd = Commit x31 x32 x33 x34;
          wtxn_state (svrs s xa) (Tn xb) = Commit x31a x32a x33a x34a
          xb \<in> x33;
      *)
      sorry.
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case sorry
  qed (auto simp add: Disjoint_RW'_def)
qed

definition RO_has_rts where
  "RO_has_rts s \<longleftrightarrow> (\<forall>t. Tn t \<in> read_only_Txs (kvs_of_s s) \<longrightarrow> (\<exists>rts. rtxn_rts s t = Some rts))"

lemmas RO_has_rtsI = RO_has_rts_def[THEN iffD2, rule_format]
lemmas RO_has_rtsE[elim] = RO_has_rts_def[THEN iffD1, elim_format, rule_format]

lemma reach_ro_in_readers [simp]: "reach tps s \<Longrightarrow> RO_has_rts s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: RO_has_rts_def tps_defs read_only_Txs_def txid_defs kvs_of_s_def)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: RO_has_rts_def tps_trans_defs) sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: RO_has_rts_def tps_trans_defs split: if_split_asm) sorry
    (* inv: if t : RO in K it remains RO in K' *)
  qed (auto simp add: RO_has_rts_def tps_trans_defs)
qed

definition SO_ROs where
  "SO_ROs s \<longleftrightarrow> (\<forall>r1 r2 rts1 rts2. (Tn r1, Tn r2) \<in> SO \<and>
    rtxn_rts s r1 = Some rts1 \<and> rtxn_rts s r2 = Some rts2 \<longrightarrow> rts1 \<le> rts2)"

lemmas SO_ROsI = SO_ROs_def[THEN iffD2, rule_format]
lemmas SO_ROsE[elim] = SO_ROs_def[THEN iffD1, elim_format, rule_format]

lemma reach_so_ro [simp]: "reach tps s \<Longrightarrow> SO_ROs s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: SO_ROs_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: SO_ROs_def tps_trans_defs SO_def SO0_def)
      apply (metis CFTid_Rtxn_Inv_def less_or_eq_imp_le option.distinct(1) reach_cftid_rtxn_inv)
      by (meson Rtxn_rts_le_Gst_def reach_rtxn_rts_le_gst)
  qed (auto simp add: SO_ROs_def tps_trans_defs)
qed

definition SO_RO_WR where
  "SO_RO_WR s \<longleftrightarrow> (\<forall>r w rts cts. (Tn r, w) \<in> SO \<and>
    rtxn_rts s r = Some rts \<and> wtxn_cts s w = Some cts \<longrightarrow> rts \<le> cts)"

lemmas SO_RO_WRI = SO_RO_WR_def[THEN iffD2, rule_format]
lemmas SO_RO_WRE[elim] = SO_RO_WR_def[THEN iffD1, elim_format, rule_format]

lemma reach_so_ro_wr [simp]: "reach tps s \<Longrightarrow> SO_RO_WR s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: SO_RO_WR_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: SO_RO_WR_def tps_trans_defs SO_def SO0_def) sorry
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: SO_RO_WR_def tps_trans_defs SO_def SO0_def) sorry
  qed (auto simp add: SO_RO_WR_def tps_trans_defs)
qed

subsection \<open>CanCommit\<close>

lemma the_T0: "(THE i. i = 0 \<and> [T0] ! i = T0) = 0" by auto

lemmas canCommit_defs = ET_CC.canCommit_def closed_def R_CC_def R_onK_def

lemma visTx_visTx': "\<comment> \<open>\<forall>k t. (k, t) \<in> u \<longrightarrow> t \<in> set (commit_order s k) \<Longrightarrow>\<close>
  visTx (kvs_of_s s) (view_of (commit_order s) u) = visTx' (kvs_of_s s) u"
  apply (auto simp add: visTx_def visTx'_def kvs_writers_def vl_writers_def image_iff) sorry

lemma closed_closed': "\<comment> \<open>\<forall>k t. (k, t) \<in> u \<longrightarrow> t \<in> set (commit_order s k) \<Longrightarrow>\<close>
  closed (kvs_of_s s) (view_of (commit_order s) u) r = closed' (kvs_of_s s) u r"
  by (simp add: closed_def closed'_def visTx_visTx')

lemma visTx'_subset_writers:
  "visTx' (kvs_of_s s) (get_view s cl) \<subseteq> kvs_writers (kvs_of_s s)"
  by (simp add: visTx'_def)

lemma visTx'_cl_ctx_subset_writers:
  "visTx' (kvs_of_s s) (cl_ctx (cls s cl)) \<subseteq> kvs_writers (kvs_of_s s)"
  by (simp add: visTx'_def)

lemma visTx'_deps_subset_writers: 
  "wtxn_state (svrs s k) t = Commit cts v rs deps
    \<Longrightarrow> visTx' (kvs_of_s s) deps \<subseteq> kvs_writers (kvs_of_s s)"
  by (simp add: visTx'_def)

lemma visTx'_cl_deps_subset_writers: 
  "txn_state (cls s cl) = WtxnCommit cts kvm deps
    \<Longrightarrow> visTx' (kvs_of_s s) deps \<subseteq> kvs_writers (kvs_of_s s)"
  by (simp add: visTx'_def)

lemma "kvs_writers (kvs_of_s s) \<subseteq> (\<Union>k. wtxns_dom (wtxn_state (svrs s k)))"
  oops

lemma "kvs_readers (kvs_of_s s) \<subseteq> (\<Union>k. wtxns_rsran (wtxn_state (svrs s k)))"
  oops

definition closed_general :: "'v set \<Rightarrow> 'v rel \<Rightarrow> 'v set \<Rightarrow> bool" where
  "closed_general vis r r_only \<equiv> vis = ((r^*) `` (vis)) - r_only"

lemma closed'_generalize: "closed' K u r = closed_general (visTx' K u) (r^-1) (read_only_Txs K)"
  by (simp add: closed'_def closed_general_def rtrancl_converse)

lemma union_closed_general:
  "closed_general vis r r_only \<Longrightarrow> closed_general vis' r r_only
    \<Longrightarrow> closed_general (vis \<union> vis') r r_only"
  by (auto simp add: closed_general_def)

lemma visTx_union_distr: "visTx' K (u \<union> u') = visTx' K u \<union> visTx' K u'"
  by (auto simp add: visTx'_def)

lemma union_closed: "closed' K u r \<Longrightarrow> closed' K u' r \<Longrightarrow> closed' K (u \<union> u') r"
  by (auto simp add: closed'_generalize union_closed_general visTx_union_distr)

lemma visTx'_insert: "snd t \<in> kvs_writers K \<Longrightarrow> visTx' K (insert t u) = insert (snd t) (visTx' K u)"
  by (auto simp add: visTx'_def)

lemma insert_t_closed_general:
  "t \<notin> vis \<Longrightarrow> t \<notin> r_only \<Longrightarrow> (\<And>x. (t, x) \<in> r^* \<Longrightarrow> x \<in> vis \<or> x \<in> r_only \<or> x = t)
    \<Longrightarrow> closed_general vis r r_only \<Longrightarrow> closed_general (insert t vis) r r_only"
  by (auto simp add: closed_general_def)

lemma insert_t_closed:
  "get_wtxn_cl s cl \<in> kvs_writers K \<Longrightarrow> closed' K (cl_ctx (cls s cl)) r \<Longrightarrow>
    closed' K (insert (k, get_wtxn_cl s cl) (cl_ctx (cls s cl))) r"
  apply (auto simp add: closed'_generalize visTx'_insert intro!: insert_t_closed_general)
  subgoal apply (auto simp add: visTx'_def) sorry
  apply (simp add: read_only_Txs_def)
  thm rtrancl.induct rtrancl_induct
  subgoal for x apply (rotate_tac -3)
    apply (induction "get_wtxn_cl s cl" x rule: rtrancl.induct, auto) oops

definition RO_le_gst :: "'v state \<Rightarrow> cl_id \<Rightarrow> txid set" where
  "RO_le_gst s cl \<equiv> {t \<in> read_only_Txs (kvs_of_s s). \<exists>t'. t = Tn t' \<and> the (rtxn_rts s t') \<le> gst (cls s cl)}"

definition RO_WO_Inv where
  "RO_WO_Inv s \<longleftrightarrow> (\<Union>k. wtxns_dom (wtxn_state (svrs s k))) \<inter> Tn ` (\<Union>k. wtxns_rsran (wtxn_state (svrs s k))) = {}"

lemmas RO_WO_InvI = RO_WO_Inv_def[THEN iffD2, rule_format]
lemmas RO_WO_InvE[elim] = RO_WO_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_ro_wo_inv [simp]: "reach tps s \<Longrightarrow> RO_WO_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: RO_WO_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4)
    then show ?case apply (auto simp add: RO_WO_Inv_def tps_trans_defs) sorry
     (*using add_to_readerset_v_writer_img[of ] apply (simp add: txid_defs) sorry \<comment> \<open>Continue here!\<close>*)
  next
    case (PrepW x1 x2 x3)
    then show ?case sorry
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case sorry
  qed (auto simp add: RO_WO_Inv_def tps_trans_defs)
qed


subsection \<open>Ctx Invariants\<close>

\<comment> \<open>deps are committed\<close>
definition Ctx_Committed where
  "Ctx_Committed s \<longleftrightarrow> (\<forall>cl k t. (k, t) \<in> cl_ctx (cls s cl) \<longrightarrow>
    is_committed (wtxn_state (svrs s k) t) \<or> 
    (\<exists>cts kvm deps. txn_state (cls s cl) = WtxnCommit cts kvm deps \<and>
      k \<in> dom kvm \<and> t = get_wtxn_cl s cl))"

lemmas Ctx_CommittedI = Ctx_Committed_def[THEN iffD2, rule_format]
lemmas Ctx_CommittedE[elim] = Ctx_Committed_def[THEN iffD1, elim_format, rule_format]

definition Deps_Committed where
  "Deps_Committed s \<longleftrightarrow> (\<forall>k t k' t' cts v rs deps. wtxn_state (svrs s k) t = Commit cts v rs deps \<and>
    (k', t') \<in> deps \<longrightarrow> is_committed (wtxn_state (svrs s k') t'))"

lemmas Deps_CommittedI = Deps_Committed_def[THEN iffD2, rule_format]
lemmas Deps_CommittedE[elim] = Deps_Committed_def[THEN iffD1, elim_format, rule_format]

definition Cl_Deps_Committed where
  "Cl_Deps_Committed s \<longleftrightarrow> (\<forall>cl k t cts kv_map deps. txn_state (cls s cl) = WtxnCommit cts kv_map deps \<and>
    (k, t) \<in> deps \<longrightarrow> is_committed (wtxn_state (svrs s k) t))"

lemmas Cl_Deps_CommittedI = Cl_Deps_Committed_def[THEN iffD2, rule_format]
lemmas Cl_Deps_CommittedE[elim] = Cl_Deps_Committed_def[THEN iffD1, elim_format, rule_format]

lemmas deps_committed_defs = Ctx_Committed_def Deps_Committed_def Cl_Deps_Committed_def

lemma reach_deps_committed[simp]:
  "reach tps s \<Longrightarrow> Ctx_Committed s \<and> Deps_Committed s \<and> Cl_Deps_Committed s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: deps_committed_defs tps_defs dep_set_init_def split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: deps_committed_defs tps_trans_defs)
      by (smt (verit) state_txn.distinct(5))
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (auto simp add: deps_committed_defs tps_trans_defs)
      by (metis state_txn.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: deps_committed_defs tps_trans_defs get_ctx_def)
      apply (metis (mono_tags, opaque_lifting) state_txn.distinct(9))
      by (metis (mono_tags, opaque_lifting))
  next
    case (WInvoke x1 x2)
    then show ?case apply (simp add: deps_committed_defs tps_trans_defs)
      by (metis state_txn.distinct(5))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: deps_committed_defs tps_trans_defs)
      by (metis (no_types, opaque_lifting) state_txn.distinct(11)) 
  next
    case (WDone x1 x2)
    then show ?case apply (auto simp add: deps_committed_defs tps_trans_defs)
      by (metis (no_types, lifting) is_committed.simps(1) state_txn.inject(3))
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (auto simp add: deps_committed_defs tps_trans_defs)
      apply (smt (verit) add_to_readerset_no_ver_inv add_to_readerset_prep_inv is_committed.elims(3))
      apply (metis add_to_readerset_commit add_to_readerset_commit' is_committed.elims(1) is_committed.simps(1))
      apply (meson add_to_readerset_commit)
      apply (smt (verit) add_to_readerset_no_ver_inv add_to_readerset_prep_inv is_committed.elims(3))
      by (smt (verit) add_to_readerset_no_ver_inv add_to_readerset_prep_inv is_committed.elims(3))
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (auto simp add: deps_committed_defs tps_trans_defs)
      by (metis is_committed.simps(2))+
  qed (simp_all add: deps_committed_defs tps_trans_defs, blast?)
qed

definition Cl_Ctx_Sub_CO where
  "Cl_Ctx_Sub_CO s k \<longleftrightarrow> (\<forall>cl t. (k, t) \<in> cl_ctx (cls s cl) \<longrightarrow> t \<in> set (commit_order s k))"

lemmas Cl_Ctx_Sub_COI = Cl_Ctx_Sub_CO_def[THEN iffD2, rule_format]
lemmas Cl_Ctx_Sub_COE[elim] = Cl_Ctx_Sub_CO_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_ctx_sub_co [simp]: "reach tps s \<Longrightarrow> Cl_Ctx_Sub_CO s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Cl_Ctx_Sub_CO_def tps_defs dep_set_init_def)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: Cl_Ctx_Sub_CO_def tps_trans_defs get_ctx_def)
      subgoal for t apply (cases t, auto)
      by (metis (no_types, opaque_lifting) Commit_Order_Complete_def reach_commit_order_complete
          reach_trans.hyps(2) txid0.exhaust)
      subgoal for t k' apply (cases t, blast)
        using Deps_Committed_def[of s] Commit_Order_Complete_def[of s]
        by (metis (no_types, lifting) is_committed.elims(2) reach_commit_order_complete
            reach_deps_committed txid0.exhaust).
  qed (auto simp add: Cl_Ctx_Sub_CO_def tps_trans_defs)
qed

definition Deps_Closed where
  "Deps_Closed s cl \<longleftrightarrow> (closed' (kvs_of_s s) (cl_ctx (cls s cl)) (R_CC (kvs_of_s s)) \<and> 
    (\<forall>k t cts v rs kv_map deps. wtxn_state (svrs s k) t = Commit cts v rs deps \<or>
      txn_state (cls s cl) = WtxnCommit cts kv_map deps \<longrightarrow>
      closed' (kvs_of_s s) deps (R_CC (kvs_of_s s))))"

lemmas Deps_ClosedI = Deps_Closed_def[THEN iffD2, rule_format]
lemmas Deps_ClosedE[elim] = Deps_Closed_def[THEN iffD1, elim_format, rule_format]

lemmas closed'_defs = closed'_def R_CC_def R_onK_def

lemma reach_deps_closed[simp]:
  "reach tps s \<Longrightarrow> Deps_Closed s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case apply (auto simp add: Deps_Closed_def tps_def closed'_defs)
    apply (metis DiffD2 read_only_Txs_def subsetD visTx'_cl_ctx_subset_writers)
    apply (rotate_tac -1) subgoal for x x' by (induction rule: rtrancl.induct,
      auto simp add: SO_def SO0_def WR_def state_init_def kvs_of_s_def visTx'_def view_of_def
        the_T0 dep_set_init_def)
    apply (metis DiffD2 read_only_Txs_def subsetD visTx'_deps_subset_writers)
    apply (rotate_tac -1) subgoal for x x' by (induction rule: rtrancl.induct,
      auto simp add: SO_def SO0_def WR_def state_init_def kvs_of_s_def visTx'_def view_of_def
        the_T0 dep_set_init_def split: if_split_asm)
    apply (metis DiffD2 read_only_Txs_def subsetD visTx'_cl_deps_subset_writers)
    apply (rotate_tac -1) subgoal for x x' by (induction rule: rtrancl.induct,
      auto simp add: SO_def SO0_def WR_def state_init_def kvs_of_s_def visTx'_def view_of_def
        the_T0 dep_set_init_def split: if_split_asm).
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2)
    { fix x x'
      assume "(x, x') \<in> (SO \<union> \<Union> (range (WR (kvs_of_s s))))\<^sup>*"
      and "x' \<in> visTx' (kvs_of_s s) (cl_ctx (cls s cl)) \<union> RO_le_gst s x1"
      and "txn_state (cls s x1) = Idle"
      then have "x \<in> visTx' (kvs_of_s s) (cl_ctx (cls s' cl)) \<union> RO_le_gst s x1"
        apply (induction rule: rtrancl.induct, simp)
         apply auto
        subgoal sorry
        subgoal sorry
        subgoal sorry \<comment> \<open>SO, c visTx\<close>
        subgoal apply (auto simp add: SO_def SO0_def visTx_visTx')
          subgoal for cla n m apply (cases "Tn (Tn_cl n cla) \<in> RO_le_gst s x1", simp)
            using Rtxn_rts_le_Gst_def[of s cla] SO_ROs_def[of s]
              apply (simp add: ) \<comment> \<open>SO, b RO, cRO\<close>
              (* inv: if rts < rts' and t' in visTx or less than gst, then t in visTx *) sorry
          sorry \<comment> \<open>SO, c RO\<close>
        subgoal sorry \<comment> \<open>WR, c visTx\<close>
        subgoal sorry \<comment> \<open>WR, c RO\<close>
        done
     }
    then show ?case apply (auto simp add: Deps_Closed_def closed'_defs)
      apply (metis DiffD2 read_only_Txs_def subsetD visTx'_cl_ctx_subset_writers)
      subgoal using RInvoke apply (auto simp add: tps_trans_defs RO_le_gst_def)
        by blast+
      sorry
  next
    case (RDone x1 x2 x3 x4)
    then show ?case sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (RegR x1 x2 x3 x4)
    then show ?case sorry
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case sorry
  qed (auto simp add: Deps_Closed_def tps_trans_defs)
qed

subsection \<open>view wellformed\<close>

lemma v_writer_set_commit_order_eq:
  assumes "Commit_Order_Sound' s k"                   
  shows "v_writer ` set (kvs_of_s s k) = set (commit_order s k)"
  using assms
  apply (auto simp add:  Commit_Order_Sound'_def kvs_of_s_def image_def split: ver_state.split)
   apply (metis (mono_tags, lifting) is_committed.cases version.select_convs(2))
   subgoal for t apply (cases "wtxn_state (svrs s k) t", simp)
      apply (metis (opaque_lifting) ver_state.distinct(5) ver_state.inject(1) version.select_convs(2))
     subgoal for cts v rs deps apply (rule exI[where x="\<lparr>v_value = v, v_writer = t,
          v_readerset = {t \<in> rs. get_sn_txn t < txn_sn (cls s (get_cl_txn t))}\<rparr>"], simp)
       by (rule bexI[where x=t], auto)
     done.

lemma reach_kvs_expands [simp]:
  assumes "state_trans s e s'" and "\<And>cl. Sqn_Inv_c s cl" and "\<And>cl. Sqn_Inv_nc s cl"
    and "\<And>cl. PTid_Inv s cl" and "\<And>cl. FTid_Wtxn_Inv s cl"
    and "Kvs_Not_Emp s" and "invariant_list_kvs s"
  shows "kvs_of_s s \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s kvs_of_s s'"
  using assms kvs_of_s_inv[of s e s']
proof (induction e)
  case (RDone x1 x2 x3 x4)
  then show ?case
    by (auto simp add: tps_trans_defs kvs_expands_def vlist_order_def version_order_def kvs_of_s_def
        view_atomic_def full_view_def split: ver_state.split) \<comment> \<open>Continue here!\<close>
next
  case (WCommit x1 x2 x3 x4 x5)
  then show ?case 
    apply (auto simp add: tps_trans_defs kvs_expands_def vlist_order_def kvs_of_s_def full_view_def)
    subgoal by (auto simp add: version_order_def split: ver_state.split)
    subgoal apply (auto simp add: version_order_def) sorry
    using t_is_fresh[of s x1 x2] unfolding fresh_txid_defs
    apply (auto simp add: view_atomic_def full_view_def)
    (*subgoal for k k' i i' apply (cases "i' = length (commit_order s k')", auto split: ver_state.split_asm)
      apply (metis domI is_prepared.simps(2))
      apply (metis domI is_prepared.simps(2))
      apply (metis domIff is_prepared.simps(2) option.distinct(1))
      subgoal sorry
      subgoal sorry
      subgoal sorry
      apply (metis domI is_prepared.simps(3))
      apply (metis domI is_prepared.simps(3))
      by (metis domI is_prepared.simps(3))
    subgoal for k y k' i i' apply (cases "i' = length (commit_order s k')", auto split: ver_state.split_asm)
      apply (metis domI is_prepared.simps(2))
      apply (metis domI is_prepared.simps(2))
      apply (metis domIff is_prepared.simps(2) option.distinct(1))
      subgoal sorry
      subgoal sorry
      subgoal sorry
      apply (metis domI is_prepared.simps(3))
      apply (metis domI is_prepared.simps(3))
      by (metis domI is_prepared.simps(3))
    done*) sorry
qed auto


subsection \<open>View invariants\<close>

lemma write_commit_views_of_s_other_cl_inv:
  assumes "write_commit cl kv_map cts sn u s s'"
(*    and "\<And>k. Commit_Order_Distinct s' k"
    and "Ctx_Committed s"*)
    and "cl' \<noteq> cl"
  shows "views_of_s s' cl' = views_of_s s cl'"
proof -
  have pre: "\<And>k. prefix (commit_order s k) (commit_order s' k)" using assms(1)
    by (simp add: write_commit_def)
  (*have "\<And>k. distinct (commit_order s' k)" using assms(2) by auto
  have "\<And>k. cl_ctx (cls s cl') `` {k} \<subseteq> set (commit_order s k)" using assms(1, 3)
    apply (auto simp add: write_commit_def Ctx_Committed_def)
  using view_of_prefix[of "commit_order s" "commit_order s'" "cl_ctx (cls s cl')"]
     
       WE need:
        \<And>k. prefix (commit_order s k) (commit_order s' k);
        \<And>k. distinct (commit_order s' k);
        \<And>k. cl_ctx (cls s cl') `` {k} \<subseteq> set (commit_order s k)
    *)
  then show ?thesis sorry
qed

definition Views_of_s_Wellformed where
  "Views_of_s_Wellformed s cl \<longleftrightarrow> (view_wellformed (kvs_of_s s) (views_of_s s cl))"

lemmas Views_of_s_WellformedI = Views_of_s_Wellformed_def[THEN iffD2, rule_format]
lemmas Views_of_s_WellformedE[elim] = Views_of_s_Wellformed_def[THEN iffD1, elim_format, rule_format]

lemma reach_views_of_s_wellformed [simp]: "reach tps s \<Longrightarrow> Views_of_s_Wellformed s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Views_of_s_Wellformed_def tps_defs view_of_def views_of_s_def the_T0
        dep_set_init_def view_wellformed_defs full_view_def kvs_of_s_def)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: Views_of_s_Wellformed_def tps_trans_defs views_of_s_def) sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Views_of_s_Wellformed_def tps_trans_defs views_of_s_def) sorry
  qed (auto simp add: Views_of_s_Wellformed_def tps_trans_defs views_of_s_def)
qed

subsection \<open>View Shift\<close>

definition Cl_Ctx_WtxnCommit where
  "Cl_Ctx_WtxnCommit s cl \<longleftrightarrow>
    (\<forall>cts kv_map deps k. txn_state (cls s cl) = WtxnCommit cts kv_map deps \<and> k \<in> dom kv_map \<longrightarrow>
      (k, get_wtxn_cl s cl) \<in> cl_ctx (cls s cl))"

lemmas Cl_Ctx_WtxnCommitI = Cl_Ctx_WtxnCommit_def[THEN iffD2, rule_format]
lemmas Cl_Ctx_WtxnCommitE[elim] = Cl_Ctx_WtxnCommit_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_ctx_wtxncommit [simp]: "reach tps s \<Longrightarrow> Cl_Ctx_WtxnCommit s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Cl_Ctx_WtxnCommit_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Cl_Ctx_WtxnCommit_def tps_trans_defs)
qed

lemma read_commit_added_txid:
  assumes "read_done cl kv_map sn u s s'"
    and "Tn (Tn_cl sn' cl) \<in> (kvs_txids (kvs_of_s s') - kvs_txids (kvs_of_s s))"
  shows "sn' = sn"
  using assms
  apply (auto simp add: read_done_def kvs_of_s_def txid_defs split: ver_state.split) sorry

subsection \<open>View Grows\<close>

lemma view_grows_view_of: "a \<subseteq> b \<Longrightarrow> view_of corder a \<sqsubseteq> view_of corder b"
  apply (simp add: view_of_def)
  by (smt (verit) Collect_mono_iff insert_subset mk_disjoint_insert view_order_def)

lemma view_and_order_grow_view_of:
  assumes "\<And>k. corder' k = (if kv_map k = None then corder k else corder k @ [t])"
    and "b = a \<union> (\<Union>k\<in>dom kv_map. {(k, t)})"
  shows "view_of corder a \<sqsubseteq> view_of corder' b"
  using assms
  apply (auto simp add: view_of_def prefix_def view_order_def split: if_split_asm)
  subgoal for k y t' apply (rule exI[where x=t']) (* showing t is not in corder *)
    sorry.

section \<open>Fp Property\<close>

\<comment> \<open>Fingerprint content invariant and Lemmas for proving the fp_property\<close>

definition RegR_Fp_Inv where
  "RegR_Fp_Inv s k \<longleftrightarrow> (\<forall>t keys kvt_map cts v rs deps.
    txn_state (cls s (get_cl_txn t)) = RtxnInProg keys kvt_map \<and> k \<in> keys \<and> kvt_map k = None \<and>
    wtxn_state (svrs s k) (read_at (wtxn_state (svrs s k)) (gst (cls s (get_cl_txn t))) (get_cl_txn t))
       = Commit cts v rs deps \<longrightarrow>
    v = v_value (last_version (kvs_of_s s k)
      (view_of (commit_order s) (cl_ctx (cls s (get_cl_txn t)) \<union> get_ctx s kvt_map) k)))"

lemmas RegR_Fp_InvI = RegR_Fp_Inv_def[THEN iffD2, rule_format]
lemmas RegR_Fp_InvE[elim] = RegR_Fp_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_reg_r_fp [simp]: "reach tps s \<Longrightarrow> RegR_Fp_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: RegR_Fp_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs get_ctx_def) sorry
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs get_ctx_def) sorry
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs get_ctx_def) sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs get_ctx_def) sorry
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs get_ctx_def) sorry
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs get_ctx_def) sorry
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs get_ctx_def) sorry
  qed (auto simp add: RegR_Fp_Inv_def tps_trans_defs get_ctx_def)
qed

definition Rtxn_Fp_Inv where
  "Rtxn_Fp_Inv s cl \<longleftrightarrow> (\<forall>k t keys kvt_map v.
    txn_state (cls s cl) = RtxnInProg keys kvt_map \<and> kvt_map k = Some (v, t) \<longrightarrow>
     v = v_value (last_version (kvs_of_s s k)
      (view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s kvt_map) k)))"

lemmas Rtxn_Fp_InvI = Rtxn_Fp_Inv_def[THEN iffD2, rule_format]
lemmas Rtxn_Fp_InvE[elim] = Rtxn_Fp_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_fp [simp]: "reach tps s \<Longrightarrow> Rtxn_Fp_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rtxn_Fp_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (Read x1 x2 x3 x4)
    then show ?case apply (auto simp add: Rtxn_Fp_Inv_def tps_trans_defs get_ctx_step) sorry
  next
    case (RDone x1 x2 x3 x4)
    then show ?case sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (RegR x1 x2 x3 x4)
    then show ?case sorry
  next
    case (PrepW x1 x2 x3)
    then show ?case sorry
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case sorry
  qed (auto simp add: Rtxn_Fp_Inv_def tps_trans_defs view_of_def get_ctx_def)
qed


section \<open>Refinement Proof\<close>

abbreviation invariant_list where
  "invariant_list s \<equiv> (\<forall>cl k. invariant_list_kvs s \<and> Sqn_Inv_c s cl \<and> Sqn_Inv_nc s cl \<and> Deps_Closed s cl
    \<and> Views_of_s_Wellformed s cl \<and> Rtxn_Fp_Inv s cl \<and> Commit_Order_Distinct s k \<and> Ctx_Committed s)"

lemma tps_refines_et_es: "tps \<sqsubseteq>\<^sub>med ET_CC.ET_ES"
proof (intro simulate_ES_fun)
  fix gs0 :: "'v state"
  assume p: "init tps gs0"
  then show "init ET_CC.ET_ES (sim gs0)"
    by (auto simp add: ET_CC.ET_ES_defs tps_defs sim_defs kvs_init_def v_list_init_def version_init_def
        dep_set_init_def view_of_def the_T0)
next
  fix gs a and gs' :: "'v state"
  assume p: "tps: gs\<midarrow>a\<rightarrow> gs'" and reach_s: "reach tps gs" and "reach ET_CC.ET_ES (sim gs)"
  hence inv: "invariant_list gs" by simp
  then show "ET_CC.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  using p kvs_of_s_inv[of gs a gs']
  proof (induction a)
    case (RDone cl kvt_map sn u'')
    then show ?case
    apply (auto simp add: read_done_def sim_def intro!: exI [where x="views_of_s gs' cl"])
      apply (auto simp add: ET_CC.ET_cl_txn_def t_is_fresh KvsOfS_Not_Emp_def)
      subgoal (* updated ctx wellformed *) sorry
      subgoal by (metis Views_of_s_Wellformed_def p reach_s reach_trans reach_views_of_s_wellformed)                   
      subgoal (* canCommit *) sorry
      subgoal apply (auto simp add: vShift_MR_RYW_def vShift_MR_def vShift_RYW_def views_of_s_def)
      \<comment> \<open>1. (writer_ver_i, t) \<in> SO \<Longrightarrow> t \<in> K'\K \<Longrightarrow> i \<in> view_of corder (cl_ctx \<union> get_ctx)
          2. writer_ver_i \<in> K'\K \<Longrightarrow> i \<in> view_of corder (cl_ctx \<union> get_ctx)\<close> sorry
      subgoal by (simp add: views_of_s_def view_grows_view_of)
      subgoal sorry
      subgoal by (auto simp add: read_done_def views_of_s_def)
      by (auto simp add: fp_property_def view_snapshot_def Rtxn_Fp_Inv_def)
  next
    case (WCommit cl kv_map cts sn u'')
    then show ?case
    apply (auto simp add: write_commit_def sim_def fp_property_def intro!: exI [where x="views_of_s gs' cl"])
      apply (auto simp add: ET_CC.ET_cl_txn_def t_is_fresh)
      subgoal (* updated ctx wellformed *) sorry
      subgoal (* updated ctx wellformed *) sorry
      subgoal by (simp add: Deps_Closed_def[of gs] closed_closed'[of gs] ET_CC.canCommit_def)
      subgoal apply (auto simp add: vShift_MR_RYW_def vShift_MR_def vShift_RYW_def views_of_s_def) sorry
      subgoal by (simp add: views_of_s_def view_grows_view_of) 
      subgoal sorry
      apply (rule ext) subgoal for cl' apply (cases "cl' = cl"; simp)
      by (metis WCommit.prems(2) state_trans.simps(5) tps_trans write_commit_views_of_s_other_cl_inv).
  qed (auto simp add: sim_def views_of_s_def tps_trans_defs)
qed

end
