section \<open>Eiger Port Plus Protocol Satisfying CCv (Causal+) - Proofs and lemmas\<close>

theory "EP+_TCCv_Proof"
  imports "EP+_Sorted"
begin

subsection \<open>wtxns lemmas\<close>

subsubsection \<open>wtxns_dom lemmas\<close>

lemma wtxns_dom_eq_empty_conv [simp]: "wtxns_dom wtxns = {} \<longleftrightarrow> wtxns = wtxns_emp"
  by (auto simp: wtxns_dom_def)

lemma wtxns_domI1: "wtxns t = Prep ts v \<Longrightarrow> t \<in> wtxns_dom wtxns"
  by (simp add: wtxns_dom_def)

lemma wtxns_domI2: "wtxns t = Commit cts sts lst v rs \<Longrightarrow> t \<in> wtxns_dom wtxns"
  by (simp add: wtxns_dom_def)

lemma wtxns_domD: "t \<in> wtxns_dom wtxns \<Longrightarrow>
  (\<exists>ts v. wtxns t = Prep ts v) \<or> (\<exists>cts sts lst v rs. wtxns t = Commit cts sts lst v rs)"
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
  "wtxns t = Commit cts sts lst v rs \<Longrightarrow> insert t (wtxns_dom wtxns) = wtxns_dom wtxns"
  unfolding wtxns_dom_def by auto


subsubsection \<open>wtxns_vran lemmas\<close>

lemma wtxns_vranI1: "wtxns t = Commit cts sts lst v rs \<Longrightarrow> v \<in> wtxns_vran wtxns"
  apply (simp add: wtxns_vran_def)
  by (metis ver_state.sel(4) wtxns_domI2)

lemma wtxns_vranI2: "wtxns t = Prep ts v \<Longrightarrow> v \<in> wtxns_vran wtxns"
  apply (simp add: wtxns_vran_def)
  by (metis ver_state.sel(3) wtxns_domI1)

lemma wtxns_vran_empty [simp]: "wtxns_vran wtxns_emp = {}"
  by (auto simp: wtxns_vran_def)

lemma wtxns_vran_map_upd [simp]:  "wtxns t = No_Ver \<Longrightarrow>
  wtxns_vran (wtxns (t := Commit cts sts lst v rs)) = insert v (wtxns_vran wtxns)"
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
      
      
subsubsection \<open>wtxns_rsran lemmas\<close>

lemma wtxns_rsranI: "wtxns t = Commit cts sts lst v rs \<Longrightarrow> rs \<subseteq> wtxns_rsran wtxns"
  apply (simp add: wtxns_rsran_def)
  by (metis (mono_tags, lifting) Sup_upper get_rs.simps(3) mem_Collect_eq wtxns_domI2)

lemma wtxns_rsran_empty [simp]: "wtxns_rsran wtxns_emp = {}"
  by (auto simp: wtxns_rsran_def)

lemma wtxns_rsran_map_upd1 [simp]:  "wtxns t = No_Ver \<Longrightarrow>
  wtxns_rsran (wtxns (t := Prep ts v)) = wtxns_rsran wtxns"
  by (auto simp add: wtxns_rsran_def)

lemma wtxns_rsran_map_upd2 [simp]:  "wtxns t = No_Ver \<Longrightarrow>
  wtxns_rsran (wtxns (t := Commit cts sts lst v rs)) = rs \<union> (wtxns_rsran wtxns)"
  by (auto simp add: wtxns_rsran_def)

lemma wtxns_rsran_map_upd3 [simp]:  "is_prepared (wtxns t) \<Longrightarrow>
  wtxns_rsran (wtxns (t := Commit cts sts lst v rs)) = rs \<union> (wtxns_rsran wtxns)"
  apply (auto simp add: wtxns_rsran_def)
  by (metis empty_iff get_rs.simps(2) is_prepared.elims(2) wtxns_domIff)

lemma wtxns_rsran_map_upd4 [simp]:  "wtxns t_wr = Commit cts sts lst v rs \<Longrightarrow>
  wtxns_rsran (wtxns (t_wr := Commit cts sts lst v (insert t3 rs))) = insert t3 (wtxns_rsran wtxns)"
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
  "wtxns_dom (add_to_readerset wtxns t rts rlst t') = wtxns_dom wtxns"
  by (auto simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_wtxns_rsran:
  assumes "is_committed (wtxns t_wr)" (* later use read_at_is_committed to fulfill this *)
  shows "wtxns_rsran (add_to_readerset wtxns t rts rlst t_wr) = insert (t, rts, rlst) (wtxns_rsran (wtxns))"
  using assms
  by (auto simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_no_ver_inv:
  "add_to_readerset wtxns t rts rlst t' t'' = No_Ver \<longleftrightarrow> wtxns t'' = No_Ver"
  by (simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_prep_inv:
  "add_to_readerset wtxns t rts rlst t' t'' = Prep ts v \<longleftrightarrow> wtxns t'' = Prep ts v"
  by (simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_commit:
  "add_to_readerset wtxns t rts rlst t' t'' = Commit cts sts lst v rs \<Longrightarrow>
    \<exists>rs'. wtxns t'' = Commit cts sts lst v rs'"
  apply (simp add: add_to_readerset_def)
  by (cases "wtxns t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_commit_subset:
  "add_to_readerset wtxns t rts rlst t' t'' = Commit cts sts lst v rs \<Longrightarrow>
    \<exists>rs'. wtxns t'' = Commit cts sts lst v rs' \<and> rs' \<subseteq> rs"
  apply (simp add: add_to_readerset_def)
  by (cases "wtxns t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_commit':
  "wtxns t'' = Commit cts sts lst v rs' \<Longrightarrow>
    \<exists>rs. add_to_readerset wtxns t rts rlst t' t'' = Commit cts sts lst v rs"
  apply (simp add: add_to_readerset_def)
  by (cases "wtxns t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_commit'_subset:
  "wtxns t'' = Commit cts sts lst v rs' \<Longrightarrow>
    \<exists>rs. add_to_readerset wtxns t rts rlst t' t'' = Commit cts sts lst v rs \<and> rs' \<subseteq> rs"
  apply (simp add: add_to_readerset_def)
  by (cases "wtxns t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_upd:
  assumes "wtxns' = add_to_readerset wtxns t rts rlst t_wr"
    and "t' \<noteq> t_wr"
  shows "wtxns' t' = wtxns t'"
  using assms
  by (simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_pres_get_ts:
  "get_ts (add_to_readerset wtxns t rts rlst t_wr t') = get_ts (wtxns t')"
  by (smt (verit, ccfv_SIG) add_to_readerset_commit add_to_readerset_no_ver_inv
      add_to_readerset_prep_inv ver_state.exhaust_sel ver_state.sel(2))

lemma add_to_readerset_pres_is_committed:
  "is_committed (add_to_readerset wtxns t rts rlst t_wr t') = is_committed (wtxns t')"
  by (smt (verit, best) add_to_readerset_no_ver_inv add_to_readerset_prep_inv is_committed.elims(1))

lemma ran_map_upd_None_finite:
  "finite (ran m) \<Longrightarrow> finite (ran (m (a := None)))"
  apply (simp add: ran_def)
  by (smt (verit) Collect_mono_iff rev_finite_subset)

lemma pending_wtxns_ts_empty:
  "pending_wtxns_ts (svr_state (svrs s k)) = {} \<longleftrightarrow>
    (\<forall>t. \<exists>cts sts lst v rs. svr_state (svrs s k) t \<in> {No_Ver, Commit cts sts lst v rs})"
  apply (auto simp add: pending_wtxns_ts_def)
  apply (metis get_rs.elims)
  by (metis ver_state.distinct(1) ver_state.distinct(5))

lemma pending_wtxns_ts_non_empty:
  assumes "svr_state (svrs s k) t \<noteq> No_Ver"
    and "\<forall>cts sts lst v rs. svr_state (svrs s k) t \<noteq> Commit cts sts lst v rs"
  shows "pending_wtxns_ts (svr_state (svrs s k)) \<noteq> {}"
  using assms apply (auto simp add: pending_wtxns_ts_def)
  by (meson get_rs.elims)

lemma finite_pending_wtxns_rtxn:
  assumes "finite (pending_wtxns_ts (svr_state (svrs s k)))"
  shows "finite (pending_wtxns_ts (add_to_readerset (svr_state (svrs s k)) t' rts rlst t))"
  using assms
  by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def add_to_readerset_prep_inv)

lemma finite_pending_wtxns_adding:
  assumes "finite (pending_wtxns_ts (svr_state (svrs s k)))"
  shows "finite (pending_wtxns_ts ((svr_state (svrs s k)) (t := Prep prep_t v)))"
  using assms
  apply (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def)
  by (metis dual_order.trans linorder_le_cases)

lemma finite_pending_wtxns_removing: 
  assumes "finite (pending_wtxns_ts (svr_state (svrs s k)))"
  shows "finite (pending_wtxns_ts ((svr_state (svrs s k)) (t := Commit cts sts lst v rs)))"
  using assms
  by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def)

lemma pending_wtxns_adding_ub:
  assumes "\<forall>ts \<in> pending_wtxns_ts (svr_state (svrs s k)). ts \<le> clk"
  shows "\<forall>ts \<in> pending_wtxns_ts ((svr_state (svrs s k)) (t := Prep clk v)). ts \<le> clk"
  using assms by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def)

lemma pending_wtxns_removing_ub:
  assumes "\<forall>ts \<in> pending_wtxns_ts (svr_state (svrs s k)). ts \<le> clk"
  shows "\<forall>ts \<in> pending_wtxns_ts ((svr_state (svrs s k)) (t := Commit cts sts lst v rs)). ts \<le> clk"
  using assms by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def)

lemma pending_wtxns_rtxn:
  "pending_wtxns_ts (add_to_readerset (svr_state (svrs s k)) t' rts rlst t) =
   pending_wtxns_ts (svr_state (svrs s k))"
  by (auto simp add: pending_wtxns_ts_def add_to_readerset_prep_inv)

lemma pending_wtxns_adding:
  assumes "\<forall>clk v. svr_state (svrs s k) t \<noteq> Prep clk v"
  shows "pending_wtxns_ts ((svr_state (svrs s k)) (t := Prep clk v)) =
         insert clk (pending_wtxns_ts (svr_state (svrs s k)))"
  using assms apply (auto simp add: pending_wtxns_ts_def)
  by metis

lemma pending_wtxns_removing:
  assumes "svr_state (svrs s k) t = Prep clk v"
  shows "pending_wtxns_ts ((svr_state (svrs s k)) (t := Commit cts sts lst v rs)) =
          pending_wtxns_ts (svr_state (svrs s k)) \<or>
         pending_wtxns_ts ((svr_state (svrs s k)) (t := Commit cts sts lst v rs)) =
          Set.remove clk (pending_wtxns_ts (svr_state (svrs s k)))"
  using assms apply (auto simp add: pending_wtxns_ts_def)
  by (metis ver_state.inject(1))+

lemma other_prep_t_inv:
  assumes "svr_state (svrs s k) t = Prep prep_t v"
    and "t \<noteq> t'"
  shows "prep_t \<in> pending_wtxns_ts ((svr_state (svrs s k))(t' := b))"
  using assms
  by (auto simp add: pending_wtxns_ts_def)

lemma view_of_prefix:
  assumes "\<And>k. prefix (corder k) (corder' k)"
    and "\<And>k. distinct (corder' k)"
    and "\<And>k. (set (corder' k) - set (corder k)) \<inter> u k = {}"
  shows "view_of corder' u = view_of corder u"
  unfolding view_of_def
proof (rule ext, rule Collect_eqI, rule iffI)
  fix k pos
  assume *: "\<exists>t. pos = index_of (corder k) t \<and> t \<in> u k \<and> t \<in> set (corder k)"
  show "\<exists>t. pos = index_of (corder' k) t \<and> t \<in> u k \<and> t \<in> set (corder' k)"
  proof -
    from assms(1) obtain zs where p: "corder k @ zs = corder' k" using prefixE by metis
    from * obtain tid where **: "tid \<in> u k" "tid \<in> set (corder k)"
      "pos = index_of (corder k) tid" by blast
    from \<open>tid \<in> set (corder k)\<close> obtain i
      where the_i: "i < length (corder k) \<and> corder k ! i = tid" by (meson in_set_conv_nth)
    with p ** have the1: "index_of (corder k) tid = i"
      using assms(2) distinct_Ex1[of "corder k" tid]
      by (metis (mono_tags, lifting) distinct_append[of "corder k" zs] the_equality)
    from ** have tid_in_corder': "tid \<in> set (corder' k)" using assms(1) set_mono_prefix by blast
    then obtain i' where the_i': "i' < length (corder' k) \<and> corder' k ! i' = tid"
      by (meson in_set_conv_nth)
    with p tid_in_corder' have the2: "index_of (corder' k) tid = i'"
      using assms(2) distinct_Ex1[of "corder' k" tid] by (simp add: the1_equality)
    from p the_i the_i' have "i = i'" using assms(1,2)[of k]
      by (metis distinct_conv_nth nth_append order_less_le_trans prefix_length_le)
    with ** have "pos = index_of (corder' k) tid"
      using the1 the2 by presburger
    then show ?thesis using ** tid_in_corder' by auto
  qed
next
  fix k pos
  assume *: "\<exists>t. pos = index_of (corder' k) t \<and> t \<in> u k \<and> t \<in> set (corder' k)"
  show "\<exists>t. pos = index_of (corder k) t \<and> t \<in> u k \<and> t \<in> set (corder k)"
  proof -
    from assms(1) obtain zs where p: "corder k @ zs = corder' k" using prefixE by metis
    from * obtain tid where **: "tid \<in> u k" "tid \<in> set (corder' k)"
      "pos = index_of (corder' k) tid" by blast
    from \<open>tid \<in> set (corder' k)\<close> obtain i' where the_i':"i' < length (corder' k) \<and> corder' k ! i' = tid"
      by (meson in_set_conv_nth)
    with p ** have the2: "index_of (corder' k) tid = i'"
      using assms(2) distinct_Ex1[of "corder' k" tid]
      by (metis (mono_tags, lifting) the_equality)
    from ** have tid_in_corder: "tid \<in> set (corder k)" using assms(3) by blast
    then obtain i where the_i:"i < length (corder k) \<and> corder k ! i = tid"
      by (meson in_set_conv_nth)
    with p tid_in_corder have the1: "index_of (corder k) tid = i" using assms(2)
      distinct_Ex1[of "corder k" tid] distinct_append[of "corder k" zs]
      by (metis (mono_tags, lifting) the_equality)
    from p the_i the_i' have "i = i'" using assms(1,2)[of k]
      by (metis distinct_conv_nth nth_append order_less_le_trans prefix_length_le)
    with ** have "pos = index_of (corder k) tid"
      using the1 the2 by presburger
    then show ?thesis using ** tid_in_corder by auto
  qed
qed


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


subsection \<open>monotonic lemmas and inequality of timestamps invariants\<close>

lemma svr_clock_monotonic:
  "state_trans s e s' \<Longrightarrow> svr_clock (svrs s' svr) \<ge> svr_clock (svrs s svr)"
  by (induction e) (auto simp add: tps_trans_defs)

lemma cl_clock_monotonic:
  "state_trans s e s' \<Longrightarrow> cl_clock (cls s' cl) \<ge> cl_clock (cls s cl)"
  by (induction e) (auto simp add: tps_trans_defs)

definition Pend_Wt_UB where
  "Pend_Wt_UB s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns_ts (svr_state (svrs s svr)). ts \<le> svr_clock (svrs s svr))"

lemmas Pend_Wt_UBI = Pend_Wt_UB_def[THEN iffD2, rule_format]
lemmas Pend_Wt_UBE[elim] = Pend_Wt_UB_def[THEN iffD1, elim_format, rule_format]

lemma reach_pend_wt_ub [simp]: "reach tps_s s \<Longrightarrow> Pend_Wt_UB s svr"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Pend_Wt_UB_def tps_s_defs pending_wtxns_ts_def split: if_split_asm)
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
    case (CommitW x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: Pend_Wt_UB_def tps_trans_defs pending_wtxns_ts_def split: if_split_asm)
      by (meson le_Suc_eq max.coboundedI1 notin_set_remove1)
  qed (auto simp add: Pend_Wt_UB_def tps_trans_defs)
qed


definition Finite_Pend_Inv where
  "Finite_Pend_Inv s svr \<longleftrightarrow> finite (pending_wtxns_ts (svr_state (svrs s svr)))"

lemmas Finite_Pend_InvI = Finite_Pend_Inv_def[THEN iffD2, rule_format]
lemmas Finite_Pend_InvE[elim] = Finite_Pend_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_finitepending [simp]: "reach tps_s s \<Longrightarrow> Finite_Pend_Inv s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Finite_Pend_Inv_def tps_s_defs pending_wtxns_ts_def)
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


definition Svr_Clk_le_Lst where
  "Svr_Clk_le_Lst s k \<longleftrightarrow> svr_lst (svrs s k) \<le> svr_clock (svrs s k)"

lemmas Svr_Clk_le_LstI = Svr_Clk_le_Lst_def[THEN iffD2, rule_format]
lemmas Svr_Clk_le_LstE[elim] = Svr_Clk_le_Lst_def[THEN iffD1, elim_format, rule_format]

lemma reach_svr_clock_svr_lst_inv [simp, dest]: "reach tps_s s \<Longrightarrow> Svr_Clk_le_Lst s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Svr_Clk_le_Lst_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (CommitW x91 x92 x93 x94)
    then show ?case
      apply (auto simp add: Svr_Clk_le_Lst_def tps_trans_defs split: if_split_asm)
      by (smt Finite_Pend_Inv_def Min_le_iff Pend_Wt_UB_def emptyE finite_pending_wtxns_removing
          le_SucI le_max_iff_disj pending_wtxns_removing_ub reach_finitepending reach_pend_wt_ub)
  qed (auto simp add: Svr_Clk_le_Lst_def tps_trans_defs)
qed

definition Pend_Wt_LB where
  "Pend_Wt_LB s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns_ts (svr_state (svrs s svr)). svr_lst (svrs s svr) \<le> ts)"

lemmas Pend_Wt_LBI = Pend_Wt_LB_def[THEN iffD2, rule_format]
lemmas Pend_Wt_LBE[elim] = Pend_Wt_LB_def[THEN iffD1, elim_format, rule_format]

lemma reach_pend_wt_lb [simp]: "reach tps_s s \<Longrightarrow> Pend_Wt_LB s svr"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Pend_Wt_LB_def tps_s_defs )
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
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (auto simp add: Pend_Wt_LB_def tps_trans_defs split: if_split_asm)
      by (meson Finite_Pend_Inv_def Min_le finite_pending_wtxns_removing reach_finitepending)
  qed(auto simp add: Pend_Wt_LB_def tps_trans_defs)
qed

lemma min_pending_wtxns_monotonic:
  assumes "state_trans s e s'"
    and "pending_wtxns_ts (svr_state (svrs s k)) \<noteq> {}"
    and "pending_wtxns_ts (svr_state (svrs s' k)) \<noteq> {}"
    and "reach tps_s s"
  shows "Min (pending_wtxns_ts (svr_state (svrs s k))) \<le>
         Min (pending_wtxns_ts (svr_state (svrs s' k)))"
  using assms
proof (induction e)
  case (RegR x1 x2 x3 x4)
  then show ?case
  apply (auto simp add: tps_trans_defs pending_wtxns_ts_def)
    by (smt (z3) Collect_cong add_to_readerset_prep_inv nat_le_linear)
next
  case (PrepW x1 x2 x3)
  then show ?case apply (auto simp add: tps_trans_defs)
    using Min_insert_larger[of "pending_wtxns_ts (svr_state (svrs s x1))"
        "pending_wtxns_ts (svr_state (svrs s' x1))" "svr_clock (svrs s x1)"]
      pending_wtxns_adding [of s x1] Pend_Wt_UB_def[of s] Finite_Pend_Inv_def[of s]
    by (cases "k = x1"; auto simp add: pending_wtxns_ts_def)
next
  case (CommitW x1 x2 x3 x4)
  then show ?case using Finite_Pend_Inv_def[of s]
    apply (auto simp add: tps_trans_defs fold_pending_wtxns_fun_upd)
    by (metis Min.coboundedI Min_in Min_remove empty_iff pending_wtxns_removing)
  qed (auto simp add: tps_trans_defs pending_wtxns_ts_def)


lemma svr_lst_monotonic:
  assumes "state_trans s e s'"
    and "reach tps_s s"
  shows "svr_lst (svrs s' svr) \<ge> svr_lst (svrs s svr)"
  using assms
  proof (induction e)
    case (CommitW k t)
    then show ?case using Svr_Clk_le_Lst_def[of s] Finite_Pend_Inv_def[of s] Pend_Wt_LB_def[of s]
      apply (auto simp add: tps_trans_defs split: if_split_asm)
      by (metis Min_in empty_iff finite_pending_wtxns_removing member_remove pending_wtxns_removing)
  qed (auto simp add: tps_trans_defs)


definition Rlst_le_Lst where
  "Rlst_le_Lst s k \<longleftrightarrow> (\<forall>t_wr cts ts lst v rs rlst rts t.
    svr_state (svrs s k) t_wr = Commit cts ts lst v rs \<and> (t, rts, rlst) \<in> rs
      \<longrightarrow> rlst \<le> svr_lst (svrs s k))"
                                                           
lemmas Rlst_le_LstI = Rlst_le_Lst_def[THEN iffD2, rule_format]
lemmas Rlst_le_LstE[elim] = Rlst_le_Lst_def[THEN iffD1, elim_format, rule_format]

lemma reach_rlst_le_lst [simp]: "reach tps_s s \<Longrightarrow> Rlst_le_Lst s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rlst_le_Lst_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: Rlst_le_Lst_def tps_trans_defs add_to_readerset_def split: ver_state.split)
      by blast+
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (auto simp add: Rlst_le_Lst_def tps_trans_defs)
      by blast
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case using svr_lst_monotonic[of s "CommitW x1 x2 x3 x4" s' x1]
      apply (auto simp add: Rlst_le_Lst_def tps_trans_defs)
      using dual_order.trans apply blast
      by (smt (z3) dual_order.trans empty_iff)
  qed (auto simp add: Rlst_le_Lst_def tps_trans_defs)
qed

definition Get_lst_le_Lst where
  "Get_lst_le_Lst s k \<longleftrightarrow> (\<forall>t cts sts lst v rs.
    svr_state (svrs s k) t = Commit cts sts lst v rs \<longrightarrow> lst \<le> svr_lst (svrs s k))"

lemmas Get_lst_le_LstI = Get_lst_le_Lst_def[THEN iffD2, rule_format]
lemmas Get_lst_le_LstE[elim] = Get_lst_le_Lst_def[THEN iffD1, elim_format, rule_format]

lemma reach_get_lst_le_lst [simp]: "reach tps_s s \<Longrightarrow> Get_lst_le_Lst s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Get_lst_le_Lst_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4)
    then show ?case apply (auto simp add: Get_lst_le_Lst_def tps_trans_defs)
      by (meson add_to_readerset_commit)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (auto simp add: Get_lst_le_Lst_def tps_trans_defs)
      by blast
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case using svr_lst_monotonic[of s "CommitW x1 x2 x3 x4" s' x1]
      apply (auto simp add: Get_lst_le_Lst_def tps_trans_defs)
      using dual_order.trans apply blast
      apply (smt (z3) empty_iff)
      by (smt (z3) empty_iff sup.absorb_iff2 sup.bounded_iff)
  qed (auto simp add: Get_lst_le_Lst_def tps_trans_defs)
qed


definition Lst_map_le_Lst where
  "Lst_map_le_Lst s cl k \<longleftrightarrow> (lst_map (cls s cl) k \<le> svr_lst (svrs s k))"
                                                           
lemmas Lst_map_le_LstI = Lst_map_le_Lst_def[THEN iffD2, rule_format]
lemmas Lst_map_le_LstE[elim] = Lst_map_le_Lst_def[THEN iffD1, elim_format, rule_format]

lemma reach_lst_map_le_svr_lst [simp]: "reach tps_s s \<Longrightarrow> Lst_map_le_Lst s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Lst_map_le_Lst_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Lst_map_le_Lst_def tps_trans_defs)
      by (smt (verit) Rlst_le_Lst_def reach_rlst_le_lst)
  next
    case (WDone x1 x2 x3)
    then obtain cts ts lst v rs where
      "k \<in> dom x2 \<Longrightarrow> svr_state (svrs s k) (get_wtxn s x1) = Commit cts ts lst v rs"
      by (auto simp add: tps_trans_defs, blast)
    then show ?case using WDone apply (auto simp add: Lst_map_le_Lst_def tps_trans_defs domI)
      by (smt (verit) Get_lst_le_Lst_def reach_get_lst_le_lst)
  next
  case (CommitW x1 x2 x3 x4)
    then show ?case using svr_lst_monotonic[of s "CommitW x1 x2 x3 x4" s' x1]
      apply (auto simp add: Lst_map_le_Lst_def tps_trans_defs)
      by (smt (z3) all_not_in_conv le_trans)
  qed (auto simp add: Lst_map_le_Lst_def tps_trans_defs)
qed

definition Rlst_ge_Lst_map where
  "Rlst_ge_Lst_map s cl k \<longleftrightarrow> (\<forall>t cts ts lst v rs rlst rts.
    svr_state (svrs s k) t = Commit cts ts lst v rs \<and> (get_txn s cl, rts, rlst) \<in> rs
      \<longrightarrow> lst_map (cls s cl) k \<le> rlst)"
                                                           
lemmas Rlst_ge_Lst_mapI = Rlst_ge_Lst_map_def[THEN iffD2, rule_format]
lemmas Rlst_ge_Lst_mapE[elim] = Rlst_ge_Lst_map_def[THEN iffD1, elim_format, rule_format]

lemma reach_rlst_ge_lst_map [simp]: "reach tps_s s \<Longrightarrow> Rlst_ge_Lst_map s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rlst_ge_Lst_map_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Rlst_ge_Lst_map_def tps_trans_defs) sorry
        (*inv : only one rst rlst for each transaction in rs*)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: Rlst_ge_Lst_map_def tps_trans_defs) sorry
  next
    case (WDone x1 x2 x3)
    then show ?case apply (auto simp add: Rlst_ge_Lst_map_def tps_trans_defs) sorry
  next
    case (RegR x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: Rlst_ge_Lst_map_def tps_trans_defs add_to_readerset_def split: ver_state.split)
      using reach_lst_map_le_svr_lst apply blast
      by blast+
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (auto simp add: Rlst_ge_Lst_map_def tps_trans_defs)
      by blast
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (auto simp add: Rlst_ge_Lst_map_def tps_trans_defs)
      by blast
  qed (auto simp add: Rlst_ge_Lst_map_def tps_trans_defs)
qed

definition Get_lst_ge_Lst_map where
  "Get_lst_ge_Lst_map s cl k \<longleftrightarrow> (\<forall>cts ts lst v rs.
    svr_state (svrs s k) (get_wtxn s cl) = Commit cts ts lst v rs \<longrightarrow> lst_map (cls s cl) k \<le> lst)"
                                                           
lemmas Get_lst_ge_Lst_mapI = Get_lst_ge_Lst_map_def[THEN iffD2, rule_format]
lemmas Get_lst_ge_Lst_mapE[elim] = Get_lst_ge_Lst_map_def[THEN iffD1, elim_format, rule_format]

lemma reach_get_lst_ge_lst_map [simp]: "reach tps_s s \<Longrightarrow> Get_lst_ge_Lst_map s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Get_lst_ge_Lst_map_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)next
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Get_lst_ge_Lst_map_def tps_trans_defs) sorry
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: Get_lst_ge_Lst_map_def tps_trans_defs) sorry
  next
    case (WDone x1 x2 x3)
    then show ?case apply (auto simp add: Get_lst_ge_Lst_map_def tps_trans_defs) sorry
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (auto simp add: Get_lst_ge_Lst_map_def tps_trans_defs)
      by (meson add_to_readerset_commit)
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (auto simp add: Get_lst_ge_Lst_map_def tps_trans_defs)
      using reach_lst_map_le_svr_lst by blast
  qed (auto simp add: Get_lst_ge_Lst_map_def tps_trans_defs)
qed

lemma lst_map_monotonic:
  assumes "state_trans s e s'"
    and "reach tps_s s"
  shows "lst_map (cls s cl) k \<le> lst_map (cls s' cl) k"
  using assms
proof (induction e)
  case (Read x1 x2 x3 x4 x5 x6 x7)
  then show ?case apply (auto simp add: tps_trans_defs)
    using Rlst_ge_Lst_map_def[of s] reach_rlst_ge_lst_map by blast
next
  case (WDone x1 x2 x3)
  then obtain cts ts lst v rs where
    "k \<in> dom x2 \<Longrightarrow> svr_state (svrs s k) (get_wtxn s x1) = Commit cts ts lst v rs"
    by (auto simp add: tps_trans_defs, blast)
  then show ?case using WDone apply (auto simp add: tps_trans_defs domI)
    using Get_lst_ge_Lst_map_def[of s] reach_get_lst_ge_lst_map by blast
qed (auto simp add: tps_trans_defs)

definition Finite_Dom_Kv_map where
  "Finite_Dom_Kv_map s cl \<longleftrightarrow>
    (\<forall>kv_map cts. cl_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map} \<longrightarrow>
      finite (dom (kv_map)))"
                                                           
lemmas Finite_Dom_Kv_mapI = Finite_Dom_Kv_map_def[THEN iffD2, rule_format]
lemmas Finite_Dom_Kv_mapE[elim] = Finite_Dom_Kv_map_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_finite_dom_kv_map [simp]: "reach tps_s s \<Longrightarrow> Finite_Dom_Kv_map s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Finite_Dom_Kv_map_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Finite_Dom_Kv_map_def tps_trans_defs)
qed

definition Finite_Dom_Kv_map_rd where
  "Finite_Dom_Kv_map_rd s cl \<longleftrightarrow>
    (\<forall>keys kv_map. cl_state (cls s cl) = RtxnInProg keys kv_map \<longrightarrow>
      finite (dom (kv_map)) \<and> keys \<noteq> {})"
                                                           
lemmas Finite_Dom_Kv_map_rdI = Finite_Dom_Kv_map_rd_def[THEN iffD2, rule_format]
lemmas Finite_Dom_Kv_map_rdE[elim] = Finite_Dom_Kv_map_rd_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_finite_dom_kv_map_rd [simp]: "reach tps_s s \<Longrightarrow> Finite_Dom_Kv_map_rd s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Finite_Dom_Kv_map_rd_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Finite_Dom_Kv_map_rd_def tps_trans_defs)
qed

definition Finite_Keys where
  "Finite_Keys s cl \<longleftrightarrow>
    (\<forall>keys kv_map. cl_state (cls s cl) = RtxnInProg keys kv_map \<longrightarrow> finite keys)"
                                                           
lemmas Finite_KeysI = Finite_Keys_def[THEN iffD2, rule_format]
lemmas Finite_KeysE[elim] = Finite_Keys_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_finite_keys [simp]: "reach tps_s s \<Longrightarrow> Finite_Keys s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Finite_Keys_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Finite_Keys_def tps_trans_defs)
qed

definition Finite_Lst_map_Ran where
  "Finite_Lst_map_Ran s cl \<longleftrightarrow> finite (range (lst_map (cls s cl)))"
                                                           
lemmas Finite_Lst_map_RanI = Finite_Lst_map_Ran_def[THEN iffD2, rule_format]
lemmas Finite_Lst_map_RanE[elim] = Finite_Lst_map_Ran_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_finite_lst_map_ran [simp]: "reach tps_s s \<Longrightarrow> Finite_Lst_map_Ran s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Finite_Lst_map_Ran_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Finite_Lst_map_Ran_def tps_trans_defs)
      by (meson image_mono rev_finite_subset subset_UNIV)
  next
    case (WDone x1 x2 x3)
    then show ?case apply (auto simp add: Finite_Lst_map_Ran_def tps_trans_defs)
       apply (meson image_mono rev_finite_subset subset_UNIV)
        using Finite_Dom_Kv_map_def[of s x1] by (simp add: image_def dom_def)
  qed (auto simp add: Finite_Lst_map_Ran_def tps_trans_defs)
qed

lemma lst_map_min_monotonic:
  assumes "state_trans s e s'"
    and "reach tps_s s"
  shows "Min (range (lst_map (cls s cl))) \<le> Min (range (lst_map (cls s' cl)))"
  using assms lst_map_monotonic[of s] Finite_Lst_map_Ran_def[of s] Finite_Lst_map_Ran_def[of s']
  apply (auto simp add: reach_trans)
  by (meson Min.coboundedI dual_order.trans rangeI)

definition Gst_le_Min_Lst_map where
  "Gst_le_Min_Lst_map s cl \<longleftrightarrow> (gst (cls s cl) \<le> Min (range (lst_map (cls s cl))))"
                                                           
lemmas Gst_le_Min_Lst_mapI = Gst_le_Min_Lst_map_def[THEN iffD2, rule_format]
lemmas Gst_le_Min_Lst_mapE[elim] = Gst_le_Min_Lst_map_def[THEN iffD1, elim_format, rule_format]

lemma reach_gst_le_min_lst_map [simp]: "reach tps_s s \<Longrightarrow> Gst_le_Min_Lst_map s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Gst_le_Min_Lst_map_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case using lst_map_min_monotonic[of s "Read x1 x2 x3 x4 x5 x6 x7" s' x1]
      apply (simp add: Gst_le_Min_Lst_map_def tps_trans_defs)
      by (smt (z3) Read.prems(1) le_trans reach.reach_trans reach_finite_lst_map_ran)
  next
    case (WDone x1 x2 x3)
    then show ?case using lst_map_min_monotonic[of s "WDone x1 x2 x3" s' x1]
      apply (simp add: Gst_le_Min_Lst_map_def tps_trans_defs)
      by (smt (z3) WDone.prems(1) le_trans reach.reach_trans reach_finite_lst_map_ran)
  qed (auto simp add: Gst_le_Min_Lst_map_def tps_trans_defs)
qed

lemma gst_monotonic:
  assumes "state_trans s e s'"
    and "reach tps_s s"
  shows "gst (cls s' cl) \<ge> gst (cls s cl)"
  using assms using Gst_le_Min_Lst_map_def[of s]
  by (induction e) (auto simp add: tps_trans_defs)

definition Gst_le_Lst_map where
  "Gst_le_Lst_map s cl k \<longleftrightarrow> (gst (cls s cl) \<le> lst_map (cls s cl) k)"
                                                           
lemmas Gst_le_Lst_mapI = Gst_le_Lst_map_def[THEN iffD2, rule_format]
lemmas Gst_le_Lst_mapE[elim] = Gst_le_Lst_map_def[THEN iffD1, elim_format, rule_format]

lemma reach_gst_le_svr_lst [simp]: "reach tps_s s \<Longrightarrow> Gst_le_Lst_map s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Gst_le_Lst_map_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RInvoke x1 x2 x3)
    then show ?case apply (simp add: Gst_le_Lst_map_def tps_trans_defs)
      by (meson Finite_Lst_map_Ran_def Min_le rangeI reach_finite_lst_map_ran)
  next
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Gst_le_Lst_map_def tps_trans_defs)
      by (smt (z3) Rlst_ge_Lst_map_def cl_conf.cases_scheme cl_conf.select_convs(2) le_trans
          reach_rlst_ge_lst_map reach_trans.hyps(2) txid0.inject)
  next
    case (WDone x1 x2 x3)
    then obtain cts ts lst v rs where
      "k \<in> dom x2 \<Longrightarrow> svr_state (svrs s k) (get_wtxn s x1) = Commit cts ts lst v rs"
      by (auto simp add: tps_trans_defs, blast)
    then show ?case using WDone apply (auto simp add: Gst_le_Lst_map_def tps_trans_defs domI)
      by (smt (z3) Get_lst_ge_Lst_map_def cl_conf.cases_scheme cl_conf.select_convs(2) le_trans
          reach_get_lst_ge_lst_map reach_trans.hyps(2) txid0.inject)
  qed (auto simp add: Gst_le_Lst_map_def tps_trans_defs)
qed

definition Pend_Wt_Inv where
  "Pend_Wt_Inv s k \<longleftrightarrow> (\<forall>prep_t. prep_t \<in> pending_wtxns_ts (svr_state (svrs s k))
    \<longleftrightarrow> (\<exists>t v. svr_state (svrs s k) t = Prep prep_t v))"
                                                           
lemmas Pend_Wt_InvI = Pend_Wt_Inv_def[THEN iffD2, rule_format]
lemmas Pend_Wt_InvE[elim] = Pend_Wt_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_pend_wt_inv [simp]: "reach tps_s s \<Longrightarrow> Pend_Wt_Inv s cl"
  by (auto simp add: Pend_Wt_Inv_def tps_def pending_wtxns_ts_def)

definition Lst_Lt_Pts where
  "Lst_Lt_Pts s k \<longleftrightarrow> (\<forall>t prep_t v. svr_state (svrs s k) t = Prep prep_t v \<longrightarrow> svr_lst (svrs s k) \<le> prep_t)"
                                                           
lemmas Lst_Lt_PtsI = Lst_Lt_Pts_def[THEN iffD2, rule_format]
lemmas Lst_Lt_PtsE[elim] = Lst_Lt_Pts_def[THEN iffD1, elim_format, rule_format]

lemma reach_svr_lst_lt_pts [simp]: "reach tps_s s \<Longrightarrow> Lst_Lt_Pts s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Lst_Lt_Pts_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
  case (RegR x1 x2 x3 x4)
  then show ?case apply (auto simp add: Lst_Lt_Pts_def tps_trans_defs)
    by (meson add_to_readerset_prep_inv)
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (auto simp add: Lst_Lt_Pts_def tps_trans_defs)
      apply (metis emptyE other_prep_t_inv)
      by (metis Finite_Pend_Inv_def Min.coboundedI finite_pending_wtxns_removing other_prep_t_inv
          reach_finitepending)
  qed(auto simp add: Lst_Lt_Pts_def tps_trans_defs)
qed

definition Finite_Wtxns_Dom where
  "Finite_Wtxns_Dom s k \<longleftrightarrow> finite (wtxns_dom (svr_state (svrs s k)))"

lemmas Finite_Wtxns_DomI = Finite_Wtxns_Dom_def[THEN iffD2, rule_format]
lemmas Finite_Wtxns_DomE[elim] = Finite_Wtxns_Dom_def[THEN iffD1, elim_format, rule_format]

lemma reach_finite_wtxns_dom [simp]: "reach tps_s s \<Longrightarrow> Finite_Wtxns_Dom s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case apply (auto simp add: Finite_Wtxns_Dom_def tps_s_defs)
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
  "Finite_Wtxns_rsran s k \<longleftrightarrow> finite (wtxns_rsran (svr_state (svrs s k)))"

lemmas Finite_Wtxns_rsranI = Finite_Wtxns_rsran_def[THEN iffD2, rule_format]
lemmas Finite_Wtxns_rsranE[elim] = Finite_Wtxns_rsran_def[THEN iffD1, elim_format, rule_format]

lemma reach_finite_wtxns_rsran [simp]: "reach tps_s s \<Longrightarrow> Finite_Wtxns_rsran s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Finite_Wtxns_rsran_def tps_s_defs)
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
  "Kvs_Not_Emp s \<longleftrightarrow> (\<forall>k. svr_state (svrs s k) \<noteq> wtxns_emp)"

lemmas Kvs_Not_EmpI = Kvs_Not_Emp_def[THEN iffD2, rule_format]
lemmas Kvs_Not_EmpE[elim] = Kvs_Not_Emp_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_not_emp [simp]: "reach tps_s s \<Longrightarrow> Kvs_Not_Emp s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    apply (auto simp add: Kvs_Not_Emp_def tps_s_defs)
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
    case (CommitW x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: Kvs_Not_Emp_def tps_trans_defs)
      by (metis fun_upd_same ver_state.distinct(3))
  qed (auto simp add: Kvs_Not_Emp_def tps_trans_defs)
qed


definition T0_in_CO where
  "T0_in_CO s k \<longleftrightarrow> T0 \<in> set (cts_order s k)"

lemmas T0_in_COI = T0_in_CO_def[THEN iffD2, rule_format]
lemmas T0_in_COE[elim] = T0_in_CO_def[THEN iffD1, elim_format, rule_format]

lemma reach_t0_in_co [simp, dest]: "reach tps_s s \<Longrightarrow> T0_in_CO s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: T0_in_CO_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: T0_in_CO_def tps_trans_all_defs)
      by (smt (verit) in_set_remove1 remove1_insort_key txid.distinct(1))
  qed (auto simp add: T0_in_CO_def tps_trans_defs)
qed

definition KvsOfS_Not_Emp where
  "KvsOfS_Not_Emp s \<longleftrightarrow> (\<forall>k. kvs_of_s s k \<noteq> [])"

lemmas KvsOfS_Not_EmpI = KvsOfS_Not_Emp_def[THEN iffD2, rule_format]
lemmas KvsOfS_Not_EmpE[elim] = KvsOfS_Not_Emp_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_of_s_not_emp [simp]: "reach tps_s s \<Longrightarrow> KvsOfS_Not_Emp s"
  apply (auto simp add: KvsOfS_Not_Emp_def T0_in_CO_def kvs_of_s_defs)
  by (smt (verit) T0_in_CO_def empty_iff empty_set reach_t0_in_co)


definition Init_Ver_Inv where
  "Init_Ver_Inv s k \<longleftrightarrow> (\<exists>rs. svr_state (svrs s k) T0 = Commit 0 0 0 undefined rs)"

lemmas Init_Ver_InvI = Init_Ver_Inv_def[THEN iffD2, rule_format]
lemmas Init_Ver_InvE[elim] = Init_Ver_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_init_ver_inv [simp, intro]: "reach tps_s s \<Longrightarrow> Init_Ver_Inv s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Init_Ver_Inv_def tps_s_defs)
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
  "CFTid_Rtxn_Inv s cl \<longleftrightarrow> (\<forall>n. n \<ge> cl_sn (cls s cl) \<longrightarrow> rtxn_rts s (Tn_cl n cl) = None)"

lemmas CFTid_Rtxn_InvI = CFTid_Rtxn_Inv_def[THEN iffD2, rule_format]
lemmas CFTid_Rtxn_InvE[elim] = CFTid_Rtxn_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_cftid_rtxn_inv [simp]: "reach tps_s s \<Longrightarrow> CFTid_Rtxn_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: CFTid_Rtxn_Inv_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case by (induction e) (auto simp add: CFTid_Rtxn_Inv_def tps_trans_defs)
qed

\<comment> \<open>Value of svr_state for future transaction ids\<close>
definition FTid_Wtxn_Inv where
  "FTid_Wtxn_Inv s cl \<longleftrightarrow> (\<forall>n k. n > cl_sn (cls s cl) \<longrightarrow> svr_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver)"

lemmas FTid_Wtxn_InvI = FTid_Wtxn_Inv_def[THEN iffD2, rule_format]
lemmas FTid_Wtxn_InvE[elim] = FTid_Wtxn_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_ftid_wtxn_inv [simp, dest]: "reach tps_s s \<Longrightarrow> FTid_Wtxn_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FTid_Wtxn_Inv_def tps_s_defs)
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

\<comment> \<open>Next 4 invariants: cl_state + cl_sn \<longrightarrow> svr_state\<close>
definition Cl_Rtxn_Inv where
  "Cl_Rtxn_Inv s cl \<longleftrightarrow> (\<forall>k keys kvm. cl_state (cls s cl) \<in> {Idle, RtxnInProg keys kvm}
    \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver)"

lemmas Cl_Rtxn_InvI = Cl_Rtxn_Inv_def[THEN iffD2, rule_format]
lemmas Cl_Rtxn_InvE[elim] = Cl_Rtxn_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_rtxn_inv [simp, dest]: "reach tps_s s \<Longrightarrow> Cl_Rtxn_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Cl_Rtxn_Inv_def tps_s_defs)
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
      by (metis get_cl_w.simps(2) txn_state.distinct(3) txn_state.distinct(7) txid0.collapse)
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (simp add: Cl_Rtxn_Inv_def tps_trans_defs)
      by force
  qed (auto simp add: Cl_Rtxn_Inv_def tps_trans_defs)
qed

definition Cl_Wtxn_Idle_Svr where
  "Cl_Wtxn_Idle_Svr s \<longleftrightarrow>
    (\<forall>cl k cts kv_map. cl_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map}
        \<and> kv_map k = None \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver)"

lemmas Cl_Wtxn_Idle_SvrI = Cl_Wtxn_Idle_Svr_def[THEN iffD2, rule_format]
lemmas Cl_Wtxn_Idle_SvrE[elim] = Cl_Wtxn_Idle_Svr_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_wtxn_idle_svr [simp]: "reach tps_s s \<Longrightarrow> Cl_Wtxn_Idle_Svr s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Cl_Wtxn_Idle_Svr_def tps_s_defs)
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
      by (smt (z3) domIff get_cl_w.simps(2) txn_state.distinct(11) txn_state.inject(2) txid0.collapse)
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (simp add: Cl_Wtxn_Idle_Svr_def tps_trans_defs)
      by force
  qed (auto simp add: Cl_Wtxn_Idle_Svr_def tps_trans_defs, blast?)
qed

definition Cl_Prep_Inv where
  "Cl_Prep_Inv s \<longleftrightarrow> (\<forall>cl k kvm. \<exists>prep_t v. cl_state (cls s cl) = WtxnPrep kvm
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) \<in> {No_Ver, Prep prep_t v}) \<and>
    (k \<notin> dom kvm \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver))"

lemmas Cl_Prep_InvI = Cl_Prep_Inv_def[THEN iffD2, rule_format]
lemmas Cl_Prep_InvE[elim] = Cl_Prep_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_prep_inv [simp]: "reach tps_s s \<Longrightarrow> Cl_Prep_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Cl_Prep_Inv_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (WInvoke x1 x2 x3)
    then show ?case by (simp add: Cl_Prep_Inv_def tps_trans_defs, blast)
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Cl_Prep_Inv_def tps_trans_defs)
      by (smt (verit) add_to_readerset_wtxns_dom add_to_readerset_prep_inv wtxns_domIff)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Cl_Prep_Inv_def tps_trans_defs)
      by (metis domI get_cl_w.simps(2) txn_state.inject(2) txid0.collapse)
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (simp add: Cl_Prep_Inv_def tps_trans_defs)
      using get_cl_w.simps(2) txn_state.distinct(11) txn_state.simps(19) by force
  qed (auto simp add: Cl_Prep_Inv_def tps_trans_defs)
qed

definition Cl_Commit_Inv where
  "Cl_Commit_Inv s \<longleftrightarrow> (\<forall>cl k cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<longrightarrow>
    (\<forall>v. kv_map k = Some v \<longrightarrow>
      (\<exists>prep_t sts lst rs. svr_state (svrs s k) (get_wtxn s cl) \<in> {Prep prep_t v, Commit cts sts lst v rs})) \<and>
    (kv_map k = None \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver))"

lemmas Cl_Commit_InvI = Cl_Commit_Inv_def[THEN iffD2, rule_format]
lemmas Cl_Commit_InvE[elim] = Cl_Commit_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_commit_inv [simp]: "reach tps_s s \<Longrightarrow> Cl_Commit_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Cl_Commit_Inv_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Cl_Commit_Inv_def tps_trans_defs)
      by (metis (no_types, lifting) Cl_Prep_Inv_def domI domIff option.inject reach_cl_prep_inv)
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Cl_Commit_Inv_def tps_trans_defs)
      by (smt add_to_readerset_commit add_to_readerset_no_ver_inv add_to_readerset_prep_inv
          ver_state.exhaust ver_state.inject(2))
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Cl_Commit_Inv_def tps_trans_defs)
      by (smt (verit) fun_upd_other get_cl_w.simps(2) txn_state.distinct(11) txid0.collapse)
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (simp add: Cl_Commit_Inv_def tps_trans_defs)
      by (metis domD get_cl_w.simps(2) txn_state.inject(3) ver_state.distinct(5) ver_state.inject(1) txid0.collapse)
  qed (auto simp add: Cl_Commit_Inv_def tps_trans_defs)
qed

\<comment> \<open>Next 2 invariants: svr_state \<longrightarrow> cl_state\<close>
definition Prep_is_Curr_wt where
  "Prep_is_Curr_wt s k \<longleftrightarrow> (\<forall>t. is_prepared (svr_state (svrs s k) t) \<longrightarrow> is_curr_wt s t)"

lemmas Prep_is_Curr_wtI = Prep_is_Curr_wt_def[THEN iffD2, rule_format]
lemmas Prep_is_Curr_wtE[elim] = Prep_is_Curr_wt_def[THEN iffD1, elim_format, rule_format]

lemma reach_prep_is_curr_wt[simp]: "reach tps_s s \<Longrightarrow> Prep_is_Curr_wt s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Prep_is_Curr_wt_def tps_s_defs split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: Prep_is_Curr_wt_def tps_trans_defs)
      by (metis Cl_Rtxn_Inv_def get_cl_w.elims get_sn_w.simps(2) insert_iff is_prepared.simps(2)
          reach_cl_rtxn_inv)
  next
    case (WDone x1 x2 x3)
    then show ?case apply (auto simp add: Prep_is_Curr_wt_def tps_trans_defs)
    apply (cases "x2 k")
       apply (smt (z3) Cl_Wtxn_Idle_Svr_def get_cl_w.simps(2) get_sn_w.cases get_sn_w.simps(2)
          insert_commute insert_compr insert_iff is_prepared.elims(1) reach_cl_wtxn_idle_svr
          ver_state.distinct(1))
      by (metis domI get_cl_w.elims get_sn_w.simps(2) is_prepared.simps(3))
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Prep_is_Curr_wt_def tps_trans_defs)
      by (smt (verit, ccfv_SIG) add_to_readerset_prep_inv is_prepared.elims(2))
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Prep_is_Curr_wt_def tps_trans_defs)
      by (metis get_cl_w.simps(2) get_sn_w.simps(2) txid0.collapse)
  qed (auto simp add: Prep_is_Curr_wt_def tps_trans_defs)
qed

definition Svr_Prep_Inv where
  "Svr_Prep_Inv s \<longleftrightarrow> (\<forall>k t ts v. svr_state (svrs s k) t = Prep ts v \<longrightarrow>
    (\<exists>cts kv_map.
      cl_state (cls s (get_cl_w t)) \<in> {WtxnPrep  kv_map, WtxnCommit cts kv_map} \<and>
      k \<in> dom kv_map))"

lemmas Svr_Prep_InvI = Svr_Prep_Inv_def[THEN iffD2, rule_format]
lemmas Svr_Prep_InvE[elim] = Svr_Prep_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_svr_prep_inv [simp]: "reach tps_s s \<Longrightarrow> Svr_Prep_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Svr_Prep_Inv_def tps_s_defs split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2 x3)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis txn_state.distinct(3) txn_state.distinct(5))
  next
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis txn_state.distinct(7) txn_state.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis txn_state.distinct(7) txn_state.distinct(9))
  next
    case (WInvoke x1 x2 x3)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis txn_state.distinct(3) txn_state.distinct(5))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis (lifting) txn_state.distinct(11) txn_state.inject(2))
  next
    case (WDone x1 x2 x3)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis (no_types, lifting) Prep_is_Curr_wt_def get_cl_w.elims get_sn_w.simps(2)
          is_prepared.simps(1) reach_prep_is_curr_wt txn_state.distinct(11) txn_state.inject(3)
          ver_state.distinct(5))
  next
    case (RegR x1 x2 x3 x4)
    then show ?case by (simp add: Svr_Prep_Inv_def tps_trans_defs add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis domI get_cl_w.simps(2) txid0.collapse)
  qed (auto simp add: Svr_Prep_Inv_def tps_trans_defs)
qed


definition Svr_Commit_Inv where
  "Svr_Commit_Inv s \<longleftrightarrow> (\<forall>k t cts sts lst v rs. 
    svr_state (svrs s k) t = Commit cts sts lst v rs \<and> is_curr_wt s t \<longrightarrow> 
      (\<exists>kv_map. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map \<and> k \<in> dom kv_map))"

lemmas Svr_Commit_InvI = Svr_Commit_Inv_def[THEN iffD2, rule_format]
lemmas Svr_Commit_InvE[elim] = Svr_Commit_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_svr_commit_inv [simp]: "reach tps_s s \<Longrightarrow> Svr_Commit_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Svr_Commit_Inv_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2 x3)
    then show ?case apply (simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis txn_state.distinct(5))
  next
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis txn_state.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis FTid_Wtxn_Inv_def get_cl_w.elims get_sn_w.simps(2) lessI
          reach_ftid_wtxn_inv ver_state.distinct(3))
  next
    case (WInvoke x1 x2 x3)
    then show ?case apply (simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis txn_state.distinct(5))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis (lifting) txn_state.distinct(11))
  next
    case (WDone x1 x2 x3)
    then show ?case apply (auto simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis (lifting) FTid_Wtxn_Inv_def get_cl_w.elims get_sn_w.simps(2)
          lessI reach_ftid_wtxn_inv ver_state.distinct(3))
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (auto simp add: Svr_Commit_Inv_def tps_trans_defs)
    by (metis add_to_readerset_commit)
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (auto simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis domI get_cl_w.simps(2) txid0.collapse)
  qed (auto simp add: Svr_Commit_Inv_def tps_trans_defs)
qed


\<comment> \<open>Values of svr_state and rtxn_rts for past transaction ids\<close>
definition PTid_Inv where
  "PTid_Inv s cl \<longleftrightarrow> (\<forall>k. \<forall>n < cl_sn (cls s cl).
   (svr_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver) \<or>
   (rtxn_rts s (Tn_cl n cl) = None \<and>
    (\<exists>cts sts lst v rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts sts lst v rs)))"

lemmas PTid_InvI = PTid_Inv_def[THEN iffD2, rule_format]
lemmas PTid_InvE[elim] = PTid_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_ptid_inv [simp]: "reach tps_s s \<Longrightarrow> PTid_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: PTid_Inv_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RDone x31 x32 x33)
    then show ?case
      apply (auto simp add: tps_trans_defs PTid_Inv_def)
      apply blast
      by (metis not_less_less_Suc_eq)+
  next
    case (WDone x61 x62)
    then show ?case
      apply (auto simp add: tps_trans_defs PTid_Inv_def)
      subgoal for _ _ n apply (cases "n = cl_sn (cls s x61)")
        apply (metis CFTid_Rtxn_Inv_def eq_imp_le reach_cftid_rtxn_inv)
        by (metis less_SucE)
      subgoal for _ k apply (cases "x62 k = None")
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
    and "get_cl t = cl" and "get_sn t \<noteq> cl_sn (cls s cl)"
  shows "\<And>k. \<exists>cts sts lst v rs. svr_state (svrs s k) (Tn t) \<in> {No_Ver, Commit cts sts lst v rs}"
  using assms
  apply (auto simp add: FTid_Wtxn_Inv_def PTid_Inv_def)
  apply (cases "get_sn t > cl_sn (cls s cl)")
  apply (metis txid0.collapse)
  by (metis txid0.collapse linorder_cases)

definition Rtxn_Wtxn_No_Ver where
  "Rtxn_Wtxn_No_Ver s cl \<longleftrightarrow>
    (\<forall>n ts. rtxn_rts s (Tn_cl n cl) = Some ts \<longrightarrow> (\<forall>k. svr_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver))"

lemmas Rtxn_Wtxn_No_VerI = Rtxn_Wtxn_No_Ver_def[THEN iffD2, rule_format]
lemmas Rtxn_Wtxn_No_VerE[elim] = Rtxn_Wtxn_No_Ver_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_wtxn_no_ver [simp]: "reach tps_s s \<Longrightarrow> Rtxn_Wtxn_No_Ver s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rtxn_Wtxn_No_Ver_def tps_s_defs)
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
      by (metis CFTid_Rtxn_Inv_def get_sn_w.simps(2) le_refl reach_cftid_rtxn_inv)
  qed (auto simp add: Rtxn_Wtxn_No_Ver_def tps_trans_defs)
qed

definition Wtxn_Rtxn_None where
  "Wtxn_Rtxn_None s k \<longleftrightarrow>
    (\<forall>cl n ts sts lst v cts rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) \<in> {Prep ts v, Commit cts sts lst v rs}
       \<longrightarrow> rtxn_rts s (Tn_cl n cl) = None)"

lemmas Wtxn_Rtxn_NoneI = Wtxn_Rtxn_None_def[THEN iffD2, rule_format]
lemmas Wtxn_Rtxn_NoneE[elim] = Wtxn_Rtxn_None_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_rtxn_none [simp]: "reach tps_s s \<Longrightarrow> Wtxn_Rtxn_None s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Wtxn_Rtxn_None_def tps_s_defs)
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
      by (metis CFTid_Rtxn_Inv_def get_cl_w.simps(2) get_sn_w.simps(2) le_refl
          reach_cftid_rtxn_inv txid0.collapse)
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (simp add: Wtxn_Rtxn_None_def tps_trans_defs)
      by (meson is_prepared.elims(2))
  qed (auto simp add: Wtxn_Rtxn_None_def tps_trans_defs)
qed

definition Wtxn_Cts_T0 where
  "Wtxn_Cts_T0 s k \<longleftrightarrow> wtxn_cts s T0 = Some 0"

lemmas Wtxn_Cts_T0I = Wtxn_Cts_T0_def[THEN iffD2, rule_format]
lemmas Wtxn_Cts_T0E[elim] = Wtxn_Cts_T0_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_cts_t0 [simp, dest]: "reach tps_s s \<Longrightarrow> Wtxn_Cts_T0 s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Wtxn_Cts_T0_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Wtxn_Cts_T0_def tps_trans_defs)
qed

definition Wtxn_Cts_Tn_None where
  "Wtxn_Cts_Tn_None s \<longleftrightarrow> (\<forall>cts kv_map keys n cl. 
    (cl_state (cls s cl) \<in> {Idle, WtxnPrep kv_map} \<and> n \<ge> cl_sn (cls s cl)) \<or>
    (cl_state (cls s cl) \<in> {RtxnInProg keys kv_map, WtxnCommit cts kv_map} \<and> n > cl_sn (cls s cl))
     \<longrightarrow> wtxn_cts s (Tn (Tn_cl n cl)) = None)"

lemmas Wtxn_Cts_Tn_NoneI = Wtxn_Cts_Tn_None_def[THEN iffD2, rule_format]
lemmas Wtxn_Cts_Tn_NoneE[elim] = Wtxn_Cts_Tn_None_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_cts_tn_none [simp, intro]: "reach tps_s s \<Longrightarrow> Wtxn_Cts_Tn_None s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Wtxn_Cts_Tn_None_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Wtxn_Cts_Tn_None_def tps_trans_defs)
qed

definition Wtxn_Cts_None where
  "Wtxn_Cts_None s \<longleftrightarrow> (\<forall>cts kv_map keys t. t \<noteq> T0 \<and> (
    (cl_state (cls s (get_cl_w t)) \<in> {Idle, WtxnPrep kv_map} \<and>
        get_sn_w t \<ge> cl_sn (cls s (get_cl_w t))) \<or>
    (cl_state (cls s (get_cl_w t)) \<in> {RtxnInProg keys kv_map, WtxnCommit cts kv_map} \<and>
        get_sn_w t > cl_sn (cls s (get_cl_w t))))
     \<longrightarrow> wtxn_cts s t = None)"

lemmas Wtxn_Cts_NoneI = Wtxn_Cts_None_def[THEN iffD2, rule_format]
lemmas Wtxn_Cts_NoneE[elim] = Wtxn_Cts_None_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_cts_none [simp, intro]: "reach tps_s s \<Longrightarrow> Wtxn_Cts_None s"
  apply (simp add: Wtxn_Cts_None_def)
  apply rule+ subgoal for cts kv_map keys t apply (cases t)
    apply metis using Wtxn_Cts_Tn_None_def[of s]
    by (smt get_cl_w.simps(2) get_sn_w.simps(2) insert_iff reach_wtxn_cts_tn_none txid0.exhaust).

definition WtxnCommit_Wtxn_Cts where
  "WtxnCommit_Wtxn_Cts s cl \<longleftrightarrow> (\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map
    \<longrightarrow> wtxn_cts s (get_wtxn s cl) = Some cts)"

lemmas WtxnCommit_Wtxn_CtsI = WtxnCommit_Wtxn_Cts_def[THEN iffD2, rule_format]
lemmas WtxnCommit_Wtxn_CtsE[elim] = WtxnCommit_Wtxn_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxncommit_wtxn_cts [simp, intro]: "reach tps_s s \<Longrightarrow> WtxnCommit_Wtxn_Cts s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: WtxnCommit_Wtxn_Cts_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: WtxnCommit_Wtxn_Cts_def tps_trans_defs)
qed

definition Wtxn_State_Cts where
  "Wtxn_State_Cts s k \<longleftrightarrow> (\<forall>t cts sts lst v rs ts kv_map.
    svr_state (svrs s k) t = Commit cts sts lst v rs \<or>
   (svr_state (svrs s k) t = Prep ts v \<and> cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map)
      \<longrightarrow> wtxn_cts s t = Some cts)"

lemmas Wtxn_State_CtsI = Wtxn_State_Cts_def[THEN iffD2, rule_format]
lemmas Wtxn_State_CtsE[elim] = Wtxn_State_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_svr_state_cts [simp]: "reach tps_s s \<Longrightarrow> Wtxn_State_Cts s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Wtxn_State_Cts_def tps_s_defs split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Wtxn_State_Cts_def tps_trans_defs domI)
      apply (metis (no_types, lifting) Cl_Prep_Inv_def reach_cl_prep_inv ver_state.distinct(3)
          ver_state.distinct(5))
    subgoal for t apply (cases t)
       apply (metis Prep_is_Curr_wt_def is_prepared.simps(1) reach_prep_is_curr_wt) 
      by (metis Prep_is_Curr_wt_def get_cl_w.simps(2) get_sn_w.cases get_sn_w.simps(2)
          is_prepared.simps(1) reach_prep_is_curr_wt).
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Wtxn_State_Cts_def tps_trans_defs domI)
      by (meson add_to_readerset_commit add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Wtxn_State_Cts_def tps_trans_defs domI)
      by (metis get_cl_w.simps(2) txid0.exhaust_sel txn_state.distinct(11))
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (simp add: Wtxn_State_Cts_def tps_trans_defs domI)
      by (metis get_cl_w.simps(2) txid0.collapse)
  qed (auto simp add: Wtxn_State_Cts_def tps_trans_defs domI)
qed

definition FTid_notin_rs where
  "FTid_notin_rs s cl \<longleftrightarrow> (\<forall>k n t cts sts lst v rs rts rlst. n > cl_sn (cls s cl) \<and>
    svr_state (svrs s k) t = Commit cts sts lst v rs \<longrightarrow> (Tn_cl n cl, rts, rlst) \<notin> rs)"

lemmas FTid_notin_rsI = FTid_notin_rs_def[THEN iffD2, rule_format]
lemmas FTid_notin_rsE[elim] = FTid_notin_rs_def[THEN iffD1, elim_format, rule_format]

lemma reach_ftid_notin_rs [simp, dest]: "reach tps_s s \<Longrightarrow> FTid_notin_rs s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: FTid_notin_rs_def tps_s_defs split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: FTid_notin_rs_def tps_trans_defs)
      by (meson Suc_lessD)
  next
    case (WDone x1 x2 x3)
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
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (simp add: FTid_notin_rs_def tps_trans_defs)
      by (smt empty_iff fun_upd_other fun_upd_same txn_state.simps(19) ver_state.inject(2)
          ver_state.simps(10))
  qed (auto simp add: FTid_notin_rs_def tps_trans_defs)
qed

definition FTid_not_wr where
  "FTid_not_wr s cl \<longleftrightarrow> (\<forall>n k. n > cl_sn (cls s cl) \<longrightarrow> Tn (Tn_cl n cl) \<notin> wtxns_dom (svr_state (svrs s k)))"

lemmas FTid_not_wrI = FTid_not_wr_def[THEN iffD2, rule_format]
lemmas FTid_not_wrE[elim] = FTid_not_wr_def[THEN iffD1, elim_format, rule_format]

lemma reach_ftid_not_wr [simp]: "reach tps_s s \<Longrightarrow> FTid_not_wr s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FTid_not_wr_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RDone x31 x32 x33)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (metis Suc_lessD)
  next
    case (WDone x61 x62)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (metis Suc_lessD)
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (simp add: add_to_readerset_wtxns_dom)
  next
    case (PrepW x81 x82 x83)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (metis get_cl_w.simps(2) get_sn_w.simps(2) nat_neq_iff txid0.collapse)
  next
    case (CommitW x91 x92)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (metis get_cl_w.simps(2) get_sn_w.simps(2) order_less_irrefl txid0.collapse)
  qed (auto simp add: FTid_not_wr_def tps_trans_defs)
qed

definition Fresh_wr_notin_rs where
  "Fresh_wr_notin_rs s cl \<longleftrightarrow> (\<forall>k t cts kv_map cts' sts' lst' v' rs' rts rlst.
    cl_state (cls s cl) \<in> {Idle, WtxnPrep kv_map, WtxnCommit cts kv_map} \<and>
    svr_state (svrs s k) t = Commit cts' sts' lst' v' rs' \<longrightarrow> (get_txn s cl, rts, rlst) \<notin> rs')"

lemmas Fresh_wr_notin_rsI = Fresh_wr_notin_rs_def[THEN iffD2, rule_format]
lemmas Fresh_wr_notin_rsE[elim] = Fresh_wr_notin_rs_def[THEN iffD1, elim_format, rule_format]

lemma reach_fresh_wr_notin_rs [simp]: "reach tps_s s \<Longrightarrow> Fresh_wr_notin_rs s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Fresh_wr_notin_rs_def tps_s_defs split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: Fresh_wr_notin_rs_def tps_trans_defs)
      using FTid_notin_rs_def lessI by blast
  next
    case (WDone x1 x2 x3)
    then show ?case apply (auto simp add: Fresh_wr_notin_rs_def tps_trans_defs)
      using FTid_notin_rs_def by blast
  next
    case (RegR x1 x2 x3 x4)
    then show ?case by (auto simp add: Fresh_wr_notin_rs_def tps_trans_defs add_to_readerset_def
          split: ver_state.split)
  qed (simp_all add: Fresh_wr_notin_rs_def tps_trans_defs split: txn_state.split, blast+)
qed

definition Fresh_wr_notin_Wts_dom where
  "Fresh_wr_notin_Wts_dom s cl \<longleftrightarrow> (\<forall>keys kv_map k. cl_state (cls s cl) \<in> {Idle, RtxnInProg keys kv_map} \<longrightarrow>
    Tn (get_txn s cl) \<notin> wtxns_dom (svr_state (svrs s k)))"

lemmas Fresh_wr_notin_Wts_domI = Fresh_wr_notin_Wts_dom_def[THEN iffD2, rule_format]
lemmas Fresh_wr_notin_Wts_domE[elim] = Fresh_wr_notin_Wts_dom_def[THEN iffD1, elim_format, rule_format]

lemma reach_fresh_wr_notin_wtxns_dom [simp]: "reach tps_s s \<Longrightarrow> Fresh_wr_notin_Wts_dom s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Fresh_wr_notin_Wts_dom_def tps_s_defs)
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
      by (metis get_cl_w.simps(2) txn_state.distinct(3) txn_state.distinct(7) txid0.collapse)
  qed (auto simp add: tps_trans_defs Fresh_wr_notin_Wts_dom_def)
qed

definition Rtxn_rts_le_Gst where
  "Rtxn_rts_le_Gst s cl \<longleftrightarrow> (\<forall>n ts. rtxn_rts s (Tn_cl n cl) = Some ts \<longrightarrow> ts \<le> gst (cls s cl))"

lemmas Rtxn_rts_le_GstI = Rtxn_rts_le_Gst_def[THEN iffD2, rule_format]
lemmas Rtxn_rts_le_GstE[elim] = Rtxn_rts_le_Gst_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_rts_le_gst [simp]: "reach tps_s s \<Longrightarrow> Rtxn_rts_le_Gst s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rtxn_rts_le_Gst_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2 x3)
    then show ?case apply (simp add: Rtxn_rts_le_Gst_def read_invoke_def read_invoke_U_def)
      by (meson Gst_le_Min_Lst_map_def dual_order.trans reach_gst_le_min_lst_map)
  qed (auto simp add: Rtxn_rts_le_Gst_def tps_trans_defs)
qed

subsection \<open>Gst, Cts, Pts relations\<close>

definition Gst_le_Pts where
  "Gst_le_Pts s cl \<longleftrightarrow> (\<forall>k prep_t v. 
      svr_state (svrs s k) (get_wtxn s cl) = Prep prep_t v \<longrightarrow> gst (cls s cl) \<le> prep_t)"
                                                           
lemmas Gst_le_PtsI = Gst_le_Pts_def[THEN iffD2, rule_format]
lemmas Gst_le_PtsE[elim] = Gst_le_Pts_def[THEN iffD1, elim_format, rule_format]

lemma reach_gst_le_pts [simp]: "reach tps_s s \<Longrightarrow> Gst_le_Pts s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Gst_le_Pts_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2 x3)
    then show ?case apply (simp add: Gst_le_Pts_def tps_trans_defs)
      by (metis Cl_Rtxn_Inv_def insert_iff reach_cl_rtxn_inv ver_state.distinct(1))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: Gst_le_Pts_def tps_trans_defs)
      by (meson FTid_not_wr_def lessI reach_ftid_not_wr wtxns_domI1)
  next
    case (WDone x1 x2 x3)
    then show ?case apply (simp add: Gst_le_Pts_def tps_trans_defs)
      by (meson FTid_not_wr_def less_Suc_eq reach_ftid_not_wr wtxns_domI1)
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Gst_le_Pts_def tps_trans_defs)
      by (meson add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (auto simp add: Gst_le_Pts_def tps_trans_defs)
      using Gst_le_Lst_map_def[of s cl x1] Lst_map_le_Lst_def Svr_Clk_le_Lst_def
      by (metis dual_order.trans reach_svr_clock_svr_lst_inv reach_gst_le_svr_lst reach_lst_map_le_svr_lst)
  qed (auto simp add: Gst_le_Pts_def tps_trans_defs)
qed

definition Gst_Lt_Cts where
  "Gst_Lt_Cts s cl \<longleftrightarrow> (\<forall>k cts sts lst v rs. 
      svr_state (svrs s k) (get_wtxn s cl) = Commit cts sts lst v rs \<longrightarrow> gst (cls s cl) < cts)"
                                                           
lemmas Gst_Lt_CtsI = Gst_Lt_Cts_def[THEN iffD2, rule_format]
lemmas Gst_Lt_CtsE[elim] = Gst_Lt_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_gst_lt_cts [simp]: "reach tps_s s \<Longrightarrow> Gst_Lt_Cts s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Gst_Lt_Cts_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2 x3)
    then show ?case apply (simp add: Gst_Lt_Cts_def tps_trans_defs)
      by (metis Fresh_wr_notin_Wts_dom_def insert_iff reach_fresh_wr_notin_wtxns_dom wtxns_domI2)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: Gst_Lt_Cts_def tps_trans_defs)
      by (metis FTid_Wtxn_Inv_def lessI reach_ftid_wtxn_inv ver_state.distinct(3))
  next
    case (WDone x1 x2 x3)
    then show ?case apply (simp add: Gst_Lt_Cts_def tps_trans_defs)
      by (meson FTid_not_wr_def less_Suc_eq reach_ftid_not_wr wtxns_domI2)
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Gst_Lt_Cts_def tps_trans_defs)
      by (meson add_to_readerset_commit)
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (simp add: Gst_Lt_Cts_def tps_trans_defs) sorry
  qed (auto simp add: Gst_Lt_Cts_def tps_trans_defs)
qed


definition Gst_Lt_Cl_Cts where
  "Gst_Lt_Cl_Cts s cl \<longleftrightarrow> (\<forall>cl' cts kv_map. cl_state (cls s cl') = WtxnCommit cts kv_map
    \<longrightarrow> gst (cls s cl) < cts)"
                                                           
lemmas Gst_Lt_Cl_CtsI = Gst_Lt_Cl_Cts_def[THEN iffD2, rule_format]
lemmas Gst_Lt_Cl_CtsE[elim] = Gst_Lt_Cl_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_gst_lt_cl_cts [simp]: "reach tps_s s \<Longrightarrow> Gst_Lt_Cl_Cts s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Gst_Lt_Cl_Cts_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2 x3)
    then show ?case apply (auto simp add: Gst_Lt_Cl_Cts_def tps_trans_defs) sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Gst_Lt_Cl_Cts_def tps_trans_defs)
      apply (cases "cl = x1"; simp) sorry
  qed (auto simp add: Gst_Lt_Cl_Cts_def tps_trans_defs, (blast+)?)
qed

subsection \<open>Commit Timestamps Order Invariants\<close>

definition CO_Tid where
  "CO_Tid s cl \<longleftrightarrow> (case cl_state (cls s cl) of
    WtxnCommit cts kv_map \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow> n \<le> cl_sn (cls s cl))
  | _ \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow> n < cl_sn (cls s cl)))"

lemmas CO_TidI = CO_Tid_def[THEN iffD2, rule_format]
lemmas CO_TidE[elim] = CO_Tid_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_tid[simp]: "reach tps_s s \<Longrightarrow> CO_Tid s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: CO_Tid_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: CO_Tid_def tps_trans_defs split: txn_state.split_asm)
      using less_SucI less_Suc_eq_le by blast+
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: CO_Tid_def tps_trans_all_defs set_insort_key split: txn_state.split_asm)
      apply (metis txn_state.distinct(3))
      apply (metis txn_state.distinct(7))
      apply (meson less_or_eq_imp_le)
      by blast
  next
    case (WDone x1 x2 x3)
    then show ?case apply (simp add: CO_Tid_def tps_trans_defs split: txn_state.split_asm)
      apply (meson less_SucI)+
      by (meson linorder_le_less_linear not_less_eq_eq)
  qed (auto simp add: CO_Tid_def tps_trans_defs split: txn_state.split_asm)
qed

definition CO_Distinct where
  "CO_Distinct s k \<longleftrightarrow> distinct (cts_order s k)"

lemmas CO_DistinctI = CO_Distinct_def[THEN iffD2, rule_format]
lemmas CO_DistinctE[elim] = CO_Distinct_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_distinct [simp]: "reach tps_s s \<Longrightarrow> CO_Distinct s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: CO_Distinct_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: CO_Distinct_def tps_trans_all_defs distinct_insort)
      by (metis (no_types, lifting) CO_Tid_def less_irrefl_nat reach_co_tid txn_state.simps(18))
  qed (simp_all add: CO_Distinct_def tps_trans_defs)
qed

definition CO_Tn_is_Cmt_Abs where
  "CO_Tn_is_Cmt_Abs s k \<longleftrightarrow> (\<forall>n cl. Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow>
    (\<exists>cts sts lst v rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts sts lst v rs) \<or> 
    ((\<exists>ts v. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Prep ts v) \<and> 
     (\<exists>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<and> 
      cl_sn (cls s cl) = n \<and> k \<in> dom kv_map)))"

lemmas CO_Tn_is_Cmt_AbsI = CO_Tn_is_Cmt_Abs_def[THEN iffD2, rule_format]
lemmas CO_Tn_is_Cmt_AbsE[elim] = CO_Tn_is_Cmt_Abs_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_tn_is_cmt_abs [simp]: "reach tps_s s \<Longrightarrow> CO_Tn_is_Cmt_Abs s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: CO_Tn_is_Cmt_Abs_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RInvoke x1 x2 x3)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_defs)
      by (metis txn_state.distinct(5))
  next
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_defs)
      by (metis txn_state.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_defs)
      by (metis txn_state.distinct(9))
  next
    case (WInvoke x1 x2 x3)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_defs)
      by (metis txn_state.distinct(5))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_all_defs set_insort_key)
      by (smt (verit) domIff is_prepared.elims(2) option.discI txn_state.distinct(11))
  next
    case (WDone x1 x2 x3)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_defs)
      by (metis (no_types, lifting) txn_state.inject(3))
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_defs)
      by (metis add_to_readerset_commit' add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_defs)
      by (metis ver_state.distinct(3))
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_defs)
      by (smt (z3) fun_upd_apply txn_state.simps(19) ver_state.simps(10))
  qed (auto simp add: CO_Tn_is_Cmt_Abs_def tps_trans_defs)
qed

definition CO_is_Cmt_Abs where
  "CO_is_Cmt_Abs s k \<longleftrightarrow> (\<forall>t. t \<in> set (cts_order s k) \<longrightarrow>
    (\<exists>cts sts lst v rs. svr_state (svrs s k) t = Commit cts sts lst v rs) \<or> 
    ((\<exists>ts v. svr_state (svrs s k) t = Prep ts v) \<and> 
     (\<exists>cts kv_map. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map \<and> k \<in> dom kv_map)))"

lemmas CO_is_Cmt_AbsI = CO_is_Cmt_Abs_def[THEN iffD2, rule_format]
lemmas CO_is_Cmt_AbsE[elim] = CO_is_Cmt_Abs_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_is_cmt_abs [simp]: "reach tps_s s \<Longrightarrow> CO_is_Cmt_Abs s k"
  apply (simp add: CO_is_Cmt_Abs_def)
  apply rule subgoal for t apply (cases t)
    apply (metis Init_Ver_Inv_def reach_init_ver_inv)
    by (smt CO_Tn_is_Cmt_Abs_def get_cl_w.simps(2) reach_co_tn_is_cmt_abs txid0.collapse).

definition CO_not_No_Ver where
  "CO_not_No_Ver s k \<longleftrightarrow> (\<forall>t \<in> set (cts_order s k). svr_state (svrs s k) t \<noteq> No_Ver)"

lemmas CO_not_No_VerI = CO_not_No_Ver_def[THEN iffD2, rule_format]
lemmas CO_not_No_VerE[elim] = CO_not_No_Ver_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_not_no_ver [simp]: "reach tps_s s \<Longrightarrow> CO_not_No_Ver s k"
  apply (auto simp add: CO_not_No_Ver_def)
  by (metis CO_is_Cmt_Abs_def reach_co_is_cmt_abs ver_state.distinct(1) ver_state.distinct(3))

definition CO_has_Cts where
  "CO_has_Cts s k \<longleftrightarrow> (\<forall>t \<in> set (cts_order s k). \<exists>cts. wtxn_cts s t = Some cts)"

lemmas CO_has_CtsI = CO_has_Cts_def[THEN iffD2, rule_format]
lemmas CO_has_CtsE[elim] = CO_has_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_has_cts [simp]: "reach tps_s s \<Longrightarrow> CO_has_Cts s k"
  apply (simp add: CO_has_Cts_def)
  apply rule subgoal for t apply (cases t)
    using Init_Ver_Inv_def Wtxn_State_Cts_def[of s k] reach_svr_state_cts
    apply (metis reach_init_ver_inv)
    by (metis CO_Tn_is_Cmt_Abs_def[of s] Wtxn_State_Cts_def WtxnCommit_Wtxn_Cts_def
        reach_co_tn_is_cmt_abs reach_svr_state_cts reach_wtxncommit_wtxn_cts txid0.exhaust).

definition Committed_Abs_Tn_in_CO where
  "Committed_Abs_Tn_in_CO s k \<longleftrightarrow> (\<forall>n cl.
    (\<exists>cts sts lst v rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts sts lst v rs) \<or> 
    ((\<exists>ts v. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Prep ts v) \<and> 
     (\<exists>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<and> cl_sn (cls s cl) = n)) \<longrightarrow>
    Tn (Tn_cl n cl) \<in> set (cts_order s k))"

lemmas Committed_Abs_Tn_in_COI = Committed_Abs_Tn_in_CO_def[THEN iffD2, rule_format]
lemmas Committed_Abs_Tn_in_COE[elim] = Committed_Abs_Tn_in_CO_def[THEN iffD1, elim_format, rule_format]

lemma reach_cmt_abs_tn_in_co [simp]: "reach tps_s s \<Longrightarrow> Committed_Abs_Tn_in_CO s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Committed_Abs_Tn_in_CO_def tps_s_defs split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Committed_Abs_Tn_in_CO_def tps_trans_defs)
      by (metis txn_state.distinct(9) txn_state.simps(17))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Committed_Abs_Tn_in_CO_def tps_trans_all_defs set_insort_key)
      by (metis (no_types, lifting) Cl_Prep_Inv_def domIff reach_cl_prep_inv ver_state.distinct(1))
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Committed_Abs_Tn_in_CO_def tps_trans_defs)
      by (smt (verit) add_to_readerset_commit add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Committed_Abs_Tn_in_CO_def tps_trans_defs)
      by (metis get_cl_w.simps(2) txn_state.distinct(11) txid0.collapse)
  qed (auto simp add: Committed_Abs_Tn_in_CO_def tps_trans_defs)
qed

definition Committed_Abs_in_CO where
  "Committed_Abs_in_CO s k \<longleftrightarrow> (\<forall>t.
    (\<exists>cts sts lst v rs. svr_state (svrs s k) t = Commit cts sts lst v rs) \<or> 
    ((\<exists>ts v. svr_state (svrs s k) t = Prep ts v) \<and>
     (\<exists>cts kv_map. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map)) \<longrightarrow>
    t \<in> set (cts_order s k))"

lemmas Committed_Abs_in_COI = Committed_Abs_in_CO_def[THEN iffD2, rule_format]
lemmas Committed_Abs_in_COE[elim] = Committed_Abs_in_CO_def[THEN iffD1, elim_format, rule_format]

lemma reach_cmt_abs_in_co [simp]: "reach tps_s s \<Longrightarrow> Committed_Abs_in_CO s k"
  apply (simp add: Committed_Abs_in_CO_def)
  apply rule subgoal for t apply (cases t, blast)
  by (metis Prep_is_Curr_wt_def[of s k] Committed_Abs_Tn_in_CO_def get_cl_w.simps(2) txid0.collapse
      get_sn_w.simps(2) is_prepared.simps(1) reach_cmt_abs_tn_in_co reach_prep_is_curr_wt).

definition CO_Sorted where
  "CO_Sorted s k \<longleftrightarrow> (\<forall>i. \<forall>i' < length (cts_order s k).
    i < i' \<longrightarrow> the (wtxn_cts s (cts_order s k ! i)) \<le> the (wtxn_cts s (cts_order s k ! i')))"

lemmas CO_SortedI = CO_Sorted_def[THEN iffD2, rule_format]
lemmas CO_SortedE[elim] = CO_Sorted_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_sorted [simp]: "reach tps_s s \<Longrightarrow> CO_Sorted s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: CO_Sorted_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then have indom: "k \<in> dom x2 \<Longrightarrow> cts_order s' k = cts_order s k @ [get_wtxn s x1]"
      apply (auto simp add: tps_trans_all_defs) (* CONTINUE! *)
    have nindom: "k \<notin> dom x2 \<Longrightarrow> cts_order s' k = cts_order s k" using WCommit
      by (auto simp add: tps_trans_all_defs)
    then show ?case using WCommit indom nindom
      apply (cases "k \<in> dom x2", auto)
      subgoal apply (auto simp add: CO_Sorted_def tps_trans_defs)
      (*apply (cases "x2 k", auto)*) sorry
  qed (auto simp add: CO_Sorted_def tps_trans_defs)
qed

lemma T0_min_unique_ts:
  assumes "reach tps_s s"
  shows "unique_ts (wtxn_cts s) t \<ge> unique_ts (wtxn_cts s) T0"
  using assms Wtxn_Cts_T0_def[of s]
  by (auto simp add: unique_ts_def less_eq_prod_def)

definition T0_First_in_CO where
  "T0_First_in_CO s k \<longleftrightarrow> cts_order s k ! 0 = T0"

lemmas T0_First_in_COI = T0_First_in_CO_def[THEN iffD2, rule_format]
lemmas T0_First_in_COE[elim] = T0_First_in_CO_def[THEN iffD1, elim_format, rule_format]

lemma reach_t0_first_in_co [simp, dest]: "reach tps_s s \<Longrightarrow> T0_First_in_CO s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: T0_First_in_CO_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: T0_First_in_CO_def tps_trans_all_defs)
      using T0_min_unique_ts[of s] T0_in_CO_def[of s] append_Cons empty_iff empty_set neq_Nil_conv nth_Cons_0 reach_t0_in_co sorry (* Continue here! *)
  qed (auto simp add: T0_First_in_CO_def tps_trans_all_defs)
qed


subsection \<open>Simulation realtion lemmas\<close>

lemma kvs_of_s_init:
  "kvs_of_s (state_init) = (\<lambda>k. [\<lparr>v_value = undefined, v_writer = T0, v_readerset = {}\<rparr>])"
  by (simp add: kvs_of_s_defs tps_s_defs)

abbreviation invariant_list_kvs where
  "invariant_list_kvs s \<equiv> \<forall>k cl. CO_not_No_Ver s k \<and>  Fresh_wr_notin_rs s cl"

lemma kvs_of_s_inv:
  assumes "state_trans s e s'"
    and "invariant_list_kvs s"
    and "\<not>commit_ev e"
  shows "kvs_of_s s' = kvs_of_s s"
  using assms
proof (induction e)
  case (WDone cl kv_map)    \<comment> \<open>write transaction already in abstract state, now just added to svr\<close>
  then show ?case 
    apply (auto simp add: tps_trans_defs)
    apply (auto simp add: kvs_of_s_defs tps_trans_defs)
    apply (intro ext)
    apply (auto split: ver_state.split)
    subgoal for cts k t cts' sts' lst' v' rs' t'
      apply (thin_tac "X = Y" for X Y)
      apply (cases "get_sn t' = cl_sn (cls s (get_cl t'))", auto)
      using Fresh_wr_notin_rs_def[of s]
      by (smt insertCI txid0.collapse).
next
  case (RegR svr t t_wr gst_ts)
  then show ?case       \<comment> \<open>extends readerset; ok since committed reads remain the same\<close>
    by (auto 3 4 simp add: kvs_of_s_defs tps_trans_defs add_to_readerset_def split: ver_state.split)
next
  case (PrepW svr t v)  \<comment> \<open>goes to Prep state; not yet added to abstract state (client not committed)\<close>
  then show ?case 
    apply (auto simp add: kvs_of_s_defs tps_trans_defs split: ver_state.split)
    apply (intro ext)
    by (auto split: ver_state.split)
next
  case (CommitW svr t v cts)   \<comment> \<open>goes to Commit state; ok: no change\<close>
  then show ?case  
    by (fastforce simp add: kvs_of_s_defs tps_trans_defs split: ver_state.split)
qed (auto 3 4 simp add: kvs_of_s_defs tps_trans_defs split: ver_state.split)

(* two auto 3 4 are SLOW *)

subsection \<open>Transaction ID Freshness\<close>

definition Sqn_Inv_nc where
  "Sqn_Inv_nc s cl \<longleftrightarrow> (\<forall>cts kv_map. cl_state (cls s cl) \<noteq> WtxnCommit cts kv_map
     \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m < cl_sn (cls s cl)))"

lemmas Sqn_Inv_ncI = Sqn_Inv_nc_def[THEN iffD2, rule_format]
lemmas Sqn_Inv_ncE[elim] = Sqn_Inv_nc_def[THEN iffD1, elim_format, rule_format]

lemma reach_sql_inv_nc [simp]: "reach tps_s s \<Longrightarrow> Sqn_Inv_nc s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Sqn_Inv_nc_def tps_s_def kvs_of_s_init get_sqns_old_def txid_defs)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    hence sqn_added: "get_sqns (kvs_of_s s') x1 = get_sqns (kvs_of_s s) x1 \<union> {cl_sn (cls s x1)}" sorry
    from RDone have "cl \<noteq> x1 \<longrightarrow> get_sqns (kvs_of_s s') cl = get_sqns (kvs_of_s s) cl"
      apply (simp add: read_done_def read_done_U_def) sorry
    then show ?case using RDone sqn_added by (auto simp add: Sqn_Inv_nc_def tps_trans_defs)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Sqn_Inv_nc_def tps_trans_defs) sorry
  next
    case (WDone x1 x2 x3)
    then show ?case apply (simp add: Sqn_Inv_nc_def tps_trans_defs)
      by (metis less_SucI nat.discI txn_state.inject(3))
  qed (auto simp add: Sqn_Inv_nc_def tps_trans_defs)
qed

definition Sqn_Inv_c where
  "Sqn_Inv_c s cl \<longleftrightarrow> (\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map
     \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m \<le> cl_sn (cls s cl)))"

lemmas Sqn_Inv_cI = Sqn_Inv_c_def[THEN iffD2, rule_format]
lemmas Sqn_Inv_cE[elim] = Sqn_Inv_c_def[THEN iffD1, elim_format, rule_format]

lemma reach_sql_inv_c [simp]: "reach tps_s s \<Longrightarrow> Sqn_Inv_c s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Sqn_Inv_c_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: Sqn_Inv_c_def)
      by (metis (full_types) Sqn_Inv_nc_def gt_ex nless_le reach.reach_trans reach_sql_inv_nc
          reach_trans.hyps(1) txn_state.inject(3))+
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Sqn_Inv_c_def)
      by (metis Sqn_Inv_nc_def less_or_eq_imp_le reach.reach_trans reach_sql_inv_nc
          reach_trans.hyps(1) txn_state.inject(3))
  qed (auto simp add: Sqn_Inv_c_def tps_trans_defs)
qed

lemma t_is_fresh:
  assumes "Sqn_Inv_c s cl" and "Sqn_Inv_nc s cl"
    and "cl_state (cls s cl) \<in> {WtxnPrep kv_map, RtxnInProg keys kv_map}"
  shows "get_txn s cl \<in> next_txids (kvs_of_s s) cl"
  using assms by (auto simp add: kvs_of_s_defs next_txids_def)

subsection \<open>At functions\<close>

\<comment> \<open>committed\<close>
lemma at_is_committed:
  assumes "Init_Ver_Inv s k"
  shows "is_committed ((svr_state (svrs s k)) (at (svr_state (svrs s k)) rts))"
proof -
  let ?P = "\<lambda>t. is_committed (svr_state (svrs s k) t) \<and> get_ts (svr_state (svrs s k) t) \<le> rts"
    and ?f = "get_ts o (svr_state (svrs s k))"
  have fin: "finite {y. \<exists>x. ?P x \<and> y = ?f x}"
    using finite_nat_set_iff_bounded_le by auto
  have "?P T0" using assms(1) by auto
  then show ?thesis apply (auto simp add: at_def ver_committed_before_def)
    by (smt arg_max_exI[of ?P ?f] P_arg_max fin)
qed

lemma newest_own_write_is_committed:
  assumes "Finite_Wtxns_Dom s k"and "newest_own_write (svr_state (svrs s k)) ts cl = Some t"
  shows "is_committed (svr_state (svrs s k) t)"
proof -
  let ?P = "\<lambda>t. is_committed (svr_state (svrs s k) t)"
    and ?Q = "\<lambda>t. ts \<le> get_ts (svr_state (svrs s k) t) \<and> get_cl_w t = cl"
    and ?PQ = "\<lambda>t. is_committed (svr_state (svrs s k) t) \<and> ts \<le> get_ts (svr_state (svrs s k) t)
      \<and> get_cl_w t = cl"
    and ?f = "get_ts o (svr_state (svrs s k))"
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
  shows "is_committed (svr_state (svrs s k) (read_at (svr_state (svrs s k)) rts cl))"
  using assms
  by (simp add: read_at_def Let_def at_is_committed newest_own_write_is_committed split: option.split)


\<comment> \<open>preserved by add_to_readerset\<close>

lemma add_to_readerset_pres_at:
  "at (add_to_readerset wtxns t rts rlst t_wr) ts = at wtxns ts"
  by (simp add: at_def ver_committed_before_def add_to_readerset_pres_get_ts o_def
      add_to_readerset_pres_is_committed)

lemma add_to_readerset_pres_newest_own_write:
  "newest_own_write (add_to_readerset wtxns t rts rlst t_wr) ts cl = newest_own_write wtxns ts cl"
  by (auto simp add: newest_own_write_def ver_committed_after_def add_to_readerset_pres_get_ts o_def
      add_to_readerset_pres_is_committed)

lemma add_to_readerset_pres_read_at:
  "read_at (add_to_readerset wtxns t rts rlst t_wr) ts cl = read_at wtxns ts cl"
  by (simp add: read_at_def add_to_readerset_pres_at add_to_readerset_pres_get_ts
      add_to_readerset_pres_newest_own_write)


\<comment> \<open>preserved by prepare write\<close>
lemma arg_max_if_not:
  "(ARG_MAX (\<lambda>x. get_ts (if x = t then X else Y x)) ta. ta \<noteq> t \<and> (ta \<noteq> t \<longrightarrow> P ta)) = 
   (ARG_MAX (\<lambda>x. get_ts (Y x)) ta. ta \<noteq> t \<and> P ta)"
  apply (auto simp add: arg_max_def is_arg_max_def)
  by metis

lemma prepare_write_pres_at:
  "wtxns t = No_Ver \<Longrightarrow> at (wtxns (t := Prep ts v)) rts = at wtxns rts"
  apply (simp add: at_def ver_committed_before_def o_def arg_max_if_not)
  by (metis is_committed.simps(2))

lemma prepare_write_pres_newest_own_write:
  "wtxns t = No_Ver \<Longrightarrow> newest_own_write (wtxns (t := Prep ts v)) rts cl = newest_own_write wtxns rts cl"
  apply (auto simp add: newest_own_write_def ver_committed_after_def o_def arg_max_if_not)
  by (metis is_committed.simps(2))+

lemma prepare_write_pres_read_at:
  "Init_Ver_Inv s k \<Longrightarrow> svr_state (svrs s k) t = No_Ver \<Longrightarrow>
   read_at ((svr_state (svrs s k)) (t := Prep ts v)) rts cl = read_at (svr_state (svrs s k)) rts cl"
  apply (simp add: read_at_def Let_def prepare_write_pres_at prepare_write_pres_newest_own_write)
  by (metis at_is_committed is_committed.simps(2))


\<comment> \<open>preserved by commit_write\<close>
lemma commit_write_pres_at:
  "wtxns t = Prep ts v \<Longrightarrow> cts > rts \<Longrightarrow> at (wtxns (t := Commit cts sts lst v {})) rts = at wtxns rts"
  apply (simp add: at_def ver_committed_before_def o_def arg_max_if_not)
  by (metis is_committed.simps(3))

lemma commit_write_pres_newest_own_write:
  "get_cl_w t \<noteq> cl \<Longrightarrow>
   newest_own_write (wtxns (t := Commit cts sts lst v {})) rts cl = newest_own_write wtxns rts cl"
  apply (auto simp add: newest_own_write_def ver_committed_after_def o_def arg_max_if_not)
  by metis

lemma commit_write_pres_read_at:
  "Init_Ver_Inv s k \<Longrightarrow> svr_state (svrs s k) t = Prep ts v \<Longrightarrow> cts > rts \<Longrightarrow> get_cl_w t \<noteq> cl \<Longrightarrow>
   read_at ((svr_state (svrs s k)) (t := Commit cts sts lst v {})) rts cl = read_at (svr_state (svrs s k)) rts cl"
  apply (simp add: read_at_def Let_def commit_write_pres_at commit_write_pres_newest_own_write)
  by (metis at_is_committed[of s k] is_committed.simps(3))


subsection \<open>Kvt_map values of read_done\<close>
definition Rtxn_IdleK_notin_rs where
  "Rtxn_IdleK_notin_rs s cl \<longleftrightarrow> (\<forall>k keys kv_map t cts sts lst v rs rts rlst.
    cl_state (cls s cl) = RtxnInProg keys kv_map \<and> k \<notin> keys \<and>
    svr_state (svrs s k) t = Commit cts sts lst v rs \<longrightarrow> (get_txn s cl, rts, rlst) \<notin> rs)"

lemmas Rtxn_IdleK_notin_rsI = Rtxn_IdleK_notin_rs_def[THEN iffD2, rule_format]
lemmas Rtxn_IdleK_notin_rsE[elim] = Rtxn_IdleK_notin_rs_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_idle_k_notin_rs [simp]: "reach tps_s s \<Longrightarrow> Rtxn_IdleK_notin_rs s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rtxn_IdleK_notin_rs_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2 x3)
    then show ?case apply (auto simp add: Rtxn_IdleK_notin_rs_def tps_trans_defs)
      using Fresh_wr_notin_rs_def[of s]
      by (metis insertCI reach_fresh_wr_notin_rs)
  next
    case (RegR x1 x2 x3 x4)
    then show ?case 
      by (auto simp add: Rtxn_IdleK_notin_rs_def tps_trans_defs add_to_readerset_def
               split: ver_state.split)
  qed (auto simp add: Rtxn_IdleK_notin_rs_def tps_trans_defs, blast?)
qed

definition Rtxn_RegK_Kvtm_Cmt_in_rs where
  "Rtxn_RegK_Kvtm_Cmt_in_rs s cl \<longleftrightarrow> (\<forall>k keys kv_map v.
    cl_state (cls s cl) = RtxnInProg keys kv_map \<and> kv_map k = Some v \<longrightarrow>
    (\<exists>t cts sts lst rs rts rlst. svr_state (svrs s k) t = Commit cts sts lst v rs \<and> (get_txn s cl, rts, rlst) \<in> rs))"

lemmas Rtxn_RegK_Kvtm_Cmt_in_rsI = Rtxn_RegK_Kvtm_Cmt_in_rs_def[THEN iffD2, rule_format]
lemmas Rtxn_RegK_Kvtm_Cmt_in_rsE[elim] = Rtxn_RegK_Kvtm_Cmt_in_rs_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_regk_kvtm_cmt_in_rs [simp]: "reach tps_s s \<Longrightarrow> Rtxn_RegK_Kvtm_Cmt_in_rs s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rtxn_RegK_Kvtm_Cmt_in_rs_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Rtxn_RegK_Kvtm_Cmt_in_rs_def tps_trans_defs)
      by (metis option.inject)
  next
    case (RegR x1 x2 x3 x4)
    then show ?case 
      apply (auto simp add: Rtxn_RegK_Kvtm_Cmt_in_rs_def tps_trans_defs add_to_readerset_def
                  split: ver_state.split)
      by (metis ver_state.inject(2))
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Rtxn_RegK_Kvtm_Cmt_in_rs_def tps_trans_defs)
      by (metis ver_state.distinct(3))
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (simp add: Rtxn_RegK_Kvtm_Cmt_in_rs_def tps_trans_defs)
      by (metis ver_state.distinct(5))
  qed (auto simp add: Rtxn_RegK_Kvtm_Cmt_in_rs_def tps_trans_defs)
qed

subsection \<open>Timestamp relations\<close>

definition Disjoint_RW where
  "Disjoint_RW s \<longleftrightarrow> ((\<Union>k. wtxns_dom (svr_state (svrs s k))) \<inter> Tn ` fst` (\<Union>k. wtxns_rsran (svr_state (svrs s k))) = {})"

lemmas Disjoint_RWI = Disjoint_RW_def[THEN iffD2, rule_format]
lemmas Disjoint_RWE[elim] = Disjoint_RW_def[THEN iffD1, elim_format, rule_format]

lemma reach_disjoint_rw [simp]: "reach tps_s s \<Longrightarrow> Disjoint_RW s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Disjoint_RW_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4)
    hence "\<And>k. wtxns_dom (svr_state (svrs s' k)) = wtxns_dom (svr_state (svrs s k))"
      by (simp add: tps_trans_defs add_to_readerset_wtxns_dom)
    hence "\<And>k. wtxns_rsran (svr_state (svrs s' k)) =
      (if k = x1
       then insert (x2, svr_clock (svrs s k), svr_lst (svrs s k)) (wtxns_rsran (svr_state (svrs s k)))
       else wtxns_rsran (svr_state (svrs s k)))" using RegR
      by (simp add: tps_trans_defs add_to_readerset_wtxns_rsran read_at_is_committed)
    then show ?case using RegR apply (simp add: Disjoint_RW_def)
      using Fresh_wr_notin_Wts_dom_def[of s "get_cl x2"] sorry
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (auto simp add: Disjoint_RW_def tps_trans_defs) sorry
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case sorry
  qed (auto simp add: Disjoint_RW_def tps_trans_defs)
qed

(*definition Disjoint_RW' where
  "Disjoint_RW' s \<longleftrightarrow> (kvs_writers (kvs_of_s s) \<inter> Tn ` kvs_readers (kvs_of_s s) = {})"

lemmas Disjoint_RW'I = Disjoint_RW'_def[THEN iffD2, rule_format]
lemmas Disjoint_RW'E[elim] = Disjoint_RW'_def[THEN iffD1, elim_format, rule_format]

lemma reach_disjoint_rw' [simp]: "reach tps_s s \<Longrightarrow> Disjoint_RW' s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case apply (auto simp add: Disjoint_RW'_def tps_def txid_defs)
    by (metis empty_set kvs_of_s_init list.simps(15) singletonD txid.distinct(1) version.select_convs(2))
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RDone cl kv_map sn u'')
    then show ?case apply (auto simp add: Disjoint_RW'_def tps_trans_defs txid_defs kvs_of_s_defs
          split: ver_state.split_asm)
      apply (metis CO_not_No_Ver_def reach_co_not_no_ver)
      apply (metis CO_not_No_Ver_def reach_co_not_no_ver)
      apply (metis CO_not_No_Ver_def reach_co_not_no_ver)
        apply (metis CO_not_No_Ver_def reach_co_not_no_ver)
      subgoal for xa xb apply (cases xb)
        by (smt (verit) CO_Tn_is_Cmt_Abs_def[of s xa] less_irrefl_nat reach_co_tn_is_cmt_abs
          reach_trans.hyps(2) txn_state.distinct(9) txid0.sel(1) txid0.sel(2) ver_state.distinct(5))
      subgoal for xa xb apply (cases xb)
        using Fresh_wr_notin_rs_def[of s] CO_Tn_is_Cmt_Abs_def[of s xa]
      (*
          xd \<in> set (cts_order s xc);
          Tn xb \<in> set (cts_order s xa);
          svr_state (svrs s xc) xd = Commit x31 x32 x33 x34;
          svr_state (svrs s xa) (Tn xb) = Commit x31a x32a x33a x34a
          xb \<in> x33;
      *)
        sorry
      done
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case sorry
  qed (auto simp add: Disjoint_RW'_def)
qed*)

definition RO_has_rts where
  "RO_has_rts s \<longleftrightarrow> (\<forall>t. Tn t \<in> read_only_Txs (kvs_of_s s) \<longrightarrow> (\<exists>rts. rtxn_rts s t = Some rts))"

lemmas RO_has_rtsI = RO_has_rts_def[THEN iffD2, rule_format]
lemmas RO_has_rtsE[elim] = RO_has_rts_def[THEN iffD1, elim_format, rule_format]

lemma reach_ro_in_readers [simp]: "reach tps_s s \<Longrightarrow> RO_has_rts s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: RO_has_rts_def tps_s_defs read_only_Txs_def txid_defs kvs_of_s_defs)
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

lemma reach_so_ro [simp]: "reach tps_s s \<Longrightarrow> SO_ROs s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: SO_ROs_def tps_s_defs)
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

lemma reach_so_ro_wr [simp]: "reach tps_s s \<Longrightarrow> SO_RO_WR s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: SO_RO_WR_def tps_s_defs)
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

subsection \<open>Closedness\<close>
lemma visTx'_union_distr: "visTx' K (u\<^sub>1 \<union> u\<^sub>2) = visTx' K u\<^sub>1 \<union> visTx' K u\<^sub>2"
  by (auto simp add: visTx'_def)

lemma visTx'_Union_distr: "visTx' K (\<Union>i\<in>I. u i) = (\<Union>i\<in>I. visTx' K (u i))"
  by (auto simp add: visTx'_def)

lemma visTx'_same_writers: "kvs_writers K' = kvs_writers K \<Longrightarrow> visTx' K' u = visTx' K u"
  by (simp add: visTx'_def)

lemma union_closed':
  assumes "closed' K u\<^sub>1 r"
    and "closed' K u\<^sub>2 r"
    and "kvs_writers K' = kvs_writers K" 
    and "read_only_Txs K \<subseteq> read_only_Txs K'"
  shows "closed' K' (u\<^sub>1 \<union> u\<^sub>2) r"
  using assms
  by (auto simp add: closed'_def visTx'_union_distr visTx'_same_writers[of K']
           intro: closed_general_set_union_closed)

lemma Union_closed':
  assumes "\<And>i. i \<in> I \<Longrightarrow> closed' K (u i) r"
    and "finite I" 
    and "kvs_writers K' = kvs_writers K" 
    and "read_only_Txs K \<subseteq> read_only_Txs K'"
  shows "closed' K' (\<Union>i\<in>I. u i) r"
  using assms                                  
  apply (simp add: closed'_def visTx'_Union_distr visTx'_same_writers[of K'])
  apply (rule closed_general_set_Union_closed)
  apply auto
  done

lemma union_closed'_extend_rel:
  assumes "closed' K u\<^sub>1 r"
    and "closed' K u\<^sub>2 r"
    and "kvs_writers K' = kvs_writers K" 
    and "read_only_Txs K \<subseteq> read_only_Txs K'"
    and "x \<notin> (r\<inverse>)\<^sup>* `` (visTx' K u\<^sub>1 \<union> visTx' K u\<^sub>2)"
    and "r' = (\<Union>y\<in>Y. {(y, x)}) \<union> r"
    and "finite Y"
  shows "closed' K' (u\<^sub>1 \<union> u\<^sub>2) r'"
  using assms
  by (auto simp add: closed'_def visTx'_union_distr visTx'_same_writers[of K']
      intro: closed_general_union_V_extend_N_extend_rel)


lemma visTx'_new_writer: "kvs_writers K' = insert t (kvs_writers K) \<Longrightarrow>
  visTx' K' (insert t u) = insert t (visTx' K u)"
  by (auto simp add: visTx'_def)

lemma insert_wr_t_closed':
  assumes "closed' K u r"
    and "closed_general {t} (r\<inverse>) (visTx' K u \<union> read_only_Txs K)"
    and "read_only_Txs K' = read_only_Txs K"
    and "kvs_writers K' = insert t (kvs_writers K)"
  shows "closed' K' (insert t u) r"
  using assms
  by (auto simp add: closed'_def visTx'_new_writer intro: closed_general_set_union_closed)

\<comment> \<open>insert (k, t) in version's deps - used in get_ctx\<close>
lemma visTx'_observes_t:
  "t \<in> kvs_writers K \<Longrightarrow> visTx' K (insert t deps) = insert t (visTx' K deps)"
  by (simp add: visTx'_def)

lemma insert_kt_to_deps_closed':
  assumes "closed' K deps r"
    and "t \<in> kvs_writers K"
    and "closed_general {t} (r\<inverse>) (visTx' K deps \<union> read_only_Txs K)"
  shows "closed' K (insert t deps) r"
  using assms
  by (auto simp add: closed'_def visTx'_observes_t intro: closed_general_set_union_closed)

(*
\<comment> \<open>concrete read_done closedness\<close>

\<comment> \<open>premises\<close>
  
lemma get_ctx_closed:
  assumes "\<And>t. t \<in> read_wtxns s cl (dom kv_map) \<Longrightarrow>
      closed' K (insert t (wtxn_deps s t)) r"
    and "cl_state (cls s cl) = RtxnInProg (dom kv_map) kv_map"
    and "Rtxn_RegK_Kvtm_Cmt_in_rs s cl"
    and "Finite_Dom_Kv_map_rd s cl"
  shows "closed' K (get_ctx s cl (dom kv_map)) r"
  using assms
  by (auto simp add: Finite_Dom_Kv_map_rd_def get_ctx_defs intro!: Union_closed')

lemma v_writer_kvs_of_s:
  assumes "\<forall>k. CO_not_No_Ver s k"
  shows "v_writer ` (\<lambda>t. case svr_state (svrs s k) t of
      Prep ts v \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = {}\<rparr>
    | Commit cts sts lst v rs \<Rightarrow> \<lparr>v_value = v, v_writer = t,
        v_readerset = {t. \<exists>rts rlst. (t, rts, rlst) \<in> rs \<and> get_sn t < cl_sn (cls s (get_cl t))}\<rparr>) ` set (cts_order s k) =
   {t \<in> set (cts_order s k). \<exists>ts v cts sts lst rs.
        svr_state (svrs s k) t \<in> {Prep ts v, Commit cts sts lst v rs}}"
  using assms
  by (auto simp add: image_iff CO_not_No_Ver_def split: ver_state.split)

lemma v_readerset_kvs_of_s_k:
  assumes "\<forall>k. CO_not_No_Ver s k"
    and "t_wr \<in> set (cts_order s k)"
  shows "v_readerset (case svr_state (svrs s k) t_wr of
      Prep ts v \<Rightarrow> \<lparr>v_value = v, v_writer = t_wr, v_readerset = {}\<rparr>
    | Commit cts sts lst v rs \<Rightarrow> \<lparr>v_value = v, v_writer = t_wr,
        v_readerset = {t. \<exists>rts rlst. (t, rts, rlst) \<in> rs \<and> get_sn t < cl_sn (cls s (get_cl t))}\<rparr>) = 
   {t. \<exists>cts sts lst v rs rts rlst. svr_state (svrs s k) t_wr = Commit cts sts lst v rs \<and>
      (t, rts, rlst) \<in> rs \<and> get_sn t < cl_sn (cls s (get_cl t))}"
  using assms
  by (auto split: ver_state.split)

lemma v_readerset_kvs_of_s:
  assumes "\<forall>k. CO_not_No_Ver s k"
  shows "(\<Union>k. \<Union>t_wr\<in>set (cts_order s k). v_readerset (case svr_state (svrs s k) t_wr of
      Prep ts v \<Rightarrow> \<lparr>v_value = v, v_writer = t_wr, v_readerset = {}\<rparr>
    | Commit cts sts lst v rs \<Rightarrow> \<lparr>v_value = v, v_writer = t_wr,
        v_readerset = {t. \<exists>rts rlst. (t, rts, rlst) \<in> rs \<and> get_sn t < cl_sn (cls s (get_cl t))}\<rparr>)) = 
   {t. \<exists>k. \<exists>t_wr \<in> set (cts_order s k).
      \<exists>cts sts lst v rs rts rlst. svr_state (svrs s k) t_wr = Commit cts sts lst v rs \<and>
      (t, rts, rlst) \<in> rs \<and> get_sn t < cl_sn (cls s (get_cl t))}"
  using assms
  apply (auto simp add: v_readerset_kvs_of_s_k)
  by blast+

lemma read_done_same_writers:
  assumes "read_done cl kv_map sn u'' s s'"
    and "\<forall>k. CO_not_No_Ver s k"
    and "\<forall>k. CO_not_No_Ver s' k"
  shows "kvs_writers (kvs_of_s s') = kvs_writers (kvs_of_s s)"
  using assms
  apply (simp add: kvs_writers_def vl_writers_def kvs_of_s_defs v_writer_kvs_of_s CO_not_No_Ver_def)
  by (simp add: read_done_def read_done_U_def)

lemma insert_Diff_if': "a \<notin> c \<Longrightarrow> insert a (b - c) = insert a b - c"
  by (simp add: insert_Diff_if)

lemma read_done_new_read:
  assumes "read_done cl kv_map sn u'' s s'"
    and "\<forall>k. CO_not_No_Ver s k"
    and "\<forall>k. CO_not_No_Ver s' k"
    and "\<forall>k. Committed_Abs_in_CO s k"
    and "\<forall>k. T0_in_CO s k"
    and "Finite_Dom_Kv_map_rd s cl"
    and "Rtxn_RegK_Kvtm_Cmt_in_rs s cl"
    and "Rtxn_RegK_Kvtm_Cmt_in_rs s cl"
    and "Tn (get_txn s cl) \<notin> kvs_writers (kvs_of_s s)"
  shows "read_only_Txs (kvs_of_s s') = insert (Tn (get_txn s cl)) (read_only_Txs (kvs_of_s s))"
  using assms
  apply (simp add: read_only_Txs_def read_done_same_writers insert_Diff_if')
  apply (rule arg_cong[where f="\<lambda>m. m - _"])
  apply (simp add: kvs_readers_def vl_readers_def kvs_of_s_defs v_readerset_kvs_of_s)
  apply (auto simp add: tps_trans_defs image_insert[symmetric] simp del: image_insert)
  using image_eqI apply blast
  apply (smt (z3) image_eqI insertCI less_SucE mem_Collect_eq txid0.collapse)
  using image_eqI apply blast
  subgoal apply (rule image_eqI, auto)
    apply (cases "dom kv_map = {}", auto simp add: ex_in_conv[symmetric] simp del: dom_eq_empty_conv)
    subgoal for k v apply (rule exI[where x=k])
      by (metis (lifting) Rtxn_RegK_Kvtm_Cmt_in_rs_def Committed_Abs_in_CO_def)
    done
  by (smt (verit) image_eqI less_Suc_eq mem_Collect_eq)

lemma fresh_rtxn_not_vis:
  assumes "Tn (get_txn s cl) \<notin> kvs_writers (kvs_of_s s)"
    and "\<forall>t \<in> kvs_writers (kvs_of_s s). get_sn_w t < cl_sn (cls s cl)"
  shows "Tn (get_txn s cl) \<notin> ((R_CC (kvs_of_s s))\<inverse>)\<^sup>* `` (visTx' (kvs_of_s s)
    (cl_ctx (cls s cl) \<union> get_ctx s cl keys))"
  apply (auto simp add: visTx'_def R_CC_def)
  subgoal for t apply (induction t "Tn (get_txn s cl)" rule: rtrancl.induct, auto)
      apply (simp add: assms(1))
     apply (simp add: SO_def SO0_def) oops

lemma read_done_WR_onK:
  assumes "read_done cl kv_map sn u'' s s'"
  shows "R_onK WR (kvs_of_s s') = (read_wtxns s cl (dom kv_map) \<times> {Tn (get_txn s cl)}) \<union> R_onK WR (kvs_of_s s)"
  apply (auto simp add: R_onK_def WR_def) sorry

lemma read_done_extend_rel:
  assumes "read_done cl kv_map sn u'' s s'"
  shows "R_CC (kvs_of_s s') = (read_wtxns s cl (dom kv_map) \<times> {Tn (get_txn s cl)}) \<union> R_CC (kvs_of_s s)"
  using assms
  by (auto simp add: R_CC_def read_done_WR_onK)


\<comment> \<open>read_done closedness (canCommit)\<close>
lemma read_done_ctx_closed:
  assumes "closed' (kvs_of_s s) (cl_ctx (cls s cl)) (R_CC (kvs_of_s s))"
    and "closed' (kvs_of_s s) (get_ctx s cl keys) (R_CC (kvs_of_s s))"
    and "kvs_writers (kvs_of_s s') = kvs_writers (kvs_of_s s)"
    and "read_only_Txs (kvs_of_s s') = insert (Tn (get_txn s cl)) (read_only_Txs (kvs_of_s s))"
    and "Tn (get_txn s cl) \<notin> ((R_CC (kvs_of_s s))\<inverse>)\<^sup>* ``
      (visTx' (kvs_of_s s) (cl_ctx (cls s cl) \<union> get_ctx s cl keys))"
    and "R_CC (kvs_of_s s') = (read_wtxns s cl keys \<times> {Tn (get_txn s cl)}) \<union> R_CC (kvs_of_s s)"
    and "Finite_Keys s cl"
    and "cl_state (cls s cl) = RtxnInProg keys kv_map"
  shows "closed' (kvs_of_s s') (cl_ctx (cls s cl) \<union> get_ctx s cl keys) (R_CC (kvs_of_s s'))"
  using assms
  by (auto simp add: closed'_def visTx'_union_distr visTx'_same_writers[of "kvs_of_s s'"] finite_read_wtxns
    Finite_Keys_def intro: closed_general_union_V_extend_N_extend_rel[where Y="read_wtxns s cl keys"]) old lemmas*)
                                                            
\<comment> \<open>write_commit closedness (canCommit)\<close>
lemma write_commit_WR_onK:
  assumes "write_commit cl kv_map commit_t sn u'' s s'"
  shows "R_onK WR (kvs_of_s s') = R_onK WR (kvs_of_s s)"
  apply (auto simp add: R_onK_def WR_def) sorry

lemma write_commit_same_rel:
  assumes "write_commit cl kv_map commit_t sn u'' s s'"
  shows "R_CC (kvs_of_s s') = R_CC (kvs_of_s s)"
  using assms
  by (auto simp add: R_CC_def write_commit_WR_onK)

lemma "dom kv_map \<noteq> {} \<Longrightarrow> snd ` (\<Union>k\<in>dom kv_map. {(k, t)}) = {t}"
  apply (auto simp add: image_def)
  by (metis domIff insertI1 sndI)

lemma write_commit_ctx_closed:    (* HERE *)
  assumes "write_commit cl kv_map commit_t sn u'' s s'"
    and "closed' (kvs_of_s s) (cl_ctx (cls s cl)) (R_CC (kvs_of_s s))"
    and "closed_general {get_wtxn s cl} ((R_CC (kvs_of_s s))\<inverse>)
          (visTx' (kvs_of_s s) (cl_ctx (cls s cl)) \<union> read_only_Txs (kvs_of_s s))"
    and "read_only_Txs (kvs_of_s s') = read_only_Txs (kvs_of_s s)"
    and "kvs_writers (kvs_of_s s') = insert (get_wtxn s cl) (kvs_writers (kvs_of_s s))"
  shows "closed' (kvs_of_s s') (insert (get_wtxn s cl) (cl_ctx (cls s cl))) (R_CC (kvs_of_s s'))"
  using assms
  apply (auto simp add: closed'_def write_commit_same_rel image_def intro: insert_wr_t_closed') 
  sorry


subsection \<open>CanCommit\<close>

lemma the_T0: "(THE i. i = 0 \<and> [T0] ! i = T0) = 0" by auto

lemmas canCommit_defs = ET_CC.canCommit_def R_CC_def R_onK_def

(*lemma visTx_visTx': "\<comment> \<open>\<forall>k t. (k, t) \<in> u \<longrightarrow> t \<in> set (cts_order s k) \<Longrightarrow>\<close>
  visTx (kvs_of_s s) (view_of (cts_order s) u) = visTx' (kvs_of_s s) u"
  apply (auto simp add: visTx_def visTx'_def (* kvs_writers_def vl_writers_def image_iff*) ) 
  
  sorry

lemma closed_closed': "closed (kvs_of_s s) (view_of (cts_order s) u) r = closed' (kvs_of_s s) u r"
  by (simp add: closed'_def visTx_visTx') *)

lemma visTx'_cl_ctx_subset_writers:
  "visTx' (kvs_of_s s) (cl_ctx (cls s cl)) \<subseteq> kvs_writers (kvs_of_s s)"
  by (simp add: visTx'_def)

lemma visTx'_wtxn_deps_subset_writers: 
  "wtxn_deps s t = deps \<Longrightarrow> visTx' (kvs_of_s s) deps \<subseteq> kvs_writers (kvs_of_s s)"
  by (simp add: visTx'_def)

lemma "kvs_writers (kvs_of_s s) \<subseteq> (\<Union>k. wtxns_dom (svr_state (svrs s k)))"
  oops

lemma "kvs_readers (kvs_of_s s) \<subseteq> fst ` (\<Union>k. wtxns_rsran (svr_state (svrs s k)))"
  oops

definition RO_le_gst :: "'v global_conf \<Rightarrow> cl_id \<Rightarrow> txid set" where
  "RO_le_gst s cl \<equiv> {t \<in> read_only_Txs (kvs_of_s s). \<exists>t'. t = Tn t' \<and> the (rtxn_rts s t') \<le> gst (cls s cl)}"

definition RO_WO_Inv where
  "RO_WO_Inv s \<longleftrightarrow> (\<Union>k. wtxns_dom (svr_state (svrs s k))) \<inter> Tn ` fst ` (\<Union>k. wtxns_rsran (svr_state (svrs s k))) = {}"

lemmas RO_WO_InvI = RO_WO_Inv_def[THEN iffD2, rule_format]
lemmas RO_WO_InvE[elim] = RO_WO_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_ro_wo_inv [simp]: "reach tps_s s \<Longrightarrow> RO_WO_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: RO_WO_Inv_def tps_s_defs)
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
    case (CommitW x1 x2 x3 x4)
    then show ?case sorry
  qed (auto simp add: RO_WO_Inv_def tps_trans_defs)
qed

(*
subsection \<open>Ctx Invariants\<close>

definition View_Init where
  "View_Init s cl \<longleftrightarrow> (T0 \<in> cl_ctx (cls s cl))"

lemmas View_InitI = View_Init_def[THEN iffD2, rule_format]
lemmas View_InitE[elim] = View_Init_def[THEN iffD1, elim_format, rule_format]

lemma reach_view_init [simp]: "reach tps_s s \<Longrightarrow> View_Init s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: View_Init_def tps_s_defs dep_set_init_def)
next
  case (reach_trans s e s')
  then show ?case 
    by (induction e) (auto simp add: View_Init_def tps_trans_defs)
qed


\<comment> \<open>deps are committed\<close>
definition Ctx_Committed where
  "Ctx_Committed s \<longleftrightarrow> (\<forall>cl t k. t \<in> cl_ctx (cls s cl) \<and> t \<in> set (cts_order s k)  \<longrightarrow>
    (is_committed (svr_state (svrs s k) t) \<or> 
    (\<exists>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<and> k \<in> dom kv_map \<and> t = get_wtxn s cl)))"

lemmas Ctx_CommittedI = Ctx_Committed_def[THEN iffD2, rule_format]
lemmas Ctx_CommittedE[elim] = Ctx_Committed_def[THEN iffD1, elim_format, rule_format]

definition Wtxn_Deps_Committed where
  "Wtxn_Deps_Committed s \<longleftrightarrow> (\<forall>t k t' deps. wtxn_deps s t' = deps \<and>
    t \<in> deps \<and> t \<in> set (cts_order s k) \<longrightarrow> is_committed (svr_state (svrs s k) t))"

lemmas Wtxn_Deps_CommittedI = Wtxn_Deps_Committed_def[THEN iffD2, rule_format]
lemmas Wtxn_Deps_CommittedE[elim] = Wtxn_Deps_Committed_def[THEN iffD1, elim_format, rule_format]

lemmas deps_committed_defs = Ctx_Committed_def Wtxn_Deps_Committed_def

lemma reach_deps_committed[simp]:
  "reach tps_s s \<Longrightarrow> Ctx_Committed s \<and> Wtxn_Deps_Committed s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: deps_committed_defs tps_s_defs dep_set_init_def split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RInvoke x1 x2 x3)
    then show ?case apply (simp add: deps_committed_defs tps_trans_defs)
      by (smt (verit) txn_state.distinct(5))
  next
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: deps_committed_defs tps_trans_defs)
      by (metis txn_state.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: deps_committed_defs tps_trans_defs get_ctx_def)
      apply (metis (mono_tags, opaque_lifting) txn_state.distinct(9)) sorry
  next
    case (WInvoke x1 x2 x3)
    then show ?case apply (simp add: deps_committed_defs tps_trans_defs)
      by (metis txn_state.distinct(5))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: deps_committed_defs tps_trans_defs)
      sorry
  next
    case (WDone x1 x2 x3)
    then show ?case apply (auto simp add: deps_committed_defs tps_trans_defs)
      by (metis (no_types, lifting) is_committed.simps(1) txn_state.inject(3))
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (auto simp add: deps_committed_defs tps_trans_defs)
      apply (smt (verit) add_to_readerset_no_ver_inv add_to_readerset_prep_inv is_committed.elims(3))
      by (metis add_to_readerset_commit' is_committed.elims(1) is_committed.simps(1))
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (auto simp add: deps_committed_defs tps_trans_defs)
      by (metis is_committed.simps(2))+
  qed (simp_all add: deps_committed_defs tps_trans_defs, blast?)
qed


definition Get_Ctx_Commited where
  "Get_Ctx_Commited s k \<longleftrightarrow> (\<forall>cl t keys kv_map. cl_state (cls s cl) = RtxnInProg keys kv_map \<and>
    t \<in> get_ctx s cl keys \<and> t \<in> set (cts_order s k) \<longrightarrow> is_committed (svr_state (svrs s k) t))"

lemmas Get_Ctx_CommitedI = Get_Ctx_Commited_def[THEN iffD2, rule_format]
lemmas Get_Ctx_CommitedE[elim] = Get_Ctx_Commited_def[THEN iffD1, elim_format, rule_format]

lemma reach_get_ctx_committed[simp]: "reach tps_s s \<Longrightarrow> Get_Ctx_Commited s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Get_Ctx_Commited_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RInvoke x1 x2 x3)
    then show ?case apply (auto simp add: Get_Ctx_Commited_def tps_trans_defs get_ctx_defs)
      using Finite_Wtxns_Dom_def Init_Ver_Inv_def read_at_is_committed
      (*apply (meson reach_finite_wtxns_dom reach_init_ver_inv read_at_is_committed)*)
      using Wtxn_Deps_Committed_def[of s] sorry
      (*by (metis is_committed.elims(2) reach_deps_committed reach_finite_wtxns_dom reach_init_ver_inv
          read_at_is_committed ver_state.sel(6))*)
  next
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Get_Ctx_Commited_def tps_trans_defs get_ctx_defs)
      by blast+
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Get_Ctx_Commited_def tps_trans_defs get_ctx_defs)
      sorry
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Get_Ctx_Commited_def tps_trans_defs get_ctx_defs)
      by (metis add_to_readerset_pres_is_committed add_to_readerset_pres_read_at)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Get_Ctx_Commited_def tps_trans_defs get_ctx_defs prepare_write_pres_read_at)
      by (smt is_committed.simps(2) reach_finite_wtxns_dom reach_init_ver_inv read_at_is_committed)
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (auto simp add: Get_Ctx_Commited_def tps_trans_defs)
      subgoal for kv_map ts using commit_write_pres_read_at[of s x1 x2 ts x3]
          Init_Ver_Inv_def[of s x1] sorry sorry
  qed (auto simp add: Get_Ctx_Commited_def tps_trans_defs get_ctx_defs)
qed


definition Deps_Closed where
  "Deps_Closed s cl \<longleftrightarrow> (closed' (kvs_of_s s) (cl_ctx (cls s cl)) (R_CC (kvs_of_s s)) \<and> 
    (\<forall>k t cts sts lst v rs kv_map deps. svr_state (svrs s k) t = Commit cts sts lst v rs \<or>
      cl_state (cls s cl) = WtxnCommit cts kv_map \<longrightarrow>
      closed' (kvs_of_s s) deps (R_CC (kvs_of_s s))))"

lemmas Deps_ClosedI = Deps_Closed_def[THEN iffD2, rule_format]
lemmas Deps_ClosedE[elim] = Deps_Closed_def[THEN iffD1, elim_format, rule_format]

lemmas closed'_defs = closed'_def R_CC_def R_onK_def

lemma reach_deps_closed[simp]:
  "reach tps_s s \<Longrightarrow> Deps_Closed s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case apply (auto simp add: Deps_Closed_def tps_def) sorry
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case using read_done_ctx_closed get_ctx_closed
      apply (auto simp add: Deps_Closed_def tps_trans_defs) sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Deps_Closed_def tps_trans_defs) sorry
  next
    case (RegR x1 x2 x3 x4)
    then show ?case sorry
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case sorry
  qed (auto simp add: Deps_Closed_def tps_trans_defs)
qed


subsection \<open>View Shift\<close>

definition Cl_Ctx_WtxnCommit where
  "Cl_Ctx_WtxnCommit s cl \<longleftrightarrow>
    (\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<longrightarrow>
      get_wtxn s cl \<in> cl_ctx (cls s cl))"

lemmas Cl_Ctx_WtxnCommitI = Cl_Ctx_WtxnCommit_def[THEN iffD2, rule_format]
lemmas Cl_Ctx_WtxnCommitE[elim] = Cl_Ctx_WtxnCommit_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_ctx_wtxncommit [simp]: "reach tps_s s \<Longrightarrow> Cl_Ctx_WtxnCommit s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Cl_Ctx_WtxnCommit_def tps_s_defs)
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
  apply (auto simp add: read_done_def kvs_of_s_defs txid_defs split: ver_state.split) sorry
*)
subsection \<open>Fp Property\<close>

\<comment> \<open>Fingerprint content invariant and Lemmas for proving the fp_property\<close>

definition RegR_Fp_Inv where
  "RegR_Fp_Inv s k \<longleftrightarrow> (\<forall>t keys kv_map cts sts lst v rs.
    cl_state (cls s (get_cl t)) = RtxnInProg keys kv_map \<and> k \<in> keys \<and> kv_map k = None \<and>
    svr_state (svrs s k) (read_at (svr_state (svrs s k)) (gst (cls s (get_cl t))) (get_cl t))
       = Commit cts sts lst v rs \<longrightarrow>
    v = v_value ((kvs_of_s s k) !
      Max (view_of (cts_order s) (get_view s (get_cl t)) k)))"

lemmas RegR_Fp_InvI = RegR_Fp_Inv_def[THEN iffD2, rule_format]
lemmas RegR_Fp_InvE[elim] = RegR_Fp_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_reg_r_fp [simp]: "reach tps_s s \<Longrightarrow> RegR_Fp_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: RegR_Fp_Inv_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2 x3)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs) sorry
  next
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs) sorry
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs) sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs) sorry
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs) sorry
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs) sorry
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs) sorry
  qed (auto simp add: RegR_Fp_Inv_def tps_trans_defs get_view_def)
qed

(* more inv to show v_value v_writer kvs_of_s commit_t kv_map relation*)

definition Rtxn_Fp_Inv where
  "Rtxn_Fp_Inv s cl \<longleftrightarrow> (\<forall>k keys kv_map v.
    cl_state (cls s cl) = RtxnInProg keys kv_map \<and> kv_map k = Some v \<longrightarrow>
     v = v_value ((kvs_of_s s k) !
        Max (view_of (cts_order s) (get_view s cl) k)))"

lemmas Rtxn_Fp_InvI = Rtxn_Fp_Inv_def[THEN iffD2, rule_format]
lemmas Rtxn_Fp_InvE[elim] = Rtxn_Fp_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_fp [simp]: "reach tps_s s \<Longrightarrow> Rtxn_Fp_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rtxn_Fp_Inv_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Rtxn_Fp_Inv_def tps_trans_defs) sorry
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
    case (CommitW x1 x2 x3 x4)
    then show ?case sorry
  qed (auto simp add: Rtxn_Fp_Inv_def tps_trans_defs view_of_def get_view_def)
qed

definition Rtxn_notin_rs_other_t where
  "Rtxn_notin_rs_other_t s cl \<longleftrightarrow>
   (\<forall>k keys kv_map t cts sts lst v rs t' cts' sts' lst' v' rs' rts rlst rts' rlst'.
    cl_state (cls s cl) = RtxnInProg keys kv_map \<and>
    svr_state (svrs s k) t = Commit cts sts lst v rs \<and> (get_txn s cl, rts, rlst) \<in> rs \<and>
    \<comment> \<open>try: t' \<noteq> cts_order s k ! Max (view_of (cts_order s) (cl_ctx (cls s cl) \<union> get_ctx s cl keys) k) \<and>\<close>
    svr_state (svrs s k) t' = Commit cts' sts' lst' v' rs' \<longrightarrow> (get_txn s cl, rts', rlst') \<notin> rs')"

lemmas Rtxn_notin_rs_other_tI = Rtxn_notin_rs_other_t_def[THEN iffD2, rule_format]
lemmas Rtxn_notin_rs_other_tE[elim] = Rtxn_notin_rs_other_t_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_notin_rs_other_t [simp]: "reach tps_s s \<Longrightarrow> Rtxn_notin_rs_other_t s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rtxn_notin_rs_other_t_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2 x3)
    then show ?case sorry
next
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Rtxn_notin_rs_other_t_def tps_trans_defs)
      by meson
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (auto simp add: Rtxn_notin_rs_other_t_def tps_trans_defs
          split: ver_state.split) sorry
  next
    case (PrepW x1 x2 x3)
    then show ?case by (simp add: Rtxn_notin_rs_other_t_def tps_trans_defs, blast)
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case by (simp add: Rtxn_notin_rs_other_t_def tps_trans_defs, blast)
  qed (auto simp add: Rtxn_notin_rs_other_t_def tps_trans_defs)
qed


subsection \<open>Proofs in progress\<close>

(**************************************)
(**************************************)

(* lemmas about lists *)

(*
lemma 
  "\<lbrakk> distinct xs; x \<in> set xs \<rbrakk> \<Longrightarrow> \<exists>!i. i < length xs \<and> xs ! i = x"
  by (fact distinct_Ex1)
*)

lemma distinct_prefix:
  "\<lbrakk> distinct xs; prefix xs' xs \<rbrakk> \<Longrightarrow> distinct xs'"
  by (metis distinct_append prefixE)

lemma nth_eq_prefix:
  "\<lbrakk> i < length xs; prefix xs ys \<rbrakk> \<Longrightarrow> xs ! i = ys ! i"
  by (metis nth_append prefix_def)


lemma nth_distinct_injective:
  "\<lbrakk> xs ! i = xs ! j; i < length xs; j < length xs; distinct xs \<rbrakk> \<Longrightarrow> i = j"
  using nth_eq_iff_index_eq by blast


(* lemma about THE *)

lemma the_the_equality:
  "\<lbrakk> P a; \<And>y. P y \<Longrightarrow> y = a; \<And>x. Q x \<longleftrightarrow> P x \<rbrakk> \<Longrightarrow> (THE x. P x) = (THE x. Q x)"
  by (rule theI2) auto




(* write_commit: preservation lemmas *)

thm kvs_of_s_defs

(*
lemma write_commit_cl_sn_update:
  assumes 
    "write_commit cl kv_map cts sn u'' gs gs'"
  shows
    "cl_sn (cls gs' cl') = cl_sn (cls gs cl')"
  using assms
  by (auto simp add: write_commit_def) 
*)


(* 
  lemmas about views 
*)

lemma get_view_cls_update:
 "\<forall>k\<in>dom kv_map. \<forall>t\<in>set (cts_order gs k). unique_ts (wtxn_cts gs) t < (cts, cl) \<Longrightarrow>
   cts > gst (cls gs cl') \<Longrightarrow>
    get_view (gs\<lparr>cls := (cls gs)(cl := cls gs cl\<lparr>cl_state := X, cl_clock := Y\<rparr>),
                  wtxn_cts := wtxn_cts gs(get_wtxn gs cl \<mapsto> cts),
                  cts_order := new_cord \<rparr>) cl'
  = get_view gs cl'"
  apply (auto simp add: get_view_def; rule ext, auto) oops

lemma views_of_s_cls_update:  (* STILL NEEDED? *)
  "\<forall>k\<in>dom kv_map. \<forall>t\<in>set (cts_order gs k). unique_ts (wtxn_cts gs) t < (cts, cl) \<Longrightarrow>
   views_of_s (gs\<lparr>cls := (cls gs)(cl := cls gs cl\<lparr>cl_state := X, cl_clock := Y\<rparr>),
                  wtxn_cts := wtxn_cts gs(get_wtxn gs cl \<mapsto> cts),
                  cts_order := new_cord \<rparr>) cl' = 
   view_of new_cord (get_view gs cl')"
  apply (auto simp add: views_of_s_def get_view_def)
  subgoal apply (intro arg_cong[where f="view_of new_cord"] ext)
    apply auto sorry
  subgoal apply (intro arg_cong[where f="view_of new_cord"] ext)
    apply auto
    subgoal sorry
    subgoal sorry
    subgoal sorry
    oops

thm view_of_def
term view_of


lemma view_of_deps_mono:     (* same as view_grows_view_of *)
  assumes "\<forall>k. u k \<subseteq> u' k"
  shows "view_of cord u \<sqsubseteq> view_of cord u'"
  using assms
  by (auto simp add: view_of_def view_order_def)

text \<open>Note: we must have @{prop "distinct corder"} for @{term view_of} to be well-defined. \<close>


thm ex1E
thm the1_equality the1_equality' the_equality theI theI2
thm prefix_length_le nth_eq_iff_index_eq

lemma view_of_mono: 
  assumes "\<forall>k. u k \<subseteq> u' k" and "\<And>k. prefix (cord k) (cord' k)" "\<And>k. distinct (cord' k)" 
  shows "view_of cord u \<sqsubseteq> view_of cord' u'"
  using assms
proof -
  { 
    fix k t i
    assume "t \<in> set (cord k)" 
    have "distinct (cord' k)" "distinct (cord k)" 
      using assms(2-3) by (auto dest: distinct_prefix) 
    have "prefix (cord k) (cord' k)" "set (cord k) \<subseteq> set (cord' k)" "length (cord k) \<le> length (cord' k)"
      using assms(2) by (auto dest: set_mono_prefix prefix_length_le)
    then have "\<exists>!i. i < length (cord k) \<and> cord k ! i = t"  
      using \<open>distinct (cord k)\<close> \<open>t \<in> set (cord k)\<close> by (intro distinct_Ex1) auto
    then obtain i where
      Pi: "i < length (cord k)" "cord k ! i = t" and
      Pj: "\<And>j. \<lbrakk> j < length (cord k); cord k ! j = t \<rbrakk> \<Longrightarrow> j = i"
      by (elim ex1E) auto
    have "index_of (cord k) t = index_of (cord' k) t" 
      using \<open>prefix (cord k) (cord' k)\<close> \<open>distinct (cord k)\<close> \<open>distinct (cord' k)\<close> 
            \<open>length (cord k) \<le> length (cord' k)\<close> Pi
      by (auto simp add: nth_eq_prefix nth_eq_iff_index_eq  intro: the_the_equality)
  }
  then show ?thesis using assms 
    by (fastforce simp add: view_of_def view_order_def dest: set_mono_prefix)
qed
(*

lemma view_of_ext_corder_cl_ctx:  
  assumes "\<And>k. distinct (ext_corder (get_wtxn gs cl) kv_map (cts_order gs) k)"
  shows "view_of (cts_order gs) (cl_ctx (cls gs cl)) \<sqsubseteq> 
         view_of (ext_corder (get_wtxn gs cl) kv_map (cts_order gs)) 
                 (insert (get_wtxn gs cl) (cl_ctx (cls gs cl)))"
  using assms
  by (intro view_of_mono) (auto simp add: ext_corder_def)

*)

(*
  lemmas about KVS updates
*)


lemma update_kv_new_txid__DO_NOT_USE:   
  assumes 
    "t \<in> kvs_txids (update_kv t0 (write_only_fp kv_map) u K)" 
    "t \<notin> kvs_txids K"
  shows
    "t = Tn t0"
  using assms
  by (simp add: kvs_txids_update_kv_write_only split: if_split_asm)



(************)

(*
  more lemmas about view updates

lemma view_of_update:
  assumes 
    "i = length (cord k)"  
    "cord' k = cord k @ [t]"
    "t \<notin> set (cord k)"
    "t \<in> deps"
  shows "i \<in> view_of cord' deps k"
  using assms
  apply (auto simp add: view_of_def)
  apply (rule exI[where x=t])
  apply (auto simp add: nth_append in_set_conv_nth intro: the_equality[symmetric] 
              split: if_split_asm)
  done



lemma DO_NOT_USE_THIS: 
  assumes 
    "i < Suc (length (kvs_of_s gs k))"  
    "\<not> i < length (kvs_of_s gs k)"
    "get_wtxn gs cl \<notin> kvs_txids (kvs_of_s gs)"
    "kv_map k = Some v" 
    (* following two must be derived from invariants *)
    "length (kvs_of_s gs k) = length (cts_order gs k)"
    "get_wtxn gs cl \<notin> set (cts_order gs k)"
  shows 
  "i \<in> view_of (ext_corder (get_wtxn gs cl) kv_map (cts_order gs)) 
               (insert (get_wtxn gs cl) (cl_ctx (cls gs cl))) k"
  using assms 
  by (intro view_of_update) (auto simp add: ext_corder_def)


lemma view_of_update2:
  assumes 
    "i = length (cord k)"  
    "cord' k = cord k @ [t]"
    "t \<in> deps"
    "(t, t') \<in> SO"
    "t' \<notin> set (cord k)"
  shows 
    "i \<in> view_of cord' deps k"
  apply (auto simp add: view_of_def)
  apply (rule exI[where x=t])
  apply (auto simp add: nth_append in_set_conv_nth intro!: the_equality[symmetric] 
              split: if_split_asm)
  oops


lemma IS_THIS_USEFUL_QM:
  "\<lbrakk>kv_map k = None; i < length (corder k); distinct (corder k); corder k ! i \<in> clctx\<rbrakk>
 \<Longrightarrow> i \<in> view_of (ext_corder t kv_map corder) 
                 (insert (get_wtxn gs cl) clctx) k"
  apply (auto simp add: view_of_def ext_corder_def)
  apply (rule exI[where x="corder k ! i"])
  apply auto
  apply (rule the_equality[symmetric], auto dest: nth_distinct_injective)
  done*)


(************)

(*
  lemmas related to commit order (CO)
*)

lemma length_cts_order: "length (cts_order gs k) = length (kvs_of_s gs k)" 
  by (simp add: kvs_of_s_def)

lemma v_writer_txn_to_vers_inverse_on_CO:
  assumes "CO_not_No_Ver gs k" "t \<in> set (cts_order gs k)"
  shows "v_writer (txn_to_vers gs k t) = t"
  using assms
  by (auto simp add: txn_to_vers_def split: ver_state.split)


lemma set_cts_order_incl_kvs_writers:
  assumes "CO_not_No_Ver gs k"
  shows "set (cts_order gs k) \<subseteq> kvs_writers (kvs_of_s gs)"
  using assms
  by (auto simp add: kvs_writers_def vl_writers_def kvs_of_s_def 
                     v_writer_txn_to_vers_inverse_on_CO image_image
           intro!: exI[where x=k])

lemma set_cts_order_incl_kvs_tids:
  assumes "CO_not_No_Ver gs k"
  shows "set (cts_order gs k) \<subseteq> kvs_txids (kvs_of_s gs)"
  using assms
  by (auto simp add: kvs_txids_def dest: set_cts_order_incl_kvs_writers)



(*****)



(******************)
(******************)
(******************)


subsubsection \<open>Write commit guard properties\<close>

lemma write_commit_txn_to_vers_get_wtxn:
  assumes "write_commit cl kv_map cts sn u'' gs gs'" 
  and "kv_map k = Some v" 
  shows "txn_to_vers gs k (get_wtxn gs cl) = new_vers (Tn (Tn_cl sn cl)) v"
  using assms
  by (auto simp add: write_commit_def write_commit_G_def txn_to_vers_def
      dest!: bspec[where x=k] split: ver_state.split)
(*
lemma write_commit_extended_view:    (* NOT USED? *)
  assumes "write_commit cl kv_map cts sn u'' gs gs'" 
  shows "u'' = view_of (cts_order gs) (cl_ctx (cls gs cl))"
  using assms
  by (simp add: write_commit_def)

lemma write_commit_seqn:    (* NOT USED? *)
  assumes "write_commit cl kv_map cts sn u'' gs gs'" 
  shows "sn = cl_sn (cls gs cl)"
  using assms
  by (simp add: write_commit_def write_commit_G_def)

lemmas write_commit_guard_simps = 
  write_commit_txn_to_vers_get_wtxn write_commit_extended_view write_commit_seqn
*)

subsubsection \<open>Write commit update properties\<close>

(*
lemma write_commit_cl_sn_update:
  assumes "write_commit cl kv_map cts sn u'' gs gs'"
  shows "cl_sn (cls gs' cl') = cl_sn (cls gs cl')"
  using assms
  by (auto simp add: write_commit_def) 
*)

lemma write_commit_txn_to_vers_pres:
  assumes "write_commit_s cl kv_map cts sn u'' gs gs'"
  shows "txn_to_vers gs' k = txn_to_vers gs k"
  using assms
  by (auto 3 4 simp add: tps_trans_defs txn_to_vers_def split: ver_state.split)


lemma write_commit_cts_order_update:
  assumes "write_commit_s cl kv_map cts sn u'' gs gs'"
  shows "cts_order gs' k = 
         (if kv_map k = None
          then cts_order gs k
          else insort_key (unique_ts ((wtxn_cts gs) (get_wtxn gs cl \<mapsto> cts))) (get_wtxn gs cl) (cts_order gs k))"
  using assms
  by (auto simp add: tps_trans_defs ext_corder_def)

(* NEEDS THE WELL-ORDERED INVARIANT
lemma write_commit_kvs_of_s:
  assumes "write_commit cl kv_map commit_t sn u'' s s'"
  shows "kvs_of_s s' = update_kv (Tn_cl sn cl)
                          (write_only_fp kv_map)
                          (view_of (cts_order s) (get_view s cl))
                          (kvs_of_s s)"
  using assms
  apply (intro ext)
  apply (auto simp add: kvs_of_s_def update_kv_write_only write_commit_txn_to_vers_pres
                     write_commit_cts_order_update write_commit_txn_to_vers_get_wtxn)


NO LONGER HOLLDS
lemma write_commit_views_of_s:
  assumes "write_commit cl kv_map commit_t sn u'' s s'"
  shows "views_of_s s' = 
         (\<lambda>cl'. view_of (ext_corder (get_wtxn s cl) kv_map (cts_order s))    
                        (if cl' = cl then insert (get_wtxn s cl) (cl_ctx (cls s cl)) 
                         else cl_ctx (cls s cl')))"
  using assms
  by (auto simp add: write_commit_def write_commit_G_def write_commit_U_def views_of_s_def)
*)


lemmas write_commit_update_simps = 
  write_commit_txn_to_vers_pres write_commit_cts_order_update (*write_commit_kvs_of_s
  write_commit_views_of_s*)

(**************************************)


lemma full_view_elem: "i \<in> full_view vl \<longleftrightarrow> i < length vl"
  by (simp add: full_view_def)


lemma length_update_kv_bound:
  "i < length (update_kv t F u K k) \<longleftrightarrow> i < length (K k) \<or> W \<in> dom (F k) \<and> i = length (K k)"
  by (smt (verit) Nat.not_less_eq domIff not_less_iff_gr_or_eq update_kv_length)

(***************************************)


lemma v_writer_set_cts_order_eq:
  assumes "CO_not_No_Ver s k"                   
  shows "v_writer ` set (kvs_of_s s k) = set (cts_order s k)"
  using assms
  apply (auto simp add:  CO_not_No_Ver_def kvs_of_s_defs image_def split: ver_state.split)
   apply (metis (mono_tags, lifting) is_committed.cases version.select_convs(2))
   subgoal for t apply (cases "svr_state (svrs s k) t", simp)
      apply (metis (opaque_lifting) ver_state.distinct(5) ver_state.inject(1) version.select_convs(2))
     subgoal for cts sts lst v rs apply (rule exI[where x="\<lparr>v_value = v, v_writer = t,
          v_readerset = {t. \<exists>rts rlst. (t, rts, rlst) \<in> rs \<and> get_sn t < cl_sn (cls s (get_cl t))}\<rparr>"], simp)
       by (rule bexI[where x=t], auto)
     done
   done

subsubsection \<open>View Wellformedness\<close>

definition FTid_notin_Ctx where
  "FTid_notin_Ctx s cl \<longleftrightarrow> (\<forall>n cl' k. (n > cl_sn (cls s cl) \<longrightarrow> Tn (Tn_cl n cl) \<notin> get_view s cl' k) \<and>
    (cl' \<noteq> cl \<longrightarrow> get_wtxn s cl \<notin> get_view s cl' k))"

lemmas FTid_notin_CtxI = FTid_notin_Ctx_def[THEN iffD2, rule_format]
lemmas FTid_notin_CtxE[elim] = FTid_notin_Ctx_def[THEN iffD1, elim_format, rule_format]

lemma reach_ftid_notin_ctx [simp]: "reach tps_s s \<Longrightarrow> FTid_notin_Ctx s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: FTid_notin_Ctx_def tps_s_defs get_view_def)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RInvoke x1 x2 x3)
    then show ?case sorry
  next
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case sorry
  next
    case (RDone x1 x2 x3 x4)
    then show ?case sorry
  next
    case (WInvoke x1 x2 x3)
    then show ?case sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (WDone x1 x2 x3)
    then show ?case sorry
  next
    case (RegR x1 x2 x3 x4)
    then show ?case sorry
  next
    case (PrepW x1 x2 x3)
    then show ?case sorry
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case sorry
  qed (auto simp add: FTid_notin_Ctx_def tps_trans_defs get_view_def)
qed

(*
lemma write_commit_views_of_s_other_cl_inv:
  assumes "write_commit_s cl kv_map cts sn u s s'"
    and "\<And>k. CO_Distinct s' k"
    and "FTid_notin_Ctx s cl"
    and "cl' \<noteq> cl"
  shows "views_of_s s' cl' = views_of_s s cl'"
proof -
  have dist: "\<And>k. distinct (cts_order s' k)" using assms(2) by auto
  have "\<And>k. (set (cts_order s' k) - set (cts_order s k)) \<inter> (get_view s cl' k) = {}"
    using assms(1, 3, 4) by (auto simp add: tps_trans_defs ext_corder_def set_insort_key)
  then show ?thesis using assms(1, 4) dist view_of_prefix
    apply (auto simp add: tps_trans_all_defs views_of_s_def get_view_def)
qed

lemma reach_kvs_expands [simp]:
  assumes "state_trans s e s'"
    and "\<And>cl. Sqn_Inv_c s cl"
    and "\<And>cl. Sqn_Inv_nc s cl"
    and "invariant_list_kvs s"
  shows "kvs_of_s s \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s kvs_of_s s'"
  using assms kvs_of_s_inv[of s e s']
proof (induction e)
  case (RDone x1 x2 x3 x4)
  then show ?case
    by (auto simp add: tps_trans_defs kvs_expands_def vlist_order_def version_order_def kvs_of_s_defs
        view_atomic_def full_view_def split: ver_state.split)
next
  case (WCommit x1 x2 x3 x4 x5)
  then show ?case using t_is_fresh[of s] write_commit_kvs_of_s[of _ x2]
    apply (auto simp add: tps_trans_defs) by (meson kvs_expands_through_update)
qed auto

definition Views_of_s_Wellformed where
  "Views_of_s_Wellformed s cl \<longleftrightarrow> (view_wellformed (kvs_of_s s) (views_of_s s cl))"

lemmas Views_of_s_WellformedI = Views_of_s_Wellformed_def[THEN iffD2, rule_format]
lemmas Views_of_s_WellformedE[elim] = Views_of_s_Wellformed_def[THEN iffD1, elim_format, rule_format]

lemma reach_views_of_s_wellformed [simp]: "reach tps_s s \<Longrightarrow> Views_of_s_Wellformed s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Views_of_s_Wellformed_def tps_s_defs view_of_def views_of_s_def the_T0
        view_wellformed_defs full_view_def get_view_def kvs_of_s_defs)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s'] reach_kvs_expands[of s e s']
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    hence "view_wellformed (kvs_of_s s') (views_of_s s cl)" apply simp
      using kvs_expanded_view_wellformed by blast
    then show ?case using RDone
      apply (auto simp add: Views_of_s_Wellformed_def) sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Views_of_s_Wellformed_def tps_trans_defs views_of_s_def) sorry
  qed (auto simp add: Views_of_s_Wellformed_def tps_trans_defs views_of_s_def)
qed*)


(**************************************)
(**************************************)

subsection \<open>Refinement Proof\<close>

definition invariant_list where
  "invariant_list s \<equiv> (\<forall>cl k. invariant_list_kvs s \<and> Sqn_Inv_c s cl \<and> Sqn_Inv_nc s cl
    \<and> \<comment> \<open>Views_of_s_Wellformed s cl \<and>\<close> Rtxn_Fp_Inv s cl \<and> CO_Distinct s k
    \<and> T0_in_CO s k \<and> T0_First_in_CO s k \<and> \<comment> \<open>View_Init s cl \<and>\<close> FTid_notin_Ctx s cl)"

lemma invariant_listE [elim]: 
  "\<lbrakk> invariant_list s; 
     \<lbrakk> invariant_list_kvs s; \<And>cl. Sqn_Inv_c s cl; \<And>cl. Sqn_Inv_nc s cl;
       \<And>cl. Rtxn_Fp_Inv s cl; \<And>k. CO_Distinct s k;
       \<And>k. T0_in_CO s k; \<And>k. T0_First_in_CO s k; FTid_notin_Ctx s cl \<rbrakk>
      \<Longrightarrow> P\<rbrakk> 
   \<Longrightarrow> P"
  by (auto simp add: invariant_list_def)

lemma invariant_list_inv [simp, intro]:
  "reach tps_s s \<Longrightarrow> invariant_list s"
  by (auto simp add: invariant_list_def)     \<comment> \<open>should work with just "auto"?\<close>

lemma tps_refines_et_es: "tps_s \<sqsubseteq>\<^sub>med ET_CC.ET_ES"
proof (intro simulate_ES_fun)
  fix gs0 :: "'v global_conf"
  assume p: "init tps_s gs0"
  then show "init ET_CC.ET_ES (sim gs0)"
    by (auto simp add: ET_CC.ET_ES_defs tps_s_defs sim_defs kvs_init_def v_list_init_def 
                       version_init_def get_view_def view_of_def the_T0)
next
  fix gs a and gs' :: "'v global_conf"
  assume p: "tps_s: gs\<midarrow>a\<rightarrow> gs'" and reach_s: "reach tps_s gs" and "reach ET_CC.ET_ES (sim gs)"
  then have I: "invariant_list gs" and reach_s': "reach tps_s gs'" by auto
  show "ET_CC.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  using p I kvs_of_s_inv[of gs a gs']
  proof (induction a)
    case (RDone cl kv_map sn u'')
    then show ?case
    proof -
      {
        assume cmt: \<open>read_done_s cl kv_map sn u'' gs gs'\<close>
        let ?u'' = "view_of (cts_order gs) (get_view gs cl)"
        have \<open>ET_CC.ET_trans_and_fp 
                (kvs_of_s gs, views_of_s gs)
                 (ET cl sn u'' (read_only_fp kv_map))
                (kvs_of_s gs', views_of_s gs')\<close>
        proof (rule ET_CC.ET_trans_rule [where u'="views_of_s gs' cl"])
          show \<open>views_of_s gs cl \<sqsubseteq> u''\<close> using cmt
            by (auto simp add: read_done_s_def read_done_G_s_def read_done_U_def views_of_s_def
                view_of_deps_mono)
        next
          show \<open>ET_CC.canCommit (kvs_of_s gs) u''
                 (read_only_fp kv_map)\<close> using cmt I
            sorry
        next
          show \<open>vShift_MR_RYW (kvs_of_s gs) u'' (kvs_of_s gs') (views_of_s gs' cl)\<close> using cmt I
            apply (auto simp add: read_done_def vShift_MR_RYW_def vShift_MR_def vShift_RYW_def views_of_s_def)
            \<comment> \<open>1. (writer_ver_i, t) \<in> SO \<Longrightarrow> t \<in> K'\K \<Longrightarrow> i \<in> view_of corder (cl_ctx \<union> get_ctx)
                2. writer_ver_i \<in> K'\K \<Longrightarrow> i \<in> view_of corder (cl_ctx \<union> get_ctx)\<close> 
            
            
            sorry
        next
          show \<open>view_wellformed (kvs_of_s gs) u''\<close> using cmt I
            apply (auto simp add: read_done_s_def) sorry
        next
          show \<open>view_wellformed (kvs_of_s gs') (views_of_s gs' cl)\<close> using I sorry (* NEEDS WO INV *)
            (*by (metis Views_of_s_Wellformed_def p reach_s reach_trans reach_views_of_s_wellformed)*)
        next
          show \<open>view_wellformed (kvs_of_s gs) (views_of_s gs cl)\<close> using cmt I sorry (* NEEDS WO INV *)
            (*by (auto simp add: read_done_def read_done_G_def read_done_U_def invariant_list_def)*)
        next
          show \<open>Tn_cl sn cl \<in> next_txids (kvs_of_s gs) cl\<close> using cmt I
            by (auto simp add: read_done_s_def read_done_G_s_def read_done_G_def t_is_fresh)
        next
          show \<open>fp_property (read_only_fp kv_map) (kvs_of_s gs) u''\<close>
            using cmt I
            by (auto simp add: read_done_s_def read_done_G_s_def read_done_G_def fp_property_def
                  view_snapshot_def Rtxn_Fp_Inv_def read_only_fp_def invariant_list_def)
        next
          show \<open>kvs_of_s gs' = update_kv (Tn_cl sn cl)
                (read_only_fp kv_map) u'' (kvs_of_s gs)\<close> using cmt I
            apply (auto simp add: read_done_s_def) sorry
        next
          show \<open>views_of_s gs' = (views_of_s gs)(cl := views_of_s gs' cl)\<close> using cmt
            by (auto simp add: read_done_s_def read_done_G_s_def read_done_G_def read_done_U_def
                views_of_s_def get_view_def)
        qed
      }
      then show ?thesis using RDone
        by (auto simp only: ET_CC.trans_ET_ES_eq tps_trans state_trans.simps sim_def med.simps)
    qed
  next
    case (WCommit cl kv_map cts sn u'')
    then show ?case
    proof -
      {
        assume cmt: \<open>write_commit_s cl kv_map cts sn u'' gs gs'\<close>
        have \<open>ET_CC.ET_trans_and_fp 
                (kvs_of_s gs, views_of_s gs)
                 (ET cl sn u'' (write_only_fp kv_map))
                (kvs_of_s gs', views_of_s gs')\<close>
        proof (rule ET_CC.ET_trans_rule [where u'="views_of_s gs' cl"])
          show \<open>views_of_s gs cl \<sqsubseteq> u''\<close> using cmt
            by (auto simp add: write_commit_s_def write_commit_G_s_def get_view_def 
                views_of_s_def view_of_deps_mono)
        next
          show \<open>ET_CC.canCommit (kvs_of_s gs) u'' (write_only_fp kv_map)\<close> using cmt I
            (*by (simp add: write_commit_def Deps_Closed_def closed_closed' ET_CC.canCommit_def
                          invariant_list_def)*) sorry
        next
         show \<open>vShift_MR_RYW (kvs_of_s gs) u'' (kvs_of_s gs') (views_of_s gs' cl)\<close> 
            using cmt I reach_s 
            apply (intro vShift_MR_RYW_I)
            subgoal  (* MR *)
              using reach_s'[THEN reach_co_distinct] CO_Distinct_def
              apply (auto simp add: write_commit_s_def write_commit_G_s_def write_commit_U_def) sorry
                  (*views_of_s_cls_update intro: view_of_ext_corder_cl_ctx)*) (* Continue Here! *)

            subgoal for t k i (* RYW.1: reflexive case *)
              apply (auto 4 3 simp add: write_commit_update_simps kvs_txids_update_kv_write_only
                                    length_update_kv_bound update_kv_v_writer_old full_view_elem
                          dest: v_writer_in_kvs_txids
                          split: if_split_asm)
              (*by (auto simp add: ext_corder_def length_cts_order intro!: view_of_update
                         dest!: reach_co_not_no_ver set_cts_order_incl_kvs_tids
                         dest: write_commit_seqn v_writer_in_kvs_txids)*) sorry

(**) 
            thm write_commit_def

            thm (*view_of_update*) view_of_mono (*views_of_s_cls_update*) length_cts_order

            thm reach_co_not_no_ver set_cts_order_incl_kvs_tids

(* all-in-one proof unfolding write_commit_def:
 
              apply (frule write_commit_kvs_of_s)
              by (auto simp add: write_commit_def ext_corder_def views_of_s_cls_update v_writer_in_kvs_txids
                                 update_kv_write_only length_update_kv nth_append length_cts_order
                       intro!: view_of_update
                       dest!: reach_co_not_no_ver set_cts_order_incl_kvs_tids
                       split: option.split_asm if_split_asm)
*)

            subgoal for t k i  (* RYW.2: SO case *)
              apply (auto simp add: write_commit_update_simps kvs_txids_update_kv_write_only
                                    length_update_kv_bound update_kv_v_writer_old full_view_elem
                          split: if_split_asm) sorry
              (*subgoal for k' v' sorry

                (* Do we need the closedness property here? *)
                apply (clarsimp simp add: write_commit_def  )*)
(*
\<lbrakk> get_wtxn gs cl \<notin> kvs_txids (kvs_of_s gs); (v_writer (kvs_of_s gs k ! i), get_wtxn gs cl) \<in> SO; 
 i < length (kvs_of_s gs k); 
 sn = cl_sn (cls gs cl); 
 u'' = view_of (cts_order gs) (cl_ctx (cls gs cl));
 cl_state (cls gs cl) = WtxnPrep kv_map;
 \<forall>k\<in>dom kv_map. \<exists>ts v. svr_state (svrs gs k) (get_wtxn gs cl) = Prep ts v \<and> kv_map k = Some v;
 ....
\<rbrakk>
\<Longrightarrow> i \<in> view_of (ext_corder (get_wtxn gs cl) kv_map (cts_order gs)) (cl_ctx (cls gs cl) \<union> dom kv_map \<times> {get_wtxn gs cl}) k 
*)

                thm CO_is_Cmt_Abs_def    (* check this out *)


                sorry
              (*subgoal for k' v' v
                by (metis SO_irreflexive update_kv_v_writer_new write_only_fp_write)
              done
            done*)
        next
          show \<open>view_wellformed (kvs_of_s gs) u''\<close> using cmt I
            apply (auto simp add: write_commit_s_def write_commit_G_s_def view_wellformed_defs) 
            subgoal using T0_First_in_CO_def[of gs] T0_in_CO_def[of gs] CO_Distinct_def[of gs] \<comment> \<open>View_Init_def[of gs cl] \<close>
              apply (auto simp add: view_of_def) apply (rule exI[where x=T0], auto) sorry
            subgoal sorry
            subgoal sorry
            done
        next
          show \<open>view_wellformed (kvs_of_s gs') (views_of_s gs' cl)\<close> sorry (* check *)
            (*by (metis (no_types, lifting) Views_of_s_Wellformed_def p reach_s reach_trans
                      reach_views_of_s_wellformed)*)
        next
          show \<open>view_wellformed (kvs_of_s gs) (views_of_s gs cl)\<close> using cmt I sorry
            (*by (auto simp add: write_commit_s_def write_commit_G_s_def write_commit_G_def
                write_commit_U_def invariant_list_def)*)
        next
          show \<open>Tn_cl sn cl \<in> next_txids (kvs_of_s gs) cl\<close> using cmt I
            by (auto simp add: write_commit_s_def write_commit_G_s_def write_commit_G_def t_is_fresh)
        next
          show \<open>fp_property (write_only_fp kv_map) (kvs_of_s gs) u''\<close>
            by (simp add: fp_property_write_only_fp)
        next
          show \<open>kvs_of_s gs' = update_kv (Tn_cl sn cl) (write_only_fp kv_map) u'' (kvs_of_s gs)\<close> 
            using cmt I sorry
            (*by (simp add: write_commit_def write_commit_G_def write_only_fp_def write_commit_kvs_of_s)*)
        next
          show \<open>views_of_s gs' = (views_of_s gs)(cl := views_of_s gs' cl)\<close> using cmt
            apply (auto simp add: write_commit_s_def) apply (rule ext) sorry
            (*by (smt (verit) cmt fun_upd_apply reach_ftid_notin_ctx reach_co_distinct reach_s reach_s'
                write_commit_views_of_s_other_cl_inv)*)
        qed
      }
      then show ?thesis using WCommit
        by (auto simp only: ET_CC.trans_ET_ES_eq tps_trans state_trans.simps sim_def med.simps)
    qed
  qed (auto simp add: sim_def views_of_s_def get_view_def tps_trans_defs invariant_list_def)
qed

end

