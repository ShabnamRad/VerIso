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

lemma wtxns_domI2: "wtxns t = Commit cts v rs \<Longrightarrow> t \<in> wtxns_dom wtxns"
  by (simp add: wtxns_dom_def)

lemma wtxns_domD: "t \<in> wtxns_dom wtxns \<Longrightarrow> (\<exists>ts v. wtxns t = Prep ts v) \<or> (\<exists>cts v rs. wtxns t = Commit cts v rs)"
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
  "wtxns t = Commit cts v rs \<Longrightarrow> insert t (wtxns_dom wtxns) = wtxns_dom wtxns"
  unfolding wtxns_dom_def by auto


subsection \<open>wtxns_vran lemmas\<close>

lemma wtxns_vranI1: "wtxns t = Commit cts v rs \<Longrightarrow> v \<in> wtxns_vran wtxns"
  apply (simp add: wtxns_vran_def)
  by (metis ver_state.sel(4) wtxns_domI2)

lemma wtxns_vranI2: "wtxns t = Prep ts v \<Longrightarrow> v \<in> wtxns_vran wtxns"
  apply (simp add: wtxns_vran_def)
  by (metis ver_state.sel(3) wtxns_domI1)

lemma wtxns_vran_empty [simp]: "wtxns_vran wtxns_emp = {}"
  by (auto simp: wtxns_vran_def)

lemma wtxns_vran_map_upd [simp]:  "wtxns t = No_Ver \<Longrightarrow>
  wtxns_vran (wtxns (t := Commit cts v rs)) = insert v (wtxns_vran wtxns)"
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

lemma wtxns_rsranI: "wtxns t = Commit cts v rs \<Longrightarrow> rs \<subseteq> wtxns_rsran wtxns"
  apply (simp add: wtxns_rsran_def)
  by (metis (mono_tags, lifting) Sup_upper get_rs.simps(3) mem_Collect_eq wtxns_domI2)

lemma wtxns_rsran_empty [simp]: "wtxns_rsran wtxns_emp = {}"
  by (auto simp: wtxns_rsran_def)

lemma wtxns_rsran_map_upd1 [simp]:  "wtxns t = No_Ver \<Longrightarrow>
  wtxns_rsran (wtxns (t := Prep ts v)) = wtxns_rsran wtxns"
  by (auto simp add: wtxns_rsran_def)

lemma wtxns_rsran_map_upd2 [simp]:  "wtxns t = No_Ver \<Longrightarrow>
  wtxns_rsran (wtxns (t := Commit cts v rs)) = rs \<union> (wtxns_rsran wtxns)"
  by (auto simp add: wtxns_rsran_def)

lemma wtxns_rsran_map_upd3 [simp]:  "is_prepared (wtxns t) \<Longrightarrow>
  wtxns_rsran (wtxns (t := Commit cts v rs)) = rs \<union> (wtxns_rsran wtxns)"
  apply (auto simp add: wtxns_rsran_def)
  by (metis empty_iff get_rs.simps(2) is_prepared.elims(2) wtxns_domIff)

lemma wtxns_rsran_map_upd4 [simp]:  "wtxns t_wr = Commit cts v rs \<Longrightarrow>
  wtxns_rsran (wtxns (t_wr := Commit cts v (insert t rs))) = insert t (wtxns_rsran wtxns)"
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
  "add_to_readerset wtxns t t' t'' = Commit cts v rs \<Longrightarrow> \<exists>rs'. wtxns t'' = Commit cts v rs'"
  apply (simp add: add_to_readerset_def)
  by (cases "wtxns t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_commit_subset:
  "add_to_readerset wtxns t t' t'' = Commit cts v rs \<Longrightarrow> \<exists>rs'. wtxns t'' = Commit cts v rs' \<and> rs' \<subseteq> rs"
  apply (simp add: add_to_readerset_def)
  by (cases "wtxns t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_commit':
  "wtxns t'' = Commit cts v rs' \<Longrightarrow> \<exists>rs. add_to_readerset wtxns t t' t'' = Commit cts v rs"
  apply (simp add: add_to_readerset_def)
  by (cases "wtxns t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_commit'_subset:
  "wtxns t'' = Commit cts v rs' \<Longrightarrow> \<exists>rs. add_to_readerset wtxns t t' t'' = Commit cts v rs \<and> rs' \<subseteq> rs"
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
    (\<forall>t. \<exists>cts v rs. wtxn_state (svrs s k) t \<in> {No_Ver, Commit cts v rs})"
  apply (auto simp add: pending_wtxns_ts_def)
  apply (metis get_rs.elims)
  by (metis ver_state.distinct(1) ver_state.distinct(5))

lemma pending_wtxns_ts_non_empty:
  assumes "wtxn_state (svrs s k) t \<noteq> No_Ver"
    and "\<forall>cts v rs. wtxn_state (svrs s k) t \<noteq> Commit cts v rs"
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

lemma get_view_inv:
  assumes "state_trans s e s'"
    and "\<forall>cl keys. e \<noteq> RInvoke cl keys" and "\<forall>k t v cts. e \<noteq> CommitW k t v cts"
  shows "get_view s' cl = get_view s cl"
  using assms
proof (induction e)
  case (RegR x1 x2 x3 x4)
  then show ?case apply (auto simp add: tps_trans_defs get_view_def)
    apply (rule ext, auto del: disjE split: if_split_asm)
    apply (metis add_to_readerset_commit)
    by (meson add_to_readerset_commit')
next
  case (PrepW x1 x2 x3)
  then show ?case apply (auto simp add: tps_trans_defs get_view_def)
    by (rule ext, auto)
qed (auto simp add: tps_trans_defs get_view_def)

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

lemma get_view_other_cl:
  assumes "gst (cls s' cl') = gst (cls s cl')" and "cl' \<noteq> cl"
    and "\<And>k t. get_cl_wtxn t \<noteq> cl \<longrightarrow> wtxn_state (svrs s' k) t = wtxn_state (svrs s k) t"
  shows "get_view s' cl' = get_view s cl'"
  using assms
  apply (simp add: get_view_def)
  apply (rule ext, rule Collect_eqI, auto) oops


lemma view_of_prefix:
  assumes "\<And>k. prefix (corder k) (corder' k)"
    and "\<And>k. distinct (corder' k)"
    and "\<And>k. u k \<subseteq> set (corder k)"
  shows "view_of corder u = view_of corder' u"
  unfolding view_of_def
proof (rule ext, rule Collect_eqI, rule iffI)
  fix k pos
  assume *: "\<exists>t. pos = (THE i. i < length (corder k) \<and> corder k ! i = t) \<and> t \<in> u k \<and> t \<in> set (corder k)"
  show "\<exists>t. pos = (THE i. i < length (corder' k) \<and> corder' k ! i = t) \<and> t \<in> u k \<and> t \<in> set (corder' k)"
  proof -
    from assms(1) obtain zs where p: "corder k @ zs = corder' k" using prefixE by metis
    from * obtain tid where **: "tid \<in> u k" "tid \<in> set (corder k)"
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
  assume *: "\<exists>t. pos = (THE i. i < length (corder' k) \<and> corder' k ! i = t) \<and> t \<in> u k \<and> t \<in> set (corder' k)"
  show "\<exists>t. pos = (THE i. i < length (corder k) \<and> corder k ! i = t) \<and> t \<in> u k \<and> t \<in> set (corder k)"
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
    case (CommitW x1 x2 x3 x4)
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
  by (auto simp add: Clk_le_Lst_def tps_defs is_curr_wt_def)
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
    case (CommitW x1 x2 x3 x4)
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
  case (CommitW x1 x2 x3 x4)
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
    case (CommitW x1 x2 x3 x4)
    then show ?case using lst_monotonic[of s "CommitW x1 x2 x3 x4" s' x1]
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
    (\<forall>kv_map cts. txn_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map} \<longrightarrow>
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
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (auto simp add: Lst_Lt_Pts_def tps_trans_defs)
      apply (metis emptyE other_prep_t_inv)
      by (metis Finite_Pend_Inv_def Min.coboundedI finite_pending_wtxns_removing other_prep_t_inv
          reach_finitepending)
  qed(auto simp add: Lst_Lt_Pts_def tps_trans_defs)
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
    case (CommitW x1 x2 x3 x4)
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
  by (auto simp add: FTid_Wtxn_Inv_def tps_defs is_curr_wt_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x71 x72 x73 x74)
    then show ?case
      apply (auto simp add: tps_trans_defs is_curr_wt_def FTid_Wtxn_Inv_def)
      by (metis add_to_readerset_no_ver_inv)
  qed (auto simp add: tps_trans_defs is_curr_wt_def FTid_Wtxn_Inv_def)
qed

\<comment> \<open>Next 4 invariants: txn_state + txn_sn \<longrightarrow> wtxn_state\<close>
definition Idle_Read_Inv where
  "Idle_Read_Inv s \<longleftrightarrow> (\<forall>cl k keys kvm. txn_state (cls s cl) \<in> {Idle, RtxnInProg keys kvm}
    \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) = No_Ver)"

lemmas Idle_Read_InvI = Idle_Read_Inv_def[THEN iffD2, rule_format]
lemmas Idle_Read_InvE[elim] = Idle_Read_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_idle_read_inv [simp, dest]: "reach tps s \<Longrightarrow> Idle_Read_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Idle_Read_Inv_def tps_defs is_curr_wt_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Idle_Read_Inv_def tps_trans_defs)
      by (metis add_to_readerset_no_ver_inv)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Idle_Read_Inv_def tps_trans_defs)
      by (metis get_cl_wtxn.simps(2) state_txn.distinct(3) state_txn.distinct(7))
  next
    case (CommitW x1 x2 x3 x4)
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

lemma reach_wr_svr_idle [simp]: "reach tps s \<Longrightarrow> Wr_Svr_Idle s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Wr_Svr_Idle_def tps_defs is_curr_wt_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Wr_Svr_Idle_def tps_trans_defs)
      by (metis add_to_readerset_no_ver_inv)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Wr_Svr_Idle_def tps_trans_defs)
      by (smt (z3) domIff get_cl_wtxn.simps(2) state_txn.distinct(11) state_txn.inject(2))
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (simp add: Wr_Svr_Idle_def tps_trans_defs)
      by force
  qed (auto simp add: Wr_Svr_Idle_def tps_trans_defs, blast?)
qed

definition Prep_Inv where
  "Prep_Inv s \<longleftrightarrow> (\<forall>cl k kvm. \<exists>prep_t v. txn_state (cls s cl) = WtxnPrep kvm
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> wtxn_state (svrs s k) (Tn (get_txn_cl s cl)) \<in> {No_Ver, Prep prep_t v}) \<and>
    (k \<notin> dom kvm \<longrightarrow> wtxn_state (svrs s k) (Tn (get_txn_cl s cl)) = No_Ver))"

lemmas Prep_InvI = Prep_Inv_def[THEN iffD2, rule_format]
lemmas Prep_InvE[elim] = Prep_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_prep_inv [simp]: "reach tps s \<Longrightarrow> Prep_Inv s"
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
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Prep_Inv_def tps_trans_defs)
      by (smt (verit) add_to_readerset_wtxns_dom add_to_readerset_prep_inv wtxns_domIff)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Prep_Inv_def tps_trans_defs)
      by (metis domI get_cl_wtxn.simps(2) state_txn.inject(2))
  next
    case (CommitW x1 x2 x3 x4)
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

lemma reach_commit_inv [simp]: "reach tps s \<Longrightarrow> Commit_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Commit_Inv_def tps_defs is_curr_wt_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Commit_Inv_def tps_trans_defs)
      by (meson Prep_Inv_def is_prepared.elims(2) reach_prep_inv)
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Commit_Inv_def tps_trans_defs)
      by (smt add_to_readerset_commit add_to_readerset_no_ver_inv add_to_readerset_prep_inv
          ver_state.exhaust ver_state.inject(2))
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Commit_Inv_def tps_trans_defs)
      by (smt (verit) fun_upd_other get_cl_wtxn.simps(2) state_txn.distinct(11))
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (simp add: Commit_Inv_def tps_trans_defs)
      using fun_upd_same get_cl_wtxn.simps(2) state_txn.simps(19) ver_state.distinct(1)
        ver_state.simps(10) by force
  qed (auto simp add: Commit_Inv_def tps_trans_defs)
qed

\<comment> \<open>Values of wtxn_state and rtxn_rts for past transaction ids\<close>
definition PTid_Inv where
  "PTid_Inv s cl \<longleftrightarrow> (\<forall>k. \<forall>n < txn_sn (cls s cl).
   (wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver) \<or>
   (rtxn_rts s (Tn_cl n cl) = None \<and> (\<exists>cts v rs. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts v rs)))"

lemmas PTid_InvI = PTid_Inv_def[THEN iffD2, rule_format]
lemmas PTid_InvE[elim] = PTid_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_ptid_inv [simp]: "reach tps s \<Longrightarrow> PTid_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: PTid_Inv_def tps_defs is_curr_wt_def)
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
      subgoal for _ _ n apply (cases "n = txn_sn (cls s x61)")
        apply (metis CFTid_Rtxn_Inv_def eq_imp_le reach_cftid_rtxn_inv)
        by (metis less_SucE)
      subgoal for _ k apply (cases "x62 k = None")
        apply (metis (lifting) Wr_Svr_Idle_def insertCI less_antisym reach_wr_svr_idle)
        by (metis (no_types, lifting) domIff less_antisym)
      done
  next
    case (RegR x71 x72 x73 x74)
    then show ?case
      apply (auto simp add: tps_trans_defs PTid_Inv_def)
      apply (metis add_to_readerset_no_ver_inv)
      by (metis add_to_readerset_commit' add_to_readerset_no_ver_inv)
  qed (auto simp add: tps_trans_defs PTid_Inv_def is_curr_wt_def)
qed

lemma other_sn_idle:  
  assumes "FTid_Wtxn_Inv s cl" and "PTid_Inv s cl"
    and "get_cl_txn t = cl" and "get_sn_txn t \<noteq> txn_sn (cls s cl)"
  shows "\<And>k. \<exists>cts v rs. wtxn_state (svrs s k) (Tn t) \<in> {No_Ver, Commit cts v rs}"
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
      using Idle_Read_Inv_def by blast
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Rtxn_Wtxn_No_Ver_def tps_trans_defs)
      by (meson add_to_readerset_no_ver_inv)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (auto simp add: Rtxn_Wtxn_No_Ver_def tps_trans_defs)
      by (metis CFTid_Rtxn_Inv_def get_cl_wtxn.simps(2) get_sn_wtxn.simps(2) le_refl
          reach_cftid_rtxn_inv is_curr_wt_def)
  qed (auto simp add: Rtxn_Wtxn_No_Ver_def tps_trans_defs)
qed

definition Wtxn_Rtxn_None where
  "Wtxn_Rtxn_None s k \<longleftrightarrow>
    (\<forall>cl n ts v cts rs. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) \<in> {Prep ts v, Commit cts v rs}
       \<longrightarrow> rtxn_rts s (Tn_cl n cl) = None)"

lemmas Wtxn_Rtxn_NoneI = Wtxn_Rtxn_None_def[THEN iffD2, rule_format]
lemmas Wtxn_Rtxn_NoneE[elim] = Wtxn_Rtxn_None_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_rtxn_none [simp]: "reach tps s \<Longrightarrow> Wtxn_Rtxn_None s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Wtxn_Rtxn_None_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case using Idle_Read_Inv_def[of s]
  proof (induction e)
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Wtxn_Rtxn_None_def tps_trans_defs)
      by (meson add_to_readerset_commit_subset add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Wtxn_Rtxn_None_def tps_trans_defs)
      by (metis CFTid_Rtxn_Inv_def get_cl_wtxn.simps(2) get_sn_wtxn.simps(2) le_refl
          reach_cftid_rtxn_inv is_curr_wt_def)
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (simp add: Wtxn_Rtxn_None_def tps_trans_defs)
      by (meson is_prepared.elims(2))
  qed (auto simp add: Wtxn_Rtxn_None_def tps_trans_defs)
qed

definition WtxnCommit_Wtxn_Cts where
  "WtxnCommit_Wtxn_Cts s cl \<longleftrightarrow> (\<forall>cts kv_map. txn_state (cls s cl) = WtxnCommit cts kv_map
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
    (\<forall>t cts v rs ts kv_map. (wtxn_state (svrs s k) t = Commit cts v rs) \<or> 
      (wtxn_state (svrs s k) t = Prep ts v \<and> is_curr_wt s t \<and>
       txn_state (cls s (get_cl_wtxn t)) = WtxnCommit cts kv_map)
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
    then show ?case apply (auto simp add: Wtxn_State_Cts_def tps_trans_defs is_curr_wt_def domI)
    apply (metis (no_types, lifting) Prep_Inv_def is_prepared.simps(3) reach_prep_inv ver_state.distinct(3))
    subgoal for t apply (cases t)
      apply (metis Init_Ver_Inv_def reach_init_ver_inv ver_state.distinct(5))
      by (metis get_cl_wtxn.simps(2) get_sn_wtxn.simps(2) txid0.exhaust).
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Wtxn_State_Cts_def tps_trans_defs is_curr_wt_def domI)
      by (meson add_to_readerset_commit add_to_readerset_prep_inv)
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (simp add: Wtxn_State_Cts_def tps_trans_defs is_curr_wt_def domI)
      by (meson domI is_prepared.elims(2))
  qed (auto simp add: Wtxn_State_Cts_def tps_trans_defs is_curr_wt_def domI)
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
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: FTid_notin_rs_def tps_trans_defs is_curr_t_def) sorry
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: FTid_notin_rs_def tps_trans_defs)
      by (metis)
  next
    case (CommitW x1 x2 x3 x4)
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
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs is_curr_wt_def)
      by (metis get_cl_wtxn.simps(2) get_sn_wtxn.simps(2) nat_neq_iff)
  next
    case (CommitW x91 x92)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (metis get_cl_wtxn.simps(2) get_sn_wtxn.simps(2) order_less_irrefl is_curr_wt_def)
  qed (auto simp add: FTid_not_wr_def tps_trans_defs)
qed

definition Fresh_rd_notin_rs where
  "Fresh_rd_notin_rs s cl k \<longleftrightarrow> (\<forall>t cts v rs. txn_state (cls s cl) = Idle \<and>
    wtxn_state (svrs s k) t = Commit cts v rs \<longrightarrow> get_txn_cl s cl \<notin> rs)"

lemmas Fresh_rd_notin_rsI = Fresh_rd_notin_rs_def[THEN iffD2, rule_format]
lemmas Fresh_rd_notin_rsE[elim] = Fresh_rd_notin_rs_def[THEN iffD1, elim_format, rule_format]

lemma reach_fresh_rd_notin_rs [simp]: "reach tps s \<Longrightarrow> Fresh_rd_notin_rs s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  apply (auto simp add: Fresh_rd_notin_rs_def tps_defs)
    by (metis ex_in_conv get_rs.simps(3) ver_state.distinct(3))
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RDone x31 x32 x33 x34)
    then show ?case by (simp add: Fresh_rd_notin_rs_def tps_trans_defs, blast)
  next
    case (WDone x61 x62)
    then show ?case by (simp add: Fresh_rd_notin_rs_def tps_trans_defs, blast)
  next
    case (RegR x71 x72 x73 x74)
    then show ?case apply (simp add: Fresh_rd_notin_rs_def tps_trans_defs is_curr_wt_def)
      apply (cases "k = x71"; cases "cl = get_cl_txn x72"; auto) sorry
  next
    case (PrepW x81 x82 x83)
    then show ?case sorry
  next
    case (CommitW x91 x92)
    then show ?case sorry
  qed (auto simp add: Fresh_rd_notin_rs_def tps_trans_defs)
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

abbreviation invariant_list_kvs where
  "invariant_list_kvs s \<equiv> \<forall>cl k. FTid_Wtxn_Inv s cl \<and> PTid_Inv s cl \<and> Kvs_Not_Emp s \<and>
   \<comment> \<open> KVS_Not_All_Pending s k \<and>\<close> Fresh_rd_notin_rs s cl k"

abbreviation not_committing_ev where
  "not_committing_ev e \<equiv> \<forall>cl kv_map cts sn u. e \<noteq> RDone cl kv_map sn u \<and> e \<noteq> WCommit cl kv_map cts sn u"

lemma kvs_of_s_inv:
  assumes "state_trans s e s'"
    and "invariant_list_kvs s"
    and "not_committing_ev e"
  shows "kvs_of_s s' = kvs_of_s s"
  using assms
proof (induction e)
  case (WDone x1 x2)
  then show ?case apply (auto simp add: kvs_of_s_def tps_trans_defs )
    apply (rule ext) apply (auto intro: list.map_cong0 split: ver_state.split) sorry
next
  case (RegR x1 x2 x3 x4)
  then show ?case sorry
next
  case (PrepW x1 x2 x3)
  then show ?case sorry
next
  case (CommitW x1 x2 x3 x4)
  then show ?case sorry
qed (auto simp add: kvs_of_s_def tps_trans_defs split: ver_state.split)

definition Sqn_Inv_nc where
  "Sqn_Inv_nc s cl \<longleftrightarrow> (\<forall>cts kvm.
    (txn_state (cls s cl) \<noteq> WtxnCommit cts kvm \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m < txn_sn (cls s cl))))"

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
    then show ?case apply (auto simp add: Sqn_Inv_nc_def)
      apply (metis (full_types) gt_ex state_txn.inject(3)) sorry
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
  "Sqn_Inv_c s cl \<longleftrightarrow> (\<forall>cts kvm.
    (txn_state (cls s cl) = WtxnCommit cts kvm \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m \<le> txn_sn (cls s cl))))"

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
    and "txn_state (cls s cl) \<in> {WtxnPrep kv_map, RtxnInProg keys kv_map}"
  shows "get_txn_cl s cl \<in> next_txids (kvs_of_s s) cl"
  using assms by (auto simp add: kvs_of_s_def next_txids_def)

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
      by (metis Idle_Read_Inv_def insert_iff reach_idle_read_inv ver_state.distinct(1))
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
  "Gst_Lt_Cts s cl \<longleftrightarrow> (\<forall>k cts v rs. 
      wtxn_state (svrs s k) (get_wtxn_cl s cl) = Commit cts v rs \<longrightarrow> gst (cls s cl) < cts)"
                                                           
lemmas Gst_Lt_CtsI = Gst_Lt_Cts_def[THEN iffD2, rule_format]
lemmas Gst_Lt_CtsE[elim] = Gst_Lt_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_Gst_Lt_Cts [simp]: "reach tps s \<Longrightarrow> Gst_Lt_Cts s cl"
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
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (simp add: Gst_Lt_Cts_def tps_trans_defs) sorry
  qed (auto simp add: Gst_Lt_Cts_def tps_trans_defs)
qed


definition Gst_lt_Cts where
  "Gst_lt_Cts s cl \<longleftrightarrow> (\<forall>cl' cts kv_map. txn_state (cls s cl') = WtxnCommit cts kv_map
    \<longrightarrow> gst (cls s cl) < cts)"
                                                           
lemmas Gst_lt_CtsI = Gst_lt_Cts_def[THEN iffD2, rule_format]
lemmas Gst_lt_CtsE[elim] = Gst_lt_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_gst_lt_cts [simp]: "reach tps s \<Longrightarrow> Gst_lt_Cts s cl"
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


subsection \<open>Invariants about commit order\<close>

definition Commit_Order_Tid where
  "Commit_Order_Tid s cl \<longleftrightarrow> (case txn_state (cls s cl) of
    WtxnCommit cts kv_map \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (commit_order s k) \<longrightarrow> n \<le> txn_sn (cls s cl))
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
    (\<exists>cts v rs. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts v rs) \<or> 
    ((\<exists>ts v. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Prep ts v) \<and> 
     (\<exists>cts kv_map. txn_state (cls s cl) = WtxnCommit cts kv_map \<and> 
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
    case (CommitW x1 x2 x3 x4)
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
    (\<exists>cts v rs. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts v rs) \<or> 
    ((\<exists>ts v. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Prep ts v) \<and> 
     (\<exists>cts kv_map. txn_state (cls s cl) = WtxnCommit cts kv_map \<and> txn_sn (cls s cl) = n)) \<longrightarrow>
    Tn (Tn_cl n cl) \<in> set (commit_order s k))"

lemmas Commit_Order_CompleteI = Commit_Order_Complete_def[THEN iffD2, rule_format]
lemmas Commit_Order_CompleteE[elim] = Commit_Order_Complete_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_complete [simp]: "reach tps s \<Longrightarrow> Commit_Order_Complete s k"
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
    case (RegR x1 x2 x3 x4)
    then show ?case apply (simp add: Commit_Order_Complete_def tps_trans_defs)
      by (smt (verit) add_to_readerset_commit add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Commit_Order_Complete_def tps_trans_defs)
      by (metis get_cl_wtxn.simps(2) state_txn.distinct(11))
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (auto simp add: Commit_Order_Complete_def tps_trans_defs)
      by (metis (no_types, opaque_lifting) get_cl_wtxn.simps(2) get_sn_wtxn.simps(2) 
          is_prepared.elims(2) is_curr_wt_def)
  qed (simp_all add: Commit_Order_Complete_def tps_trans_defs)
qed

definition Commit_Order_Superset_View where
  "Commit_Order_Superset_View s k \<longleftrightarrow> (\<forall>cl. (cl_view (cls s cl)) k \<subseteq> set (commit_order s k))"

lemmas Commit_Order_Superset_ViewI = Commit_Order_Superset_View_def[THEN iffD2, rule_format]
lemmas Commit_Order_Superset_ViewE[elim] = Commit_Order_Superset_View_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_superset_view [simp]: "reach tps s \<Longrightarrow> Commit_Order_Superset_View s k"
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

lemma reach_commit_order_superset_get_view [simp]:
  "reach tps s \<Longrightarrow> Commit_Order_Superset_Get_View s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Commit_Order_Superset_Get_View_def tps_defs get_view_def split:if_split_asm)
next
  case (reach_trans s e s')
  then show ?case using get_view_inv[of s e s']
  proof (induction e)
    case (CommitW x1 x2 x3 x4)
    then show ?case
      apply (simp add: Commit_Order_Superset_Get_View_def tps_trans_defs get_view_def)
      apply (rule, rule, rule) subgoal for cl x apply (cases "x = x2"; auto)
        using Gst_lt_Cts_def linorder_not_less reach_gst_lt_cts apply blast
          apply (cases x, blast)
        subgoal for kv_map y x2a apply (cases x2a)
          using Commit_Order_Complete_def[of s x1]
          by (metis (no_types, lifting) get_cl_wtxn.simps(2) get_sn_wtxn.simps(2)
              is_prepared.elims(2) reach_commit_order_complete is_curr_wt_def)
        by blast+.
  qed (simp_all add: Commit_Order_Superset_Get_View_def tps_trans_defs get_view_def, (blast+)?)
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
      apply (cases "x2 k", auto) sorry \<comment> \<open>Continue here!\<close>
  qed (auto simp add: Commit_Order_Sorted_def tps_trans_defs)
qed

definition Commit_Order_len where
  "Commit_Order_len s k \<longleftrightarrow> length (commit_order s k) = length (kvs_of_s s k)"

lemmas Commit_Order_lenI = Commit_Order_len_def[THEN iffD2, rule_format]
lemmas Commit_Order_lenE[elim] = Commit_Order_len_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_order_len [simp]: "reach tps s \<Longrightarrow> Commit_Order_len s cl"
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
          reach_kvs_not_emp reach_ftid_wtxn_inv reach_ptid_inv tps_trans)
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
    case (WDone x1 x2)
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
  qed simp
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
     subgoal for cts v rs apply (rule exI[where x="\<lparr>v_value = v, v_writer = t,
          v_readerset = {t \<in> rs. get_sn_txn t < txn_sn (cls s (get_cl_txn t))}\<rparr>"], simp)
       by (rule bexI[where x=t], auto)
     done.

lemma reach_kvs_expands [simp]:
  assumes "state_trans s e s'" and "\<And>cl. Sqn_Inv_c s cl" and "\<And>cl. Sqn_Inv_nc s cl"
    and "\<And>cl. PTid_Inv s cl" and "\<And>cl. FTid_Wtxn_Inv s cl"
    and "Kvs_Not_Emp s" and "\<And>cl k. Fresh_rd_notin_rs s cl k"
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


definition Get_view_Wellformed where
  "Get_view_Wellformed s cl \<longleftrightarrow> (view_wellformed (kvs_of_s s) (view_of (commit_order s) (get_view s cl)))"

lemmas Get_view_WellformedI = Get_view_Wellformed_def[THEN iffD2, rule_format]
lemmas Get_view_WellformedE[elim] = Get_view_Wellformed_def[THEN iffD1, elim_format, rule_format]

lemma reach_get_view_wellformed [simp]: "reach tps s \<Longrightarrow> Get_view_Wellformed s cl"
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
    case (CommitW x1 x2 x3 x4)
    then show ?case sorry
  qed (auto simp add: Get_view_Wellformed_def tps_trans_defs)
qed

lemma visTx_in_kvs_of_s_writers[simp]:
  "reach tps s \<Longrightarrow>
   visTx (kvs_of_s s) ((view_of (commit_order s) (get_view s cl))) \<subseteq> kvs_writers (kvs_of_s s)"
  apply (rule visTx_in_kvs_writers, rule view_wellformed_range)
  using reach_get_view_wellformed by blast


subsection \<open>Timestamp relations\<close>

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
    case (CommitW x1 x2 x3 x4)
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
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: Disjoint_RW'_def tps_trans_defs txid_defs kvs_of_s_def) sorry
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

lemmas canCommit_defs = ET_CC.canCommit_def closed_def R_CC_def R_onK_def

lemma the_T0: "(THE i. i = 0 \<and> [T0] ! i = T0) = 0" by auto

lemma visTx_visTx': "visTx (kvs_of_s s) (view_of (commit_order s) u) = visTx' u"
  apply (simp add: view_of_def visTx_def visTx'_def) sorry

lemma closed_closed': "closed (kvs_of_s s) (view_of (commit_order s) u) r = closed' (kvs_of_s s) u r"
  by (simp add: closed_def closed'_def visTx_visTx')

lemma visTx'_subset_writers: "visTx' (get_view s cl) \<subseteq> kvs_writers (kvs_of_s s)" sorry

lemma "kvs_writers (kvs_of_s s) \<subseteq> (\<Union>k. wtxns_dom (wtxn_state (svrs s k)))"
  oops

lemma "kvs_readers (kvs_of_s s) \<subseteq> (\<Union>k. wtxns_rsran (wtxn_state (svrs s k)))"
  oops

definition RO_le_gst :: "'v state \<Rightarrow> cl_id \<Rightarrow> txid set" where
  "RO_le_gst s cl \<equiv> {t \<in> read_only_Txs (kvs_of_s s). \<exists>t'. t = Tn t' \<and> the (rtxn_rts s t') \<le> gst (cls s cl)}"

definition Get_view_Closed where
  "Get_view_Closed s cl \<longleftrightarrow> (\<forall>F. ET_CC.canCommit (kvs_of_s s) (view_of (commit_order s) (get_view s cl)) F)"

lemmas Get_view_ClosedI = Get_view_Closed_def[THEN iffD2, rule_format]
lemmas Get_view_ClosedE[elim] = Get_view_Closed_def[THEN iffD1, elim_format, rule_format]

lemma reach_get_view_closed [simp]: "reach tps s \<Longrightarrow> Get_view_Closed s cl"
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
      and "x' \<in> visTx (kvs_of_s s) (view_of (commit_order s) (get_view s' cl)) \<union> RO_le_gst s x1"
      and "txn_state (cls s x1) = Idle"
      then have "x \<in> visTx (kvs_of_s s) (view_of (commit_order s) (get_view s' cl)) \<union> RO_le_gst s x1"
        apply (induction rule: rtrancl.induct, simp)
        apply auto
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
    then show ?case apply (auto simp add: Get_view_Closed_def canCommit_defs)
      apply (metis DiffD2 read_only_Txs_def subsetD visTx'_subset_writers visTx_visTx')
      using RInvoke by (auto simp add: tps_trans_defs RO_le_gst_def)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case sorry
  qed (auto simp add: Get_view_Closed_def tps_trans_defs)
qed


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
    case (CommitW x1 x2 x3 x4)
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
  case (WDone x1 x2)
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

definition Views_of_s_Wellformed where
  "Views_of_s_Wellformed s cl \<longleftrightarrow> (view_wellformed (kvs_of_s s) (views_of_s s cl))"

lemmas Views_of_s_WellformedI = Views_of_s_Wellformed_def[THEN iffD2, rule_format]
lemmas Views_of_s_WellformedE[elim] = Views_of_s_Wellformed_def[THEN iffD1, elim_format, rule_format]

lemma reach_views_of_s_wellformed [simp]: "reach tps s \<Longrightarrow> Views_of_s_Wellformed s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Views_of_s_Wellformed_def tps_defs view_of_def views_of_s_def the_T0
        view_txid_init_def view_wellformed_defs full_view_def kvs_of_s_def)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s'] views_of_s_inv[of s e s']
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: Views_of_s_Wellformed_def tps_trans_defs
          view_wellformed_defs views_of_s_def view_of_def full_view_def) sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case sorry
  qed (auto simp add: Views_of_s_Wellformed_def)
qed

subsection \<open>View Shift\<close>

lemma get_view_grows:
  assumes "state_trans s e s'" and "Gst_le_Min_Lst_map s cl"
  shows "get_view s cl \<sqsubseteq> get_view s' cl"
  using assms get_view_inv[of s e s']
  by (induction e) (auto simp add: tps_trans_defs view_order_def get_view_def)

definition Cl_View_WtxnCommit where
  "Cl_View_WtxnCommit s cl \<longleftrightarrow>
    (\<forall>cts kv_map k. txn_state (cls s cl) = WtxnCommit cts kv_map \<longrightarrow>
      cl_view (cls s cl) k = (case kv_map k of None \<Rightarrow> get_view s cl k |
        Some _ \<Rightarrow> insert (get_wtxn_cl s cl) (get_view s cl k)))"

lemmas Cl_View_WtxnCommitI = Cl_View_WtxnCommit_def[THEN iffD2, rule_format]
lemmas Cl_View_WtxnCommitE[elim] = Cl_View_WtxnCommit_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_view_wtxncommit [simp]: "reach tps s \<Longrightarrow> Cl_View_WtxnCommit s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Cl_View_WtxnCommit_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case using get_view_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case sorry
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case sorry
  qed (auto simp add: Cl_View_WtxnCommit_def tps_trans_defs split: option.split)
qed

definition Cl_Sub_Get_View where
  "Cl_Sub_Get_View s cl \<longleftrightarrow>
    (\<forall>keys kv_map. txn_state (cls s cl) \<in> {Idle, RtxnInProg keys kv_map, WtxnPrep kv_map} \<longrightarrow>
      cl_view (cls s cl) \<sqsubseteq> get_view s cl)"

lemmas Cl_Sub_Get_ViewI = Cl_Sub_Get_View_def[THEN iffD2, rule_format]
lemmas Cl_Sub_Get_ViewE[elim] = Cl_Sub_Get_View_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_sub_get_view [simp]: "reach tps s \<Longrightarrow> Cl_Sub_Get_View s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Cl_Sub_Get_View_def tps_defs version_order_def view_txid_init_def get_view_def)
next
  case (reach_trans s e s')
  then show ?case using get_view_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: Cl_Sub_Get_View_def tps_trans_defs)
      by (metis get_view_grows reach_gst_le_min_lst_map reach_trans.hyps(1) tps_trans
          view_order_transitive)
  next
    case (WDone x1 x2)
    then show ?case apply (auto simp add: Cl_Sub_Get_View_def tps_trans_defs get_view_def view_order_def) sorry
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (auto simp add: Cl_Sub_Get_View_def tps_trans_defs) sorry
  qed (auto simp add: Cl_Sub_Get_View_def tps_trans_defs)
qed

lemma read_commit_added_txid:
  assumes "read_done cl kv_map sn u s s'"
    and "Tn (Tn_cl sn' cl) \<in> (kvs_txids (kvs_of_s s') - kvs_txids (kvs_of_s s))"
  shows "sn' = sn"
  using assms
  apply (auto simp add: read_done_def kvs_of_s_def txid_defs split: ver_state.split) sorry

subsection \<open>View Grows\<close>

lemma view_grows_view_of: "a \<sqsubseteq> b \<Longrightarrow> view_of corder a \<sqsubseteq> view_of corder b"
  apply (simp add: view_of_def)
  by (smt (verit) Collect_mono_iff insert_subset mk_disjoint_insert view_order_def)

definition View_Grows where
  "View_Grows s cl \<longleftrightarrow>
    (\<forall>keys kv_map. txn_state (cls s cl) \<in> {Idle, RtxnInProg keys kv_map, WtxnPrep kv_map} \<longrightarrow>
      views_of_s s cl \<sqsubseteq> view_of (commit_order s) (get_view s cl))"

lemmas View_GrowsI = View_Grows_def[THEN iffD2, rule_format]
lemmas View_GrowsE[elim] = View_Grows_def[THEN iffD1, elim_format, rule_format]

lemma reach_view_grows [simp]: "reach tps s \<Longrightarrow> View_Grows s cl"
  apply (simp add: View_Grows_def views_of_s_def)
  by (metis view_grows_view_of Cl_Sub_Get_View_def insertI1 insertI2 reach_cl_sub_get_view)

section \<open>Fp Property\<close>

\<comment> \<open>Fingerprint content invariant and Lemmas for proving the fp_property\<close>

definition RegR_Fp_Inv where
  "RegR_Fp_Inv s k \<longleftrightarrow> (\<forall>t keys kv_map cts v rs.
    txn_state (cls s (get_cl_txn t)) = RtxnInProg keys kv_map \<and> k \<in> keys \<and> kv_map k = None \<and>
    wtxn_state (svrs s k) (read_at (wtxn_state (svrs s k)) (gst (cls s (get_cl_txn t))) (get_cl_txn t))
       = Commit cts v rs \<longrightarrow>
    v = v_value (last_version (kvs_of_s s k) (view_of (commit_order s) (get_view s (get_cl_txn t)) k)))"

lemmas RegR_Fp_InvI = RegR_Fp_Inv_def[THEN iffD2, rule_format]
lemmas RegR_Fp_InvE[elim] = RegR_Fp_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_reg_r_fp [simp]: "reach tps s \<Longrightarrow> RegR_Fp_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: RegR_Fp_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s'] get_view_inv[of s e s']
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
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (RegR x1 x2 x3 x4)
    then show ?case sorry
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs) sorry
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case sorry
  qed (auto simp add: RegR_Fp_Inv_def tps_trans_defs)
qed

definition Rtxn_Fp_Inv where
  "Rtxn_Fp_Inv s cl \<longleftrightarrow> (\<forall>keys kv_map k v. txn_state (cls s cl) = RtxnInProg keys kv_map \<and>
    kv_map k = Some v \<longrightarrow>
      v = v_value (last_version (kvs_of_s s k) (view_of (commit_order s) (get_view s cl) k)))"

lemmas Rtxn_Fp_InvI = Rtxn_Fp_Inv_def[THEN iffD2, rule_format]
lemmas Rtxn_Fp_InvE[elim] = Rtxn_Fp_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_fp [simp]: "reach tps s \<Longrightarrow> Rtxn_Fp_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rtxn_Fp_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s'] get_view_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case sorry
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (auto simp add: Rtxn_Fp_Inv_def read_def split: if_split_asm) sorry
  next
    case (RDone x1 x2 x3 x4)
    then show ?case sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case sorry
  qed (auto simp add: Rtxn_Fp_Inv_def tps_trans_defs)
qed
  

abbreviation invariant_list where
  "invariant_list s \<equiv> (\<forall>cl. invariant_list_kvs s \<and> Sqn_Inv_c s cl \<and> Sqn_Inv_nc s cl \<and> Get_view_Closed s cl
    \<and>  Get_view_Wellformed s cl \<and> Views_of_s_Wellformed s cl \<and> View_Grows s cl \<and> Rtxn_Fp_Inv s cl)"


section \<open>Refinement Proof\<close>

lemma tps_refines_et_es: "tps \<sqsubseteq>\<^sub>med ET_CC.ET_ES"
proof (intro simulate_ES_fun)
  fix gs0 :: "'v state"
  assume p: "init tps gs0"
  then show "init ET_CC.ET_ES (sim gs0)"
    by (auto simp add: ET_CC.ET_ES_defs tps_defs sim_defs kvs_init_def v_list_init_def version_init_def
        view_txid_init_def view_of_def the_T0)
next
  fix gs a and gs' :: "'v state"
  assume p: "tps: gs\<midarrow>a\<rightarrow> gs'" and reach_s: "reach tps gs" and "reach ET_CC.ET_ES (sim gs)"
  hence inv: "invariant_list gs" by simp
  then show "ET_CC.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  using p kvs_of_s_inv[of gs a gs'] views_of_s_inv[of gs a gs'] get_view_inv[of gs a gs'] (*needed?*)
  proof (induction a)
    case (RDone cl kv_map sn u'')
    then show ?case
    apply (auto simp add: read_done_def sim_def intro!: exI [where x="views_of_s gs' cl"])
    subgoal apply (auto simp add: ET_CC.ET_cl_txn_def t_is_fresh KvsOfS_Not_Emp_def Get_view_Closed_def)
      subgoal by (metis Views_of_s_Wellformed_def p reach_s reach_trans reach_views_of_s_wellformed)                   
      subgoal apply (auto simp add: vShift_MR_RYW_def vShift_MR_def vShift_RYW_def views_of_s_def)
        \<comment> \<open>1. view_of corder get_view \<sqsubseteq> view_of corder' cl_view'
            2. (writer_ver_i, t) \<in> SO \<Longrightarrow> t \<in> K'\K \<Longrightarrow> i \<in> view_of corder' cl_view'
            3. writer_ver_i \<in> K'\K \<Longrightarrow> i \<in> view_of corder' cl_view'\<close>
        sorry
      subgoal using View_Grows_def insert_compr mem_Collect_eq by blast
      subgoal sorry
      done
      subgoal by (rule ext, simp add: read_done_def views_of_s_def read_done_s'_def)
      subgoal apply (auto simp add: fp_property_def view_snapshot_def) by blast.
  next
    case (WCommit cl kv_map cts sn u'')
    then show ?case
    apply (auto simp add: write_commit_def sim_def fp_property_def intro!: exI [where x="views_of_s gs' cl"])
      subgoal apply (auto simp add: ET_CC.ET_cl_txn_def t_is_fresh Get_view_Closed_def)
        subgoal by (metis Views_of_s_Wellformed_def p reach_s reach_trans reach_views_of_s_wellformed)
        subgoal sorry
        subgoal using View_Grows_def insert_compr mem_Collect_eq by blast
        subgoal sorry
        done
    subgoal apply (rule ext)
      subgoal for cl' apply (cases "cl' = cl"; simp)
      using write_commit_views_of_s_other_cl_inv [where s=gs and s'=gs' and cl=cl and cl'=cl']
      by (metis WCommit.prems(2) state_trans.simps(5) tps_trans).
    done
  qed (auto simp add: sim_def)
qed

end
