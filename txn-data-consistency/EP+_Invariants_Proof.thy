section \<open>Eiger Port Plus Protocol (not sorted) - Proofs and lemmas\<close>

theory "EP+_Invariants_Proof"
  imports "EP+"
begin

subsection \<open>wtxns lemmas\<close>

subsubsection \<open>wtxns_dom lemmas\<close>

lemma wtxns_domI1: "wtxns t = Prep pd ts v \<Longrightarrow> t \<in> wtxns_dom wtxns"
  by (simp add: wtxns_dom_def)

lemma wtxns_domI2: "wtxns t = Commit cts sts lst v rs \<Longrightarrow> t \<in> wtxns_dom wtxns"
  by (simp add: wtxns_dom_def)

lemma wtxns_domD: "t \<in> wtxns_dom wtxns \<Longrightarrow>
  (\<exists>pd ts v. wtxns t = Prep pd ts v) \<or> (\<exists>cts sts lst v rs. wtxns t = Commit cts sts lst v rs)"
  by (cases "wtxns t") (auto simp add: wtxns_dom_def)

lemma wtxns_domIff [iff, simp del, code_unfold]:
  "t \<in> wtxns_dom wtxns \<longleftrightarrow> wtxns t \<noteq> No_Ver \<and> wtxns t \<noteq> Reg"
  by (simp add: wtxns_dom_def)

lemma wtxns_dom_fun_upd [simp]:
  "wtxns_dom(wtxns(t := x)) = (if x \<in> {No_Ver, Reg} then wtxns_dom wtxns - {t} else insert t (wtxns_dom wtxns))"
  by (auto simp: wtxns_dom_def)

lemma wtxns_dom_if:
  "wtxns_dom (\<lambda>x. if P x then f x else g x) = wtxns_dom f \<inter> {x. P x} \<union> wtxns_dom g \<inter> {x. \<not> P x}"
  by (auto split: if_splits)

lemma wtxns_dom_minus:
  "wtxns t = No_Ver \<Longrightarrow> wtxns_dom wtxns - insert t A = wtxns_dom wtxns - A"
  unfolding wtxns_dom_def by simp

lemma insert_prep_wtxns_dom:
  "wtxns t = Prep pd ts v \<Longrightarrow> insert t (wtxns_dom wtxns) = wtxns_dom wtxns"
  unfolding wtxns_dom_def by auto

lemma insert_commit_wtxns_dom:
  "wtxns t = Commit cts sts lst v rs \<Longrightarrow> insert t (wtxns_dom wtxns) = wtxns_dom wtxns"
  unfolding wtxns_dom_def by auto


subsubsection \<open>wtxns_vran lemmas\<close>

lemma wtxns_vranI1: "wtxns t = Commit cts sts lst v rs \<Longrightarrow> v \<in> wtxns_vran wtxns"
  apply (simp add: wtxns_vran_def)
  by (metis ver_state.sel(4) wtxns_domI2)

lemma wtxns_vranI2: "wtxns t = Prep pd ts v \<Longrightarrow> v \<in> wtxns_vran wtxns"
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

lemma wtxns_rsranI: "wtxns t = Commit cts sts lst v rs \<Longrightarrow> dom rs \<subseteq> wtxns_rsran wtxns"
  apply (simp add: wtxns_rsran_def)
  by (metis (mono_tags, lifting) Sup_upper get_rs.simps(2) mem_Collect_eq wtxns_domI2)

lemma wtxns_rsran_empty [simp]: "wtxns_rsran wtxns_emp = {}"
  by (auto simp: wtxns_rsran_def)

lemma wtxns_rsran_map_upd1 [simp]:  "wtxns t = No_Ver \<Longrightarrow>
  wtxns_rsran (wtxns (t := Prep pd ts v)) = wtxns_rsran wtxns"
  apply (auto simp add: wtxns_rsran_def)
  by (metis domI wtxns_domIff)

lemma wtxns_rsran_map_upd2 [simp]:  "wtxns t = No_Ver \<Longrightarrow>
  wtxns_rsran (wtxns (t := Commit cts sts lst v rs)) = dom rs \<union> (wtxns_rsran wtxns)"
  apply (auto simp add: wtxns_rsran_def)
  by (metis domI wtxns_domIff)

lemma wtxns_rsran_map_upd3 [simp]:  "is_prepared (wtxns t) \<Longrightarrow>
  wtxns_rsran (wtxns (t := Commit cts sts lst v rs)) = dom rs \<union> (wtxns_rsran wtxns)"
  apply (auto simp add: wtxns_rsran_def)
  by (metis get_rs.simps(1) is_prepared.elims(2) wtxns_domIff domI option.discI)

lemma wtxns_rsran_map_upd4 [simp]:  "wtxns t_wr = Commit cts sts lst v rs \<Longrightarrow>
  wtxns_rsran (wtxns (t_wr := Commit cts sts lst v (rs (t \<mapsto> (x, y))))) = insert t (wtxns_rsran wtxns)"
  apply (auto simp add: wtxns_rsran_def)
  apply (metis domI get_rs.simps(2) wtxns_domI2)
  by (metis domI get_rs.simps(2) insertI2 wtxns_domIff)


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
  "wtxns (Tn t) = No_Ver \<Longrightarrow> wtxns_dom (add_to_readerset wtxns t rts rlst t') = wtxns_dom wtxns"
  by (auto simp add: add_to_readerset_def split: ver_state.split)

lemma wtxns_rsran_inv:
  "wtxns (Tn t) = No_Ver \<Longrightarrow> wtxns_rsran (wtxns (Tn t := Reg)) = wtxns_rsran (wtxns)"
  apply (auto simp add: wtxns_rsran_def)
  by (metis domI wtxns_domIff)

lemma add_to_readerset_wtxns_rsran:
  assumes "is_committed (wtxns t_wr)" \<comment> \<open>later use read_at_is_committed to fulfill this\<close>
    and "wtxns (Tn t) = No_Ver"
  shows "wtxns_rsran (add_to_readerset wtxns t rclk rlst t_wr) = insert t (wtxns_rsran (wtxns))"
  using assms
  apply (auto simp add: add_to_readerset_def split: ver_state.split)
  apply (metis wtxns_rsran_inv fun_upd_other insert_iff ver_state.distinct(5) wtxns_rsran_map_upd4)
  apply (metis fun_upd_def fun_upd_upd insertI1 wtxns_rsran_map_upd4)
  by (metis wtxns_rsran_inv fun_upd_other insertCI ver_state.distinct(5) wtxns_rsran_map_upd4)

lemma add_to_readerset_no_ver_inv:
  "add_to_readerset wtxns t rclk rlst t' t'' = No_Ver \<Longrightarrow> wtxns t'' = No_Ver"
  by (auto simp add: add_to_readerset_def split: ver_state.split_asm if_split_asm)

lemma add_to_readerset_no_ver_inv_rev:
  "wtxns t'' = No_Ver \<Longrightarrow> t'' \<noteq> Tn t \<Longrightarrow> add_to_readerset wtxns t rclk rlst t' t'' = No_Ver"
  by (auto simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_prep_inv:
  "add_to_readerset wtxns t rclk rlst t' t'' = Prep pd ts v \<Longrightarrow> wtxns t'' = Prep pd ts v"
  by (auto simp add: add_to_readerset_def split: ver_state.split_asm if_split_asm)

lemma add_to_readerset_prep_inv_rev:
  "wtxns (Tn t) = No_Ver \<Longrightarrow> wtxns t'' = Prep pd ts v \<Longrightarrow>
   add_to_readerset wtxns t rclk rlst t' t'' = Prep pd ts v"
  by (auto simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_commit:
  "add_to_readerset wtxns t rclk rlst t' t'' = Commit cts sts lst v rs \<Longrightarrow>
    \<exists>rs'. wtxns t'' = Commit cts sts lst v rs'"
  by (auto simp add: add_to_readerset_def split: ver_state.split_asm if_split_asm)

lemma add_to_readerset_commit_subset:
  "add_to_readerset wtxns t rclk rlst t' t'' = Commit cts sts lst v rs \<Longrightarrow>
    \<exists>rs'. wtxns t'' = Commit cts sts lst v rs' \<and> dom rs' \<subseteq> dom rs"
  by (auto simp add: add_to_readerset_def split: ver_state.split_asm if_split_asm)

lemma add_to_readerset_commit_rev:
  "wtxns (Tn t) = No_Ver \<Longrightarrow>
   wtxns t'' = Commit cts sts lst v rs' \<Longrightarrow>
    \<exists>rs. add_to_readerset wtxns t rclk rlst t' t'' = Commit cts sts lst v rs"
  by (auto simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_commit_rev_subset:
  "wtxns (Tn t) = No_Ver \<Longrightarrow>
   wtxns t'' = Commit cts sts lst v rs' \<Longrightarrow>
    \<exists>rs. add_to_readerset wtxns t rclk rlst t' t'' = Commit cts sts lst v rs \<and> dom rs' \<subseteq> dom rs"
  by (auto simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_upd:
  assumes "wtxns' = add_to_readerset wtxns t rclk rlst t_wr"
    and "t' \<noteq> t_wr"
    and "t' \<noteq> Tn t"
  shows "wtxns' t' = wtxns t'"
  using assms
  by (simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_pres_get_ts:
  "wtxns (Tn t) = No_Ver \<Longrightarrow>
   get_ts (add_to_readerset wtxns t rclk rlst t_wr t') = get_ts (wtxns t')"
  by (auto simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_pres_is_committed:
  "wtxns (Tn t) = No_Ver \<Longrightarrow>
   is_committed (add_to_readerset wtxns t rclk rlst t_wr t') = is_committed (wtxns t')"
  by (smt (verit) add_to_readerset_prep_inv add_to_readerset_prep_inv_rev wtxns_domIff
      add_to_readerset_wtxns_dom is_committed.elims(3) is_committed.simps(2) is_committed.simps(3))

lemma ran_map_upd_None_finite:
  "finite (ran m) \<Longrightarrow> finite (ran (m (a := None)))"
  apply (simp add: ran_def)
  by (smt (verit) Collect_mono_iff rev_finite_subset)

lemma pending_wtxns_ts_empty:
  "pending_wtxns_ts (svr_state (svrs s k)) = {} \<longleftrightarrow>
    (\<forall>t. \<exists>cts sts lst v rs. svr_state (svrs s k) t \<in> {No_Ver, Reg, Commit cts sts lst v rs})"
  apply (auto simp add: pending_wtxns_ts_def)
  apply (metis get_rs.elims)
  by (metis ver_state.distinct(11) wtxns_domI1 wtxns_domIff)

lemma pending_wtxns_ts_non_empty:
  assumes "svr_state (svrs s k) t \<noteq> No_Ver"
    and "svr_state (svrs s k) t \<noteq> Reg"
    and "\<forall>cts sts lst v rs. svr_state (svrs s k) t \<noteq> Commit cts sts lst v rs"
  shows "pending_wtxns_ts (svr_state (svrs s k)) \<noteq> {}"
  using assms apply (auto simp add: pending_wtxns_ts_def)
  by (meson get_rs.elims)

lemma finite_pending_wtxns_rtxn:
  assumes "finite (pending_wtxns_ts (svr_state (svrs s k)))"
  shows "finite (pending_wtxns_ts (add_to_readerset (svr_state (svrs s k)) t' rclk rlst t))"
  using assms
  apply (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def)
  by (meson add_to_readerset_prep_inv)

lemma finite_pending_wtxns_adding:
  assumes "finite (pending_wtxns_ts (svr_state (svrs s k)))"
  shows "finite (pending_wtxns_ts ((svr_state (svrs s k)) (Tn t := Prep pend_t prep_t v)))"
  using assms
  apply (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def)
  by (metis dual_order.trans linorder_le_cases)

lemma finite_pending_wtxns_removing: 
  assumes "finite (pending_wtxns_ts (svr_state (svrs s k)))"
  shows "finite (pending_wtxns_ts ((svr_state (svrs s k)) (Tn t := Commit cts sts lst v rs)))"
  using assms
  apply (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def)
  by blast

lemma pending_wtxns_adding_ub:
  assumes "\<forall>ts \<in> pending_wtxns_ts (svr_state (svrs s k)). ts \<le> clk"
  shows "\<forall>ts \<in> pending_wtxns_ts ((svr_state (svrs s k)) (Tn t := Prep clk pts v)). ts \<le> clk"
  using assms by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def)

lemma pending_wtxns_removing_ub:
  assumes "\<forall>ts \<in> pending_wtxns_ts (svr_state (svrs s k)). ts \<le> clk"
  shows "\<forall>ts \<in> pending_wtxns_ts ((svr_state (svrs s k)) (Tn t := Commit cts sts lst v rs)). ts \<le> clk"
  using assms by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def)

lemma pending_wtxns_adding_lb:
  assumes "\<forall>ts \<in> pending_wtxns_ts (svr_state (svrs s k)). ts \<ge> clk"
  shows "\<forall>ts \<in> pending_wtxns_ts ((svr_state (svrs s k)) (Tn t := Prep clk pts v)). ts \<ge> clk"
  using assms by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def)

lemma pending_wtxns_removing_lb:
  assumes "\<forall> ts \<in> pending_wtxns_ts (svr_state (svrs s k)). ts \<ge> clk"
  shows "\<forall>ts \<in> pending_wtxns_ts ((svr_state (svrs s k)) (Tn t := Commit cts sts lst v rs)). ts \<ge> clk"
  using assms by (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_ts_def)

lemma pending_wtxns_rtxn:
  "svr_state (svrs s k) (Tn t') = No_Ver \<Longrightarrow>
   pending_wtxns_ts (add_to_readerset (svr_state (svrs s k)) t' rclk rlst t) =
   pending_wtxns_ts (svr_state (svrs s k))"
  apply (auto simp add: pending_wtxns_ts_def)
  apply (meson add_to_readerset_prep_inv)
  by (meson add_to_readerset_prep_inv_rev)

lemma pending_wtxns_adding:
  assumes "\<forall>clk pts v. svr_state (svrs s k) (Tn t) \<noteq> Prep clk pts v"
  shows "pending_wtxns_ts ((svr_state (svrs s k)) (Tn t := Prep clk pts v)) =
         insert clk (pending_wtxns_ts (svr_state (svrs s k)))"
  using assms apply (auto simp add: pending_wtxns_ts_def)
  by metis

lemma pending_wtxns_removing:
  assumes "svr_state (svrs s k) (Tn t) = Prep clk pts v"
  shows "pending_wtxns_ts ((svr_state (svrs s k)) (Tn t := Commit cts sts lst v rs)) =
          pending_wtxns_ts (svr_state (svrs s k)) \<or>
         pending_wtxns_ts ((svr_state (svrs s k)) (Tn t := Commit cts sts lst v rs)) =
          Set.remove clk (pending_wtxns_ts (svr_state (svrs s k)))"
  using assms apply (auto simp add: pending_wtxns_ts_def)
  by (metis ver_state.inject(1))+

lemma other_prep_t_inv:
  assumes "svr_state (svrs s k) t = Prep pend_t prep_t v"
    and "t \<noteq> t'"
  shows "pend_t \<in> pending_wtxns_ts ((svr_state (svrs s k))(t' := b))"
  using assms
  by (auto simp add: pending_wtxns_ts_def)


subsection \<open>Extra: general lemmas\<close>

lemma find_Some_in_set:
  "find P vl = Some ver \<Longrightarrow> ver \<in> set vl \<and> P ver"
  apply (simp add: find_Some_iff)
  by (meson nth_mem)

lemma find_append:
  "find P (vl1 @ vl2) = (case find P vl1 of None \<Rightarrow> find P vl2 | Some ver \<Rightarrow> Some ver)"
  by (induction vl1; simp)

lemma Max_reduced_add_cond:
  "{B k |k. P k \<and> Q k} \<noteq> {} \<Longrightarrow>
   finite ({B k |k. P k}) \<Longrightarrow>
   Max {B k |k. P k \<and> Q k} \<le> Max {B k |k. P k}"
   apply auto
  by (smt (verit) Collect_mono Max_mono empty_Collect_eq)

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

subsection \<open>Invariants about initializations and finity of kvs and its versions\<close>

definition T0_in_CO where
  "T0_in_CO s k \<longleftrightarrow> T0 \<in> set (cts_order s k)"

lemmas T0_in_COI = T0_in_CO_def[THEN iffD2, rule_format]
lemmas T0_in_COE[elim] = T0_in_CO_def[THEN iffD1, elim_format, rule_format]

lemma reach_t0_in_co [simp, dest]: "reach tps s \<Longrightarrow> T0_in_CO s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: T0_in_CO_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: T0_in_CO_def tps_trans_all_defs)
      by (smt (verit) in_set_remove1 remove1_insort_key txid.distinct(1))
  qed (auto simp add: T0_in_CO_def tps_trans_defs)
qed

definition Kvs_Not_Emp where
  "Kvs_Not_Emp s \<longleftrightarrow> (\<forall>k. svr_state (svrs s k) \<noteq> wtxns_emp)"

lemmas Kvs_Not_EmpI = Kvs_Not_Emp_def[THEN iffD2, rule_format]
lemmas Kvs_Not_EmpE[elim] = Kvs_Not_Emp_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_not_emp [simp]: "reach tps s \<Longrightarrow> Kvs_Not_Emp s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    apply (auto simp add: Kvs_Not_Emp_def tps_defs)
    by (metis fun_upd_same ver_state.distinct(5))
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      apply (auto simp add: Kvs_Not_Emp_def tps_trans_defs)
      by (meson add_to_readerset_no_ver_inv)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: Kvs_Not_Emp_def tps_trans_defs)
      by (metis fun_upd_same ver_state.distinct(3))
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      apply (auto simp add: Kvs_Not_Emp_def tps_trans_defs)
      by (metis fun_upd_same ver_state.distinct(5))
  qed (auto simp add: Kvs_Not_Emp_def tps_trans_defs)
qed


definition Dom_Kv_map_Not_Emp where
  "Dom_Kv_map_Not_Emp s cl \<longleftrightarrow> 
    (\<forall>kv_map cts. cl_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map} \<longrightarrow>
      dom kv_map \<noteq> {})"

lemmas Dom_Kv_map_Not_EmpI = Dom_Kv_map_Not_Emp_def[THEN iffD2, rule_format]
lemmas Dom_Kv_map_Not_EmpE[elim] = Dom_Kv_map_Not_Emp_def[THEN iffD1, elim_format, rule_format]

lemma reach_dom_kv_map_not_emp [simp]: "reach tps s \<Longrightarrow> Dom_Kv_map_Not_Emp s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Dom_Kv_map_Not_Emp_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Dom_Kv_map_Not_Emp_def tps_trans_defs)
qed

definition Init_Ver_Inv where
  "Init_Ver_Inv s k \<longleftrightarrow> (\<exists>rs. svr_state (svrs s k) T0 = Commit 0 0 0 undefined rs)"

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
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Init_Ver_Inv_def tps_trans_defs)
      by (meson add_to_readerset_commit_rev)
  qed (auto simp add: Init_Ver_Inv_def tps_trans_defs)
qed

definition Finite_Wtxns_Dom where
  "Finite_Wtxns_Dom s k \<longleftrightarrow> finite (wtxns_dom (svr_state (svrs s k)))"

lemmas Finite_Wtxns_DomI = Finite_Wtxns_Dom_def[THEN iffD2, rule_format]
lemmas Finite_Wtxns_DomE[elim] = Finite_Wtxns_Dom_def[THEN iffD1, elim_format, rule_format]

lemma reach_finite_wtxns_dom [simp]: "reach tps s \<Longrightarrow> Finite_Wtxns_Dom s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Finite_Wtxns_Dom_def tps_defs wtxns_dom_def)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      by (auto simp add: Finite_Wtxns_Dom_def tps_trans_defs add_to_readerset_def
               split: ver_state.split)
  qed (auto simp add: Finite_Wtxns_Dom_def tps_trans_defs)
qed

definition Finite_Wtxns_rsran where
  "Finite_Wtxns_rsran s k \<longleftrightarrow> finite (wtxns_rsran (svr_state (svrs s k)))"

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
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      apply (auto simp add: Finite_Wtxns_rsran_def tps_trans_defs add_to_readerset_def
               split: ver_state.split)
      by (metis (no_types, lifting) finite_insert fun_upd_other ver_state.distinct(5)
          wtxns_rsran_inv wtxns_rsran_map_upd4)
  qed (auto simp add: Finite_Wtxns_rsran_def tps_trans_defs)
qed

definition Finite_Pend_Inv where
  "Finite_Pend_Inv s svr \<longleftrightarrow> finite (pending_wtxns_ts (svr_state (svrs s svr)))"

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
    case (RegR x71 x72 x73 x74 x75 x76 x77)
    then show ?case
      by (auto simp add: Finite_Pend_Inv_def tps_trans_defs finite_pending_wtxns_rtxn)
  next
    case (PrepW x81 x82 x83 x84 x85)
    then show ?case
      by (auto simp add: Finite_Pend_Inv_def tps_trans_defs finite_pending_wtxns_adding)
  next
    case (CommitW x91 x92 x93 x94 x95 x96 x97)
    then show ?case
      by (auto simp add: Finite_Pend_Inv_def tps_trans_defs finite_pending_wtxns_removing)
  qed (auto simp add: Finite_Pend_Inv_def tps_trans_defs)
qed

definition Finite_Dom_Kv_map where
  "Finite_Dom_Kv_map s cl \<longleftrightarrow>
    (\<forall>kv_map cts. cl_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map} \<longrightarrow>
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

definition Finite_Dom_Kv_map_rd where
  "Finite_Dom_Kv_map_rd s cl \<longleftrightarrow>
    (\<forall>cclk keys kv_map. cl_state (cls s cl) = RtxnInProg cclk keys kv_map \<longrightarrow>
      finite (dom (kv_map)) \<and> keys \<noteq> {})"
                                                           
lemmas Finite_Dom_Kv_map_rdI = Finite_Dom_Kv_map_rd_def[THEN iffD2, rule_format]
lemmas Finite_Dom_Kv_map_rdE[elim] = Finite_Dom_Kv_map_rd_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_finite_dom_kv_map_rd [simp]: "reach tps s \<Longrightarrow> Finite_Dom_Kv_map_rd s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Finite_Dom_Kv_map_rd_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Finite_Dom_Kv_map_rd_def tps_trans_defs)
qed

definition Finite_Keys where
  "Finite_Keys s cl \<longleftrightarrow>
    (\<forall>cclk keys kv_map. cl_state (cls s cl) = RtxnInProg cclk keys kv_map \<longrightarrow> finite keys)"
                                                           
lemmas Finite_KeysI = Finite_Keys_def[THEN iffD2, rule_format]
lemmas Finite_KeysE[elim] = Finite_Keys_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_finite_keys [simp]: "reach tps s \<Longrightarrow> Finite_Keys s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Finite_Keys_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Finite_Keys_def tps_trans_defs)
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
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Finite_Lst_map_Ran_def tps_trans_defs)
      by (meson image_mono rev_finite_subset subset_UNIV)
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Finite_Lst_map_Ran_def tps_trans_defs)
       apply (meson image_mono rev_finite_subset subset_UNIV)
        using Finite_Dom_Kv_map_def[of s x1] by (simp add: image_def dom_def)
  qed (auto simp add: Finite_Lst_map_Ran_def tps_trans_defs)
qed

lemma finite_get_ts:
  "reach tps s \<Longrightarrow>
   cl_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map} \<Longrightarrow>
   finite {get_ts (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map}"
  using Finite_Dom_Kv_map_def[of s cl] dom_def by auto


subsection \<open>At functions\<close>

lemma full_ts_less_prod:
  assumes "reach tps s"
    and "get_ts (svr_state (svrs s k) t) < get_ts (svr_state (svrs s k) t')"
  shows "full_ts (svr_state (svrs s k)) t < full_ts (svr_state (svrs s k)) t'"
  using assms Init_Ver_Inv_def[of s k]
  by (auto simp add: full_ts_def less_prod_def)

lemma get_ts_less_prod_eq:
  assumes "full_ts wtxns t \<le> full_ts wtxns t'"
  shows "get_ts (wtxns t) \<le> get_ts (wtxns t')"
  using assms
  by (auto simp add: full_ts_def less_eq_prod_def)

lemma arg_max_if_not:
  "(ARG_MAX (\<lambda>x. get_ts (if x = t then X else Y x)) ta. ta \<noteq> t \<and> (ta \<noteq> t \<longrightarrow> P ta)) = 
   (ARG_MAX (\<lambda>x. get_ts (Y x)) ta. ta \<noteq> t \<and> P ta)"
  apply (auto simp add: arg_max_def is_arg_max_def)
  by metis

subsubsection \<open>at\<close>

\<comment> \<open>committed\<close>
lemma at_is_committed:
  assumes "reach tps s"
  shows "is_committed ((svr_state (svrs s k)) (at (svr_state (svrs s k)) rts))"
proof -
  let ?P = "\<lambda>t. is_committed (svr_state (svrs s k) t) \<and> get_ts (svr_state (svrs s k) t) \<le> rts"
    and ?f = "full_ts (svr_state (svrs s k))"
  have "finite {t. is_committed (svr_state (svrs s k) t)}"
    using Finite_Wtxns_Dom_def[of s k] assms(1)
    apply (auto simp add: wtxns_dom_def)
    by (smt Collect_mono_iff finite_subset is_committed.simps(2,3))
  then have fin: "finite {y. \<exists>x. ?P x \<and> y = ?f x}" by simp
  have "?P T0" using assms(1) Init_Ver_Inv_def[of s k] by auto
  then show ?thesis apply (auto simp add: at_def ver_committed_before_def)
    by (smt arg_max_exI[of ?P ?f] P_arg_max fin)
qed

\<comment> \<open>finite\<close>
lemma at_finite:
  assumes "reach tps s"
  shows "finite {y. \<exists>x. (\<lambda>t. is_committed (svr_state (svrs s k) t) \<and> get_ts (svr_state (svrs s k) t) \<le> rts) x
    \<and> y = full_ts (svr_state (svrs s k)) x}"
proof -
  have "finite {t. is_committed (svr_state (svrs s k) t)}"
    using Finite_Wtxns_Dom_def[of s k] assms(1)
    apply (auto simp add: wtxns_dom_def)
    by (smt (verit) Collect_mono_iff finite_subset is_committed.simps(2,3))
  then show ?thesis by simp
qed

\<comment> \<open>realtion to rts\<close>
lemma at_le_rts:
  assumes "reach tps s"
  shows "get_ts (svr_state (svrs s k) (at (svr_state (svrs s k)) rts)) \<le> rts"
proof -
  let ?P = "\<lambda>t. is_committed (svr_state (svrs s k) t) \<and> get_ts (svr_state (svrs s k) t) \<le> rts"
    and ?f = "full_ts (svr_state (svrs s k))"
  have "?P T0" using assms(1) Init_Ver_Inv_def[of s k] by auto
  then show ?thesis apply (auto simp add: at_def ver_committed_before_def)
    using arg_max_exI[of ?P ?f] P_arg_max at_finite[OF assms]
    by fastforce
qed

\<comment> \<open>realtion to get_ts\<close>
lemma get_ts_at_le:
  assumes "reach tps s"
    and "rts \<le> rts'"
  shows "get_ts (svr_state (svrs s k) (at (svr_state (svrs s k)) rts)) \<le>
    get_ts (svr_state (svrs s k) (at (svr_state (svrs s k)) rts'))"
proof -
  let ?P = "\<lambda>t. is_committed (svr_state (svrs s k) t) \<and> get_ts (svr_state (svrs s k) t) \<le> rts'"
    and ?f = "full_ts (svr_state (svrs s k))"
  have non_emp: "?P T0" using assms(1) Init_Ver_Inv_def[of s k] by auto
  have "?P (at (svr_state (svrs s k)) rts)"
    using assms(2) at_is_committed[OF assms(1)] at_le_rts[OF assms(1)] le_trans by blast
  then show ?thesis using assms
    using arg_max_exI[OF at_finite[OF assms(1)] non_emp] 
    apply (auto simp add: at_def ver_committed_before_def)
    by (smt (verit) arg_max_equality is_arg_max_linorder get_ts_less_prod_eq)
qed

\<comment> \<open>preserved by add_to_readerset\<close>
lemma add_to_readerset_pres_at:
  "wtxns (Tn t) = No_Ver \<Longrightarrow>
   at (add_to_readerset wtxns t rclk rlst t_wr) ts = at wtxns ts"
  by (auto simp add: at_def ver_committed_before_def add_to_readerset_pres_get_ts o_def
      add_to_readerset_pres_is_committed full_ts_def)

\<comment> \<open>preserved by prepare write\<close>
lemma prepare_write_pres_at:
  "wtxns t = No_Ver \<Longrightarrow> at (wtxns (t := Prep pd ts v)) rts = at wtxns rts"
  apply (simp add: at_def ver_committed_before_def o_def arg_max_def is_arg_max_def
      full_ts_def less_prod_def)
  by (smt (verit) Eps_cong is_committed.simps(2))


\<comment> \<open>preserved by commit_write\<close>
lemma commit_write_pres_at:
  "wtxns t = Prep pd ts v \<Longrightarrow> cts > rts \<Longrightarrow> at (wtxns (t := Commit cts sts lst v rs_emp)) rts = at wtxns rts"
  apply (simp add: at_def ver_committed_before_def o_def arg_max_def is_arg_max_def
      full_ts_def less_prod_def)
  by (smt (verit) Eps_cong is_committed.simps(4))


subsubsection \<open>neweset_own_write\<close>

\<comment> \<open>committed\<close>
lemma newest_own_write_is_committed:
  assumes "Finite_Wtxns_Dom s k"
    and "newest_own_write (svr_state (svrs s k)) ts cl = Some t"
  shows "is_committed (svr_state (svrs s k) t)"
proof -
  let ?P = "\<lambda>t. is_committed (svr_state (svrs s k) t)"
    and ?Q = "\<lambda>t. ts < get_ts (svr_state (svrs s k) t) \<and> t \<noteq> T0 \<and> get_cl_w t = cl"
    and ?PQ = "\<lambda>t. is_committed (svr_state (svrs s k) t) \<and> ts < get_ts (svr_state (svrs s k) t)
      \<and> t \<noteq> T0 \<and> get_cl_w t = cl"
    and ?f = "get_ts o (svr_state (svrs s k))"
  obtain tw where P_tw: "?PQ tw" using assms
    by (auto simp add: newest_own_write_def ver_committed_after_def split: if_split_asm)
  have "finite {x. ?P x}" using assms(1) Finite_Wtxns_Dom_def
    by (smt (verit) wtxns_dom_def Collect_mono is_committed.simps(2,3) rev_finite_subset)
  hence fin: "finite {y. \<exists>x. ?PQ x \<and> y = ?f x}" by auto
  show ?thesis using assms P_Q_arg_max[of ?f ?P ?Q] arg_max_exI[OF fin P_tw]
    by (auto simp add: newest_own_write_def ver_committed_after_def split: if_split_asm)
qed

\<comment> \<open>exists\<close>
lemma newest_own_write_exists:
  assumes "reach tps s"
    and "newest_own_write (svr_state (svrs s k)) rts cl = Some t"
  shows "\<exists>t. is_arg_max (get_ts o (svr_state (svrs s k)))
    (\<lambda>t. ver_committed_after (svr_state (svrs s k) t) rts \<and> t \<noteq> T0 \<and> get_cl_w t = cl) t"
proof -
  let ?P = "\<lambda>t. ver_committed_after (svr_state (svrs s k) t) rts \<and> t \<noteq> T0 \<and> get_cl_w t = cl"
    and ?f = "get_ts o (svr_state (svrs s k))"
  have "finite {t. is_committed (svr_state (svrs s k) t)}"
    using Finite_Wtxns_Dom_def[of s k] assms(1) apply (auto simp add: wtxns_dom_def)
    by (metis (mono_tags, lifting) Collect_mono_iff finite_subset is_committed.simps(2,3))
  then have fin: "finite {y. \<exists>x. ?P x \<and> y = ?f x}"
    by (simp add: ver_committed_after_def)
  obtain t' where ex: "?P t'"
    using assms by (auto simp add: newest_own_write_def split: if_split_asm)
  then show ?thesis
    using fin arg_max_exI[of ?P ?f] by blast
qed

\<comment> \<open>realation to rts\<close>
lemma newest_own_write_gt_rts:
  assumes "reach tps s"
    and "newest_own_write (svr_state (svrs s k)) rts cl = Some t"
  shows "get_ts (svr_state (svrs s k) t) > rts"
proof -
  let ?P = "\<lambda>t. ver_committed_after (svr_state (svrs s k) t) rts \<and> t \<noteq> T0 \<and> get_cl_w t = cl"
    and ?f = "get_ts o (svr_state (svrs s k))"
  have "ver_committed_after (svr_state (svrs s k) (ARG_MAX ?f t. ?P t)) rts"
    using newest_own_write_exists[OF assms] by (smt (z3) P_arg_max)
  then show ?thesis using assms
    by (auto simp add: newest_own_write_def ver_committed_after_def split: if_split_asm)
qed

\<comment> \<open>owned\<close>
lemma newest_own_write_owned:
  assumes "reach tps s"
    and "newest_own_write (svr_state (svrs s k)) rts cl = Some t"
  shows "get_cl_w t = cl"
proof -
  let ?P = "\<lambda>t. ver_committed_after (svr_state (svrs s k) t) rts \<and> t \<noteq> T0 \<and> get_cl_w t = cl"
    and ?f = "get_ts o (svr_state (svrs s k))"
  have "get_cl_w (ARG_MAX ?f t. ?P t) = cl"
    using newest_own_write_exists[OF assms] by (smt (z3) P_arg_max)
  then show ?thesis using assms
    by (auto simp add: newest_own_write_def split: if_split_asm)
qed

\<comment> \<open>owned\<close>
lemma newest_own_write_Tn:
  assumes "reach tps s"
    and "newest_own_write (svr_state (svrs s k)) rts cl = Some t"
  shows "t \<noteq> T0"
proof -
  let ?P = "\<lambda>t. ver_committed_after (svr_state (svrs s k) t) rts \<and> t \<noteq> T0 \<and> get_cl_w t = cl"
    and ?f = "get_ts o (svr_state (svrs s k))"
  have "(ARG_MAX ?f t. ?P t) \<noteq> T0"
    using newest_own_write_exists[OF assms] by (smt (z3) P_arg_max)
  then show ?thesis using assms
    by (auto simp add: newest_own_write_def split: if_split_asm)
qed

\<comment> \<open>none and some\<close>
lemma newest_own_write_none_pres:
  assumes "newest_own_write (svr_state (svrs s k)) rts cl = None"  
    and "rts \<le> rts'"
  shows "newest_own_write (svr_state (svrs s k)) rts' cl = None"
  using assms
  by (auto simp add: newest_own_write_def ver_committed_after_def split: if_split_asm)

lemma newest_own_write_some_pres:
  assumes "newest_own_write (svr_state (svrs s k)) rts' cl = Some t"
    and "rts \<le> rts'"
  shows "newest_own_write (svr_state (svrs s k)) rts cl = Some t"
  using assms
  apply (auto simp add: newest_own_write_def ver_committed_after_def arg_max_def is_arg_max_def
              split: if_split_asm)
  apply (smt (verit) Eps_cong dual_order.trans linorder_le_less_linear nle_le order_less_le_trans)
  using order_le_less_trans by blast

\<comment> \<open>preserved by add_to_readerset\<close>
lemma add_to_readerset_pres_newest_own_write:
  "wtxns (Tn t) = No_Ver \<Longrightarrow>
   newest_own_write (add_to_readerset wtxns t rclk rlst t_wr) ts cl = newest_own_write wtxns ts cl"
  by (auto simp add: newest_own_write_def ver_committed_after_def add_to_readerset_pres_get_ts o_def
      add_to_readerset_pres_is_committed)

\<comment> \<open>preserved by prepare write\<close>
lemma prepare_write_pres_newest_own_write:
  "wtxns t = No_Ver \<Longrightarrow>
   newest_own_write (wtxns (t := Prep pd ts v)) rts cl = newest_own_write wtxns rts cl"
  apply (auto simp add: newest_own_write_def ver_committed_after_def o_def arg_max_if_not)
  by (metis is_committed.simps(2))+

\<comment> \<open>preserved by commite write\<close>
lemma commit_write_pres_newest_own_write:
  "get_cl_w t \<noteq> cl \<Longrightarrow>
   newest_own_write (wtxns (t := Commit cts sts lst v rs_emp)) rts cl = newest_own_write wtxns rts cl"
  apply (auto simp add: newest_own_write_def ver_committed_after_def o_def arg_max_if_not)
  by metis


subsubsection \<open>read_at\<close>

\<comment> \<open>committed\<close>
lemma read_at_is_committed:
  assumes "reach tps s"
  shows "is_committed (svr_state (svrs s k) (read_at (svr_state (svrs s k)) rts cl))"
  using assms
  by (simp add: read_at_def Let_def at_is_committed newest_own_write_is_committed split: option.split)

\<comment> \<open>preserved by add_to_readerset\<close>
lemma add_to_readerset_pres_read_at:
  "wtxns (Tn t) = No_Ver \<Longrightarrow>
   read_at (add_to_readerset wtxns t rclk rlst t_wr) ts cl = read_at wtxns ts cl"
  by (simp add: read_at_def add_to_readerset_pres_at add_to_readerset_pres_get_ts
      add_to_readerset_pres_newest_own_write split: option.split)

\<comment> \<open>preserved by prepare write\<close>
lemma prepare_write_pres_read_at:
  "wtxns t = No_Ver \<Longrightarrow> read_at (wtxns (t := Prep pd ts v)) rts cl = read_at wtxns rts cl"
  by (simp add: read_at_def Let_def prepare_write_pres_at prepare_write_pres_newest_own_write
      split: option.split)

\<comment> \<open>preserved by commit write\<close>
lemma commit_write_pres_read_at:
  "wtxns t = Prep pd ts v \<Longrightarrow> cts > rts \<Longrightarrow> get_cl_w t \<noteq> cl \<Longrightarrow>
   read_at (wtxns (t := Commit cts sts lst v rs_emp)) rts cl = read_at wtxns rts cl"
  by (simp add: read_at_def Let_def commit_write_pres_at commit_write_pres_newest_own_write
      split: option.split)


subsection \<open>Invariant about server and client state relations and (future and past) transactions ids\<close>

\<comment> \<open>Value of svr_state for future transaction ids\<close>
definition FTid_Wtxn_Inv where
  "FTid_Wtxn_Inv s cl \<longleftrightarrow> (\<forall>n k. n > cl_sn (cls s cl) \<longrightarrow> svr_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver)"

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
    case (RegR x71 x72 x73 x74 x75 x76 x77)
    then show ?case
      apply (auto simp add: tps_trans_defs FTid_Wtxn_Inv_def)
      by (metis add_to_readerset_no_ver_inv_rev nat_neq_iff txid.inject txid0.collapse txid0.inject)
  qed (auto simp add: tps_trans_defs FTid_Wtxn_Inv_def)
qed


subsubsection \<open>cl_state + cl_sn \<longrightarrow> svr_state\<close>

definition Cl_Rtxn_Inv where
  "Cl_Rtxn_Inv s cl \<longleftrightarrow> (\<forall>k cclk keys kvm. cl_state (cls s cl) \<in> {Idle, RtxnInProg cclk keys kvm}
    \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) \<in> {No_Ver, Reg})"

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
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Rtxn_Inv_def tps_trans_defs)
      using add_to_readerset_wtxns_dom by blast
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Cl_Rtxn_Inv_def tps_trans_defs)
      by (metis get_cl_w.simps(2) txn_state.distinct(3) txn_state.distinct(7) txid0.collapse)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Rtxn_Inv_def tps_trans_defs)
      by force
  qed (auto simp add: Cl_Rtxn_Inv_def tps_trans_defs)
qed

definition Cl_Wtxn_Idle_Svr where
  "Cl_Wtxn_Idle_Svr s cl k \<longleftrightarrow> (\<forall>cts kv_map. cl_state (cls s cl) = Idle \<or>
    (cl_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map} \<and> kv_map k = None)
    \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver)"

lemmas Cl_Wtxn_Idle_SvrI = Cl_Wtxn_Idle_Svr_def[THEN iffD2, rule_format]
lemmas Cl_Wtxn_Idle_SvrE[elim] = Cl_Wtxn_Idle_Svr_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_wtxn_idle_svr [simp]: "reach tps s \<Longrightarrow> Cl_Wtxn_Idle_Svr s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Cl_Wtxn_Idle_Svr_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Wtxn_Idle_Svr_def tps_trans_defs)
      by (metis (mono_tags, lifting) add_to_readerset_no_ver_inv_rev get_cl_w.simps(2)
          get_cl_w_Tn txn_state.distinct(1) txn_state.distinct(7) txn_state.distinct(9))
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Cl_Wtxn_Idle_Svr_def tps_trans_defs)
      by (metis txid0.sel(2) txn_state.distinct(11) txn_state.distinct(3) txn_state.inject(2))
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Wtxn_Idle_Svr_def tps_trans_defs)
      by (metis not_None_eq ver_state.distinct(3))
  qed (auto simp add: Cl_Wtxn_Idle_Svr_def tps_trans_defs)
qed

definition Cl_Prep_Inv where
  "Cl_Prep_Inv s \<longleftrightarrow> (\<forall>cl k kvm. \<exists>pend_t prep_t v. cl_state (cls s cl) = WtxnPrep kvm
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) \<in> {No_Ver, Prep pend_t prep_t v}) \<and>
    (k \<notin> dom kvm \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver))"

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
    case (WInvoke x1 x2 x3 x4)
    then show ?case apply (simp add: Cl_Prep_Inv_def tps_trans_defs)
      by (metis Cl_Wtxn_Idle_Svr_def reach_cl_wtxn_idle_svr)
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Prep_Inv_def tps_trans_defs)
      by (smt (verit) add_to_readerset_upd get_cl_w_Tn txid0.sel(2)
          txn_state.distinct(7) ver_state.distinct(11) ver_state.distinct(5))
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Cl_Prep_Inv_def tps_trans_defs)
      by (metis domI get_cl_w.simps(2) txn_state.inject(2) txid0.collapse)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Prep_Inv_def tps_trans_defs)
      by (metis txid0.sel(2) txn_state.distinct(11))
  qed (auto simp add: Cl_Prep_Inv_def tps_trans_defs)
qed

definition Cl_Commit_Inv where
  "Cl_Commit_Inv s cl k \<longleftrightarrow> (\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<longrightarrow>
    (\<forall>v. kv_map k = Some v \<longrightarrow>
      (\<exists>pend_t prep_t sts lst rs. svr_state (svrs s k) (get_wtxn s cl) \<in> {Prep pend_t prep_t v, Commit cts sts lst v rs})) \<and>
    (kv_map k = None \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver))"

lemmas Cl_Commit_InvI = Cl_Commit_Inv_def[THEN iffD2, rule_format]
lemmas Cl_Commit_InvE[elim] = Cl_Commit_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_commit_inv [simp]: "reach tps s \<Longrightarrow> Cl_Commit_Inv s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Cl_Commit_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Commit_Inv_def tps_trans_defs)
      by (metis (no_types, lifting) Cl_Prep_Inv_def domI domIff option.inject reach_cl_prep_inv)
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Commit_Inv_def tps_trans_defs)
      by (metis (no_types, opaque_lifting) add_to_readerset_commit_rev add_to_readerset_upd
          txid.inject txid0.sel(2) txn_state.distinct(9) ver_state.distinct(11) ver_state.distinct(5))
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Cl_Commit_Inv_def tps_trans_defs)
      by (smt (verit) fun_upd_other get_cl_w.simps(2) txn_state.distinct(11) txid0.collapse)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Commit_Inv_def tps_trans_defs)
      by (metis domD get_cl_w.simps(2) txn_state.inject(3) ver_state.distinct(11) ver_state.inject(1) txid0.collapse)
  qed (auto simp add: Cl_Commit_Inv_def tps_trans_defs)
qed


subsubsection \<open>svr_state \<longrightarrow> cl_state\<close>

definition Prep_is_Curr_wt where
  "Prep_is_Curr_wt s k \<longleftrightarrow> (\<forall>t. is_prepared (svr_state (svrs s k) t) \<longrightarrow> is_curr_wt s t)"

lemmas Prep_is_Curr_wtI = Prep_is_Curr_wt_def[THEN iffD2, rule_format]
lemmas Prep_is_Curr_wtE[elim] = Prep_is_Curr_wt_def[THEN iffD1, elim_format, rule_format]

lemma reach_prep_is_curr_wt[simp]: "reach tps s \<Longrightarrow> Prep_is_Curr_wt s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Prep_is_Curr_wt_def tps_defs split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RDone x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Prep_is_Curr_wt_def tps_trans_defs)
      by (smt (verit) Cl_Rtxn_Inv_def get_cl_w.elims get_sn_w.simps(2) insert_iff is_prepared.simps(2,3)
          reach_cl_rtxn_inv singletonD)
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Prep_is_Curr_wt_def tps_trans_defs)
      apply (cases "x2 k")
       apply (smt (verit) Cl_Wtxn_Idle_Svr_def get_cl_w.simps(2) get_sn_w.cases get_sn_w.simps(2)
          insert_iff is_prepared.simps(2) reach_cl_wtxn_idle_svr)
      by (metis (no_types, lifting) domI get_cl_w.simps(2) get_sn_w.cases
          get_sn_w.simps(2) is_prepared.simps(4))
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Prep_is_Curr_wt_def tps_trans_defs)
      by (smt (verit, ccfv_SIG) add_to_readerset_prep_inv is_prepared.elims(2))
  qed (auto simp add: Prep_is_Curr_wt_def tps_trans_defs)
qed

definition Svr_Prep_Inv where
  "Svr_Prep_Inv s \<longleftrightarrow> (\<forall>k t pd ts v. svr_state (svrs s k) t = Prep pd ts v \<longrightarrow>
    (\<exists>cts kv_map.
      cl_state (cls s (get_cl_w t)) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map} \<and>
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
    case (RInvoke x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis txn_state.distinct(3) txn_state.distinct(5))
  next
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis txn_state.distinct(7) txn_state.distinct(9))
  next
    case (RDone x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis txn_state.distinct(7) txn_state.distinct(9))
  next
    case (WInvoke x1 x2 x3 x4)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis txn_state.distinct(3) txn_state.distinct(5))
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis (lifting) txn_state.distinct(11) txn_state.inject(2))
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis (no_types, lifting) Prep_is_Curr_wt_def get_cl_w.elims get_sn_w.simps(2)
          is_prepared.simps(1) reach_prep_is_curr_wt txn_state.distinct(11) txn_state.inject(3)
          ver_state.distinct(11))
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (meson add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Svr_Prep_Inv_def tps_trans_defs)
      by (metis domI)
  qed (auto simp add: Svr_Prep_Inv_def tps_trans_defs)
qed


definition Svr_Commit_Inv where
  "Svr_Commit_Inv s \<longleftrightarrow> (\<forall>k t cts sts lst v rs. 
    svr_state (svrs s k) t = Commit cts sts lst v rs \<and> is_curr_wt s t \<longrightarrow> 
      (\<exists>kv_map. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map \<and> k \<in> dom kv_map))"

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
    case (RInvoke x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis txn_state.distinct(5))
  next
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis txn_state.distinct(9))
  next
    case (RDone x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis FTid_Wtxn_Inv_def get_cl_w.elims get_sn_w.simps(2) lessI
          reach_ftid_wtxn_inv ver_state.distinct(5))
  next
    case (WInvoke x1 x2 x3 x4)
    then show ?case apply (simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis txn_state.distinct(5))
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis (lifting) txn_state.distinct(11))
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Svr_Commit_Inv_def tps_trans_defs)
      by (metis (lifting) FTid_Wtxn_Inv_def get_cl_w.elims get_sn_w.simps(2)
          lessI reach_ftid_wtxn_inv ver_state.distinct(5))
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Svr_Commit_Inv_def tps_trans_defs)
    by (metis add_to_readerset_commit)
  qed (auto simp add: Svr_Commit_Inv_def tps_trans_defs)
qed


subsubsection \<open>fresh/future transactions\<close>

definition CFTid_Rtxn_Inv where
  "CFTid_Rtxn_Inv s cl \<longleftrightarrow> (\<forall>n. n \<ge> cl_sn (cls s cl) \<longrightarrow> rtxn_rts s (Tn_cl n cl) = None)"

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


lemma commit_write_pres_max_get_ts:
  assumes
    "cts = Max {get_ts (svr_state (svrs s k) t) |k. k \<in> dom kv_map}"
    "finite {get_ts (svr_state (svrs s k) t) |k. k \<in> dom kv_map}"
    "s' = s \<lparr>svrs := (svrs s) (x1 := svrs s x1
      \<lparr>svr_state := (svr_state (svrs s x1))(t := Commit cts a b c d),
       svr_clock := a,
       svr_lst := b\<rparr>)\<rparr>"
    "x1 \<in> dom kv_map"
  shows
    "Max {get_ts (svr_state (svrs s k) t) |k. k \<in> dom kv_map} = 
     Max {get_ts (svr_state (svrs s' k) t) |k. k \<in> dom kv_map}"
proof -
  let ?A = "{get_ts (svr_state (svrs s k) t) |k. k \<in> dom kv_map \<and> k \<noteq> x1}"
  have *: "{get_ts (svr_state (svrs s' k) t) |k. k \<in> dom kv_map} = {cts} \<union> ?A"
    using assms(3-) by auto
  then show ?thesis
  proof (cases "?A = {}")
    case True
    then show ?thesis using *
    by (smt (verit) Max_singleton assms(1) sup_bot_right)
  next
    case False
    have fin: "finite ?A" using assms(2)
      by (smt (verit) Collect_cong finite_Collect_conjI)
    then have "Max ?A \<le> cts" using assms(1,2)
      by (smt (verit) False Max_ge Max_in mem_Collect_eq)
    then show ?thesis
      using \<open>?A \<noteq> {}\<close> assms(1) * fin by auto
  qed
qed


definition CTid_Cts where
  "CTid_Cts s cl \<longleftrightarrow> (\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<longrightarrow> 
    cts = Max {get_ts (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map})"

lemmas CTid_CtsI = CTid_Cts_def[THEN iffD2, rule_format]
lemmas CTid_CtsE[elim] = CTid_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_ctid_cts_inv [simp]: "reach tps s \<Longrightarrow> CTid_Cts s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: CTid_Cts_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: CTid_Cts_def tps_trans_defs)
      by (metis (full_types, opaque_lifting) add_to_readerset_pres_get_ts)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: CTid_Cts_def tps_trans_defs)
      by metis
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case
    proof (cases "x2 = get_txn s cl")
      case True
      then obtain kv_map where "cl_state (cls s cl) = WtxnCommit x4 kv_map"
        using CommitW by (auto simp add: tps_trans_defs)
      moreover have "x4 = Max {get_ts (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map}"
        using CommitW by (simp add: CTid_Cts_def calculation)
      ultimately show ?thesis unfolding CTid_Cts_def
        apply (auto dest!: commit_write_pres_max_get_ts[where s=s and s'=s'])
         using CommitW \<open>x2 = get_txn s cl\<close>
        by (auto simp add: tps_trans_defs finite_get_ts reach_trans)
    qed (auto simp add: CTid_Cts_def tps_trans_defs, metis)
  qed (auto simp add: CTid_Cts_def tps_trans_defs)
qed

definition FTid_notin_rs where
  "FTid_notin_rs s cl \<longleftrightarrow> (\<forall>k n t cts sts lst v rs. n > cl_sn (cls s cl) \<and>
    svr_state (svrs s k) t = Commit cts sts lst v rs \<longrightarrow> rs (Tn_cl n cl) = None)"

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
    case (RDone x1 x2 x3 x4 x5)
    then show ?case apply (simp add: FTid_notin_rs_def tps_trans_defs)
      by (meson Suc_lessD)
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case apply (simp add: FTid_notin_rs_def tps_trans_defs)
      by (meson Suc_lessD)
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: FTid_notin_rs_def tps_trans_defs add_to_readerset_def
          split: ver_state.split)
      by (smt (verit) less_irrefl_nat txid0.sel(1) txid0.sel(2))
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: FTid_notin_rs_def tps_trans_defs)
      by (metis)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: FTid_notin_rs_def tps_trans_defs)
      by (smt empty_iff fun_upd_other fun_upd_same txn_state.simps(19) ver_state.inject(2)
          ver_state.simps(10))
  qed (auto simp add: FTid_notin_rs_def tps_trans_defs)
qed


definition FTid_not_wr where
  "FTid_not_wr s cl \<longleftrightarrow> (\<forall>n k. n > cl_sn (cls s cl) \<longrightarrow> Tn (Tn_cl n cl) \<notin> wtxns_dom (svr_state (svrs s k)))"

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
    case (RDone x31 x32 x33)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (metis Suc_lessD)
  next
    case (WDone x61 x62)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (metis Suc_lessD)
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (simp add: add_to_readerset_wtxns_dom)
  next
    case (PrepW x81 x82 x83 x84 x85)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (metis get_cl_w.simps(2) get_sn_w.simps(2) nat_neq_iff txid0.collapse)
  next
    case (CommitW x91 x92 x93 x94 x95 x96 x97)
    then show ?case apply (simp add: FTid_not_wr_def tps_trans_defs)
      by (metis get_cl_w.simps(2) get_sn_w.simps(2) order_less_irrefl txid0.collapse)
  qed (auto simp add: FTid_not_wr_def tps_trans_defs)
qed


definition Fresh_wr_notin_Wts_dom where
  "Fresh_wr_notin_Wts_dom s cl \<longleftrightarrow> (\<forall>cclk keys kv_map k. cl_state (cls s cl) \<in> {Idle, RtxnInProg cclk keys kv_map} \<longrightarrow>
    Tn (get_txn s cl) \<notin> wtxns_dom (svr_state (svrs s k)))"

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
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: tps_trans_defs Fresh_wr_notin_Wts_dom_def)
      by (metis add_to_readerset_wtxns_dom)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: tps_trans_defs Fresh_wr_notin_Wts_dom_def)
      by (metis get_cl_w.simps(2) txn_state.distinct(3) txn_state.distinct(7) txid0.collapse)
  qed (auto simp add: tps_trans_defs Fresh_wr_notin_Wts_dom_def)
qed


definition Fresh_wr_notin_rs where
  "Fresh_wr_notin_rs s cl \<longleftrightarrow> (\<forall>k t cts kv_map cts' sts' lst' v' rs'.
    svr_state (svrs s k) t = Commit cts' sts' lst' v' rs' \<and>
    cl_state (cls s cl) \<in> {Idle, WtxnPrep kv_map, WtxnCommit cts kv_map}
     \<longrightarrow> rs' (get_txn s cl) = None)"

lemmas Fresh_wr_notin_rsI = Fresh_wr_notin_rs_def[THEN iffD2, rule_format]
lemmas Fresh_wr_notin_rsE[elim] = Fresh_wr_notin_rs_def[THEN iffD1, elim_format, rule_format]

lemma reach_fresh_wr_notin_rs [simp]: "reach tps s \<Longrightarrow> Fresh_wr_notin_rs s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Fresh_wr_notin_rs_def tps_defs split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RDone x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Fresh_wr_notin_rs_def tps_trans_defs)
      using FTid_notin_rs_def lessI by blast
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Fresh_wr_notin_rs_def tps_trans_defs)
      using FTid_notin_rs_def by blast
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Fresh_wr_notin_rs_def tps_trans_defs)
      by (auto simp add: add_to_readerset_def split: if_split_asm)
  qed (auto simp add: Fresh_wr_notin_rs_def tps_trans_defs)
qed


subsubsection \<open>past transactions\<close>

definition PTid_Inv where
  "PTid_Inv s cl \<longleftrightarrow> (\<forall>k. \<forall>n < cl_sn (cls s cl).
   (svr_state (svrs s k) (Tn (Tn_cl n cl)) \<in> {No_Ver, Reg}) \<or>
   (rtxn_rts s (Tn_cl n cl) = None \<and>
    (\<exists>cts sts lst v rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts sts lst v rs)))"

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
    case (RegR x71 x72 x73 x74 x75 x76 x77)
    then show ?case
      apply (auto simp add: tps_trans_defs PTid_Inv_def)
      using add_to_readerset_wtxns_dom apply blast
      by (metis (no_types, opaque_lifting) add_to_readerset_prep_inv is_prepared.elims(2,3))
  qed (auto simp add: tps_trans_defs PTid_Inv_def)
qed

lemma other_sn_idle:  
  assumes "FTid_Wtxn_Inv s cl" and "PTid_Inv s cl"
    and "get_cl t = cl" and "get_sn t \<noteq> cl_sn (cls s cl)"
  shows "\<And>k. \<exists>cts sts lst v rs. svr_state (svrs s k) (Tn t) \<in> {No_Ver, Reg, Commit cts sts lst v rs}"
  using assms
  apply (auto simp add: FTid_Wtxn_Inv_def PTid_Inv_def)
  apply (cases "get_sn t > cl_sn (cls s cl)")
  apply (metis txid0.collapse)
  by (metis txid0.collapse linorder_cases)

definition Rtxn_Wtxn_No_Ver where
  "Rtxn_Wtxn_No_Ver s cl \<longleftrightarrow>
    (\<forall>n ts. rtxn_rts s (Tn_cl n cl) = Some ts \<longrightarrow> (\<forall>k. svr_state (svrs s k) (Tn (Tn_cl n cl)) \<in> {No_Ver, Reg}))"

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
    case (RDone x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Rtxn_Wtxn_No_Ver_def tps_trans_defs)
      using Cl_Rtxn_Inv_def[of s x1] by blast
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Rtxn_Wtxn_No_Ver_def tps_trans_defs)
      using add_to_readerset_wtxns_dom by blast
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Rtxn_Wtxn_No_Ver_def tps_trans_defs)
      by (metis CFTid_Rtxn_Inv_def get_sn_w.simps(2) le_refl reach_cftid_rtxn_inv)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Rtxn_Wtxn_No_Ver_def tps_trans_defs)
      by (metis option.exhaust ver_state.distinct(3) ver_state.distinct(7))
  qed (auto simp add: Rtxn_Wtxn_No_Ver_def tps_trans_defs)
qed

definition Wtxn_Rtxn_None where
  "Wtxn_Rtxn_None s k \<longleftrightarrow>
    (\<forall>cl n pd ts sts lst v cts rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) \<in> {Prep pd ts v, Commit cts sts lst v rs}
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
    case (RDone x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Wtxn_Rtxn_None_def tps_trans_defs)
      by (meson wtxns_domI1 wtxns_domI2 wtxns_domIff)
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Wtxn_Rtxn_None_def tps_trans_defs)
      by (meson add_to_readerset_commit_subset add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Wtxn_Rtxn_None_def tps_trans_defs)
      by (metis CFTid_Rtxn_Inv_def get_cl_w.simps(2) get_sn_w.simps(2) le_refl
          reach_cftid_rtxn_inv txid0.collapse)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Wtxn_Rtxn_None_def tps_trans_defs)
      by (meson is_prepared.elims(2))
  qed (auto simp add: Wtxn_Rtxn_None_def tps_trans_defs)
qed

definition Wtxn_Cts_T0 where
  "Wtxn_Cts_T0 s \<longleftrightarrow> wtxn_cts s T0 = Some 0"

lemmas Wtxn_Cts_T0I = Wtxn_Cts_T0_def[THEN iffD2, rule_format]
lemmas Wtxn_Cts_T0E[elim] = Wtxn_Cts_T0_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_cts_t0 [simp, dest]: "reach tps s \<Longrightarrow> Wtxn_Cts_T0 s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Wtxn_Cts_T0_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Wtxn_Cts_T0_def tps_trans_defs)
qed

definition Wtxn_Cts_Tn_None where
  "Wtxn_Cts_Tn_None s cl \<longleftrightarrow> (\<forall>cts kv_map cclk keys n. 
    (cl_state (cls s cl) \<in> {Idle, WtxnPrep kv_map} \<and> n \<ge> cl_sn (cls s cl)) \<or>
    (cl_state (cls s cl) \<in> {RtxnInProg cclk keys kv_map, WtxnCommit cts kv_map} \<and> n > cl_sn (cls s cl))
     \<longrightarrow> wtxn_cts s (Tn (Tn_cl n cl)) = None)"

lemmas Wtxn_Cts_Tn_NoneI = Wtxn_Cts_Tn_None_def[THEN iffD2, rule_format]
lemmas Wtxn_Cts_Tn_NoneE[elim] = Wtxn_Cts_Tn_None_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_cts_tn_none [simp, intro]: "reach tps s \<Longrightarrow> Wtxn_Cts_Tn_None s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Wtxn_Cts_Tn_None_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Wtxn_Cts_Tn_None_def tps_trans_defs)
qed

definition Wtxn_Cts_None where
  "Wtxn_Cts_None s \<longleftrightarrow> (\<forall>cts kv_map cclk keys t. t \<noteq> T0 \<and> (
    (cl_state (cls s (get_cl_w t)) \<in> {Idle, WtxnPrep kv_map} \<and>
        get_sn_w t \<ge> cl_sn (cls s (get_cl_w t))) \<or>
    (cl_state (cls s (get_cl_w t)) \<in> {RtxnInProg cclk keys kv_map, WtxnCommit cts kv_map} \<and>
        get_sn_w t > cl_sn (cls s (get_cl_w t))))
     \<longrightarrow> wtxn_cts s t = None)"

lemmas Wtxn_Cts_NoneI = Wtxn_Cts_None_def[THEN iffD2, rule_format]
lemmas Wtxn_Cts_NoneE[elim] = Wtxn_Cts_None_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_cts_none [simp, intro]: "reach tps s \<Longrightarrow> Wtxn_Cts_None s"
  apply (simp add: Wtxn_Cts_None_def)
  apply rule+ subgoal for cts kv_map cclk keys t apply (cases t)
    apply metis using Wtxn_Cts_Tn_None_def[of s "get_cl_w t"]
    by (smt get_cl_w.elims get_sn_w.simps(2) insert_iff reach_wtxn_cts_tn_none).

definition WtxnCommit_Wtxn_Cts where
  "WtxnCommit_Wtxn_Cts s cl \<longleftrightarrow> (\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map
    \<longrightarrow> wtxn_cts s (get_wtxn s cl) = Some cts)"

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

definition Committed_Abs_has_Wtxn_Cts where
  "Committed_Abs_has_Wtxn_Cts s k \<longleftrightarrow> (\<forall>t cts sts lst v rs pd ts kv_map.
    svr_state (svrs s k) t = Commit cts sts lst v rs \<or>
   (svr_state (svrs s k) t = Prep pd ts v \<and> cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map)
      \<longrightarrow> wtxn_cts s t = Some cts)"

lemmas Committed_Abs_has_Wtxn_CtsI = Committed_Abs_has_Wtxn_Cts_def[THEN iffD2, rule_format]
lemmas Committed_Abs_has_Wtxn_CtsE[elim] = Committed_Abs_has_Wtxn_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_cmt_abs_wtxn_cts [simp]: "reach tps s \<Longrightarrow> Committed_Abs_has_Wtxn_Cts s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Committed_Abs_has_Wtxn_Cts_def tps_defs split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Committed_Abs_has_Wtxn_Cts_def tps_trans_defs domI)
      apply (metis (no_types, lifting) Cl_Prep_Inv_def reach_cl_prep_inv ver_state.distinct(5)
          ver_state.distinct(11))
    subgoal for t apply (cases t)
       apply (metis Prep_is_Curr_wt_def is_prepared.simps(1) reach_prep_is_curr_wt) 
      by (metis Prep_is_Curr_wt_def get_cl_w.simps(2) get_sn_w.cases get_sn_w.simps(2)
          is_prepared.simps(1) reach_prep_is_curr_wt).
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Committed_Abs_has_Wtxn_Cts_def tps_trans_defs domI)
      by (meson add_to_readerset_commit add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Committed_Abs_has_Wtxn_Cts_def tps_trans_defs domI)
      by (metis txn_state.distinct(11))
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Committed_Abs_has_Wtxn_Cts_def tps_trans_defs domI)
      by (metis get_cl_w.simps(2) txid0.collapse)
  qed (auto simp add: Committed_Abs_has_Wtxn_Cts_def tps_trans_defs domI)
qed


subsection \<open>monotonic lemmas and inequality of timestamps invariants\<close>

lemma svr_clock_monotonic:
  "state_trans s e s' \<Longrightarrow> svr_clock (svrs s' svr) \<ge> svr_clock (svrs s svr)"
  by (induction e) (auto simp add: tps_trans_defs)

definition Cl_Clk_le_Prep where
  "Cl_Clk_le_Prep s cl \<longleftrightarrow>
    (\<forall>kv_map k v. cl_state (cls s cl) = WtxnPrep kv_map \<and> kv_map k = Some v \<and>
     is_prepared (svr_state (svrs s k) (get_wtxn s cl)) \<longrightarrow>
     cl_clock (cls s cl) \<le> get_ts (svr_state (svrs s k) (get_wtxn s cl)))"

lemmas Cl_Clk_le_PrepI = Cl_Clk_le_Prep_def[THEN iffD2, rule_format]
lemmas Cl_Clk_le_PrepE[elim] = Cl_Clk_le_Prep_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_clk_le_prep [simp]: "reach tps s \<Longrightarrow> Cl_Clk_le_Prep s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Cl_Clk_le_Prep_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (WInvoke x1 x2 x3 x4)
    then show ?case using Cl_Rtxn_Inv_def[of s x1]
      apply (auto simp add: Cl_Clk_le_Prep_def tps_trans_defs)
      by (metis is_prepared.simps(2) is_prepared.simps(3))
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Cl_Clk_le_Prep_def tps_trans_defs)
      by (smt (verit) add_to_readerset_prep_inv is_prepared.elims(2))
  qed (auto simp add: Cl_Clk_le_Prep_def tps_trans_defs)
qed

lemma cl_clock_monotonic_WCommit:
  assumes
    "state_trans s (WCommit cl kv_map cts sn u'' clk mmap) s'"
    "reach tps s"
  shows "cl_clock (cls s' cl) > (cl_clock (cls s cl))"
  using assms
proof -
  have a: "\<forall>ts \<in> {get_ts (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map}.
    cl_clock (cls s cl) \<le> ts"
    using assms Cl_Clk_le_Prep_def[of s cl] 
    apply (auto simp add: tps_trans_defs)
    by (metis (no_types, lifting) domI is_prepared.simps(1))
  then have b: "{get_ts (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map} \<noteq> {}"
    using assms Dom_Kv_map_Not_Emp_def[of s cl] by (simp add: tps_trans_defs)
  then have c: "finite ({get_ts (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map})"
    using assms Finite_Dom_Kv_map_def[of s cl] by (simp add: tps_trans_defs)
  have "cl_clock (cls s cl) \<le> Max {get_ts (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map}"
    using a b c by (meson Max_in)
  then show ?thesis using assms
    by (simp add: tps_trans_defs)
qed

lemma cl_clock_monotonic:
  "state_trans s e s' \<Longrightarrow> reach tps s \<Longrightarrow> cl_clock (cls s' cl) \<ge> cl_clock (cls s cl)"
proof (induction e)
  case (WCommit x1 x2 x3 x4 x5 x6 x7)
  then show ?case using cl_clock_monotonic_WCommit[of s x1]
    by (auto simp add: tps_trans_defs)
qed (auto simp add: tps_trans_defs)

definition Pend_le_Clk where
  "Pend_le_Clk s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns_ts (svr_state (svrs s svr)). ts \<le> svr_clock (svrs s svr))"

lemmas Pend_le_ClkI = Pend_le_Clk_def[THEN iffD2, rule_format]
lemmas Pend_le_ClkE[elim] = Pend_le_Clk_def[THEN iffD1, elim_format, rule_format]

lemma reach_pend_le_clk [simp]: "reach tps s \<Longrightarrow> Pend_le_Clk s svr"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Pend_le_Clk_def tps_defs pending_wtxns_ts_def split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      apply (auto simp add: Pend_le_Clk_def tps_trans_defs pending_wtxns_ts_def)
      by (meson add_to_readerset_prep_inv le_SucI le_trans max.cobounded1)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: Pend_le_Clk_def tps_trans_defs pending_wtxns_ts_def)
      by (meson le_Suc_eq max.coboundedI1)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      apply (auto simp add: Pend_le_Clk_def tps_trans_defs pending_wtxns_ts_def split: if_split_asm)
      by (meson le_Suc_eq max.coboundedI1 notin_set_remove1)
  qed (auto simp add: Pend_le_Clk_def tps_trans_defs)
qed

definition Prep_le_Clk where
  "Prep_le_Clk s svr \<longleftrightarrow>
    (\<forall>t pd ts v. svr_state (svrs s svr) t = Prep pd ts v \<longrightarrow> ts \<le> svr_clock (svrs s svr))"

lemmas Prep_le_ClkI = Prep_le_Clk_def[THEN iffD2, rule_format]
lemmas Prep_le_ClkE[elim] = Prep_le_Clk_def[THEN iffD1, elim_format, rule_format]

lemma reach_prep_le_clk [simp]: "reach tps s \<Longrightarrow> Prep_le_Clk s svr"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Prep_le_Clk_def tps_defs pending_wtxns_ts_def split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      apply (auto simp add: Prep_le_Clk_def tps_trans_defs pending_wtxns_ts_def)
      by (meson add_to_readerset_prep_inv le_SucI le_trans max.cobounded1)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: Prep_le_Clk_def tps_trans_defs pending_wtxns_ts_def)
      by (meson le_Suc_eq max.coboundedI1)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      apply (auto simp add: Prep_le_Clk_def tps_trans_defs pending_wtxns_ts_def split: if_split_asm)
      by (meson le_Suc_eq max.coboundedI1 notin_set_remove1)
  qed (auto simp add: Prep_le_Clk_def tps_trans_defs)
qed

definition Pend_lt_Prep where
  "Pend_lt_Prep s svr \<longleftrightarrow>
    (\<forall>t pd ts v. svr_state (svrs s svr) t = Prep pd ts v \<longrightarrow> pd < ts)"

lemmas Pend_lt_PrepI = Pend_lt_Prep_def[THEN iffD2, rule_format]
lemmas Pend_lt_PrepE[elim] = Pend_lt_Prep_def[THEN iffD1, elim_format, rule_format]

lemma reach_pend_lt_prep [simp]: "reach tps s \<Longrightarrow> Pend_lt_Prep s svr"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Pend_lt_Prep_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Pend_lt_Prep_def tps_trans_defs)
      by (meson add_to_readerset_prep_inv)
  qed (auto simp add: Pend_lt_Prep_def tps_trans_defs)
qed


definition Lst_le_Clk where
  "Lst_le_Clk s k \<longleftrightarrow> svr_lst (svrs s k) \<le> svr_clock (svrs s k)"

lemmas Lst_le_ClkI = Lst_le_Clk_def[THEN iffD2, rule_format]
lemmas Lst_le_ClkE[elim] = Lst_le_Clk_def[THEN iffD1, elim_format, rule_format]

lemma reach_lst_le_clk [simp, dest]: "reach tps s \<Longrightarrow> Lst_le_Clk s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Lst_le_Clk_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (CommitW x91 x92 x93 x94 x95 x96 x97)
    then show ?case
      apply (auto simp add: Lst_le_Clk_def tps_trans_defs split: if_split_asm)
      by (smt Finite_Pend_Inv_def Min_le_iff Pend_le_Clk_def emptyE finite_pending_wtxns_removing
          le_SucI le_max_iff_disj pending_wtxns_removing_ub reach_finitepending reach_pend_le_clk)
  qed (auto simp add: Lst_le_Clk_def tps_trans_defs)
qed

definition Lst_le_Pend where
  "Lst_le_Pend s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns_ts (svr_state (svrs s svr)). svr_lst (svrs s svr) \<le> ts)"

lemmas Lst_le_PendI = Lst_le_Pend_def[THEN iffD2, rule_format]
lemmas Lst_le_PendE[elim] = Lst_le_Pend_def[THEN iffD1, elim_format, rule_format]

lemma reach_lst_le_pend [simp]: "reach tps s \<Longrightarrow> Lst_le_Pend s svr"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Lst_le_Pend_def tps_defs )
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case by (auto simp add: Lst_le_Pend_def tps_trans_defs pending_wtxns_rtxn)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case by (auto simp add: Lst_le_Pend_def tps_trans_defs pending_wtxns_adding)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Lst_le_Pend_def tps_trans_defs split: if_split_asm)
      by (metis Finite_Pend_Inv_def Min.coboundedI finite_pending_wtxns_removing reach_finitepending)
  qed(auto simp add: Lst_le_Pend_def tps_trans_defs)
qed

lemma min_pending_wtxns_monotonic:
  assumes "state_trans s e s'"
    and "pending_wtxns_ts (svr_state (svrs s k)) \<noteq> {}"
    and "pending_wtxns_ts (svr_state (svrs s' k)) \<noteq> {}"
    and "reach tps s"
  shows "Min (pending_wtxns_ts (svr_state (svrs s k))) \<le>
         Min (pending_wtxns_ts (svr_state (svrs s' k)))"
  using assms
proof (induction e)
  case (RegR x1 x2 x3 x4 x5 x6 x7)
  then show ?case
  apply (auto simp add: tps_trans_defs pending_wtxns_ts_def)
    by (metis le_refl pending_wtxns_rtxn pending_wtxns_ts_def)
next
  case (PrepW x1 x2 x3 x4 x5)
  then show ?case apply (auto simp add: tps_trans_defs)
    using Min_insert_larger[of "pending_wtxns_ts (svr_state (svrs s x1))"
        "pending_wtxns_ts (svr_state (svrs s' x1))" "svr_clock (svrs s x1)"]
      pending_wtxns_adding [of s] Pend_le_Clk_def[of s] Finite_Pend_Inv_def[of s]
    by (cases "k = x1"; auto simp add: pending_wtxns_ts_def)
next
  case (CommitW x1 x2 x3 x4 x5 x6 x7)
  then show ?case using Finite_Pend_Inv_def[of s]
    apply (auto simp add: tps_trans_defs fold_pending_wtxns_fun_upd)
    by (metis Min.coboundedI Min_in Min_remove empty_iff pending_wtxns_removing)
  qed (auto simp add: tps_trans_defs pending_wtxns_ts_def)


lemma svr_lst_monotonic:
  assumes "state_trans s e s'"
    and "reach tps s"
  shows "svr_lst (svrs s' svr) \<ge> svr_lst (svrs s svr)"
  using assms
  proof (induction e)
    case (CommitW svr t v cts clk lst m)
    then show ?case using Lst_le_Clk_def[of s] Finite_Pend_Inv_def[of s] Lst_le_Pend_def[of s]
      apply (auto simp add: tps_trans_defs split: if_split_asm)
      apply (meson le_SucI max.coboundedI1)
      by (metis Min_in empty_iff finite_pending_wtxns_removing member_remove pending_wtxns_removing)
  qed (auto simp add: tps_trans_defs)


definition Rlst_le_Lst where
  "Rlst_le_Lst s k \<longleftrightarrow> (\<forall>t_wr cts ts lst v rs rclk rlst t.
    svr_state (svrs s k) t_wr = Commit cts ts lst v rs \<and> rs t = Some (rclk, rlst)
      \<longrightarrow> rlst \<le> svr_lst (svrs s k))"
                                                           
lemmas Rlst_le_LstI = Rlst_le_Lst_def[THEN iffD2, rule_format]
lemmas Rlst_le_LstE[elim] = Rlst_le_Lst_def[THEN iffD1, elim_format, rule_format]

lemma reach_rlst_le_lst [simp]: "reach tps s \<Longrightarrow> Rlst_le_Lst s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rlst_le_Lst_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      apply (auto simp add: Rlst_le_Lst_def tps_trans_defs add_to_readerset_def split: ver_state.split)
      by blast+
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Rlst_le_Lst_def tps_trans_defs)
      by blast
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case using svr_lst_monotonic[of s "CommitW x1 x2 x3 x4 x5 x6 x7" s' x1]
      apply (auto simp add: Rlst_le_Lst_def tps_trans_defs)
      using dual_order.trans by blast
  qed (auto simp add: Rlst_le_Lst_def tps_trans_defs)
qed

definition Get_lst_le_Lst where
  "Get_lst_le_Lst s k \<longleftrightarrow> (\<forall>t cts sts lst v rs.
    svr_state (svrs s k) t = Commit cts sts lst v rs \<longrightarrow> lst \<le> svr_lst (svrs s k))"

lemmas Get_lst_le_LstI = Get_lst_le_Lst_def[THEN iffD2, rule_format]
lemmas Get_lst_le_LstE[elim] = Get_lst_le_Lst_def[THEN iffD1, elim_format, rule_format]

lemma reach_get_lst_le_lst [simp]: "reach tps s \<Longrightarrow> Get_lst_le_Lst s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Get_lst_le_Lst_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Get_lst_le_Lst_def tps_trans_defs)
      by (meson add_to_readerset_commit)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Get_lst_le_Lst_def tps_trans_defs)
      by blast
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case using svr_lst_monotonic[of s "CommitW x1 x2 x3 x4 x5 x6 x7" s' x1]
      apply (auto simp add: Get_lst_le_Lst_def tps_trans_defs)
      using dual_order.trans by blast
  qed (auto simp add: Get_lst_le_Lst_def tps_trans_defs)
qed


definition Lst_map_le_Lst where
  "Lst_map_le_Lst s cl k \<longleftrightarrow> (lst_map (cls s cl) k \<le> svr_lst (svrs s k))"
                                                           
lemmas Lst_map_le_LstI = Lst_map_le_Lst_def[THEN iffD2, rule_format]
lemmas Lst_map_le_LstE[elim] = Lst_map_le_Lst_def[THEN iffD1, elim_format, rule_format]

lemma reach_lst_map_le_svr_lst [simp]: "reach tps s \<Longrightarrow> Lst_map_le_Lst s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Lst_map_le_Lst_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (cases x7, auto simp add: Lst_map_le_Lst_def tps_trans_defs)
      by (smt (verit) Rlst_le_Lst_def reach_rlst_le_lst)
  next
    case (WDone x1 x2 x3 x4 x5)
    then obtain cts ts lst v rs where
      "k \<in> dom x2 \<Longrightarrow> svr_state (svrs s k) (get_wtxn s x1) = Commit cts ts lst v rs"
      by (auto simp add: tps_trans_defs, blast)
    then show ?case using WDone apply (auto simp add: Lst_map_le_Lst_def tps_trans_defs domI)
      by (smt (verit) Get_lst_le_Lst_def reach_get_lst_le_lst)
  next
  case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case using svr_lst_monotonic[of s "CommitW x1 x2 x3 x4 x5 x6 x7" s' x1]
      by (auto simp add: Lst_map_le_Lst_def tps_trans_defs)
  qed (auto simp add: Lst_map_le_Lst_def tps_trans_defs)
qed


definition Prep_le_Cl_Cts where
  "Prep_le_Cl_Cts s cl \<longleftrightarrow> (\<forall>cts kv_map k pend_t prep_t v. 
      cl_state (cls s cl) = WtxnCommit cts kv_map \<and>
      svr_state (svrs s k) (get_wtxn s cl) = Prep pend_t prep_t v \<longrightarrow> prep_t \<le> cts)"
                                                           
lemmas Prep_le_Cl_CtsI = Prep_le_Cl_Cts_def[THEN iffD2, rule_format]
lemmas Prep_le_Cl_CtsE[elim] = Prep_le_Cl_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_prep_le_cl_cts [simp]: "reach tps s \<Longrightarrow> Prep_le_Cl_Cts s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Prep_le_Cl_Cts_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then have "finite {get_ts (svr_state (svrs s k) (get_wtxn s x1)) |k. k \<in> dom x2}"
      by (auto simp add: tps_trans_defs finite_get_ts)
    then show ?case using WCommit
      apply (auto simp add: Prep_le_Cl_Cts_def tps_trans_defs)
      subgoal for k apply (cases "x2 k")
        subgoal using Cl_Prep_Inv_def[of s] by (simp add: domIff)
        by (smt (verit, best) Max_ge domI mem_Collect_eq get_ts.simps(1)).
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Prep_le_Cl_Cts_def tps_trans_defs)
      by (metis add_to_readerset_prep_inv)
  qed (auto simp add: Prep_le_Cl_Cts_def tps_trans_defs, (metis+)?)
qed

definition Lst_map_le_Get_lst where
  "Lst_map_le_Get_lst s cl k \<longleftrightarrow> (\<forall>cts ts lst v rs.
    svr_state (svrs s k) (get_wtxn s cl) = Commit cts ts lst v rs \<longrightarrow> lst_map (cls s cl) k \<le> lst)"
                                                           
lemmas Lst_map_le_Get_lstI = Lst_map_le_Get_lst_def[THEN iffD2, rule_format]
lemmas Lst_map_le_Get_lstE[elim] = Lst_map_le_Get_lst_def[THEN iffD1, elim_format, rule_format]

lemma reach_lst_map_le_get_lst [simp]: "reach tps s \<Longrightarrow> Lst_map_le_Get_lst s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Lst_map_le_Get_lst_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RDone x1 x2 x3 x4 x5)
    then show ?case using FTid_Wtxn_Inv_def[of s]
      by (auto simp add: Lst_map_le_Get_lst_def tps_trans_defs)
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case using FTid_Wtxn_Inv_def[of s]
      by (auto simp add: Lst_map_le_Get_lst_def tps_trans_defs)
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Lst_map_le_Get_lst_def tps_trans_defs)
      by (meson add_to_readerset_commit)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then have "svr_lst (svrs s x1) \<le> x6"
      using svr_lst_monotonic[of s "CommitW x1 x2 x3 x4 x5 x6 x7" s' x1]
      by (auto simp add: tps_trans_defs)
    then show ?case using CommitW
      apply (auto simp add: Lst_map_le_Get_lst_def tps_trans_defs)
      by (metis Lst_map_le_Lst_def reach_lst_map_le_svr_lst le_trans reach_trans.hyps(2))
  qed (auto simp add: Lst_map_le_Get_lst_def tps_trans_defs)
qed


\<comment> \<open>circular dependent invariants\<close>
definition Gst_lt_Cl_Cts where
  "Gst_lt_Cl_Cts s cl k \<longleftrightarrow> (\<forall>cl' sn' pd ts v cts kv_map.
    svr_state (svrs s k) (Tn (Tn_cl sn' cl')) = Prep pd ts v \<and>
    cl_state (cls s cl') = WtxnCommit cts kv_map \<and>
    k \<in> dom kv_map
    \<longrightarrow> gst (cls s cl) < cts)"

lemmas Gst_lt_Cl_CtsI = Gst_lt_Cl_Cts_def[THEN iffD2, rule_format]
lemmas Gst_lt_Cl_CtsE[elim] = Gst_lt_Cl_Cts_def[THEN iffD1, elim_format, rule_format]

definition Fresh_rd_notin_other_rs where
  "Fresh_rd_notin_other_rs s cl k \<longleftrightarrow> (\<forall>t cclk keys kv_map cts sts lst v rs.
    cl_state (cls s cl) = RtxnInProg cclk keys kv_map \<and>
    svr_state (svrs s k) t = Commit cts sts lst v rs \<and>
    t \<noteq> read_at (svr_state (svrs s k)) (gst (cls s cl)) cl
     \<longrightarrow> rs (get_txn s cl) = None)"

lemmas Fresh_rd_notin_other_rsI = Fresh_rd_notin_other_rs_def[THEN iffD2, rule_format]
lemmas Fresh_rd_notin_other_rsE[elim] = Fresh_rd_notin_other_rs_def[THEN iffD1, elim_format, rule_format]

definition Once_in_rs where
  "Once_in_rs s k t \<longleftrightarrow> (\<forall>t_wr cts ts lst v rs m t_wr' cts' ts' lst' v' rs'.
    svr_state (svrs s k) t_wr = Commit cts ts lst v rs \<and> rs t = Some m \<and>
    t_wr' \<noteq> t_wr \<and> svr_state (svrs s k) t_wr' = Commit cts' ts' lst' v' rs' \<longrightarrow> rs' t = None)"
                                                           
lemmas Once_in_rsI = Once_in_rs_def[THEN iffD2, rule_format]
lemmas Once_in_rsE[elim] = Once_in_rs_def[THEN iffD1, elim_format, rule_format]

definition Lst_map_le_Rlst where
  "Lst_map_le_Rlst s cl k \<longleftrightarrow> (\<forall>t cts ts lst v rs rlst rts.
    svr_state (svrs s k) t = Commit cts ts lst v rs \<and> rs (get_txn s cl) = Some (rts, rlst)
      \<longrightarrow> lst_map (cls s cl) k \<le> rlst)"
                                                           
lemmas Lst_map_le_RlstI = Lst_map_le_Rlst_def[THEN iffD2, rule_format]
lemmas Lst_map_le_RlstE[elim] = Lst_map_le_Rlst_def[THEN iffD1, elim_format, rule_format]

definition Gst_le_Min_Lst_map where
  "Gst_le_Min_Lst_map s cl \<longleftrightarrow> (gst (cls s cl) \<le> Min (range (lst_map (cls s cl))))"
                                                           
lemmas Gst_le_Min_Lst_mapI = Gst_le_Min_Lst_map_def[THEN iffD2, rule_format]
lemmas Gst_le_Min_Lst_mapE[elim] = Gst_le_Min_Lst_map_def[THEN iffD1, elim_format, rule_format]

definition Gst_le_Pend_t where
  "Gst_le_Pend_t s cl \<longleftrightarrow> (\<forall>k t pend_t prep_t v. 
      svr_state (svrs s k) t = Prep pend_t prep_t v \<longrightarrow> gst (cls s cl) \<le> pend_t)"
                                                           
lemmas Gst_le_Pend_tI = Gst_le_Pend_t_def[THEN iffD2, rule_format]
lemmas Gst_le_Pend_tE[elim] = Gst_le_Pend_t_def[THEN iffD1, elim_format, rule_format]

lemmas circular_defs = Fresh_rd_notin_other_rs_def Once_in_rs_def
    Lst_map_le_Rlst_def Gst_le_Min_Lst_map_def Gst_le_Pend_t_def


lemma lst_map_monotonic_dep:
  assumes "state_trans s e s'"
    and "reach tps s"
    and "\<And>cl k. Lst_map_le_Rlst s cl k"
  shows "lst_map (cls s cl) k \<le> lst_map (cls s' cl) k"
  using assms
proof (induction e)
  case (Read x1 x2 x3 x4 x5 x6 x7)
  then show ?case apply (cases x7, auto simp add: tps_trans_defs)
    using Lst_map_le_Rlst_def[of s] by blast
next
  case (WDone x1 x2 x3 x4 x5)
  then obtain cts ts lst v rs where
    "k \<in> dom x2 \<Longrightarrow> svr_state (svrs s k) (get_wtxn s x1) = Commit cts ts lst v rs"
    by (auto simp add: tps_trans_defs, blast)
  then show ?case using WDone apply (auto simp add: tps_trans_defs domI)
    using Lst_map_le_Get_lst_def[of s] reach_lst_map_le_get_lst by blast
qed (auto simp add: tps_trans_defs)

(*** The start of dependent lemmas/invariants ***)
lemma lst_map_min_monotonic_dep:
  assumes "state_trans s e s'"
    and "reach tps s"
    and "\<And>cl k. Lst_map_le_Rlst s cl k"
  shows "Min (range (lst_map (cls s cl))) \<le> Min (range (lst_map (cls s' cl)))"
  using assms lst_map_monotonic_dep[of s] Finite_Lst_map_Ran_def[of s] Finite_Lst_map_Ran_def[of s']
  apply (auto simp add: reach_trans)
  by (meson Min.coboundedI dual_order.trans rangeI)

lemma reach_gst_lt_cl_cts_dep:
  assumes "reach tps s"                                   
    "Gst_le_Pend_t s cl"
  shows "Gst_lt_Cl_Cts s cl k"
  using assms
  apply (auto simp add: Gst_lt_Cl_Cts_def)
  subgoal for cl' using Gst_le_Pend_t_def Pend_lt_Prep_def Prep_le_Cl_Cts_def[of s cl']
  by (metis Prep_is_Curr_wt_def dual_order.trans get_cl_w.simps(2) get_sn_w.simps(2)
      is_prepared.simps(1) leD linorder_le_less_linear reach_pend_lt_prep
      reach_prep_is_curr_wt reach_prep_le_cl_cts txid0.collapse)
  done

lemma reach_gst_le_pd_dep: 
  assumes "reach tps s"
    "\<And>k. Gst_le_Min_Lst_map s k"
  shows "Gst_le_Pend_t s cl"
  using assms Gst_le_Min_Lst_map_def[of s cl] Lst_map_le_Lst_def[of s cl] Lst_le_Pend_def[of s]
  apply (auto simp add: Gst_le_Pend_t_def pending_wtxns_ts_def)
  using Finite_Lst_map_Ran_def[of s cl]
  by (meson Min.coboundedI dual_order.trans rangeI reach_finite_lst_map_ran)

lemma reach_all_circular:
  "reach tps s \<Longrightarrow> (\<forall>cl k. Fresh_rd_notin_other_rs s cl k) \<and> (\<forall>k t. Once_in_rs s k t) \<and>
    (\<forall>cl k. Lst_map_le_Rlst s cl k) \<and> (\<forall>cl. Gst_le_Min_Lst_map s cl)"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: circular_defs tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (intro allI conjI; elim conjE)
    fix cl k
    assume a: "tps: s \<midarrow>e\<rightarrow> s'" "reach tps s" "\<forall>cl. Gst_le_Min_Lst_map s cl"
      "\<forall>cl k. Fresh_rd_notin_other_rs s cl k"
    then have "Fresh_rd_notin_other_rs s cl k" by simp
    then show "Fresh_rd_notin_other_rs s' cl k" using a
    proof (induction e)
      case (RInvoke x1 x2 x3 x4 x5)
      then show ?case using Fresh_wr_notin_rs_def[of s]
        by (auto simp add: Fresh_rd_notin_other_rs_def tps_trans_defs)
    next
      case (RegR x1 x2 x3 x4 x5 x6 x7)
      then show ?case apply (auto simp add: Fresh_rd_notin_other_rs_def tps_trans_defs)
        using add_to_readerset_pres_read_at[of "svr_state (svrs s x1)" _
              _ _ "read_at (svr_state (svrs s x1)) (gst (cls s (get_cl x2))) (get_cl x2)"]
        by (auto simp add: add_to_readerset_def split: if_split_asm)
    next
      case (PrepW x1 x2 x3 x4 x5)
      then show ?case apply (auto simp add: Fresh_rd_notin_other_rs_def tps_trans_defs)
        by (metis prepare_write_pres_read_at)
    next
      case (CommitW x1 x2 x3 x4 x5 x6 x7)
      then have a: "\<forall>cclk keys kv_map. cl_state (cls s cl) = RtxnInProg cclk keys kv_map
        \<longrightarrow> get_cl_w (Tn x2) \<noteq> cl" by (auto simp add: tps_trans_defs)
      have "gst (cls s cl) < x4" using CommitW Gst_lt_Cl_Cts_def[of s cl]
        apply (auto simp add: tps_trans_defs reach_gst_le_pd_dep reach_gst_lt_cl_cts_dep)
        by (metis domI txid0.collapse)
      then show ?case using CommitW
        apply (auto simp add: Fresh_rd_notin_other_rs_def tps_trans_defs)
        using commit_write_pres_read_at[of "svr_state (svrs s k)"] a by auto
    qed (auto simp add: Fresh_rd_notin_other_rs_def tps_trans_defs split: txn_state.split)
  next
    fix k t
    assume a: "tps: s \<midarrow>e\<rightarrow> s'" "reach tps s" "\<forall>cl k. Fresh_rd_notin_other_rs s cl k"
      "\<forall>k t. Once_in_rs s k t"
    then have "Once_in_rs s k t" by simp
    then show "Once_in_rs s' k t" using a
    proof (induction e)
      case (RegR x1 x2 x3 x4 x5 x6 x7)
      then show ?case apply (auto simp add: Once_in_rs_def tps_trans_defs)
        apply (auto simp add: add_to_readerset_def split: if_split_asm ver_state.split)
        using Fresh_rd_notin_other_rs_def[of s]
          apply (metis txid0.collapse)
        using Fresh_rd_notin_other_rs_def[of s]
         apply (metis not_None_eq txid0.collapse)
        by metis
    qed (auto simp add: Once_in_rs_def tps_trans_defs)
  next
    fix cl k
    assume a: "tps: s \<midarrow>e\<rightarrow> s'" "reach tps s" "\<forall>k t. Once_in_rs s k t"
      "\<forall>cl k. Lst_map_le_Rlst s cl k"
    then have "Lst_map_le_Rlst s cl k" by simp
    then show "Lst_map_le_Rlst s' cl k" using a
    proof (induction e)
      case (Read x1 x2 x3 x4 x5 x6 x7)
      then show ?case apply (cases x7, auto simp add: Lst_map_le_Rlst_def tps_trans_defs)
        using Once_in_rs_def[of s x2]
        by (metis option.inject order_class.order_eq_iff prod.inject ver_state.inject(2))
    next
      case (RDone x1 x2 x3 x4 x5)
      then show ?case apply (auto simp add: Lst_map_le_Rlst_def tps_trans_defs)
        using FTid_notin_rs_def[of s]
        by (metis lessI not_None_eq reach_ftid_notin_rs)
    next
      case (WDone x1 x2 x3 x4 x5)
      then show ?case apply (auto simp add: Lst_map_le_Rlst_def tps_trans_defs)
        using FTid_notin_rs_def[of s x1]
         apply (metis less_Suc_eq option.distinct(1) reach_ftid_notin_rs)
        using FTid_notin_rs_def[of s x1]
        by (metis lessI option.discI reach_ftid_notin_rs)
    next
      case (RegR x1 x2 x3 x4 x5 x6 x7)
      then show ?case
        apply (auto simp add: Lst_map_le_Rlst_def tps_trans_defs)
        apply(auto simp add: add_to_readerset_def split: ver_state.split)
        using Lst_map_le_Lst_def[of s cl] reach_lst_map_le_svr_lst
        by (metis (no_types, lifting) fun_upd_apply map_upd_eqD1 prod.inject
            ver_state.distinct(9) ver_state.inject(2))
    next
      case (PrepW x1 x2 x3 x4 x5)
      then show ?case by (auto simp add: Lst_map_le_Rlst_def tps_trans_defs)
    next
      case (CommitW x1 x2 x3 x4 x5 x6 x7)
      then show ?case by (auto simp add: Lst_map_le_Rlst_def tps_trans_defs)
    qed (auto simp add: Lst_map_le_Rlst_def tps_trans_defs)
  next
    fix k
    assume a: "tps: s \<midarrow>e\<rightarrow> s'" "reach tps s" "\<forall>cl k. Lst_map_le_Rlst s cl k"
      "\<forall>k. Gst_le_Min_Lst_map s k"
    then have "Gst_le_Min_Lst_map s k" by simp
    then show "Gst_le_Min_Lst_map s' k" using a
    proof (induction e)
      case (Read x1 x2 x3 x4 x5 x6 x7)
      then show ?case using lst_map_min_monotonic_dep[of s "Read x1 x2 x3 x4 x5 x6 x7" s' x1]
        apply (simp add: Gst_le_Min_Lst_map_def tps_trans_defs)
        by (smt (z3) Read.prems(1) le_trans reach.reach_trans reach_finite_lst_map_ran)
    next
      case (WDone x1 x2 x3 x4 x5)
      then show ?case using lst_map_min_monotonic_dep[of s "WDone x1 x2 x3 x4 x5" s' x1]
        apply (simp add: Gst_le_Min_Lst_map_def tps_trans_defs)
        by (smt (z3) WDone.prems(1) le_trans reach.reach_trans reach_finite_lst_map_ran)
    qed (auto simp add: Gst_le_Min_Lst_map_def tps_trans_defs)
  qed
qed
(*** The end of dependent lemmas/invariants ***)

lemma reach_fresh_rd_notin_other_rs [simp]:
  "reach tps s \<Longrightarrow> Fresh_rd_notin_other_rs s cl k"
  by (simp add: reach_all_circular)

lemma reach_once_in_rs [simp]:
  "reach tps s \<Longrightarrow> Once_in_rs s k t"
  by (simp add: reach_all_circular)

lemma reach_lst_map_le_rlst [simp]:
  "reach tps s \<Longrightarrow> Lst_map_le_Rlst s cl k"
  by (simp add: reach_all_circular)

lemma reach_gst_le_min_lst_map [simp]:
  "reach tps s \<Longrightarrow> Gst_le_Min_Lst_map s k"
  by (simp add: reach_all_circular)

lemma lst_map_monotonic:
  assumes "state_trans s e s'"
    and "reach tps s"
  shows "lst_map (cls s cl) k \<le> lst_map (cls s' cl) k"
  using assms
  by (simp add: reach_all_circular lst_map_monotonic_dep)

lemma lst_map_min_monotonic:
  assumes "state_trans s e s'"
    and "reach tps s"
  shows "Min (range (lst_map (cls s cl))) \<le> Min (range (lst_map (cls s' cl)))"
  using assms
  by (simp add: reach_all_circular lst_map_min_monotonic_dep)

lemma reach_gst_lt_cl_cts [simp]: "reach tps s \<Longrightarrow> Gst_lt_Cl_Cts s cl k"
  by (simp add: reach_all_circular reach_gst_le_pd_dep reach_gst_lt_cl_cts_dep)

lemma reach_gst_le_pd [simp]: "reach tps s \<Longrightarrow> Gst_le_Pend_t s cl"
  by (simp add: reach_all_circular reach_gst_le_pd_dep)

definition Gst_lt_Cts where
  "Gst_lt_Cts s cl \<longleftrightarrow> (\<forall>k cts sts lst v rs. 
      svr_state (svrs s k) (get_wtxn s cl) = Commit cts sts lst v rs \<longrightarrow> gst (cls s cl) < cts)"
                                                           
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
    case (RInvoke x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Gst_lt_Cts_def tps_trans_defs)
      by (metis Fresh_wr_notin_Wts_dom_def insert_iff reach_fresh_wr_notin_wtxns_dom wtxns_domI2)
  next
    case (RDone x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Gst_lt_Cts_def tps_trans_defs)
      by (metis FTid_Wtxn_Inv_def lessI reach_ftid_wtxn_inv ver_state.distinct(5))
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Gst_lt_Cts_def tps_trans_defs)
      by (meson FTid_not_wr_def less_Suc_eq reach_ftid_not_wr wtxns_domI2)
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Gst_lt_Cts_def tps_trans_defs)
      by (meson add_to_readerset_commit)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      using Gst_le_Pend_t_def[of s] Pend_lt_Prep_def[of s] Prep_le_Cl_Cts_def[of s]
      apply (auto simp add: Gst_lt_Cts_def tps_trans_defs)
      by (meson leD leI order.trans)
  qed (auto simp add: Gst_lt_Cts_def tps_trans_defs)
qed


lemma gst_monotonic:
  assumes "state_trans s e s'"
    and "reach tps s"
  shows "gst (cls s' cl) \<ge> gst (cls s cl)"
  using assms using Gst_le_Min_Lst_map_def[of s]
  by (induction e) (auto simp add: tps_trans_defs)


definition Rtxn_Rts_le_Gst where
  "Rtxn_Rts_le_Gst s cl \<longleftrightarrow> (\<forall>n ts. rtxn_rts s (Tn_cl n cl) = Some ts \<longrightarrow> ts \<le> gst (cls s cl))"

lemmas Rtxn_Rts_le_GstI = Rtxn_Rts_le_Gst_def[THEN iffD2, rule_format]
lemmas Rtxn_Rts_le_GstE[elim] = Rtxn_Rts_le_Gst_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_rts_le_gst [simp]: "reach tps s \<Longrightarrow> Rtxn_Rts_le_Gst s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rtxn_Rts_le_Gst_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Rtxn_Rts_le_Gst_def cl_read_invoke_def cl_read_invoke_U_def)
      by (meson Gst_le_Min_Lst_map_def order.trans reach_gst_le_min_lst_map reach_gst_lt_cl_cts)
  qed (auto simp add: Rtxn_Rts_le_Gst_def tps_trans_defs)
qed


subsection \<open>Commit Order Invariants\<close>

definition CO_Tid where
  "CO_Tid s cl \<longleftrightarrow> (case cl_state (cls s cl) of
    WtxnCommit cts kv_map \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow> n \<le> cl_sn (cls s cl))
  | _ \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow> n < cl_sn (cls s cl)))"

lemmas CO_TidI = CO_Tid_def[THEN iffD2, rule_format]
lemmas CO_TidE[elim] = CO_Tid_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_tid[simp]: "reach tps s \<Longrightarrow> CO_Tid s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: CO_Tid_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RDone x1 x2 x3 x4 x5)
    then show ?case apply (simp add: CO_Tid_def tps_trans_defs split: txn_state.split_asm)
      using less_SucI less_Suc_eq_le by blast+
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: CO_Tid_def tps_trans_all_defs set_insort_key split: txn_state.split_asm)
      apply (metis txn_state.distinct(3))
      apply (metis txn_state.distinct(7))
      apply (meson less_or_eq_imp_le)
      by blast
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case apply (simp add: CO_Tid_def tps_trans_defs split: txn_state.split_asm)
      apply (meson less_SucI)+
      by (meson linorder_le_less_linear not_less_eq_eq)
  qed (auto simp add: CO_Tid_def tps_trans_defs split: txn_state.split_asm)
qed


end