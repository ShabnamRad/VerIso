section \<open>Tapir Falsification\<close>

theory "Tapir_Falsification"
  imports "Tapir"
begin

subsection \<open>Lemmas and Invariants\<close>

lemma occ_check_res:
  "occ_check k t ts rto wvo s \<in> {aborted, prepared ts rto wvo}"
  by (simp add: occ_check_def)

lemma occ_check_resE [elim]:
  "\<lbrakk>occ_check k t ts rto wvo s = X; X = aborted \<Longrightarrow> P ; X = prepared ts rto wvo \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (meson insertE occ_check_res singletonD)


lemma read_resp_abs_committed_reads_inv:
  assumes "svr_state (svrs s k) (Tn t) = idle"
  shows
    "abs_committed_reads (s \<lparr>svrs := (svrs s)
      (k := svrs s k \<lparr>svr_state := (svr_state (svrs s k)) (Tn t := read X)\<rparr>)\<rparr>) k' t_wr =
     abs_committed_reads s k' t_wr"
  using assms
  by (auto simp add: abs_committed_reads_def)

lemma prep_abs_committed_reads_inv:
  assumes "svr_state (svrs s k) (Tn t) = read X"
    and "cl_state (cls s (get_cl t)) = cl_prepared x y z"
  shows
    "abs_committed_reads (s \<lparr>svrs := (svrs s)
      (k := svrs s k \<lparr>svr_state := (svr_state (svrs s k)) (Tn t := occ_check a b c d e f)\<rparr>)\<rparr>) k' t_wr =
     abs_committed_reads s k' t_wr"
  using assms
  by (auto simp add: abs_committed_reads_def)

lemma commit_wr_abs_committed_reads_inv:
  assumes "svr_state (svrs s k) (Tn t) = prepared a b c"
    and "cl_state (cls s (get_cl t)) = cl_committed a d e"
  shows
    "abs_committed_reads (s \<lparr>svrs := (svrs s)
      (k := svrs s k \<lparr>
        svr_state := (svr_state (svrs s k)) (Tn t := committed a b c)\<rparr>)\<rparr>) k' t_wr =
     abs_committed_reads s k' t_wr"
  using assms
  by (auto simp add: abs_committed_reads_def)

lemma commit_rd_abs_committed_reads_inv:
  assumes "svr_state (svrs s k) (Tn t) = prepared a b c"
    and "cl_state (cls s (get_cl t)) = cl_committed a d e"
  shows
    "abs_committed_reads (s \<lparr>svrs := (svrs s)
      (k := svrs s k \<lparr>svr_state := (svr_state (svrs s k)) (Tn t := committed a b c)\<rparr>)\<rparr>) k' t_wr =
     abs_committed_reads s k' t_wr"
  using assms
  by (auto simp add: abs_committed_reads_def)

lemma abort_abs_committed_reads_inv:
  assumes "svr_state (svrs s k) (Tn t) \<in> {prepared a b c, aborted}"
    and "cl_state (cls s (get_cl t)) = cl_aborted"
  shows
    "abs_committed_reads (s \<lparr>svrs := (svrs s)
      (k := svrs s k \<lparr>svr_state := (svr_state (svrs s k)) (Tn t := aborted)\<rparr>)\<rparr>) k' t_wr =
     abs_committed_reads s k' t_wr"
  using assms
  by (auto simp add: abs_committed_reads_def)


lemma corder_sub_ext_corder:
  "t \<in> set (corder k) \<Longrightarrow> t \<in> set (ext_corder t wm corder k)"
  by (auto simp add: ext_corder_def)

definition T0_Committed where
  "T0_Committed s k \<longleftrightarrow> (is_committed_wr (svr_state (svrs s k) T0))"
                                                           
lemmas T0_CommittedI = T0_Committed_def[THEN iffD2, rule_format]
lemmas T0_CommittedE[elim] = T0_Committed_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_t0_committed [simp, dest]: "reach tapir s \<Longrightarrow> T0_Committed s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: T0_Committed_def tapir_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: T0_Committed_def tapir_trans_defs)
qed

definition CO_Non_Emp where
  "CO_Non_Emp s k \<longleftrightarrow> (commit_order s k \<noteq> [])"
                                                           
lemmas CO_Non_EmpI = CO_Non_Emp_def[THEN iffD2, rule_format]
lemmas CO_Non_EmpE[elim] = CO_Non_Emp_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_co_non_emp [simp, dest]: "reach tapir s \<Longrightarrow> CO_Non_Emp s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: CO_Non_Emp_def tapir_defs kvs_of_s_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: CO_Non_Emp_def tapir_trans_all_defs kvs_of_s_defs)
qed

definition KVS_Non_Emp where
  "KVS_Non_Emp s k \<longleftrightarrow> (kvs_of_s s k \<noteq> [])"
                                                           
lemmas KVS_Non_EmpI = KVS_Non_Emp_def[THEN iffD2, rule_format]
lemmas KVS_Non_EmpE[elim] = KVS_Non_Emp_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_kvs_non_emp [simp, dest]: "reach tapir s \<Longrightarrow> KVS_Non_Emp s k"
  using CO_Non_Emp_def[of s]
  by (simp add: KVS_Non_Emp_def kvs_of_s_def)

definition CO_Tn_is_Cmt_Abs where
  "CO_Tn_is_Cmt_Abs s k \<longleftrightarrow> (\<forall>n cl. Tn (Tn_cl n cl) \<in> set (commit_order s k) \<longrightarrow>
    (is_committed_wr (svr_state (svrs s k) (Tn (Tn_cl n cl)))) \<or> 
    (is_prepared_wr (svr_state (svrs s k) (Tn (Tn_cl n cl))) \<and> 
     (\<exists>ts r_map w_map. cl_state (cls s cl) = cl_committed ts r_map w_map \<and> 
      cl_sn (cls s cl) = n \<and> k \<in> dom w_map)))"

lemmas CO_Tn_is_Cmt_AbsI = CO_Tn_is_Cmt_Abs_def[THEN iffD2, rule_format]
lemmas CO_Tn_is_Cmt_AbsE[elim] = CO_Tn_is_Cmt_Abs_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_tn_is_cmt_abs [simp]: "reach tapir s \<Longrightarrow> CO_Tn_is_Cmt_Abs s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: CO_Tn_is_Cmt_Abs_def tapir_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Cl_Issue x1 x2 x3)
    then show ?case
      apply (simp add: CO_Tn_is_Cmt_Abs_def tapir_trans_defs)
      by (metis cl_state.distinct(5))
  next
    case (Cl_Read_Resp x1 x2 x3 x4)
    then show ?case
      apply (simp add: CO_Tn_is_Cmt_Abs_def tapir_trans_defs)
      by (metis cl_state.distinct(11))
  next
    case (Cl_Prep x1 x2 x3 x4)
    then show ?case
      apply (simp add: CO_Tn_is_Cmt_Abs_def tapir_trans_defs)
      by (metis cl_state.distinct(11))
  next
    case (Cl_Commit x1 x2 x3 x4 x5a x6 x7)
    then show ?case
      apply (simp add: CO_Tn_is_Cmt_Abs_def tapir_trans_all_defs)
      by (metis (lifting) Un_iff cl_state.distinct(15) domIff is_prepared_wr.simps(1) option.discI)
  next
    case (Cl_Abort x)
    then show ?case
      apply (simp add: CO_Tn_is_Cmt_Abs_def tapir_trans_defs)
      by (metis cl_state.distinct(15))
  next
    case (Cl_ReadyC x1 x2)
    then show ?case
      apply (simp add: CO_Tn_is_Cmt_Abs_def tapir_trans_defs)
      by (metis Un_iff cl_state.inject(3) is_prepared_wr.simps(5))
  next
    case (Cl_ReadyA x1 x2)
    then show ?case
      apply (simp add: CO_Tn_is_Cmt_Abs_def tapir_trans_defs)
      by (metis is_prepared_wr.simps(6))
  next
    case (Read_Resp x1 x2 x3)
    then show ?case
      apply (simp add: CO_Tn_is_Cmt_Abs_def tapir_trans_defs)
      by (metis is_committed_wr.simps(2) is_prepared_wr.simps(2))
  next
    case (Prep x1 x2 x3 x4 x5a)
    then show ?case
      apply (simp add: CO_Tn_is_Cmt_Abs_def tapir_trans_defs)
      by (metis is_committed_wr.simps(3) is_prepared_wr.simps(3))
  next
    case (Commit x1 x2 x3 x4 x5a)
    then show ?case
      apply (simp add: CO_Tn_is_Cmt_Abs_def tapir_trans_defs)
      by (metis is_committed_wr.simps(1,4) is_prepared_wr.elims(2) svr_state.inject(2))
  next
    case (Abort x1 x2)
    then show ?case
      apply (simp add: CO_Tn_is_Cmt_Abs_def tapir_trans_defs)
      by (metis cl_state.distinct(19) is_committed_wr.simps(4,6) txid0.sel(2))
   qed simp
qed

definition is_committed_in_kvs where
  "is_committed_in_kvs s k t \<equiv> 
    is_committed_wr (svr_state (svrs s k) t) \<or> 
    (is_prepared_wr (svr_state (svrs s k) t) \<and>
     (\<exists>ts r_map w_map. cl_state (cls s (get_cl_w t)) = cl_committed ts r_map w_map \<and> k \<in> dom w_map))"

definition CO_is_Cmt_Abs where
  "CO_is_Cmt_Abs s k \<longleftrightarrow> (\<forall>t. t \<in> set (commit_order s k) \<longrightarrow> is_committed_in_kvs s k t)"

lemmas CO_is_Cmt_AbsI = CO_is_Cmt_Abs_def[THEN iffD2, rule_format]
lemmas CO_is_Cmt_AbsE[elim] = CO_is_Cmt_Abs_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_is_cmt_abs [simp]: "reach tapir s \<Longrightarrow> CO_is_Cmt_Abs s k"
  using CO_Tn_is_Cmt_Abs_def[of s k]
  apply (simp add: CO_is_Cmt_Abs_def is_committed_in_kvs_def)
  by (metis T0_Committed_def get_cl_w.elims reach_t0_committed)

definition CO_not_non_cmt where
  "CO_not_non_cmt s k \<longleftrightarrow> (\<forall>t \<in> set (commit_order s k).
    \<forall>rto ts r_map. svr_state (svrs s k) t
      \<notin> {idle, read rto, prepared ts r_map None, committed ts r_map None, aborted})"

lemmas CO_not_non_cmtI = CO_not_non_cmt_def[THEN iffD2, rule_format]
lemmas CO_not_non_cmtE[elim] = CO_not_non_cmt_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_not_no_ver [simp, dest]: "reach tapir s \<Longrightarrow> CO_not_non_cmt s k"
  using CO_is_Cmt_Abs_def[of s k]
  by (auto simp add: CO_not_non_cmt_def is_committed_in_kvs_def)

lemma v_writer_kvs_of_s_nth:
  "reach tapir s \<Longrightarrow> i < length (kvs_of_s s k) \<Longrightarrow> v_writer (kvs_of_s s k ! i) = commit_order s k ! i"
  using CO_not_non_cmt_def[of s k]
  apply (auto simp add: kvs_of_s_defs is_committed_in_kvs_def split: svr_state.split)
  by (metis nth_mem option.case_eq_if version.ext_inject version.surjective)+

lemma length_kvs_of_s:
  "length (kvs_of_s s k) = length (commit_order s k)"
  by (simp add: kvs_of_s_def)

definition KVS_T0_Init where
  "KVS_T0_Init s \<longleftrightarrow> (kvs_T0_init (kvs_of_s s))"
                                                           
lemmas KVS_T0_InitI = KVS_T0_Init_def[THEN iffD2, rule_format]
lemmas KVS_T0_InitE[elim] = KVS_T0_Init_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_kvs_t0_init [simp, dest]: "reach tapir s \<Longrightarrow> KVS_T0_Init s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: KVS_T0_Init_def kvs_T0_init_def tapir_defs kvs_of_s_defs)
next
  case (reach_trans s e s')
  then have "reach tapir s'" by blast
  then show ?case using reach_trans
  proof (induction e)
    case (Cl_Commit x1 x2 x3 x4 x5a x6 x7)
    then show ?case 
      apply (auto simp add: KVS_T0_Init_def kvs_T0_init_def tapir_trans_all_defs v_writer_kvs_of_s_nth
          length_kvs_of_s full_view_def)
      apply (metis full_view_def full_view_elemI length_kvs_of_s less_antisym nth_append
          nth_append_length txid.distinct(1))
      by (metis CO_Non_Emp_def reach_co_non_emp append_Cons length_greater_0_conv lessThan_iff
          neq_Nil_conv nth_Cons_0)
  qed (auto simp add: KVS_T0_Init_def kvs_T0_init_def tapir_trans_defs v_writer_kvs_of_s_nth
      length_kvs_of_s full_view_def)
qed


definition Finite_Committed where
  "Finite_Committed s k \<longleftrightarrow> (finite {t. is_committed_wr (svr_state (svrs s k) t)})"
                                                           
lemmas Finite_CommittedI = Finite_Committed_def[THEN iffD2, rule_format]
lemmas Finite_CommittedE[elim] = Finite_Committed_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_finite_committed [simp, dest]: "reach tapir s \<Longrightarrow> Finite_Committed s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Finite_Committed_def tapir_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Prep x1 x2 x3 x4 x5a)
    then show ?case
      apply (simp add: Finite_Committed_def tapir_trans_defs)
      by (smt (verit, best) Collect_cong is_committed_wr.elims(2) is_committed_wr.simps(3)
          is_committed_wr.simps(6) occ_check_resE svr_state.distinct(15))
  next
    case (Commit x1 x2 x3 x4 x5a)
    then have "finite (insert (Tn x2) {t. is_committed_wr (svr_state (svrs s k) t)})" by auto
    then show ?case using Commit
      by (auto simp add: Finite_Committed_def tapir_trans_defs insert_Collect)
  qed (auto simp add: Finite_Committed_def tapir_trans_defs Collect_mono rev_finite_subset)
qed

definition Finite_Committed_Ts where
  "Finite_Committed_Ts s k \<longleftrightarrow>
    (finite {ts. \<exists>t. is_committed_wr (svr_state (svrs s k) t) \<and> ts = v_ts (svr_state (svrs s k) t)})"

lemmas Finite_Committed_TsI = Finite_Committed_Ts_def[THEN iffD2, rule_format]
lemmas Finite_Committed_TsE[elim] = Finite_Committed_Ts_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_finite_committed_ts [simp, dest]: "reach tapir s \<Longrightarrow> Finite_Committed_Ts s k"
  using Finite_Committed_def[of s] by (simp add: Finite_Committed_Ts_def)

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

definition Latest_Committed_Wtxn where
  "Latest_Committed_Wtxn s k \<longleftrightarrow> (\<exists>t. latest_committed_wtxn s k t)"

lemmas Latest_Committed_WtxnI = Latest_Committed_Wtxn_def[THEN iffD2, rule_format]
lemmas Latest_Committed_WtxnE[elim] = Latest_Committed_Wtxn_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_latest_committed_wtxn [simp, dest]: "reach tapir s \<Longrightarrow> Latest_Committed_Wtxn s k"
  using T0_Committed_def[of s k] Finite_Committed_Ts_def[of s k]
  by (auto simp add: Latest_Committed_Wtxn_def arg_max_exI)


definition Read_Twr_Cmt where
  "Read_Twr_Cmt s k \<longleftrightarrow> (\<forall>t t_wr ts wvo.
    svr_state (svrs s k) t \<in> {read (Some t_wr),
                              prepared ts (Some t_wr) wvo,
                              committed ts (Some t_wr) wvo} \<longrightarrow> 
    is_committed_wr (svr_state (svrs s k) t_wr))"
                                                           
lemmas Read_Twr_CmtI = Read_Twr_Cmt_def[THEN iffD2, rule_format]
lemmas Read_Twr_CmtE[elim] = Read_Twr_Cmt_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_read_t_wr_cmt [simp, dest]: "reach tapir s \<Longrightarrow> Read_Twr_Cmt s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Read_Twr_Cmt_def tapir_defs split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Read_Resp x1 x2 x3)
    then show ?case
    proof (cases "k = x1")
      case True
      then show ?thesis unfolding Read_Twr_Cmt_def
      proof (intro allI)
        fix t t_wr ts wvo
        show "svr_state (svrs s' k) t \<in> {read (Some t_wr),
                                         prepared ts (Some t_wr) wvo,
                                         committed ts (Some t_wr) wvo} \<longrightarrow>
          is_committed_wr (svr_state (svrs s' k) t_wr)"
        proof (cases "t = Tn x2")
          case True
          then show ?thesis
            using Read_Resp(1,2) \<open>k = x1\<close> Latest_Committed_Wtxn_def[of s x1]
            apply (auto simp add: tapir_trans_defs split: if_split_asm)
            apply (metis is_arg_max_def is_committed_wr.simps(2) some_eq_imp)
            by (metis is_arg_max_def some_eq_imp)
        next
          case False
          then show ?thesis using Read_Resp \<open>k = x1\<close>
            apply (auto simp add: Read_Twr_Cmt_def tapir_trans_defs)
            by (metis is_committed_wr.simps(2))+
        qed
      qed
    qed (auto simp add: tapir_trans_defs Read_Twr_Cmt_def)
  next
    case (Prep x1 x2 x3 x4 x5a)
    then show ?case
      apply (auto simp add: Read_Twr_Cmt_def tapir_trans_defs)
      apply (metis is_committed_wr.simps(3) occ_check_resE svr_state.distinct(17) svr_state.inject(2))
      by (metis is_committed_wr.simps(3))+
  next
    case (Commit x1 x2 x3 x4 x5a)
    then show ?case
      apply (auto simp add: Read_Twr_Cmt_def tapir_trans_defs)
      by (metis is_committed_wr.simps(4))+
  next
    case (Abort x1 x2)
    then show ?case
      apply (simp add: Read_Twr_Cmt_def tapir_trans_defs)
      by (metis is_committed_wr.simps(4) is_committed_wr.simps(6))
  qed (auto simp add: Read_Twr_Cmt_def tapir_trans_defs)
qed

definition CO_Tid where
  "CO_Tid s cl \<longleftrightarrow> (case cl_state (cls s cl) of
    cl_committed ts r_map w_map  \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (commit_order s k) \<longrightarrow> n \<le> cl_sn (cls s cl))
  | _ \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (commit_order s k) \<longrightarrow> n < cl_sn (cls s cl)))"

lemmas CO_TidI = CO_Tid_def[THEN iffD2, rule_format]
lemmas CO_TidE[elim] = CO_Tid_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_tid[simp]: "reach tapir s \<Longrightarrow> CO_Tid s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: CO_Tid_def tapir_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Cl_Commit x1 x2 x3 x4 x5a x6 x7)
    then show ?case using Cl_Commit
      apply (auto simp add: CO_Tid_def tapir_trans_defs ext_corder_def
                  split: cl_state.split cl_state.split_asm)
      using less_or_eq_imp_le by blast+
  next
    case (Cl_ReadyC x1 x2)
    then show ?case
      apply (auto simp add: CO_Tid_def tapir_trans_defs split: cl_state.split_asm)
      using less_Suc_eq_le by blast
  next
    case (Cl_ReadyA x1 x2)
    then show ?case
      apply (auto simp add: CO_Tid_def tapir_trans_defs split: cl_state.split_asm)
      using less_SucI by blast
  qed (auto simp add: CO_Tid_def tapir_trans_defs split: cl_state.split_asm)
qed

lemma kvs_of_s_initialized [simp, dest]:
  "reach tapir s \<Longrightarrow> kvs_initialized (kvs_of_s s)"
  by (auto simp add: kvs_initialized_def)

fun commit_ev :: "'v ev \<Rightarrow> bool" where
  "commit_ev (Cl_Commit _ _ _ _ _ _ _) = True" |
  "commit_ev _ = False"

lemma commit_order_inv:
  assumes "reach tapir s"
    and "s_trans s e s'"
    and "\<not>commit_ev e"
  shows "commit_order s' = commit_order s"
  using assms
  by (induction e) (auto simp add: tapir_trans_defs)

lemma kvs_of_s_inv:
  assumes "reach tapir s"
    and "s_trans s e s'"
    and "\<not>commit_ev e"
  shows "kvs_of_s s' = kvs_of_s s"
proof -
  have "reach tapir s'" using assms(1,2) by auto
  then show ?thesis
    using assms commit_order_inv[of s e s'] CO_not_non_cmt_def[of s] CO_not_non_cmt_def[of s']
  proof (auto simp add: kvs_of_s_defs, induction e)
    case (Cl_ReadyC x1 x2)
    then show ?case sorry
  next
    case (Cl_ReadyA x1 x2)
    then show ?case sorry
  next
    case (Read_Resp x1 x2 x3)
    then show ?case sorry
  next
    case (Prep x1 x2 x3 x4 x5a)
    then show ?case sorry
  next
    case (Commit x1 x2 x3 x4 x5a)
    then show ?case sorry
  next
    case (Abort x1 x2)
    then show ?case sorry
  qed (auto intro!: ext simp add: tapir_trans_defs abs_committed_reads_def
    split: svr_state.split option.split)
qed


subsection \<open>Refinement Attempt\<close>

abbreviation invariants_list where                                   
  "invariants_list s \<equiv> (\<forall>k. KVS_Non_Emp s k) \<and> (KVS_T0_Init s) \<and> (\<forall>k. T0_Committed s k) \<and>
    (\<forall>k. Finite_Committed s k) \<and> (\<forall>k. Read_Twr_Cmt s k) \<and> (\<forall>cl. CO_Tid s cl)"

lemma tps_refines_et_es: "tapir \<sqsubseteq>\<^sub>med ET_SER.ET_ES"
proof (intro simulate_ES_fun)
  fix gs0 :: "'v global_conf"
  assume p: "init tapir gs0"
  then show "init ET_SER.ET_ES (sim gs0)"
    by (auto simp add: ET_SER.ET_ES_defs tapir_defs sim_all_defs kvs_init_def v_list_init_def 
                       version_init_def)
next
  fix gs a and gs' :: "'v global_conf"
  assume p: "tapir: gs\<midarrow>a\<rightarrow> gs'" and reach_s: "reach tapir gs" and "reach ET_SER.ET_ES (sim gs)"
  then have reach_s': "reach tapir gs'" by auto
  with reach_s have I: "invariants_list gs" and I': "invariants_list gs'" by auto
  with p show "ET_SER.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  proof (induction a)
    case (Cl_Commit cl sn u'' F ts r_map w_map)
    show ?case 
    proof -
      { 
        assume cmt: \<open>cl_commit cl sn u'' F ts r_map w_map gs gs'\<close>
        have \<open>ET_SER.ET_trans_and_fp 
                (kvs_of_s gs, views_of_s gs) (ET cl sn u'' F) (kvs_of_s gs', views_of_s gs')\<close>
        proof (rule ET_SER.ET_trans_rule [where u'="view_init"])
          show \<open>views_of_s gs cl \<sqsubseteq> u''\<close> using cmt reach_s
            by (auto simp add: cl_commit_def views_of_s_def)
        next 
          show \<open>ET_SER.canCommit (kvs_of_s gs) u'' F\<close> using cmt
            by (auto simp add: cl_commit_def full_view_satisfies_ET_SER_canCommit)
        next 
          show \<open>view_wellformed (kvs_of_s gs) u''\<close> using cmt reach_s
            by (auto simp add: cl_commit_def)
        next 
          show \<open>view_wellformed (kvs_of_s gs') view_init\<close> using cmt reach_s' by auto
        next 
          show \<open>view_wellformed (kvs_of_s gs) (views_of_s gs cl)\<close> using reach_s
            by (auto simp add: views_of_s_def)
        next 
          show \<open>Tn_cl sn cl \<in> next_txids (kvs_of_s gs) cl\<close> using cmt (*I
            by (auto simp add: cl_commit_def t_is_fresh)*) sorry
        next 
          show \<open>fp_property F (kvs_of_s gs) u''\<close> unfolding fp_property_def
          proof (intro allI impI)
            fix k
            assume "R \<in> dom (F k)"
            then obtain t_wr where "r_map k = Some t_wr" using cmt
              apply (auto simp add: cl_commit_def)
              using \<open>R \<in> dom (F k)\<close> domIff fun_upd_apply op_type.distinct(1) by force
            then obtain ts' rto' v where "svr_state (svrs gs k) t_wr = committed ts' rto' (Some v)"
              using cmt reach_s Read_Twr_Cmt_def[of gs]
              apply (auto simp add: cl_commit_def)
              by (metis Un_iff domI is_committed_wr.elims(2))
            then show "F k R = Some (view_snapshot (kvs_of_s gs) u'' k)"
              using cmt \<open>r_map k = Some t_wr\<close>
              apply (auto simp add: cl_commit_def view_snapshot_def)
              (* Invariant: there is no timestamp inversion *)
              (*apply (cases "svr_state (svrs gs k) (get_txn cl gs) = no_lock")
              subgoal by (auto simp add: NoLockFpInv_def invariant_list_def)
              subgoal by (smt (verit) RLockFpContentInv_def WLockFpContentInv_def
                                      empty_iff insertCI insertE invariant_listE o_apply 
                                      option.distinct(1) option.inject svr_vl_kvs_eq_lv) 
              done*) sorry
          qed
        next 
          show \<open>kvs_of_s gs' = update_kv (Tn_cl sn cl) F u'' (kvs_of_s gs)\<close> using cmt (*I
            by (auto 4 3 simp add: cl_commit_def kvs_of_gs_def update_kv_def 
                                   kvs_of_gs_cl_commit svr_cl_cl'_unchanged_def)*) sorry
        next 
          show \<open>views_of_s gs' = (views_of_s gs) (cl := view_init)\<close>
            by (auto simp add: views_of_s_def)
        qed simp
      }
      then show ?thesis using Cl_Commit
        by (simp only: ET_SER.trans_ET_ES_eq tapir_trans s_trans.simps sim_def med.simps)
    qed
  next
    case (Cl_Issue x1 x2 x3)
    then show ?case
      apply (auto simp add: sim_def tapir_trans_defs)
      by (rule ext, auto simp add: sim_all_defs split: svr_state.split option.split)
  next
    case (Cl_Read_Resp x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: sim_def tapir_trans_defs)
      by (rule ext, auto simp add: sim_all_defs split: svr_state.split option.split)
  next
    case (Cl_Prep x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: sim_def tapir_trans_defs)
      by (rule ext, auto simp add: sim_all_defs split: svr_state.split option.split)
  next
    case (Cl_Abort x)
    then show ?case
      apply (auto simp add: sim_def tapir_trans_defs)
      by (rule ext, auto simp add: sim_all_defs split: svr_state.split option.split)+
  next
    case (Cl_ReadyC x1 x2)
    then show ?case
      apply (auto simp add: sim_def tapir_trans_defs)
       apply (rule ext, auto simp add: sim_all_defs split: svr_state.split option.split)
      (* inv: new (uncommitted) write is not read by any transactions *)sorry
  next
    case (Cl_ReadyA x1 x2)
    then show ?case
      apply (auto simp add: sim_def tapir_trans_defs)
      by (rule ext, auto simp add: sim_all_defs split: svr_state.split option.split)
  next
    case (Read_Resp x1 x2 x3)
    then show ?case
      using read_resp_abs_committed_reads_inv[of gs]
      apply (auto simp add: sim_defs tapir_trans_defs)
      by (rule ext, auto split: svr_state.split)
  next
    case (Prep x1 x2 x3 x4 x5)
    then show ?case
      using prep_abs_committed_reads_inv[of gs] CO_Tid_def[of gs] reach_s
      apply (auto simp add: sim_defs tapir_trans_defs)
      apply (rule ext, auto split: svr_state.split)
      by (metis (no_types, lifting) cl_state.simps(26) nless_le txid0.collapse)
  next
    case (Commit x1 x2 x3 x4 x5)
    then show ?case
      using commit_wr_abs_committed_reads_inv[of gs]
            commit_rd_abs_committed_reads_inv[of gs]
      apply (auto simp add: sim_defs tapir_trans_defs)
       apply (rule ext, auto split: svr_state.split)+
      (* inv: newly committed version's readerset is empty *)
      sorry
  next
    case (Abort x1 x2)
    then show ?case
      using abort_abs_committed_reads_inv[of gs]
      apply (auto simp add: sim_defs tapir_trans_defs)
       apply (rule ext, auto split: svr_state.split)+
      (* inv: aborted txn not in commit_order *) sorry
  qed simp                            
qed

end
