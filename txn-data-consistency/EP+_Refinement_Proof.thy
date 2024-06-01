section \<open>Eiger Port Plus Protocol Satisfying CCv (Causal+) - Proofs and lemmas\<close>

theory "EP+_Refinement_Proof"
  imports "EP+_Sorted" "EP+_Trace"
begin


subsection \<open>(New) helper functions lemmas\<close>

\<comment> \<open>index_of\<close>
lemma index_of_nth:
  "distinct xs \<Longrightarrow> i' < length xs \<Longrightarrow> index_of xs (xs ! i') = i'"
  apply (intro the1_equality, simp_all)
  by (metis distinct_Ex1 in_set_conv_nth)

lemma index_of_append:
  assumes 
    "distinct (xs @ [t'])"
    "t \<in> set xs"
  shows "index_of (xs @ [t']) t = index_of xs t"
proof -
  obtain i where i_: "i < length xs" "xs ! i = t" using assms(2)
    by (meson in_set_conv_nth)
  then have "index_of (xs @ [t']) t = i"
    using index_of_nth[OF assms(1), of i]
    by (simp add: nth_append)
  then show ?thesis
    using i_ assms(1) index_of_nth rotate1.simps(2) by fastforce
qed

lemma index_of_neq:
  assumes "distinct xs"
    and "a \<noteq> b"
    and "a \<in> set xs"
    and "b \<in> set xs"
  shows "index_of xs a \<noteq> index_of xs b"
  using assms
  apply auto
  by (smt (verit, del_insts) distinct_Ex1 the_equality)

lemma index_of_nth_rev:
  assumes "index_of xs x = i"
    "i < length xs"
    "distinct xs"
    "x \<in> set xs"
  shows "x = xs ! i"
  using assms index_of_nth index_of_neq
  by fastforce

lemma index_of_p:
  "distinct ts \<Longrightarrow> (t \<notin> set ts \<or> index_of ts t < length ts) \<and> (t \<notin> set ts \<or> ts ! index_of ts t = t)"
  apply auto
  apply (smt exists_least_iff in_set_conv_nth nth_eq_iff_index_eq theI)
  by (smt distinct_Ex1 the_equality)

lemma the_the_equality:
  "\<lbrakk> P a; \<And>y. P y \<Longrightarrow> y = a; \<And>x. Q x \<longleftrightarrow> P x \<rbrakk> \<Longrightarrow> (THE x. P x) = (THE x. Q x)"
  by (rule theI2) auto


\<comment> \<open>lists\<close>
lemma distinct_prefix:
  "\<lbrakk> distinct xs; prefix xs' xs \<rbrakk> \<Longrightarrow> distinct xs'"
  by (metis distinct_append prefixE)

lemma nth_eq_prefix:
  "\<lbrakk> i < length xs; prefix xs ys \<rbrakk> \<Longrightarrow> xs ! i = ys ! i"
  by (metis nth_append prefix_def)

lemma nth_distinct_injective:
  "\<lbrakk> xs ! i = xs ! j; i < length xs; j < length xs; distinct xs \<rbrakk> \<Longrightarrow> i = j"
  using nth_eq_iff_index_eq by blast

\<comment> \<open>view_of\<close>
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


lemma view_of_deps_mono:
  assumes "\<forall>k. u k \<subseteq> u' k"
  shows "view_of cord u \<sqsubseteq> view_of cord u'"
  using assms
  by (auto simp add: view_of_def view_order_def)

text \<open>Note: we must have @{prop "distinct corder"} for @{term view_of} to be well-defined. \<close>

lemma view_of_mono: 
  assumes "\<forall>k. u k \<subseteq> u' k"
    and "\<And>k. prefix (cord k) (cord' k)"
    and "\<And>k. distinct (cord' k)" 
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

lemma view_of_update:
  assumes 
    "i = length (cord k)"  
    "cord' k = cord k @ [t]"
    "t \<notin> set (cord k)"
    "t \<in> u k"
  shows "i \<in> view_of cord' u k"
  using assms
  apply (auto simp add: view_of_def)
  apply (rule exI[where x=t])
  apply (auto simp add: nth_append in_set_conv_nth intro: the_equality[symmetric] 
              split: if_split_asm)
  done


subsection \<open>Commit Timestamps Order Invariants\<close>

lemma T0_min_unique_ts:
  assumes "reach tps_s s"
  shows "unique_ts (wtxn_cts s) (Tn t) > unique_ts (wtxn_cts s) T0"
  using assms Wtxn_Cts_T0_def[of s]
    unique_ts_def ects_def min_ects by auto

lemma insort_key_pres_T0:
  "l ! 0 = x \<Longrightarrow> x \<in> set l \<Longrightarrow> f x < f t \<Longrightarrow> insort_key f t l ! 0 = x"
  by (cases l, auto)

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
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then have "reach tps_s s'" by blast
    then show ?case using WCommit
      apply (auto simp add: T0_First_in_CO_def tps_trans_all_defs intro!: insort_key_pres_T0)
      using T0_min_unique_ts[of s'] by auto
  qed (auto simp add: T0_First_in_CO_def tps_trans_all_defs)
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
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: CO_Distinct_def tps_trans_all_defs distinct_insort)
      by (metis (no_types, lifting) CO_Tid_def less_irrefl_nat reach_tps reach_co_tid txn_state.simps(18))
  qed (simp_all add: CO_Distinct_def tps_trans_defs)
qed

definition CO_Tn_is_Cmt_Abs where
  "CO_Tn_is_Cmt_Abs s k \<longleftrightarrow> (\<forall>n cl. Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow>
    (\<exists>cts sts lst v rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts sts lst v rs) \<or> 
    ((\<exists>pd ts v. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Prep pd ts v) \<and> 
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
    case (RInvoke x1 x2 x3 x4 x5)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_defs)
      by (metis txn_state.distinct(5))
  next
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_defs)
      by (metis txn_state.distinct(9))
  next
    case (RDone x1 x2 x3 x4 x5)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_defs)
      by (metis txn_state.distinct(9))
  next
    case (WInvoke x1 x2 x3 x4)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_defs)
      by (metis txn_state.distinct(5))
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_all_defs set_insort_key)
      by (smt (verit) domIff is_prepared.elims(2) option.discI txn_state.distinct(11))
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_defs)
      by (metis (no_types, lifting) txn_state.inject(3))
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_defs)
      by (metis add_to_readerset_commit' add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_defs)
      by (metis ver_state.distinct(3))
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: CO_Tn_is_Cmt_Abs_def tps_trans_defs)
      by (smt (z3) fun_upd_apply txn_state.simps(19) ver_state.simps(10))
  qed
qed

definition is_committed_in_kvs where
  "is_committed_in_kvs s k t \<equiv> 
    is_committed (svr_state (svrs s k) t) \<or> 
    (is_prepared (svr_state (svrs s k) t) \<and>
     (\<exists>cts kv_map. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map \<and> k \<in> dom kv_map))"

definition CO_is_Cmt_Abs where
  "CO_is_Cmt_Abs s k \<longleftrightarrow> (\<forall>t. t \<in> set (cts_order s k) \<longrightarrow> is_committed_in_kvs s k t)"

lemmas CO_is_Cmt_AbsI = CO_is_Cmt_Abs_def[THEN iffD2, rule_format]
lemmas CO_is_Cmt_AbsE[elim] = CO_is_Cmt_Abs_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_is_cmt_abs [simp]: "reach tps_s s \<Longrightarrow> CO_is_Cmt_Abs s k"
  apply (simp add: CO_is_Cmt_Abs_def is_committed_in_kvs_def)
  apply rule subgoal for t apply (cases t)
     apply (metis Init_Ver_Inv_def is_committed.simps(1) reach_init_ver_inv reach_tps)
    using CO_Tn_is_Cmt_Abs_def[of s k]
    by (metis get_cl_w_Tn is_committed.simps(1) is_prepared.simps(1) reach_co_tn_is_cmt_abs txid0.collapse).

definition CO_not_No_Ver where
  "CO_not_No_Ver s k \<longleftrightarrow> (\<forall>t \<in> set (cts_order s k). svr_state (svrs s k) t \<noteq> No_Ver)"

lemmas CO_not_No_VerI = CO_not_No_Ver_def[THEN iffD2, rule_format]
lemmas CO_not_No_VerE[elim] = CO_not_No_Ver_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_not_no_ver [simp]: "reach tps_s s \<Longrightarrow> CO_not_No_Ver s k"
  apply (auto simp add: CO_not_No_Ver_def)
  using CO_is_Cmt_Abs_def is_committed_in_kvs_def
  by (metis is_committed.simps(2) is_prepared.simps(2) reach_co_is_cmt_abs)

definition CO_has_Cts where
  "CO_has_Cts s k \<longleftrightarrow> (\<forall>t \<in> set (cts_order s k). \<exists>cts. wtxn_cts s t = Some cts)"

lemmas CO_has_CtsI = CO_has_Cts_def[THEN iffD2, rule_format]
lemmas CO_has_CtsE[elim] = CO_has_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_has_cts [simp]: "reach tps_s s \<Longrightarrow> CO_has_Cts s k"
  apply (simp add: CO_has_Cts_def)
  apply rule subgoal for t apply (cases t)
    using Init_Ver_Inv_def Committed_Abs_has_Wtxn_Cts_def[of s k] reach_cmt_abs_wtxn_cts
    apply (metis reach_tps reach_init_ver_inv)
    by (metis CO_Tn_is_Cmt_Abs_def[of s] Committed_Abs_has_Wtxn_Cts_def WtxnCommit_Wtxn_Cts_def reach_tps
        reach_co_tn_is_cmt_abs reach_cmt_abs_wtxn_cts reach_wtxncommit_wtxn_cts txid0.exhaust).

definition Committed_Abs_Tn_in_CO where
  "Committed_Abs_Tn_in_CO s k \<longleftrightarrow> (\<forall>n cl.
    (\<exists>cts sts lst v rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts sts lst v rs) \<or> 
    ((\<exists>pd ts v. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Prep pd ts v) \<and> 
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
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Committed_Abs_Tn_in_CO_def tps_trans_all_defs set_insort_key)
      by (metis (no_types, lifting) Cl_Prep_Inv_def domIff reach_tps reach_cl_prep_inv ver_state.distinct(1))
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Committed_Abs_Tn_in_CO_def tps_trans_defs)
      by (smt (verit) add_to_readerset_commit add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Committed_Abs_Tn_in_CO_def tps_trans_defs)
      by (metis get_cl_w.simps(2) txn_state.distinct(11) txid0.collapse)
  qed (auto simp add: Committed_Abs_Tn_in_CO_def tps_trans_defs)
qed

definition Committed_Abs_in_CO where
  "Committed_Abs_in_CO s k \<longleftrightarrow> (\<forall>t. is_committed_in_kvs s k t \<longrightarrow> t \<in> set (cts_order s k))"

lemmas Committed_Abs_in_COI = Committed_Abs_in_CO_def[THEN iffD2, rule_format]
lemmas Committed_Abs_in_COE[elim] = Committed_Abs_in_CO_def[THEN iffD1, elim_format, rule_format]

lemma reach_cmt_abs_in_co [simp]: "reach tps_s s \<Longrightarrow> Committed_Abs_in_CO s k"
  apply (simp add: Committed_Abs_in_CO_def is_committed_in_kvs_def)
  apply rule subgoal for t apply (cases t, blast)
    using Committed_Abs_Tn_in_CO_def[of s k]
    by (metis Prep_is_Curr_wt_def get_sn_w.simps(2) is_committed.elims(2) is_committed.elims(3)
        reach_tps get_cl_w_Tn is_prepared.simps(2) reach_cmt_abs_tn_in_co reach_prep_is_curr_wt
        txid0.collapse).


definition CO_Sub_Wtxn_Cts where
  "CO_Sub_Wtxn_Cts s k \<longleftrightarrow> set (cts_order s k) \<subseteq> dom (wtxn_cts s)"

lemmas CO_Sub_Wtxn_CtsI = CO_Sub_Wtxn_Cts_def[THEN iffD2, rule_format]
lemmas CO_Sub_Wtxn_CtsE[elim] = CO_Sub_Wtxn_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_sub_wtxn_cts[simp, dest]:
  "reach tps_s s \<Longrightarrow> CO_Sub_Wtxn_Cts s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: CO_Sub_Wtxn_Cts_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
    by (induction e)
      (auto simp add: CO_Sub_Wtxn_Cts_def tps_trans_all_defs set_insort_key)
qed


definition Wtxn_Cts_Tn_is_Abs_Cmt where
  "Wtxn_Cts_Tn_is_Abs_Cmt s cl k \<longleftrightarrow> (\<forall>n cts. wtxn_cts s (Tn (Tn_cl n cl)) = Some cts \<and>
    Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow>
    (\<exists>sts lst v rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts sts lst v rs) \<or> 
    ((\<exists>pd ts v. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Prep pd ts v) \<and> 
     (\<exists>kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<and>
        cl_sn (cls s cl) = n \<and> k \<in> dom kv_map)))"

lemmas Wtxn_Cts_Tn_is_Abs_CmtI = Wtxn_Cts_Tn_is_Abs_Cmt_def[THEN iffD2, rule_format]
lemmas Wtxn_Cts_Tn_is_Abs_CmtE[elim] = Wtxn_Cts_Tn_is_Abs_Cmt_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_cts_tn_is_abs_cmt [simp]: "reach tps_s s \<Longrightarrow> Wtxn_Cts_Tn_is_Abs_Cmt s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Wtxn_Cts_Tn_is_Abs_Cmt_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case using CO_Tn_is_Cmt_Abs_def[of s k]
      apply (simp add: Wtxn_Cts_Tn_is_Abs_Cmt_def tps_trans_all_defs set_insort_key)
      using Cl_Prep_Inv_def[of s] reach_tps
      by (metis (no_types, lifting) domI reach_cl_prep_inv txn_state.distinct(11) ver_state.distinct(3))
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: Wtxn_Cts_Tn_is_Abs_Cmt_def tps_trans_defs)
      by blast
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      apply (simp add: Wtxn_Cts_Tn_is_Abs_Cmt_def tps_trans_defs)
      by (smt add_to_readerset_commit' add_to_readerset_prep_inv)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case
      apply (simp add: Wtxn_Cts_Tn_is_Abs_Cmt_def tps_trans_defs)
      by (metis ver_state.distinct(3))
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      apply (simp add: Wtxn_Cts_Tn_is_Abs_Cmt_def tps_trans_defs)
      by (metis txid0.sel(2) txn_state.inject(3) ver_state.distinct(5))
  qed (auto simp add: Wtxn_Cts_Tn_is_Abs_Cmt_def tps_trans_defs)
qed


definition CO_Sorted where
  "CO_Sorted s k \<longleftrightarrow> sorted (map (unique_ts (wtxn_cts s)) (cts_order s k))"
                                   
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
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then have "get_wtxn s x1 \<notin> set (cts_order s k)"
      using CO_is_Cmt_Abs_def[of s] Cl_Prep_Inv_def[of s]
      apply (auto simp add: tps_trans_defs is_committed_in_kvs_def)
      by (metis (lifting) get_cl_w.simps(2) is_committed.simps(2) is_committed.simps(3)
          txn_state.distinct(11))
    then have map_pres: "\<And>X.
      map (unique_ts ((wtxn_cts s) (get_wtxn s x1 \<mapsto> X))) (cts_order s k) =
      map (unique_ts (wtxn_cts s)) (cts_order s k)"
      by (auto simp add: unique_ts_def)
    then show ?case using WCommit
      by (simp add: CO_Sorted_def tps_trans_all_defs sorted_insort_key map_pres)
  qed (auto simp add: CO_Sorted_def tps_trans_defs)
qed

\<comment> \<open>commit order lemmas\<close>
lemma length_cts_order:
  "length (cts_order gs k) = length (kvs_of_s gs k)" 
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



subsection \<open>UpdateKV for wtxn\<close>

lemma sorted_insort_key_is_snoc:
  "sorted (map f l) \<Longrightarrow> \<forall>x \<in> set l. f x < f t \<Longrightarrow> insort_key f t l = l @ [t]"
  by (induction l, auto)

lemma wtxn_cts_tn_le_cts_same_cl:
  assumes
    "reach tps_s s"
    "write_commit_s cl kv_map cts sn u'' clk mmap s s'"
    "Tn (Tn_cl sn' cl) \<in> set (cts_order s k)"
  shows "the (wtxn_cts s (Tn (Tn_cl sn' cl))) < cts"
proof -
  obtain \<tau> where tr_s: "tps_s: state_init \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s" using assms(1)
    by (metis (full_types) ES.select_convs(1) reach_trace_equiv tps_s_def)
  then have "tps_s: state_init \<midarrow>\<langle>\<tau> @ [WCommit cl kv_map cts sn u'' clk mmap]\<rangle>\<rightarrow> s'"
    using assms(2) by (simp add: trace_snoc)
  then have tr:
    "tps: state_init \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s"
    "tps: state_init \<midarrow>\<langle>\<tau> @ [WCommit cl kv_map cts sn u'' clk mmap]\<rangle>\<rightarrow> s'"
    by (simp_all add: tr_s tps_s_tr_sub_tps)
  obtain cts' where has_cts: "wtxn_cts s (Tn (Tn_cl sn' cl)) = Some cts'"
    using assms(1,3)
    by (metis CO_has_Cts_def reach_co_has_cts)
  obtain kv_map' u''' clk' mmap'
    where "WCommit cl kv_map' cts' sn' u''' clk' mmap' \<in> set \<tau>"
    using wtxn_cts_WC_in_\<tau>[OF tr(1), of sn' cl]
    by (metis (full_types) ES.select_convs(1) has_cts tps_def)
  then obtain j where j_:
    "\<tau> ! j = WCommit cl kv_map' cts' sn' u''' clk' mmap'" "j < length \<tau>"
    by (meson in_set_conv_nth)
  then have "(\<tau> @ [WCommit cl kv_map cts sn u'' clk mmap]): j \<prec> length \<tau>" using j_
    apply (intro r_into_trancl)
    by (auto simp add: cl_ord_def nth_append intro!: causal_dep0I_cl)
  then show ?thesis using assms
    using j_ has_cts WCommit_cts_causal_dep_gt_past[OF tr(2), of "length \<tau>" j]
    by (auto simp add: nth_append less_prod_def tps_def)
qed

lemma ver_cts_tn_le_cts_same_cl:
  assumes
    "reach tps_s s"
    "write_commit_s cl kv_map cts sn u'' clk mmap s s'"
    "svr_state (svrs s k) (Tn (Tn_cl sn' cl)) = Commit cts' sclk slst v rs"
  shows "cts' < cts"
proof -
  have "the (wtxn_cts s (Tn (Tn_cl sn' cl))) = cts'"
    using assms(1,3) Committed_Abs_has_Wtxn_Cts_def[of s k] by auto
  then show ?thesis
  using assms(1,3) Committed_Abs_Tn_in_CO_def[of s]
    wtxn_cts_tn_le_cts_same_cl[OF assms(1,2), of sn' k] by auto
qed

lemma wtxn_cts_tn_le_cts:
  assumes
    "Tn t' \<in> set (cts_order s k)"
    "reach tps_s s"
    "write_commit_s cl kv_map cts sn u'' clk mmap s s'"
  shows "unique_ts ((wtxn_cts s)(get_wtxn s cl \<mapsto> cts)) (Tn t')
    < unique_ts ((wtxn_cts s)(get_wtxn s cl \<mapsto> cts)) (get_wtxn s cl)"
proof -
  have notin: "get_wtxn s cl \<notin> set (cts_order s k)"
    using assms CO_is_Cmt_Abs_def[of s] Cl_Prep_Inv_def[of s]
    apply (auto simp add: tps_trans_defs is_committed_in_kvs_def)
    by (metis (lifting) get_cl_w.simps(2) is_committed.simps(2) is_committed.simps(3)
        txn_state.distinct(11))
  then show ?thesis
  proof (cases "get_cl t' = cl")
    case True
    then show ?thesis using assms
      apply (auto simp add: unique_ts_def ects_def less_prod_def)
        using notin apply presburger
        by (metis txid0.collapse wtxn_cts_tn_le_cts_same_cl)
  next
    case False
    then show ?thesis using assms
      apply (auto simp add: tps_trans_all_defs unique_ts_def ects_def notin)
      by (smt (z3) get_cl_w.simps(2) nat.inject old.prod.inject order_le_imp_less_or_eq
          txid.distinct(1) txid0.collapse)
  qed
qed


lemma write_commit_is_snoc:
  assumes "reach tps_s s"
    "write_commit_s cl kv_map cts sn u'' clk mmap s s'"
  shows
    "insort_key (unique_ts ((wtxn_cts s) (get_wtxn s cl \<mapsto> cts))) (get_wtxn s cl)
      (cts_order s k) =
      (cts_order s k) @ [get_wtxn s cl]"
  using assms
proof -
  have "reach tps_s s'" using assms 
    by (metis reach_trans state_trans.simps(5) tps_trans)
  show ?thesis
  proof (intro sorted_insort_key_is_snoc ballI)
    show "sorted (map (unique_ts ((wtxn_cts s)(get_wtxn s cl \<mapsto> cts))) (cts_order s k))"
      using assms \<open>reach tps_s s'\<close> CO_Sorted_def[of s' k]
      apply (simp add: tps_trans_all_defs)
      by (smt (verit, best) sorted_insort_key)
  next
    fix t
    assume "t \<in> set (cts_order s k)"
    then show "unique_ts ((wtxn_cts s)(get_wtxn s cl \<mapsto> cts)) t <
       unique_ts ((wtxn_cts s)(get_wtxn s cl \<mapsto> cts)) (get_wtxn s cl)" using assms
    apply (induction t)
      subgoal using T0_min_unique_ts[OF \<open>reach tps_s s'\<close>] by (simp add: tps_trans_defs)
      subgoal by (simp add: wtxn_cts_tn_le_cts) 
      done
  qed
qed


subsubsection \<open>Write commit guard properties\<close>

lemma write_commit_txn_to_vers_get_wtxn:
  assumes "write_commit_s cl kv_map commit_t sn u'' clk mmap gs gs'" 
  and "kv_map k = Some v" 
  shows "txn_to_vers gs k (get_wtxn gs cl) = new_vers (Tn (Tn_cl sn cl)) v"
  using assms
  by (auto simp add: write_commit_s_def write_commit_G_s_def write_commit_G_def txn_to_vers_def
      dest!: bspec[where x=k] split: ver_state.split)


subsubsection \<open>Write commit update properties\<close>

lemma write_commit_txn_to_vers_pres:
  assumes "write_commit_s cl kv_map cts sn u'' clk mmap gs gs'"
  shows "txn_to_vers gs' k = txn_to_vers gs k"
  using assms
  by (auto 3 4 simp add: tps_trans_defs txn_to_vers_def split: ver_state.split)


lemma write_commit_cts_order_update:
  assumes "write_commit_s cl kv_map cts sn u'' clk mmap gs gs'"
  shows "cts_order gs' = (\<lambda>k.
         (if kv_map k = None
          then cts_order gs k
          else insort_key (unique_ts ((wtxn_cts gs) (get_wtxn gs cl \<mapsto> cts))) (get_wtxn gs cl) (cts_order gs k)))"
  using assms
  by (auto simp add: tps_trans_defs ext_corder_def)


lemma write_commit_kvs_of_s:
  assumes "reach tps_s s"
    "write_commit_s cl kv_map cts sn u'' clk mmap s s'"
  shows "kvs_of_s s' = update_kv (Tn_cl sn cl)
                          (write_only_fp kv_map)
                          (view_of (cts_order s) (get_view s cl))
                          (kvs_of_s s)"
  using assms write_commit_is_snoc[OF assms]
  apply (intro ext)
  by (auto simp add: kvs_of_s_def update_kv_write_only write_commit_txn_to_vers_pres
    write_commit_cts_order_update write_commit_txn_to_vers_get_wtxn split: option.split)


lemma write_commit_get_view:
  assumes "reach tps_s s"
    and "write_commit_s cl kv_map cts sn u'' clk mmap s s'"
  shows "get_view s' cl =
    (\<lambda>k. if kv_map k = None
         then get_view s cl k
         else insert (get_wtxn s cl) (get_view s cl k))"
  using assms CO_Tid_def[of s cl]
  apply (intro ext)
  by (auto simp add: get_view_def tps_trans_all_defs set_insort_key)
  

lemma write_commit_view_of:
  assumes "reach tps_s s"
    and "write_commit_s cl kv_map cts sn u'' clk mmap s s'"
  shows "view_of (cts_order s') (get_view s' cl) = 
    (\<lambda>k. if kv_map k = None
         then view_of (cts_order s) (get_view s cl) k
         else insert (length (cts_order s k)) (view_of (cts_order s) (get_view s cl) k))"
  using assms
    write_commit_is_snoc[OF assms] write_commit_get_view[OF assms]
    CO_Distinct_def[of s'] CO_Distinct_def[of s]
  apply (intro ext)
  apply (auto simp add: view_of_def tps_trans_all_defs set_insort_key)
  subgoal for k
    using index_of_nth[of "cts_order s k @ [get_wtxn s cl]" "length (cts_order s k)"]
    apply (simp add: tps_trans_defs)
    by (meson assms(2) nless_le wtxn_cts_tn_le_cts)
  subgoal by (meson assms(2) nless_le wtxn_cts_tn_le_cts)
  subgoal for k 
    using index_of_nth[of "cts_order s k @ [get_wtxn s cl]" "length (cts_order s k)"]
    apply (simp add: tps_trans_defs)
    by (meson assms(2) nless_le wtxn_cts_tn_le_cts)
  subgoal for k _ t
    apply (intro exI[where x=t], auto)
    using index_of_append[of "cts_order s k" "get_wtxn s cl" t]
    apply (simp add: tps_trans_defs)
    by (meson assms(2) nless_le wtxn_cts_tn_le_cts)
  subgoal for k
    apply (intro exI[where x="get_wtxn s cl"], auto)
    using index_of_nth[of "cts_order s k @ [get_wtxn s cl]" "length (cts_order s k)"]
    apply (simp add: tps_trans_defs)
    by (metis (lifting) assms(2) nless_le wtxn_cts_tn_le_cts)
  subgoal for k _ t
    apply (intro exI[where x=t], auto)
    using index_of_append[of "cts_order s k" "get_wtxn s cl" t]
    apply (simp add: tps_trans_defs)
    by (metis (lifting) assms(2) nless_le wtxn_cts_tn_le_cts)
  done

lemmas write_commit_update_simps = 
  write_commit_txn_to_vers_pres write_commit_cts_order_update write_commit_kvs_of_s
   write_commit_get_view write_commit_view_of


(***************************************)

lemma full_view_elem: "i \<in> full_view vl \<longleftrightarrow> i < length vl"
  by (simp add: full_view_def)


lemma length_update_kv_bound:
  "i < length (update_kv t F u K k) \<longleftrightarrow> i < length (K k) \<or> W \<in> dom (F k) \<and> i = length (K k)"
  by (smt (verit) Nat.not_less_eq domIff not_less_iff_gr_or_eq length_update_kv)

(***************************************)

lemma v_writer_set_cts_order_eq:
  assumes "reach tps_s s"                   
  shows "v_writer ` set (kvs_of_s s k) = set (cts_order s k)"
  using assms reach_co_not_no_ver[OF assms]
  apply (auto simp add: CO_not_No_Ver_def kvs_of_s_defs image_def split: ver_state.split)
   apply (metis (mono_tags, lifting) is_committed.cases version.select_convs(2))
   subgoal for t apply (cases "svr_state (svrs s k) t", simp)
      apply (metis (opaque_lifting) ver_state.distinct(5) ver_state.inject(1) version.select_convs(2))
     by (smt ver_state.distinct(5) ver_state.inject(2) version.select_convs(2))
   done


subsection \<open>Simulation realtion lemmas\<close>

lemma kvs_of_s_init:
  "kvs_of_s (state_init) = (\<lambda>k. [new_vers T0 undefined])"
  by (simp add: kvs_of_s_defs tps_s_defs)

lemma kvs_of_s_inv:
  assumes "reach tps_s s"
    and "state_trans s e s'"
    and "\<not>commit_ev e"
  shows "kvs_of_s s' = kvs_of_s s"
  using assms(2, 3)
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
      using assms(1) Fresh_wr_notin_rs_def reach_fresh_wr_notin_rs
      by (smt reach_tps insert_commute insert_compr mem_Collect_eq not_None_eq singleton_conv2 txid0.collapse).
next
  case (RegR svr t t_wr gst_ts)
  then show ?case       \<comment> \<open>extends readerset; ok since committed reads remain the same\<close>
    by (auto 3 4 simp add: kvs_of_s_defs tps_trans_defs add_to_readerset_def split: ver_state.split)
next
  case (PrepW svr t v)  \<comment> \<open>goes to Prep state; not yet added to abstract state (client not committed)\<close>
  then show ?case using assms(1) CO_not_No_Ver_def reach_co_not_no_ver
    apply (auto simp add: kvs_of_s_defs, intro ext)
    by (auto simp add: tps_trans_defs split: ver_state.split)
next
  case (CommitW svr t v cts)   \<comment> \<open>goes to Commit state; ok: no change\<close>
  then show ?case  
    by (fastforce simp add: kvs_of_s_defs tps_trans_defs split: ver_state.split)
qed (auto 3 4 simp add: kvs_of_s_defs tps_trans_defs split: ver_state.split)


lemma cts_order_inv:
  assumes "reach tps_s s"
    and "state_trans s e s'"
    and "\<forall>cl kv_map cts sn u'' clk mmap. 
      e \<noteq> WCommit cl kv_map cts sn u'' clk mmap"
  shows "cts_order s' = cts_order s"
  using assms
  by (induction e) (auto simp add: tps_trans_defs)

lemma wtxn_cts_dom_inv:
  assumes "state_trans s e s'"
    and "reach tps_s s"
    and "wtxn_cts s' = wtxn_cts s"
  shows "cts_order s' = cts_order s"
  using assms
proof (induction e)
  case (WCommit x1 x2 x3 x4 x5 x6 x7)
  then show ?case apply (auto simp add: tps_trans_defs)
    using Wtxn_Cts_Tn_None_def[of s x1]
    apply (intro ext, simp)
    by (metis domI domIff le_refl)
qed (auto simp add: tps_trans_defs)

lemma get_view_inv:
  assumes "reach tps_s s"
    and "state_trans s e s'"
    and "\<not>v_ext_ev e cl"
  shows "get_view s' cl = get_view s cl"
  using assms
proof (induction e)
  case (WCommit x1 x2 x3 x4 x5 x6 x7)
  then have wtxn_None: "wtxn_cts s (get_wtxn s x1) = None"
    using Wtxn_Cts_Tn_None_def[of s]
    by (auto simp add: tps_trans_defs)
  have reach_s': "reach tps_s s'" using WCommit
    by (metis tps_trans reach_trans)
  obtain k pd ts v where
    "svr_state (svrs s k) (get_wtxn s x1) = Prep pd ts v \<and> k \<in> dom x2"
    using WCommit Dom_Kv_map_Not_Emp_def[of s]
    apply (simp add: tps_trans_defs)
    by (meson domIff)
  then have "gst (cls s cl) < Max {get_ts (svr_state (svrs s k) (get_wtxn s x1)) |k. k \<in> dom x2}"
    using WCommit Gst_lt_Cl_Cts_def[of s' cl k] reach_s'
    apply (auto simp add: tps_trans_defs split: if_split_asm)
    by blast
  then show ?case using WCommit
    by (auto simp add: wtxn_None get_view_def tps_trans_all_defs set_insort_key)
qed (auto simp add: tps_trans_defs get_view_def)


lemma views_of_s_inv:
  assumes "reach tps_s s"
    and "state_trans s e s'"
    and "\<not>v_ext_ev e cl"
  shows "views_of_s s' cl = views_of_s s cl"
  using assms cts_order_inv[of s e s'] get_view_inv[of s e s']
proof (induction e)
  case (WCommit x1 x2 x3 x4 x5 x6 x7)
  have wtxn_None: "wtxn_cts s (get_wtxn s x1) = None"
    using WCommit Wtxn_Cts_Tn_None_def[of s]
    by (auto simp add: tps_trans_defs)
  then have gv: "get_view s' cl = get_view s cl"
    using assms by (simp add: get_view_inv)
  then show ?case unfolding views_of_s_def gv
  proof (intro view_of_prefix)
    fix k
    show "prefix (cts_order s k) (cts_order s' k)"
      using WCommit(2) write_commit_is_snoc[OF WCommit(1,2)[simplified], of k]
      by (auto simp add: tps_trans_all_defs)
  next
    fix k
    show "distinct (cts_order s' k)" 
    using assms CO_Distinct_def reach_co_distinct
    by (metis tps_trans reach_trans)
  next
    fix k
    show "(set (cts_order s' k) - set (cts_order s k)) \<inter> get_view s cl k = {}"
      using WCommit(2) write_commit_is_snoc[OF WCommit(1,2)[simplified], of k]
      by (auto simp add: get_view_def wtxn_None tps_trans_all_defs)
  qed
qed (auto simp add: tps_trans_defs views_of_s_def)
  
lemma read_at_inv:
  assumes "reach tps_s s"
    and "state_trans s e s'"
    and "get_cl (ev_txn e) \<noteq> cl"
  shows "read_at (svr_state (svrs s' k)) (gst (cls s cl)) cl =
         read_at (svr_state (svrs s k)) (gst (cls s cl)) cl"
  using assms
proof (induction e)
  case (RegR x1 x2 x3 x4 x5 x6 x7)
  then show ?case by (auto simp add: tps_trans_defs add_to_readerset_pres_read_at)
next
  case (PrepW x1 x2 x3 x4 x5)
  then show ?case
    using prepare_write_pres_read_at[of "svr_state (svrs s x1)", simp]
    by (auto simp add: tps_trans_defs)
next
  case (CommitW x1 x2 x3 x4 x5 x6 x7)
  then have "gst (cls s cl) < x4"
    using Gst_lt_Cl_Cts_def[of s cl x1]
    apply (auto simp add: tps_trans_defs)
    by (metis domI txid0.collapse)
  then show ?case using CommitW
    using commit_write_pres_read_at[of "svr_state (svrs s x1)", simp]
    by (auto simp add: tps_trans_defs)
qed (auto simp add: tps_trans_defs)



subsection \<open>UpdateKV for rtxn\<close>

subsubsection \<open>View Invariants\<close>

definition View_Init where
  "View_Init s cl k \<longleftrightarrow> (T0 \<in> get_view s cl k)"

lemmas View_InitI = View_Init_def[THEN iffD2, rule_format]
lemmas View_InitE[elim] = View_Init_def[THEN iffD1, elim_format, rule_format]

lemma reach_view_init [simp]: "reach tps_s s \<Longrightarrow> View_Init s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: View_Init_def tps_s_defs get_view_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2 x3 x4 x5)
    then show ?case apply (simp add: View_Init_def tps_trans_defs get_view_def)
      by (meson Gst_le_Min_Lst_map_def linorder_not_le order.strict_trans2
          reach_tps reach_gst_le_min_lst_map reach_gst_lt_cl_cts)
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      by (auto simp add: View_Init_def tps_trans_all_defs get_view_def set_insort_key)
  qed (auto simp add: View_Init_def tps_trans_defs get_view_def)
qed

definition Get_View_Committed where
  "Get_View_Committed s cl k \<longleftrightarrow> (\<forall>t. t \<in> get_view s cl k \<longrightarrow> is_committed_in_kvs s k t)"

lemmas Get_View_CommittedI = Get_View_Committed_def[THEN iffD2, rule_format]
lemmas Get_View_CommittedE[elim] = Get_View_Committed_def[THEN iffD1, elim_format, rule_format]

lemma reach_get_view_committed[simp]:
  "reach tps_s s \<Longrightarrow> Get_View_Committed s cl k"
  apply (simp add: Get_View_Committed_def get_view_def)
  using CO_is_Cmt_Abs_def[of s k] by auto


subsubsection \<open>view_of, index_of: some more lemmas\<close>

lemma view_of_in_range:
  assumes "reach tps_s s"
    and "i \<in> view_of (cts_order s) u k"
  shows "i < length (cts_order s k)"
  using assms CO_Distinct_def[of s]
  apply (auto simp add: view_of_def Image_def)
  by (smt (verit, best) distinct_Ex1 the1_equality)

lemma views_of_s_in_range:
  assumes "reach tps_s s"
    and "i \<in> views_of_s s cl k"
  shows "i < length (cts_order s k)"
  using assms CO_Distinct_def[of s]
  apply (auto simp add: views_of_s_def view_of_def Image_def)
  by (smt (verit, best) distinct_Ex1 the1_equality)

lemma finite_views_of_s:
  "finite (views_of_s s cl k)"
  by (simp add: views_of_s_def view_of_def)

lemma views_of_s_non_emp:
  "reach tps_s s \<Longrightarrow> views_of_s s cl k \<noteq> {}"
  using View_Init_def[of s]
  by (auto simp add: views_of_s_def view_of_def)

lemma index_of_T0:
  assumes "reach tps_s s"
  shows "index_of (cts_order s k) T0 = 0"
proof -
  have "\<And>cl. T0 \<in> {t. t \<in> get_view s cl k \<and> t \<in> set (cts_order s k)}"
    apply (simp add: get_view_def) using assms
    by (metis T0_in_CO_def Wtxn_Cts_T0_def domI le_0_eq linorder_le_cases option.sel
        reach_t0_in_co reach_tps reach_wtxn_cts_t0)
  then show ?thesis
    using assms T0_First_in_CO_def[of s k] CO_Distinct_def[of s k]
    by (smt (z3) length_pos_if_in_set mem_Collect_eq nth_eq_iff_index_eq
        reach_co_distinct reach_t0_first_in_co the_equality)
qed

lemma zero_in_views_of_s:
  assumes "reach tps_s s"
  shows "0 \<in> views_of_s s cl k"
proof -
  have "T0 \<in> {t. t \<in> get_view s cl k \<and> t \<in> set (cts_order s k)}"
    apply (simp add: get_view_def) using assms
    by (metis T0_in_CO_def Wtxn_Cts_T0_def domI le_0_eq linorder_le_cases option.sel
        reach_t0_in_co reach_tps reach_wtxn_cts_t0)
  then show ?thesis using index_of_T0[OF assms]
    by (auto simp add: views_of_s_def view_of_def)
qed

lemma Max_views_of_s_in_range:
  assumes "reach tps_s s"
  shows "Max (views_of_s s cl k) < length (cts_order s k)"
  using assms CO_Distinct_def[of s]
  by (simp add: views_of_s_in_range views_of_s_non_emp finite_views_of_s)


subsubsection \<open>Rtxn reads max\<close>

definition Cts_le_Cl_Cts where
  "Cts_le_Cl_Cts s cl k \<longleftrightarrow> (\<forall>sn cts kv_map ts sclk slst v rs.
    cl_state (cls s cl) = WtxnCommit cts kv_map \<and>
    svr_state (svrs s k) (Tn (Tn_cl sn cl)) = Commit ts sclk slst v rs \<longrightarrow>
    (if sn = cl_sn (cls s cl) then ts = cts else ts < cts))"
                                   
lemmas Cts_le_Cl_CtsI = Cts_le_Cl_Cts_def[THEN iffD2, rule_format]
lemmas Cts_le_Cl_CtsE[elim] = Cts_le_Cl_Cts_def[THEN iffD1, elim_format, rule_format]

lemma reach_cts_le_cl_cts [simp]: "reach tps_s s \<Longrightarrow> Cts_le_Cl_Cts s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Cts_le_Cl_Cts_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case
    proof (cases "cl = x1")
      case True
      then show ?thesis using WCommit
        apply (auto simp add: Cts_le_Cl_Cts_def tps_trans_defs)
        using ver_cts_tn_le_cts_same_cl[OF WCommit(2,1)[simplified]]
          Cl_Prep_Inv_def[of s] apply auto
        by (metis (no_types, lifting) ver_state.distinct(3) ver_state.distinct(5))
    qed (auto simp add: Cts_le_Cl_Cts_def tps_trans_defs)
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cts_le_Cl_Cts_def tps_trans_defs)
      by (metis add_to_readerset_commit)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Cts_le_Cl_Cts_def tps_trans_defs)
      by metis
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cts_le_Cl_Cts_def tps_trans_defs)
      by (smt txid0.sel(1) txid0.sel(2) txn_state.inject(3))
  qed (auto simp add: Cts_le_Cl_Cts_def tps_trans_defs, (metis+)?)
qed

definition Cl_Curr_Tn_Right where
  "Cl_Curr_Tn_Right s k \<longleftrightarrow> (\<forall>t i j.
    is_curr_t s t \<and> cts_order s k ! j = Tn t \<and> j < i \<and> i < length (cts_order s k) \<longrightarrow>
    get_cl_w (cts_order s k ! i) \<noteq> get_cl t)"
                                   
lemmas Cl_Curr_Tn_RightI = Cl_Curr_Tn_Right_def[THEN iffD2, rule_format]
lemmas Cl_Curr_Tn_RightE[elim] = Cl_Curr_Tn_Right_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_curr_tn_right [simp]: "reach tps_s s \<Longrightarrow> Cl_Curr_Tn_Right s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Cl_Curr_Tn_Right_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RDone x1 x2 x3 x4 x5)
    then show ?case using CO_Tid_def[of s x1]
      apply (auto simp add: Cl_Curr_Tn_Right_def tps_trans_defs)
      by (metis Suc_n_not_le_n nth_mem order.strict_implies_order order.strict_trans txid0.collapse)
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then have reach_s': "reach tps_s s'" by blast
    then have "\<And>t. is_curr_t s' t \<Longrightarrow> is_curr_t s t" using WCommit
      subgoal for t apply (cases "get_cl t = x1")
      by (auto simp add: tps_trans_defs).
    then show ?case using WCommit
      using write_commit_cts_order_update[OF WCommit(1)[simplified]]
        write_commit_is_snoc[OF WCommit(2,1)[simplified]]
      apply (auto simp add: Cl_Curr_Tn_Right_def)
      by (smt (verit) Suc_less_eq get_cl_w_Tn less_Suc_eq less_trans_Suc nth_append
          nth_append_length nth_mem order_less_imp_not_less txid0.collapse txid0.sel(2)
          wtxn_cts_tn_le_cts)
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case using CO_Tid_def[of s x1]
      apply (auto simp add: Cl_Curr_Tn_Right_def tps_trans_defs)
      by (metis Suc_n_not_le_n nth_mem order.strict_trans txid0.collapse)
  qed (auto simp add: Cl_Curr_Tn_Right_def tps_trans_defs)
qed

definition Ts_Non_Zero where
  "Ts_Non_Zero s cl k \<longleftrightarrow> (\<forall>sn ts kv_map pd sclk slst v rs.
    cl_state (cls s cl) = WtxnCommit ts kv_map \<or>
    svr_state (svrs s k) (Tn (Tn_cl sn cl)) = Prep pd ts v \<or> 
    svr_state (svrs s k) (Tn (Tn_cl sn cl)) = Commit ts sclk slst v rs \<longrightarrow>
    ts > 0)"
                                   
lemmas Ts_Non_ZeroI = Ts_Non_Zero_def[THEN iffD2, rule_format]
lemmas Ts_Non_ZeroE[elim] = Ts_Non_Zero_def[THEN iffD1, elim_format, rule_format]

lemma reach_ts_non_zero [simp]: "reach tps_s s \<Longrightarrow> Ts_Non_Zero s cl k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Ts_Non_Zero_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      using Dom_Kv_map_Not_Emp_def[of s x1] Prep_le_Cl_Cts_def[of s' x1]
        reach.reach_trans[OF WCommit(1,2)]
      apply (auto simp add: Ts_Non_Zero_def tps_trans_defs)
      by (metis (no_types, lifting) bot_nat_0.extremum_uniqueI gr0I domIff)
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      apply (auto simp add: Ts_Non_Zero_def tps_trans_defs)
      apply (meson add_to_readerset_prep_inv)
      by (meson add_to_readerset_commit)
  qed (auto simp add: Ts_Non_Zero_def tps_trans_defs)
qed


definition Bellow_Gst_Committed where
  "Bellow_Gst_Committed s cl k \<longleftrightarrow> (\<forall>t \<in> set (cts_order s k).
    get_ts (svr_state (svrs s k) t) \<le> gst (cls s cl) \<longrightarrow> is_committed (svr_state (svrs s k) t))"
                                   
lemmas Bellow_Gst_CommittedI = Bellow_Gst_Committed_def[THEN iffD2, rule_format]
lemmas Bellow_Gst_CommittedE[elim] = Bellow_Gst_Committed_def[THEN iffD1, elim_format, rule_format]

lemma reach_bellow_gst_cmt [simp]: "reach tps_s s \<Longrightarrow> Bellow_Gst_Committed s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Bellow_Gst_Committed_def tps_s_defs)
next
  case (reach_trans s e s')
  then have reach_s': "reach tps_s s'" by (simp add: reach.reach_trans)
  show ?case using reach_trans
  proof (induction e)
    case (RInvoke x1 x2 x3 x4 x5)
    then have l: "\<And>s t. reach tps_s s \<Longrightarrow> is_prepared (svr_state (svrs s k) t)
        \<Longrightarrow> get_ts (svr_state (svrs s k) t) > gst (cls s x1)"
      apply auto subgoal for s
      using Gst_le_Pend_t_def[of s x1] Pend_lt_Prep_def[of s k] apply auto
      by (metis is_prepared.elims(2) order_le_less_trans ver_state.sel(2)).
    then show ?case using RInvoke
      using CO_is_Cmt_Abs_def[of s k]
      apply (auto simp add: Bellow_Gst_Committed_def tps_trans_defs is_committed_in_kvs_def)
      subgoal for t using l[OF reach_s', of t] by auto.
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then obtain pd ts v where "\<And>y. x2 k = Some y \<Longrightarrow> svr_state (svrs s k) (get_wtxn s x1) = Prep pd ts v"
      apply (auto simp add: tps_trans_defs)
      by (meson domI)
    then have "\<And>cl y. x2 k = Some y \<Longrightarrow> get_ts (svr_state (svrs s k) (get_wtxn s x1)) > gst (cls s cl)"
      apply auto subgoal for cl
      using Gst_le_Pend_t_def[of s cl] reach_tps[OF WCommit(2)] apply auto
      by (metis Pend_lt_Prep_def order_le_less order_less_le_trans reach_pend_lt_prep).
    then show ?case using WCommit
      using write_commit_cts_order_update[OF WCommit(1)[simplified]]
      apply (auto simp add: Bellow_Gst_Committed_def set_insort_key tps_trans_all_defs)
      by (meson leD)+
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      by (auto simp add: Bellow_Gst_Committed_def tps_trans_defs add_to_readerset_pres_get_ts
          add_to_readerset_pres_is_committed)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Bellow_Gst_Committed_def tps_trans_defs)
      by (meson CO_not_No_Ver_def reach_co_not_no_ver)
  qed (auto simp add: Bellow_Gst_Committed_def tps_trans_defs)
qed

definition Full_Ts_Inj where
  "Full_Ts_Inj s k \<longleftrightarrow> (\<forall>t t'. t \<noteq> t' \<and>
    is_committed (svr_state (svrs s k) t) \<and> 
    is_committed (svr_state (svrs s k) t')  \<longrightarrow>
    full_ts (svr_state (svrs s k)) t \<noteq> full_ts (svr_state (svrs s k)) t')"

lemmas Full_Ts_InjI = Full_Ts_Inj_def[THEN iffD2, rule_format]
lemmas Full_Ts_InjE[elim] = Full_Ts_Inj_def[THEN iffD1, elim_format, rule_format]

lemma reach_full_ts_inj [simp]: "reach tps_s s \<Longrightarrow> Full_Ts_Inj s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Full_Ts_Inj_def full_ts_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Full_Ts_Inj_def full_ts_def tps_trans_defs)
      by (metis add_to_readerset_pres_get_ts add_to_readerset_pres_is_committed)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Full_Ts_Inj_def full_ts_def tps_trans_defs)
      by metis
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then have "reach tps_s s'" by blast
    then show ?case using CommitW
      apply (auto simp add: Full_Ts_Inj_def full_ts_def tps_trans_defs)
      subgoal for _ _ _ _ t' apply (cases t', auto) 
      using Cts_le_Cl_Cts_def[of s' "get_cl x2" x1] apply auto
      by (metis is_committed.elims(2) less_irrefl_nat txid0.collapse ver_state.sel(3))
    subgoal for _ _ _ _ t apply (cases t, auto) 
      using Cts_le_Cl_Cts_def[of s' "get_cl x2" x1] apply auto
      by (metis is_committed.elims(2) less_irrefl_nat txid0.collapse ver_state.sel(3))
    by metis
  qed (auto simp add: Full_Ts_Inj_def tps_trans_defs)
qed

lemma index_of_T0_init: "index_of [T0] T0 = 0" by auto

lemma read_at_init:
  "read_at (wtxns_emp(T0 := Commit 0 0 0 undefined (\<lambda>x. None))) 0 cl = T0"
  by (auto simp add: read_at_def newest_own_write_def at_def
      ver_committed_before_def ver_committed_after_def arg_max_def is_arg_max_def)

lemma arg_max_get_ts:
  assumes "\<forall>sn ts. (\<exists>sclk slst v rs.
      svr_state (svrs s k) (Tn (Tn_cl sn (get_cl t))) = Commit ts sclk slst v rs) \<longrightarrow>
      (if sn = get_sn t then ts = cts else ts < cts)"
    and "Init_Ver_Inv s k"
    and "Ts_Non_Zero s (get_cl t) k"
    and "cts > rts"
  shows "(ARG_MAX (\<lambda>x. get_ts
           (if x = Tn t
            then Commit cts clk lst v rs
            else svr_state (svrs s k) x)) t'.
            t' \<noteq> Tn t \<longrightarrow>
            is_committed (svr_state (svrs s k) t') \<and>
            rts < get_ts (svr_state (svrs s k) t') \<and> t' \<noteq> T0 \<and> get_cl_w t' = get_cl t) =
            Tn t"
proof -
  have "\<forall>t'. t' \<noteq> Tn t \<and> is_committed (svr_state (svrs s k) t') \<and> get_cl_w t' = get_cl t
    \<longrightarrow> get_ts (svr_state (svrs s k) t') < cts" using assms
  apply (auto split: if_split_asm)
  subgoal for t' apply (cases t', auto)
    by (metis is_committed.elims(2) txid0.collapse ver_state.sel(3)).
  then show ?thesis
    apply (auto simp add: arg_max_def is_arg_max_def)
    using order_less_imp_not_less by blast
qed

lemma newest_own_write_commit_write_upd:
  assumes "reach tps_s s"
    and "commit_write k t v cts sts lst m s s'"
    and "get_cl t = cl"
    and "cts > rts"
  shows "newest_own_write (svr_state (svrs s' k)) rts cl = Some (Tn t)"
  using assms Cts_le_Cl_Cts_def[of s cl k]
  apply (auto simp add: tps_trans_defs newest_own_write_def ver_committed_after_def o_def)
  using arg_max_get_ts[of s k t cts rts]
  by auto

lemma read_at_commit_write_upd:
  assumes "reach tps_s s"
    and "commit_write k t v cts sts lst m s s'"
    and "get_cl t = cl"
    and "cts > rts"
  shows "read_at (svr_state (svrs s' k)) rts cl = Tn t"
proof -
  have reach_s': "reach tps_s s'" using assms(1,2)
    by (metis state_trans.simps(9) reach_trans tps_trans)
  then have "get_ts (svr_state (svrs s' k) (at (svr_state (svrs s' k)) rts)) < cts"
    using assms(1,4) at_le_rts[of s' k rts] by auto
  then show ?thesis using assms(4)
    newest_own_write_commit_write_upd[OF assms(1-3)]
    by (auto simp add: read_at_def)
qed

lemma get_view_def':
  assumes "reach tps_s s"
  shows "get_view s cl = (\<lambda>k. {t \<in> set (cts_order s k).
    (the (wtxn_cts s t) \<le> gst (cls s cl) \<or> get_cl_w t = cl)})"
  using assms CO_Sub_Wtxn_Cts_def[of s]
  by (auto simp add: get_view_def)

lemma views_of_s_def':
  "views_of_s s cl = (\<lambda>k. {index_of (cts_order s k) t | t. t \<in> get_view s cl k})"
  by (auto simp add: views_of_s_def view_of_def get_view_def)

lemma wtxn_cts_mono_full_ts:
  assumes "reach tps_s s"
    and "is_committed (svr_state (svrs s k) t)"
    and "is_committed (svr_state (svrs s k) t')"
    and "full_ts (svr_state (svrs s k)) t < full_ts (svr_state (svrs s k)) t'"
  shows "the (wtxn_cts s t) < the (wtxn_cts s t') \<or>
    (the (wtxn_cts s t) = the (wtxn_cts s t') \<and>
      (if t = T0 then 0 else Suc (get_cl_w t)) < (if t' = T0 then 0 else Suc (get_cl_w t')))"
proof -
  obtain cts where cts_: "wtxn_cts s t = Some cts"
    "\<exists>sts lst v rs. svr_state (svrs s k) t = Commit cts sts lst v rs"
    using assms(1,2) Committed_Abs_has_Wtxn_Cts_def[of s k]
    by (meson is_committed.elims(2) reach_cmt_abs_wtxn_cts reach_tps)
  obtain cts' where cts'_: "wtxn_cts s t' = Some cts'"
    "\<exists>sts lst v rs. svr_state (svrs s k) t' = Commit cts' sts lst v rs"
    using assms(1,3) Committed_Abs_has_Wtxn_Cts_def[of s k]
    by (meson is_committed.elims(2) reach_cmt_abs_wtxn_cts reach_tps)
  show ?thesis using assms cts_ cts'_ by (auto simp add: full_ts_def less_prod_def)
qed

lemma get_ts_wtxn_cts_eq:
  assumes "reach tps_s s"
    and "is_committed (svr_state (svrs s k) t)"
  shows "get_ts (svr_state (svrs s k) t) = the (wtxn_cts s t)"
  using assms Init_Ver_Inv_def[of s k] Wtxn_Cts_T0_def[of s]
proof (cases t)
  case (Tn x2)
  then have t_in_co: "t \<in> set (cts_order s k)"
    using assms Committed_Abs_in_CO_def[of s k]
    by (auto simp add: is_committed_in_kvs_def)
  then show ?thesis using assms
  proof (cases "wtxn_cts s t")
    case (Some cts)
    then show ?thesis
      proof (cases x2)
        case (Tn_cl sn cl)
        then show ?thesis
          using assms Tn t_in_co Wtxn_Cts_Tn_is_Abs_Cmt_def[of s cl]
          by fastforce
      qed
  qed auto
qed auto

lemma get_ts_wtxn_cts_le_rts:
  assumes "reach tps_s s"
    and "t \<in> set (cts_order s k)"
    and "the (wtxn_cts s t) \<le> rts"
  shows "get_ts (svr_state (svrs s k) t) \<le> rts"
  using assms Init_Ver_Inv_def[of s k]
proof (cases t)
  case (Tn x2)
  then show ?thesis using assms
  proof (cases "wtxn_cts s t")
    case (Some cts)
    then show ?thesis
      proof (cases x2)
        case (Tn_cl sn cl)
        then show ?thesis
          using assms Some Tn Wtxn_Cts_Tn_is_Abs_Cmt_def[of s cl] CO_not_No_Ver_def[of s k]
          apply (cases "svr_state (svrs s k) (Tn (Tn_cl sn cl))", auto)
          using Prep_le_Cl_Cts_def[of s cl]
          apply (smt (verit) dual_order.trans reach_prep_le_cl_cts reach_tps ver_state.distinct(5))
          by fastforce
      qed
  qed auto
qed auto


lemma sorted_wtxn_cts:
  assumes "reach tps_s s"
    and "i < j"
    and "j < length (cts_order s k)"
  shows "the (wtxn_cts s (cts_order s k ! i)) \<le> the (wtxn_cts s (cts_order s k ! j))"
  using assms CO_Sorted_def[of s k]
  apply (auto simp add: unique_ts_def sorted_map less_eq_prod_def)
  by (smt (verit) less_or_eq_imp_le sorted_wrt_iff_nth_less)

lemma index_of_mono_wtxn_cts:
  assumes "reach tps_s s"
    and "t \<in> set (cts_order s k)"
    and "t' \<in> set (cts_order s k)"
    and "the (wtxn_cts s t) < the (wtxn_cts s t')"
  shows "index_of (cts_order s k) t < index_of (cts_order s k) t'"
proof -
  have ts_ineq: "unique_ts (wtxn_cts s) t < unique_ts (wtxn_cts s) t'"
    using assms(4) by (auto simp add: unique_ts_def less_prod_def)
  then obtain i where i_: "cts_order s k ! i = t" "i < length (cts_order s k)"
    using assms(2) by (meson in_set_conv_nth)
  then obtain i' where i'_: "cts_order s k ! i' = t'" "i' < length (cts_order s k)"
    using assms(3) by (meson in_set_conv_nth)
  then show ?thesis using assms CO_Sorted_def[of s k] CO_Distinct_def[of s k]
      ts_ineq i_ i'_ index_of_nth[of "cts_order s k"]
    apply auto
    by (smt (z3) leD leI length_map nth_map sorted_nth_mono)
qed

lemma index_of_mono_eq_wtxn_cts:
  assumes "reach tps_s s"
    and "t \<in> set (cts_order s k)"
    and "t' \<in> set (cts_order s k)"
    and "the (wtxn_cts s t) < the (wtxn_cts s t') \<or>
        (the (wtxn_cts s t) = the (wtxn_cts s t') \<and>
          (if t = T0 then 0 else Suc (get_cl_w t)) < (if t' = T0 then 0 else Suc (get_cl_w t')))"
  shows "index_of (cts_order s k) t \<le> index_of (cts_order s k) t'"
proof -
  have ts_ineq: "unique_ts (wtxn_cts s) t < unique_ts (wtxn_cts s) t'"
    using assms(4) by (auto simp add: unique_ts_def less_prod_def)
  then obtain i where i_: "cts_order s k ! i = t" "i < length (cts_order s k)"
    using assms(2) by (meson in_set_conv_nth)
  then obtain i' where i'_: "cts_order s k ! i' = t'" "i' < length (cts_order s k)"
    using assms(3) by (meson in_set_conv_nth)
  then show ?thesis using assms CO_Sorted_def[of s k] CO_Distinct_def[of s k]
      ts_ineq i_ i'_ index_of_nth[of "cts_order s k"]
    apply auto
    apply (meson leD leI sorted_wtxn_cts)
    by (metis (no_types, lifting) leD length_map nat_le_linear nth_map sorted_nth_mono)
qed

lemma at_in_co:
  assumes "reach tps_s s"
  shows "at (svr_state (svrs s k)) rts \<in> set (cts_order s k)"
  using assms at_is_committed[OF reach_tps[OF assms]]
    Committed_Abs_in_CO_def[of s k]
  by (auto simp add: is_committed_in_kvs_def)

lemma at_wtxn_cts_le_rts:
  assumes "reach tps_s s"
  shows "the (wtxn_cts s (at (svr_state (svrs s k)) rts)) \<le> rts"
  using assms at_le_rts[OF reach_tps[OF assms], of k rts]
    get_ts_wtxn_cts_eq[OF assms, of k "at (svr_state (svrs s k)) rts"]
    at_is_committed[OF reach_tps[OF assms]]
  by auto

lemma newest_own_write_in_co:
  assumes "reach tps_s s"
    and "newest_own_write (svr_state (svrs s k)) rts cl = Some t"
  shows "t \<in> set (cts_order s k)"
  using assms newest_own_write_is_committed[OF _ assms(2)]
    Committed_Abs_in_CO_def[of s k]
  by (auto simp add: is_committed_in_kvs_def)

lemma newest_own_write_wtxn_cts_gt_rts:
  assumes "reach tps_s s"
    and "newest_own_write (svr_state (svrs s k)) rts cl = Some t"
  shows "the (wtxn_cts s t) > rts"
  using assms newest_own_write_gt_rts[OF reach_tps[OF assms(1)] assms(2)]
    get_ts_wtxn_cts_le_rts[OF assms(1)] newest_own_write_in_co[OF assms]
  by fastforce

lemma newest_own_write_none_wtxn_cts_le_rts:
  assumes "reach tps_s s"
    and "newest_own_write (svr_state (svrs s k)) rts cl = None"
    and "t \<in> set (cts_order s k)"
    and "\<And>ts kv_map. cl_state (cls s cl) \<noteq> WtxnCommit ts kv_map"
    and "get_cl_w t = cl"
    and "t \<noteq> T0"
  shows "get_ts (svr_state (svrs s k) t) \<le> rts"
proof -
  have "is_committed (svr_state (svrs s k) t)"
    using assms CO_is_Cmt_Abs_def[of s k]
    apply (auto simp add: is_committed_in_kvs_def) by blast
  then show ?thesis using assms
    apply (auto simp add: newest_own_write_def ver_committed_after_def split: if_split_asm)
    by (metis leI)
qed

lemma Max_Collect_ge: 
  "finite {f t| t. P t} \<Longrightarrow> P t \<Longrightarrow> f t \<le> Max {f t| t. P t}"
  using Max_ge by blast

lemma Max_Collect_eq:
  fixes f :: "'a \<Rightarrow> 'b :: linorder"
  assumes "finite {f t| t. P t}"
    and "P t"
    and "\<forall>t'. P t' \<longrightarrow> f t' \<le> f t"
  shows "f t = Max {f t |t. P t}"
  using assms
  by (smt (verit) Collect_empty_eq Max_ge Max_in finite_has_maximal2 mem_Collect_eq)

lemma arg_max_f_ge:
  fixes f :: "'a \<Rightarrow> 'b :: linorder"
  assumes "finite {y. \<exists>x. P x \<and> y = f x}"
    and "P t"
  shows "f t \<le> f (ARG_MAX f t. P t)"
  using assms arg_max_exI[OF assms]
  apply (auto simp add: arg_max_def is_arg_max_def)
  by (smt (verit, best) linorder_le_less_linear tfl_some)

definition Rtxn_Reads_Max where
  "Rtxn_Reads_Max s cl k \<longleftrightarrow>
   read_at (svr_state (svrs s k)) (gst (cls s cl)) cl =
    (case cl_state (cls s cl) of
      WtxnCommit cts kv_map \<Rightarrow>
        (if is_committed (svr_state (svrs s k) (get_wtxn s cl)) \<or> kv_map k = None
         then cts_order s k ! Max (views_of_s s cl k)
         else cts_order s k ! Max (views_of_s s cl k - {index_of (cts_order s k) (get_wtxn s cl)})) |
      _ \<Rightarrow> cts_order s k ! Max (views_of_s s cl k))"

lemmas Rtxn_Reads_MaxI = Rtxn_Reads_Max_def[THEN iffD2, rule_format]
lemmas Rtxn_Reads_MaxE[elim] = Rtxn_Reads_Max_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_reads_max [simp]: "reach tps_s s \<Longrightarrow> Rtxn_Reads_Max s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rtxn_Reads_Max_def tps_s_defs
        views_of_s_def view_of_def get_view_def index_of_T0_init[simplified] read_at_init)
next
  case (reach_trans s e s')
  then show ?case using views_of_s_inv[of s e s'] cts_order_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2 x3 x4 x5)
    let ?rts = "gst (cls s x1)" and
      ?rts' = "Min (range (lst_map (cls s x1)))"
    have rts_ineq: "?rts \<le> ?rts'"
      using RInvoke gst_monotonic[of s "RInvoke x1 x2 x3 x4 x5" s' x1]
      by (auto simp add: read_invoke_s_def read_invoke_def read_invoke_G_s_def read_invoke_U_def)
    have reach_s': "reach tps_s s'" using RInvoke by blast
    then show ?case using RInvoke
    proof (cases "cl = x1")
      case True
      then show ?thesis
      proof (cases "newest_own_write (svr_state (svrs s k)) ?rts' x1")
        case None
        let ?at_t = "at (svr_state (svrs s k)) ?rts'"
        have at_t_in_co: "?at_t \<in> set (cts_order s k)"
          using at_in_co[OF RInvoke(2)] by simp
        then obtain at_i where i_: "?at_t = cts_order s k ! at_i" "at_i < length (cts_order s k)"
          by (metis in_set_conv_nth)
        then have at_i_index_of: "at_i = index_of (cts_order s k) ?at_t"
          using index_of_nth[OF _ i_(2)] CO_Distinct_def[of s k] RInvoke(2) by auto
        have own_t_cmt:
          "\<And>t'. t' \<in> set (cts_order s k) \<and> get_cl_w t' = x1
            \<Longrightarrow> is_committed (svr_state (svrs s k) t')"
          using RInvoke(1,2) CO_is_Cmt_Abs_def[of s k]
          by (auto simp add: is_committed_in_kvs_def tps_trans_defs)
        have t_le_rts_cmt:
          "\<And>t'. t' \<in> set (cts_order s k) \<and> the (wtxn_cts s t') \<le> ?rts'
            \<Longrightarrow> is_committed (svr_state (svrs s k) t')"
          using RInvoke Bellow_Gst_Committed_def[of s' x1 k] reach_s'
          by (simp add: tps_trans_defs, meson get_ts_wtxn_cts_le_rts)
        have "\<And>ts kv_map. cl_state (cls s x1) \<noteq> WtxnCommit ts kv_map" using RInvoke
          by (auto simp add: tps_trans_defs)
        then have own_t_get_ts:
          "\<And>t'. is_committed (svr_state (svrs s k) t') \<and> get_cl_w t' = x1 \<and> t' \<noteq> T0 \<and> t' \<noteq> ?at_t \<Longrightarrow>
            full_ts (svr_state (svrs s k)) t' < full_ts (svr_state (svrs s k)) ?at_t"
          using own_t_cmt newest_own_write_none_wtxn_cts_le_rts[OF RInvoke(2) None]
          apply (auto simp add: at_def)
          using at_finite[OF reach_tps[OF RInvoke(2)]]
          apply (intro le_neq_trans arg_max_f_ge, auto)
          using at_is_committed[OF reach_tps[OF RInvoke(2)]] RInvoke(2) Full_Ts_Inj_def[of s k]
            Committed_Abs_in_CO_def[of s k]
          by (auto simp add: at_def ver_committed_before_def is_committed_in_kvs_def)
        have t_le_rts_get_ts:
          "\<And>t'. is_committed (svr_state (svrs s k) t') \<and> the (wtxn_cts s t') \<le> ?rts' \<and> t' \<noteq> T0 \<and> t' \<noteq> ?at_t \<Longrightarrow>
            full_ts (svr_state (svrs s k)) t' < full_ts (svr_state (svrs s k)) ?at_t"
          using t_le_rts_cmt get_ts_wtxn_cts_le_rts
          apply (auto simp add: at_def)
          using at_finite[OF reach_tps[OF RInvoke(2)]]
          apply (intro le_neq_trans arg_max_f_ge, auto)
          using at_is_committed[OF reach_tps[OF RInvoke(2)]] RInvoke(2) Full_Ts_Inj_def[of s k]
          by (auto simp add: at_def ver_committed_before_def get_ts_wtxn_cts_eq)
        show ?thesis using RInvoke(1,2,5) True None i_
          apply (auto simp add: Rtxn_Reads_Max_def read_at_def tps_trans_defs del: equalityI)
          apply (intro arg_cong[where f="(!) (cts_order s k)"])
          apply (auto simp add: views_of_s_def' get_view_def'[OF RInvoke(2)] del: equalityI)
          apply (auto simp add: at_i_index_of get_view_def del: equalityI)
          using at_t_in_co at_wtxn_cts_le_rts
          apply (intro Max_Collect_eq, auto del: equalityI)
          subgoal for t' apply (cases t'; cases "t' = ?at_t"; simp add: index_of_T0)
            using index_of_mono_eq_wtxn_cts[OF RInvoke(2)] t_le_rts_get_ts
              wtxn_cts_mono_full_ts[OF RInvoke(2) _ at_is_committed[OF reach_tps[OF RInvoke(2)]], of k t']
            by (auto simp add: t_le_rts_cmt del: equalityI)
          subgoal for t' apply (cases t'; cases "t' = ?at_t"; simp add: index_of_T0)
            using index_of_mono_eq_wtxn_cts[OF RInvoke(2)] own_t_get_ts
              wtxn_cts_mono_full_ts[OF RInvoke(2) _ at_is_committed[OF reach_tps[OF RInvoke(2)]], of k t']
            by (auto simp add: own_t_cmt)
          done
      next
        case (Some t)
        then have "newest_own_write (svr_state (svrs s k)) ?rts x1 = Some t"
          using rts_ineq newest_own_write_some_pres by metis
        then have t_in_co: "t \<in> set (cts_order s k)"
          using newest_own_write_in_co[OF RInvoke(2) Some] by simp
        then have t_wtxn_gt_rts: "the (wtxn_cts s t) > ?rts'"
          using newest_own_write_wtxn_cts_gt_rts[OF RInvoke(2)] Some by simp
        have index_of_t: "index_of (cts_order s k) t = Max (views_of_s s x1 k)"
          using index_of_nth[of "cts_order s k"] Max_views_of_s_in_range
            RInvoke(1-3) True CO_Distinct_def[of s k]
            \<open>newest_own_write (svr_state (svrs s k)) ?rts x1 = Some t\<close>
          by (auto simp add: Rtxn_Reads_Max_def read_at_def tps_trans_defs)
        show ?thesis
          using RInvoke True Some t_in_co 
            \<open>newest_own_write (svr_state (svrs s k)) ?rts x1 = Some t\<close>
            newest_own_write_owned[OF reach_tps[OF RInvoke(2)], of k ?rts' x1 t]
          apply (auto simp add: Rtxn_Reads_Max_def read_at_def tps_trans_defs del: equalityI)
          apply (intro arg_cong[where f="(!) (cts_order s k)"] Max_eq_if)
          apply (auto simp add: finite_views_of_s del: equalityI)
          subgoal for i apply (intro bexI[where x=i])
            apply (auto simp add: views_of_s_def' get_view_def'[OF RInvoke(2)] del: equalityI)
            apply (auto simp add: get_view_def del: equalityI)
            subgoal for t apply (intro exI[where x=t], auto)
              using rts_ineq by linarith
            subgoal for t by (intro exI[where x=t], auto).
          subgoal apply (intro bexI[where x="index_of (cts_order s k) t"])
            apply (auto simp add: views_of_s_def' get_view_def'[OF RInvoke(2)] del: equalityI)
            apply (auto simp add: get_view_def del: equalityI)
            subgoal using t_wtxn_gt_rts
              by (auto dest!: index_of_mono_wtxn_cts[OF RInvoke(2) _ t_in_co])
            subgoal using index_of_t Max_Collect_ge[of "index_of (cts_order s k)"]
              by (auto simp add: views_of_s_def' get_view_def'[OF RInvoke(2)]).
          done
      qed
    qed (auto simp add: Rtxn_Reads_Max_def read_invoke_s_def read_invoke_U_def split: txn_state.split)
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then have t_in: "\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<and> k \<in> dom kv_map \<longrightarrow>
          get_wtxn s cl \<in> set (cts_order s k)"
      using Committed_Abs_in_CO_def[of s k] Cl_Commit_Inv_def[of s cl k]
      by (auto simp add: domI is_committed_in_kvs_def)
    then have "\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<and> k \<in> dom kv_map \<longrightarrow>
      index_of (cts_order s k) (get_wtxn s cl) \<noteq> index_of (cts_order s k) T0"
      using WCommit(2) CO_Distinct_def[of s] T0_First_in_CO_def[of s]
      by (intro allI impI index_of_neq[of "cts_order s k" "get_wtxn s cl" T0], auto)
    then have "\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<and> k \<in> dom kv_map \<longrightarrow>
      views_of_s s cl k - {index_of (cts_order s k) (get_wtxn s cl)} \<noteq> {}"
      using WCommit(2) zero_in_views_of_s[of s cl k] index_of_T0[of s] by auto
    then have max_minus_in_range:
      "\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<and> k \<in> dom kv_map \<longrightarrow>
       Max (views_of_s s cl k - {index_of (cts_order s k) (get_wtxn s cl)}) < length (cts_order s k)"
      using WCommit(2) CO_Distinct_def[of s] index_of_nth[of "cts_order s k"]
      by (auto simp add: views_of_s_def view_of_def in_set_conv_nth)
    have cts_upd: "x2 k \<noteq> None \<longrightarrow> cts_order s' k = cts_order s k @ [get_wtxn s x1]"
      using WCommit(1) write_commit_is_snoc[OF WCommit(2,1)[simplified]]
      by (simp add: tps_trans_all_defs)
    then have ind_app:
      "\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<and> k \<in> dom kv_map \<and> x2 k \<noteq> None \<longrightarrow>
      index_of (cts_order s k @ [get_wtxn s x1]) (get_wtxn s cl) =
      index_of (cts_order s k) (get_wtxn s cl)"
      using WCommit(1,2) CO_Distinct_def[of s' k] t_in 
      apply (intro allI impI index_of_append[of "cts_order s k" "get_wtxn s x1" "get_wtxn s cl"])
      apply (metis reach.reach_trans reach_co_distinct)
      by auto
    have new_wr_notin_view: "length (cts_order s k) \<notin> views_of_s s x1 k"
      using WCommit(2) by (auto dest!: views_of_s_in_range)
    then show ?case
    proof (cases "cl = x1")
      case True
      then show ?thesis
        using WCommit cts_upd Max_views_of_s_in_range[of s] new_wr_notin_view
          write_commit_view_of[OF WCommit(2,1)[simplified]]
        apply (auto simp add: Rtxn_Reads_Max_def tps_trans_all_defs views_of_s_def)
        apply (metis domI is_committed.simps(3))
        using index_of_nth[of "cts_order s k @ [get_wtxn s x1]" "length (cts_order s k)"] 
          CO_Distinct_def[of s' k] CO_Distinct_def[of s] apply auto
        apply (metis nth_append)
        using reach_co_distinct state_trans.simps(5) tps_trans WCommit.prems(1) wtxn_cts_tn_le_cts
        by blast
    next
      case False
      then show ?thesis
        using WCommit cts_upd Max_views_of_s_in_range[of s]
        apply (auto simp add: Rtxn_Reads_Max_def write_commit_s_def write_commit_U_def ext_corder_def
                    split: txn_state.split)
        using max_minus_in_range ind_app[simplified]
        by (simp_all add: domI nth_append)
  qed
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: Rtxn_Reads_Max_def tps_trans_defs split: txn_state.split)
      by (metis domI is_committed.simps(1))
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      by (auto simp add: Rtxn_Reads_Max_def register_read_def register_read_U_def
          add_to_readerset_pres_read_at add_to_readerset_pres_is_committed split: txn_state.split)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case
      by (auto simp add: Rtxn_Reads_Max_def tps_trans_defs prepare_write_pres_read_at
          split: txn_state.split)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then have reach_s': "reach tps_s s'" by blast
    then show ?case
    proof (cases "get_cl x2 = cl")
      case True
      have in_co: "Tn x2 \<in> set (cts_order s x1)"
        using CommitW Committed_Abs_Tn_in_CO_def[of s]
        apply (auto simp add: tps_trans_defs)
        by (metis (no_types, lifting) txid0.collapse)
      then obtain j where j_: "cts_order s x1 ! j = Tn x2" "j < length (cts_order s x1)" "j > 0"
        using T0_First_in_CO_def reach_t0_first_in_co[OF CommitW(2)]
        by (metis gr_zeroI in_set_conv_nth txid.distinct(1))
      then have indj: "index_of (cts_order s x1) (Tn x2) = j"
        using CommitW(2) CO_Distinct_def[of s] index_of_nth by fastforce
      have wts_x2: "wtxn_cts s (Tn x2) = Some x4"
        using CommitW Committed_Abs_has_Wtxn_Cts_def[of s x1]
        by (auto simp add: tps_trans_defs)
      have gst_x4: "gst (cls s (get_cl x2)) < x4"
        using CommitW Gst_lt_Cl_Cts_def[of s]
        apply (simp add: tps_trans_defs)
        by (metis txid0.collapse)
      then have "\<forall>i < length (cts_order s x1). i > j \<longrightarrow> get_cl_w (cts_order s x1 ! i) \<noteq> get_cl x2"
        using CommitW indj j_ in_co Cl_Curr_Tn_Right_def[of s x1]
        by (auto simp add: tps_trans_defs)
      with in_co have a: "\<forall>i \<in> views_of_s s (get_cl x2) x1 - {j}. i < j"
        using CommitW j_ \<open>get_cl x2 = cl\<close> CO_Distinct_def[of s] index_of_p[of "cts_order s x1"]
        apply (auto simp add: views_of_s_def view_of_def get_view_def'[OF CommitW(2)] get_view_def'[OF reach_s'])
        subgoal for t
          using CO_Sorted_def[of s] CO_Distinct_def[of s] gst_x4 wts_x2
            sorted_wtxn_cts[OF CommitW(2), of j]
          by (metis (no_types, lifting) leD linorder_neqE_nat option.sel order.strict_trans1)
        by (smt linorder_neqE_nat reach_trans.hyps(2))
      have "finite (views_of_s s (get_cl x2) x1 - {j})"
           "views_of_s s (get_cl x2) x1 - {j} \<noteq> {}"
        using zero_in_views_of_s[OF CommitW(2), of "get_cl x2" x1]
          finite_views_of_s[of s "get_cl x2" x1] j_ by auto
      then have ind_max: "index_of (cts_order s x1) (Tn x2) >
          Max (views_of_s s (get_cl x2) x1 - {index_of (cts_order s x1) (Tn x2)})"
        using a by (auto simp add: views_of_s_def indj)
      from in_co have "index_of (cts_order s x1) (Tn x2) \<in> views_of_s s (get_cl x2) x1"
        by (auto simp add: views_of_s_def view_of_def get_view_def'[OF CommitW(2)])
      then have "index_of (cts_order s x1) (Tn x2) = Max (views_of_s s (get_cl x2) x1)"
        using ind_max by (simp add: Max.remove finite_views_of_s)
      then have ind: "Tn x2 = cts_order s x1 ! Max (views_of_s s (get_cl x2) x1)"
        using CommitW(2) Max_views_of_s_in_range CO_Distinct_def[of s x1] in_co
          by (auto intro: index_of_nth_rev)
      have "gst (cls s (get_cl x2)) < x4"
        using \<open>get_cl x2 = cl\<close> CommitW Gst_lt_Cl_Cts_def[of s cl x1]
        apply (auto simp add: tps_trans_defs)
        by (metis domI txid0.collapse)
      then have "read_at (svr_state (svrs s' x1)) (gst (cls s cl)) cl = Tn x2"
        using \<open>get_cl x2 = cl\<close> CommitW
          read_at_commit_write_upd[of s x1 x2 _ x4]
        by (auto simp add: tps_trans_defs)
      then show ?thesis using \<open>get_cl x2 = cl\<close> CommitW ind
        apply (auto simp add: Rtxn_Reads_Max_def commit_write_def commit_write_U_def
                    split: txn_state.split txn_state.split_asm)
        by (simp add: commit_write_G_def)
    next
      case False
      then show ?thesis using CommitW
        using read_at_inv[where e="CommitW x1 x2 x3 x4 x5 x6 x7", OF CommitW(2)]
      by (auto simp add: Rtxn_Reads_Max_def commit_write_def commit_write_U_def split: txn_state.split)
    qed
  qed (auto simp add: Rtxn_Reads_Max_def tps_trans_defs split: txn_state.split)
qed

(* The last auto is very slow: ~20s *)
  


subsubsection \<open>Kvt_map values of read_done\<close>

definition Rtxn_IdleK_notin_rs where
  "Rtxn_IdleK_notin_rs s cl \<longleftrightarrow> (\<forall>k cclk keys kv_map t cts sts lst v rs.
    cl_state (cls s cl) = RtxnInProg cclk keys kv_map \<and> k \<notin> keys \<and>
    svr_state (svrs s k) t = Commit cts sts lst v rs \<longrightarrow> rs (get_txn s cl) = None)"

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
    case (RInvoke x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Rtxn_IdleK_notin_rs_def tps_trans_defs)
      using Fresh_wr_notin_rs_def[of s]
      by (smt insertCI reach_tps reach_fresh_wr_notin_rs)
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case 
      by (auto simp add: Rtxn_IdleK_notin_rs_def tps_trans_defs add_to_readerset_def
               split: ver_state.split)
  qed (auto simp add: Rtxn_IdleK_notin_rs_def tps_trans_defs, blast?)
qed

definition Rtxn_RegK_Kvtm_Cmt_in_rs where
  "Rtxn_RegK_Kvtm_Cmt_in_rs s cl k \<longleftrightarrow> (\<forall>cclk keys kv_map v.
    cl_state (cls s cl) = RtxnInProg cclk keys kv_map \<and> kv_map k = Some v \<longrightarrow>
    (\<exists>t cts sts lst rs rts rlst. svr_state (svrs s k) t = Commit cts sts lst v rs \<and> rs (get_txn s cl) = Some (rts, rlst)))"

lemmas Rtxn_RegK_Kvtm_Cmt_in_rsI = Rtxn_RegK_Kvtm_Cmt_in_rs_def[THEN iffD2, rule_format]
lemmas Rtxn_RegK_Kvtm_Cmt_in_rsE[elim] = Rtxn_RegK_Kvtm_Cmt_in_rs_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_regk_kvtm_cmt_in_rs [simp]: "reach tps_s s \<Longrightarrow> Rtxn_RegK_Kvtm_Cmt_in_rs s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rtxn_RegK_Kvtm_Cmt_in_rs_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (cases x7, auto simp add: Rtxn_RegK_Kvtm_Cmt_in_rs_def tps_trans_defs)
      by (metis option.inject)
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case 
      apply (auto simp add: Rtxn_RegK_Kvtm_Cmt_in_rs_def tps_trans_defs add_to_readerset_def
                  split: ver_state.split)
      by (metis ver_state.inject(2))
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Rtxn_RegK_Kvtm_Cmt_in_rs_def tps_trans_defs)
      by (metis ver_state.distinct(3))
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Rtxn_RegK_Kvtm_Cmt_in_rs_def tps_trans_defs)
      by (metis ver_state.distinct(5))
  qed (auto simp add: Rtxn_RegK_Kvtm_Cmt_in_rs_def tps_trans_defs)
qed


subsubsection \<open>Read done update properties\<close>

lemma map_list_update:
  "i < length l \<Longrightarrow> distinct l \<Longrightarrow>
   (map f l) [i := (map f l ! i) \<lparr>v_readerset := x\<rparr>] =
    map (f (l ! i := (f (l ! i)) \<lparr>v_readerset := x\<rparr>)) l"
  by (smt (verit) fun_upd_apply length_list_update length_map nth_eq_iff_index_eq
      nth_equalityI nth_list_update nth_map)

lemma theI_of_ctx_in_CO:
  assumes "i = index_of (cts_order s k) t"
    and "t \<in> set (cts_order s k)"
    and "CO_Distinct s k"
  shows "cts_order s k ! i = t"
  using assms
  by (smt (verit, del_insts) CO_Distinct_def distinct_Ex1 theI_unique)

lemma view_of_committed_in_kvs: (* NEEDED? *)
  assumes "cl_state (cls s cl) = RtxnInProg cclk keys kv_map"
    and "reach tps_s s"
    and "i \<in> view_of (cts_order s) (get_view s cl) k"
    and "t_wr = cts_order s k ! i"
  shows "is_committed_in_kvs s k t_wr"
  using assms Get_View_Committed_def[of s cl k] theI_of_ctx_in_CO[of i s]
  by (auto simp add: view_of_def)

lemma read_done_txn_to_vers_update:
  assumes "reach tps_s s"
    "read_done_s cl kv_map sn u'' clk s s'"
  shows "txn_to_vers s' k =
    (case kv_map k of
      None \<Rightarrow> txn_to_vers s k |
      Some _ \<Rightarrow> (txn_to_vers s k)
          (read_at (svr_state (svrs s k)) (gst (cls s cl)) cl :=
            txn_to_vers s k (read_at (svr_state (svrs s k)) (gst (cls s cl)) cl)
              \<lparr>v_readerset := insert (get_txn s cl)
                (v_readerset (txn_to_vers s k (read_at (svr_state (svrs s k)) (gst (cls s cl)) cl)))\<rparr>))"
proof (cases "kv_map k")
  case None
  then show ?thesis using assms
    apply (auto simp add: tps_trans_defs txn_to_vers_def; intro ext)
    apply (auto split: ver_state.split)
    using Rtxn_IdleK_notin_rs_def[of s]
    by (metis domIff less_SucE option.discI reach_rtxn_idle_k_notin_rs txid0.collapse)
next
  case (Some a)
  then show ?thesis using assms
      read_at_is_committed[OF reach_tps[OF assms(1)], of k "gst (cls s cl)" cl]
    apply (auto simp add: tps_trans_defs txn_to_vers_def; intro ext)
    subgoal for _ t
      using CO_not_No_Ver_def[of s]
        Rtxn_RegK_Kvtm_Cmt_in_rs_def[of s]
        Fresh_rd_notin_other_rs_def[of s]
      apply (cases "svr_state (svrs s k) t", auto)
      apply (metis less_antisym txid0.collapse)
      apply (metis option.discI ver_state.inject(2))
      by (metis less_SucE option.discI txid0.collapse).
qed


lemma read_done_kvs_of_s:
  assumes "reach tps_s s"
    "read_done_s cl kv_map sn u'' clk s s'"
  shows "kvs_of_s s' = update_kv (Tn_cl sn cl)
                          (read_only_fp kv_map)
                          (view_of (cts_order s) (get_view s cl))
                          (kvs_of_s s)"
  using assms
  apply (intro ext)
  apply (simp add: kvs_of_s_def update_kv_read_only read_done_txn_to_vers_update)
  apply (auto simp add: tps_trans_defs Let_def split: option.split)
  apply (subst map_list_update)
  subgoal by (metis Max_views_of_s_in_range views_of_s_def)
  subgoal using reach_co_distinct by auto
  subgoal for k using Rtxn_Reads_Max_def[of s cl k]
    apply (auto simp add: views_of_s_def)
    by (metis Max_views_of_s_in_range nth_map views_of_s_def)
  done


lemmas read_done_update_simps = 
 read_done_txn_to_vers_update cts_order_inv read_done_kvs_of_s
   get_view_inv views_of_s_inv

subsection \<open>Transaction ID Freshness\<close>

(* TODO: move these lemmas to Key_Value_Stores and make the simp work automatically for the last two *)

lemma kvs_txids_update_kv_r: 
  assumes "\<And>k. Max (u k) < length (K k)" 
  shows "kvs_txids (update_kv t F u K) = 
         (if \<forall>k. F k = Map.empty then kvs_txids K else insert (Tn t) (kvs_txids K))"
  using assms
  by (auto simp add: kvs_txids_def kvs_writers_update_kv kvs_readers_update_kv)
    (metis (full_types) op_type.exhaust)

lemma kvs_txids_update_kv_read_only:       
  assumes "\<And>k. Max (u k) < length (K k)"
  shows "kvs_txids (update_kv t (read_only_fp kv_map) u K) = 
   (if \<forall>k. kv_map k = None then kvs_txids K else insert (Tn t) (kvs_txids K))"
  using kvs_txids_update_kv_r[OF assms]
  by simp

lemma kvs_txids_update_kv_read_only_concrete:       
  assumes "reach tps_s s"
  shows "kvs_txids (update_kv t (read_only_fp kv_map) (views_of_s s cl) (kvs_of_s s)) = 
   (if kv_map = Map.empty then kvs_txids (kvs_of_s s) else insert (Tn t) (kvs_txids (kvs_of_s s)))"
  using kvs_txids_update_kv_read_only[of "views_of_s s cl" "kvs_of_s s"]
    Max_views_of_s_in_range[OF assms]
  by (auto simp add: length_cts_order)

definition Sqn_Inv_c where
  "Sqn_Inv_c s cl \<longleftrightarrow> (\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map
     \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m \<le> cl_sn (cls s cl)))"

lemmas Sqn_Inv_cI = Sqn_Inv_c_def[THEN iffD2, rule_format]
lemmas Sqn_Inv_cE[elim] = Sqn_Inv_c_def[THEN iffD1, elim_format, rule_format]

definition Sqn_Inv_nc where
  "Sqn_Inv_nc s cl \<longleftrightarrow> ((\<forall>cts kv_map. cl_state (cls s cl) \<noteq> WtxnCommit cts kv_map)
     \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m < cl_sn (cls s cl)))"

lemmas Sqn_Inv_ncI = Sqn_Inv_nc_def[THEN iffD2, rule_format]
lemmas Sqn_Inv_ncE[elim] = Sqn_Inv_nc_def[THEN iffD1, elim_format, rule_format]

lemma reach_sql_inv [simp]: "reach tps_s s \<Longrightarrow> Sqn_Inv_c s cl \<and> Sqn_Inv_nc s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Sqn_Inv_c_def Sqn_Inv_nc_def tps_s_def kvs_of_s_init get_sqns_old_def txid_defs)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RDone x1 x2 x3 x4 x5)
    hence sqn_added:
      "get_sqns (kvs_of_s s') x1 = get_sqns (kvs_of_s s) x1 \<union> {cl_sn (cls s x1)}"
      using kvs_txids_update_kv_read_only_concrete[OF RDone(2)]
      apply (auto simp add: get_sqns_old_def read_done_kvs_of_s views_of_s_def)
      using Finite_Dom_Kv_map_rd_def[of s x1]
      by (auto simp add: tps_trans_defs)
    from RDone have "cl \<noteq> x1 \<longrightarrow> get_sqns (kvs_of_s s') cl = get_sqns (kvs_of_s s) cl"
      using kvs_txids_update_kv_read_only_concrete[OF RDone(2)]
      by (auto simp add: get_sqns_old_def read_done_kvs_of_s views_of_s_def)
    then show ?case using RDone sqn_added
      by (auto simp add: Sqn_Inv_c_def Sqn_Inv_nc_def tps_trans_defs)
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    hence sqn_added:
      "get_sqns (kvs_of_s s') x1 = get_sqns (kvs_of_s s) x1 \<union> {cl_sn (cls s x1)}"
      apply (simp add: get_sqns_old_def write_commit_kvs_of_s kvs_txids_update_kv)
      using Dom_Kv_map_Not_Emp_def[of s x1]
      by (auto simp add: tps_trans_defs)
    from WCommit have
      "cl \<noteq> x1 \<longrightarrow> get_sqns (kvs_of_s s') cl = get_sqns (kvs_of_s s) cl"
      by (simp add: get_sqns_old_def write_commit_kvs_of_s kvs_txids_update_kv)
    then show ?case using WCommit sqn_added
      by (auto simp add: Sqn_Inv_c_def Sqn_Inv_nc_def tps_trans_defs)
  qed (auto simp add: Sqn_Inv_c_def Sqn_Inv_nc_def tps_trans_defs)
qed

lemma t_is_fresh:
  assumes "Sqn_Inv_c s cl" and "Sqn_Inv_nc s cl"
    and "cl_state (cls s cl) \<in> {WtxnPrep kv_map, RtxnInProg cclk keys kv_map}"
  shows "get_txn s cl \<in> next_txids (kvs_of_s s) cl"
  using assms by (auto simp add: kvs_of_s_defs next_txids_def)


subsection \<open>Read-Only and Write-Only\<close>

definition Disjoint_RW where
  "Disjoint_RW s \<longleftrightarrow> ((\<Union>k. wtxns_dom (svr_state (svrs s k))) \<inter> Tn ` (\<Union>k. wtxns_rsran (svr_state (svrs s k))) = {})"

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
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    hence "\<And>k. wtxns_dom (svr_state (svrs s' k)) = wtxns_dom (svr_state (svrs s k))"
      by (simp add: tps_trans_defs add_to_readerset_wtxns_dom)
    hence "\<And>k. wtxns_rsran (svr_state (svrs s' k)) =
      (if k = x1
       then insert x2 (wtxns_rsran (svr_state (svrs s k)))
       else wtxns_rsran (svr_state (svrs s k)))" using RegR
      by (simp add: tps_trans_defs add_to_readerset_wtxns_rsran read_at_is_committed)
    then show ?case using RegR apply (simp add: Disjoint_RW_def)
      using Fresh_wr_notin_Wts_dom_def[of s "get_cl x2"] sorry
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Disjoint_RW_def tps_trans_defs) sorry
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
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
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
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
    case (RDone x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: RO_has_rts_def tps_trans_defs) sorry
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
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
    case (RDone x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: SO_ROs_def tps_trans_defs SO_def SO0_def)
      apply (metis CFTid_Rtxn_Inv_def less_or_eq_imp_le option.distinct(1) reach_tps reach_cftid_rtxn_inv)
      by (meson Rtxn_Rts_le_Gst_def reach_tps reach_rtxn_rts_le_gst)
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
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: SO_RO_WR_def tps_trans_defs SO_def SO0_def) sorry
  next
    case (RDone x1 x2 x3 x4 x5)
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
  "t \<in> kvs_writers K \<Longrightarrow> visTx' K (insert t u) = insert t (visTx' K u)"
  by (simp add: visTx'_def)

lemma insert_kt_to_u_closed':
  assumes "closed' K u r"
    and "t \<in> kvs_writers K"
    and "closed_general {t} (r\<inverse>) (visTx' K u \<union> read_only_Txs K)"
  shows "closed' K (insert t u) r"
  using assms
  by (auto simp add: closed'_def visTx'_observes_t intro: closed_general_set_union_closed)


\<comment> \<open>concrete read_done closedness\<close>

\<comment> \<open>premises\<close>
 
lemma v_writer_kvs_of_s:
  assumes "reach tps_s s"
  shows "v_writer ` set (kvs_of_s s k) = set (cts_order s k)"
  using assms CO_not_No_Ver_def[of s]
  by (auto simp add: kvs_of_s_defs image_iff split: ver_state.split)

lemma v_readerset_kvs_of_s:
  assumes "reach tps_s s"
  shows "\<Union> (v_readerset ` set (kvs_of_s s k)) = 
   {t. \<exists>t_wr \<in> set (cts_order s k).
      \<exists>cts sts lst v rs rts rlst. svr_state (svrs s k) t_wr = Commit cts sts lst v rs \<and>
      rs t = Some (rts, rlst) \<and> get_sn t < cl_sn (cls s (get_cl t))}"
  using assms CO_not_No_Ver_def[of s]
  apply (auto simp add: kvs_of_s_defs split: ver_state.split ver_state.split_asm)
  by blast

lemma v_writer_kvs_of_s_nth:
  "reach tps_s s \<Longrightarrow> i < length (cts_order s k) \<Longrightarrow> v_writer (kvs_of_s s k ! i) = cts_order s k ! i"
  using CO_not_No_Ver_def[of s k]
  by (auto simp add: kvs_of_s_defs split: ver_state.split)

lemma v_readerset_kvs_of_s_nth:
  "reach tps_s s \<Longrightarrow> i < length (cts_order s k) \<Longrightarrow>
    v_readerset (kvs_of_s s k ! i) = get_abst_rs s k (cts_order s k ! i)"
  using CO_not_No_Ver_def[of s k]
  by (auto simp add: kvs_of_s_defs split: ver_state.split)

lemma read_done_same_writers:
  assumes "reach tps_s s"
    and "read_done_s cl kv_map sn u'' clk s s'"
  shows "kvs_writers (kvs_of_s s') = kvs_writers (kvs_of_s s)"
proof -
  have "reach tps_s s'"
    using assms reach.reach_trans[of tps_s s "RDone cl kv_map sn u'' clk" s'] by auto
  then show ?thesis
    using assms CO_not_No_Ver_def[of s]
    apply (simp add: kvs_writers_def vl_writers_def v_writer_kvs_of_s)
    by (simp add: read_done_s_def read_done_U_def)
qed

lemma insert_Diff_if': "a \<notin> c \<Longrightarrow> insert a (b - c) = insert a b - c"
  by (simp add: insert_Diff_if)

lemma read_done_t_notin_kvs_writers:
  assumes "reach tps_s s"
    and "read_done_s cl kv_map sn u'' clk s s'"
  shows "Tn (get_txn s cl) \<notin> kvs_writers (kvs_of_s s)"
  using assms
  apply (simp add: kvs_writers_def vl_writers_def v_writer_kvs_of_s)
  using CO_Tid_def[of s cl] 
  apply (auto simp add: tps_trans_defs)
  by blast

lemma UNIV_ex: "(\<Union>x. {t. P t x}) = ({t. \<exists>x. P t x})"
  by auto

lemma read_done_new_read:
  assumes "reach tps_s s"
    and "read_done_s cl kv_map sn u'' clk s s'"
  shows "read_only_Txs (kvs_of_s s') = insert (Tn (get_txn s cl)) (read_only_Txs (kvs_of_s s))"
proof -
  have reach_s': "reach tps_s s'" 
    using assms reach.reach_trans[of tps_s s "RDone cl kv_map sn u'' clk" s'] by auto
  show ?thesis
  using assms read_done_t_notin_kvs_writers[OF assms] read_done_same_writers[OF assms(1)]
  apply (simp add: read_only_Txs_def insert_Diff_if')
  apply (rule arg_cong[where f="\<lambda>m. m - _"])
  apply (simp add: kvs_readers_def vl_readers_def v_readerset_kvs_of_s[OF assms(1)]
      v_readerset_kvs_of_s[OF reach_s'] UNIV_ex)
  using CO_not_No_Ver_def[of s']
  apply (auto simp add: tps_trans_defs image_insert[symmetric] simp del: image_insert)
  using image_eqI apply blast
  apply (smt (z3) image_eqI insertCI less_SucE mem_Collect_eq txid0.collapse)
  using image_eqI apply blast
  subgoal apply (rule image_eqI, auto)
    using Finite_Dom_Kv_map_rd_def[of s cl]
    apply (cases "dom kv_map = {}", auto simp add: ex_in_conv[symmetric] simp del: dom_eq_empty_conv)
    subgoal for k v apply (rule exI[where x=k])
      using Rtxn_RegK_Kvtm_Cmt_in_rs_def[of s cl] Committed_Abs_in_CO_def[of s]
      apply (auto simp add: is_committed_in_kvs_def)
      by (metis (no_types, lifting) is_committed.simps(1))
    done
  by (smt (verit) image_eqI less_Suc_eq mem_Collect_eq)
qed

lemma fresh_rtxn_not_vis:
  assumes "Tn (get_txn s cl) \<notin> kvs_writers (kvs_of_s s)"
    and "\<forall>t \<in> kvs_writers (kvs_of_s s). get_sn_w t < cl_sn (cls s cl)"
  shows "Tn (get_txn s cl) \<notin> ((R_CC (kvs_of_s s))\<inverse>)\<^sup>* `` (visTx' (kvs_of_s s)
    (\<Union>k. get_view s cl k))"
  apply (auto simp add: visTx'_def R_CC_def)
  subgoal for t apply (induction t "Tn (get_txn s cl)" rule: rtrancl.induct, auto)
      apply (simp add: assms(1))
     apply (simp add: SO_def SO0_def) oops

definition wtxns_readable :: "('v, 'm) global_conf_scheme \<Rightarrow> cl_id \<Rightarrow> key set \<Rightarrow> txid set" where
  "wtxns_readable s cl keys \<equiv> {read_at (svr_state (svrs s k)) (gst (cls s cl)) cl | k. k \<in> keys}"

lemma finite_wtxns_readable: "finite keys \<longrightarrow> finite (wtxns_readable s cl keys)"
  by (simp add: wtxns_readable_def)

lemma get_view_closed:
  assumes "reach tps_s s"
    and "\<And>t. t \<in> wtxns_readable s cl (dom kv_map) \<Longrightarrow> closed' K (insert t (\<Union>k. get_view s cl k)) r"
    and "cl_state (cls s cl) = RtxnInProg cclk (dom kv_map) kv_map"
  shows "closed' K (\<Union>k \<in> dom kv_map. get_view s cl k) r"
  using assms Rtxn_RegK_Kvtm_Cmt_in_rs_def[of s cl] Finite_Dom_Kv_map_rd_def[of s cl]
  apply (auto intro!: Union_closed')
  oops

lemma read_done_WR_onK:
  assumes "reach tps_s s"
    and "read_done_s cl kv_map sn u'' clk s s'"
  shows "R_onK WR (kvs_of_s s') = (wtxns_readable s cl (dom kv_map) \<times> {Tn (get_txn s cl)}) \<union> R_onK WR (kvs_of_s s)"
proof -
  have reach_s': "reach tps_s s'"
    using assms reach.reach_trans[of tps_s s "RDone cl kv_map sn u'' clk" s'] by auto
  then show ?thesis using assms
    apply (auto simp add: R_onK_def WR_def full_view_def v_writer_kvs_of_s_nth simp flip: length_cts_order) sorry
qed

lemma read_done_extend_rel:
  assumes "reach tps_s s"
    and "read_done_s cl kv_map sn u'' clk s s'"
  shows "R_CC (kvs_of_s s') = (wtxns_readable s cl (dom kv_map) \<times> {Tn (get_txn s cl)}) \<union> R_CC (kvs_of_s s)"
  using assms
  by (auto simp add: R_CC_def read_done_WR_onK)


\<comment> \<open>read_done closedness (canCommit)\<close>
lemma read_done_view_closed:
  assumes "closed' (kvs_of_s s) (\<Union>k. get_view s cl k) (R_CC (kvs_of_s s))"
    and "kvs_writers (kvs_of_s s') = kvs_writers (kvs_of_s s)"
    and "read_only_Txs (kvs_of_s s') = insert (Tn (get_txn s cl)) (read_only_Txs (kvs_of_s s))"
    and "Tn (get_txn s cl) \<notin> ((R_CC (kvs_of_s s))\<inverse>)\<^sup>* ``
      (visTx' (kvs_of_s s) (\<Union>k. get_view s cl k))"
    and "R_CC (kvs_of_s s') = (wtxns_readable s cl keys \<times> {Tn (get_txn s cl)}) \<union> R_CC (kvs_of_s s)"
    and "Finite_Keys s cl"
    and "cl_state (cls s cl) = RtxnInProg cclk keys kv_map"
  shows "closed' (kvs_of_s s') (\<Union>k. get_view s cl k) (R_CC (kvs_of_s s'))"
  using assms
  by (auto simp add: closed'_def visTx'_union_distr visTx'_same_writers[of "kvs_of_s s'"] finite_wtxns_readable
    Finite_Keys_def intro: closed_general_union_V_extend_N_extend_rel[where Y="wtxns_readable s cl keys"])
                                                            
\<comment> \<open>write_commit closedness (canCommit)\<close>
lemma write_commit_WR_onK:
  assumes "reach tps_s s"
    and "write_commit_s cl kv_map commit_t sn u'' clk mmap s s'"
  shows "R_onK WR (kvs_of_s s') = R_onK WR (kvs_of_s s)"
  apply (auto simp add: R_onK_def WR_def) sorry

lemma write_commit_same_rel:
  assumes "reach tps_s s"
    and "write_commit_s cl kv_map cts sn u'' clk mmap s s'"
  shows "R_CC (kvs_of_s s') = R_CC (kvs_of_s s)"
  using assms
  by (auto simp add: R_CC_def write_commit_WR_onK)

lemma "dom kv_map \<noteq> {} \<Longrightarrow> snd ` (\<Union>k\<in>dom kv_map. {(k, t)}) = {t}"
  apply (auto simp add: image_def)
  by (metis domIff insertI1 sndI)

lemma write_commit_view_closed:
  assumes "reach tps_s s"
    and "write_commit_s cl kv_map cts sn u'' clk mmap s s'"
    and "closed' (kvs_of_s s) (\<Union>k. get_view s cl k) (R_CC (kvs_of_s s))"
    and "closed_general {get_wtxn s cl} ((R_CC (kvs_of_s s))\<inverse>)
          (visTx' (kvs_of_s s) (\<Union>k. get_view s cl k) \<union> read_only_Txs (kvs_of_s s))"
    and "read_only_Txs (kvs_of_s s') = read_only_Txs (kvs_of_s s)"
    and "kvs_writers (kvs_of_s s') = insert (get_wtxn s cl) (kvs_writers (kvs_of_s s))"
  shows "closed' (kvs_of_s s') (insert (get_wtxn s cl) (\<Union>k. get_view s cl k)) (R_CC (kvs_of_s s'))"
  using assms
  by (auto simp add: write_commit_same_rel intro: insert_wr_t_closed')


subsection \<open>CanCommit\<close>

lemmas canCommit_defs = ET_CC.canCommit_def R_CC_def R_onK_def

lemma visTx_visTx': "reach tps_s s \<Longrightarrow> 
  visTx (kvs_of_s s) (view_of (cts_order s) u) = visTx' (kvs_of_s s) (\<Union>k. u k)"
  apply (auto simp add: visTx_def visTx'_def kvs_writers_def vl_writers_def image_iff)
    apply (metis length_cts_order nth_mem view_of_in_range) 
  subgoal for i k apply (intro exI[where x=k])
    using v_writer_kvs_of_s_nth sorry
  subgoal for k k' ver apply (simp add: view_of_def)
    apply (rule exI[where x="index_of (cts_order s k) (v_writer ver)"])
    apply (rule exI[where x=k'], auto)
    subgoal sorry
    apply (rule exI[where x="v_writer ver"])
  
    sorry
  done

lemma closed_closed': "reach tps_s s \<Longrightarrow> closed (kvs_of_s s) (view_of (cts_order s) u) r =
  closed' (kvs_of_s s) (\<Union>k. u k) r"
  by (simp add: closed'_def visTx_visTx')

lemma visTx'_cl_ctx_subset_writers:
  "visTx' (kvs_of_s s) (cl_ctx (cls s cl)) \<subseteq> kvs_writers (kvs_of_s s)"
  by (simp add: visTx'_def)

lemma visTx'_subset_writers: 
  "visTx' (kvs_of_s s) u \<subseteq> kvs_writers (kvs_of_s s)"
  by (simp add: visTx'_def)

lemma "kvs_writers (kvs_of_s s) \<subseteq> (\<Union>k. wtxns_dom (svr_state (svrs s k)))"
  oops

lemma "kvs_readers (kvs_of_s s) \<subseteq> (\<Union>k. wtxns_rsran (svr_state (svrs s k)))"
  oops

definition RO_le_gst :: "'v global_conf \<Rightarrow> cl_id \<Rightarrow> txid set" where
  "RO_le_gst s cl \<equiv> {t \<in> read_only_Txs (kvs_of_s s). \<exists>t'. t = Tn t' \<and> the (rtxn_rts s t') \<le> gst (cls s cl)}"

definition RO_WO_Inv where
  "RO_WO_Inv s \<longleftrightarrow> (\<Union>k. wtxns_dom (svr_state (svrs s k))) \<inter> Tn ` (\<Union>k. wtxns_rsran (svr_state (svrs s k))) = {}"

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
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: RO_WO_Inv_def tps_trans_defs) sorry
     (*using add_to_readerset_v_writer_img[of ] apply (simp add: txid_defs)*)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case sorry
  qed (auto simp add: RO_WO_Inv_def tps_trans_defs)
qed


subsection \<open>Views\<close>

subsubsection \<open>View update lemmas\<close>

lemma get_view_update_cls:
  "cl' \<noteq> cl \<Longrightarrow>
   get_view (s\<lparr>cls := (cls s)(cl := X) \<rparr>) cl' = get_view s cl'"
  by (auto simp add: get_view_def)

lemma get_view_update_cls_rtxn_rts:
  "cl' \<noteq> cl \<Longrightarrow>
   get_view (s\<lparr>cls := (cls s)(cl := X), rtxn_rts := Y \<rparr>) cl' = get_view s cl'"
  by (auto simp add: get_view_def)


lemmas get_view_update_lemmas = 
  get_view_update_cls get_view_update_cls_rtxn_rts


subsubsection \<open>View Invariants\<close>

lemma get_view_init: "get_view state_init cl = (\<lambda>k. {T0})"
  by (auto simp add: tps_s_defs get_view_def)

lemma Union_image_map:
  "\<Union> (f ` {x. m x = None}) \<union> \<Union> (f ` {x. \<exists>y. m x = Some y}) = (\<Union>x. f x)"
  apply auto
  by blast

lemma read_only_Txs_update_kv:
  assumes "\<And>k. F k R = None \<or> Max (u k) < length (K k)"
  shows "read_only_Txs (update_kv t F u K) = 
   (if \<forall>k. F k R = None then read_only_Txs K else insert (Tn t) (read_only_Txs K))"
  using assms
  apply (auto simp add: update_kv_def update_kv_key_def read_only_Txs_def image_def
      kvs_readers_def kvs_writers_def)
  apply (simp_all add: vl_readers_def vl_writers_def)
  apply (metis insertCI option.distinct(1)) sorry

definition View_Closed where
  "View_Closed s cl \<longleftrightarrow> closed' (kvs_of_s s) (\<Union>k. get_view s cl k) (R_CC (kvs_of_s s))"

lemmas View_ClosedI = View_Closed_def[THEN iffD2, rule_format]
lemmas View_ClosedE[elim] = View_Closed_def[THEN iffD1, elim_format, rule_format]

lemmas R_CC_defs = R_CC_def R_onK_def SO_def SO0_def WR_def

lemma reach_view_closed[simp]:
  "reach tps_s s \<Longrightarrow> View_Closed s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    apply (auto simp add: View_Closed_def tps_s_def kvs_of_s_init get_view_init closed'_def
        closed_general_def visTx'_def kvs_writers_def R_CC_defs trancl_converse)
    using prod.inject trancl.cases txid.distinct(1) by force
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s'] get_view_inv[of s e s' cl]
  proof (induction e)
    case (RInvoke x1 x2 x3 x4 x5)
    then show ?case apply (cases "cl = x1"; auto simp add: View_Closed_def) sorry
  next
    case (RDone x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: View_Closed_def)
      apply (intro read_done_view_closed[of s cl s'], auto simp add: read_done_same_writers) sorry
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case
    proof (cases "x1 = cl")
      case True
      then show ?thesis using WCommit
          write_commit_get_view[OF WCommit(2,1)[simplified]]
        apply (auto simp add: View_Closed_def)
        subgoal sorry
        subgoal apply (simp add: Union_image_map[of "get_view s cl" x2])
          using write_commit_kvs_of_s[OF WCommit(2,1)[simplified]]
          apply (intro write_commit_view_closed)
          apply (auto simp add: kvs_writers_update_kv read_only_Txs_update_kv)
          subgoal
            apply (auto simp add: closed'_def closed_general_def visTx'_def R_CC_defs 
                kvs_writers_def vl_writers_def v_writer_kvs_of_s Image_def trancl_converse) sorry
          by (simp_all add: tps_trans_defs)
        done
    next
      case False
      then show ?thesis using WCommit
      apply (auto simp add: View_Closed_def) sorry
    qed
  qed (simp_all add: View_Closed_def tps_trans_defs)
qed


subsubsection \<open>View Shift\<close>

definition Cl_WtxnCommit_Get_View where
  "Cl_WtxnCommit_Get_View s cl \<longleftrightarrow>
    (\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<longrightarrow>
      (\<forall>k \<in> dom kv_map. get_wtxn s cl \<in> get_view s cl k))"

lemmas Cl_WtxnCommit_Get_ViewI = Cl_WtxnCommit_Get_View_def[THEN iffD2, rule_format]
lemmas Cl_WtxnCommit_Get_ViewE[elim] = Cl_WtxnCommit_Get_View_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_wtxncommit_get_view [simp]: "reach tps_s s \<Longrightarrow> Cl_WtxnCommit_Get_View s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Cl_WtxnCommit_Get_View_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e)
    (auto simp add: Cl_WtxnCommit_Get_View_def tps_trans_all_defs get_view_def set_insort_key)
qed


abbreviation cl_txids :: "cl_id \<Rightarrow> txid set" where
  "cl_txids cl \<equiv> {Tn (Tn_cl sn cl)| sn. True}"

definition View_RYW where
  "View_RYW s cl k \<longleftrightarrow>
    (\<forall>sn. Tn (Tn_cl sn cl) \<in> vl_writers (kvs_of_s s k) \<longrightarrow> Tn (Tn_cl sn cl) \<in> get_view s cl k)"

lemmas View_RYWI = View_RYW_def[THEN iffD2, rule_format]
lemmas View_RYWE[elim] = View_RYW_def[THEN iffD1, elim_format, rule_format]

lemma reach_view_ryw [simp]: "reach tps_s s \<Longrightarrow> View_RYW s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: View_RYW_def tps_s_defs kvs_of_s_defs)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2 x3 x4 x5)
    then show ?case using CO_not_No_Ver_def[of s]
      apply (auto simp add: View_RYW_def kvs_of_s_defs vl_writers_def split: ver_state.split_asm)
      apply (simp_all add: tps_trans_defs get_view_def)
      by (meson CO_has_Cts_def domI reach_co_has_cts)+
  next
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case using CO_not_No_Ver_def[of s]
      apply (auto simp add: View_RYW_def kvs_of_s_defs vl_writers_def split: ver_state.split_asm)
      apply (simp_all add: tps_trans_defs get_view_def)
      by (meson CO_has_Cts_def domI reach_co_has_cts)+
  next
    case (RDone x1 x2 x3 x4 x5)
    then show ?case using CO_not_No_Ver_def[of s]
      apply (auto simp add: View_RYW_def kvs_of_s_defs vl_writers_def split: ver_state.split_asm)
      apply (simp_all add: tps_trans_defs get_view_def)
      by (meson CO_has_Cts_def domI reach_co_has_cts)+
  next
    case (WInvoke x1 x2 x3 x4)
    then show ?case using CO_not_No_Ver_def[of s]
      apply (auto simp add: View_RYW_def kvs_of_s_defs vl_writers_def split: ver_state.split_asm)
      apply (simp_all add: tps_trans_defs get_view_def)
      by (meson CO_has_Cts_def domI reach_co_has_cts)+
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      using CO_not_No_Ver_def[of s] CO_not_No_Ver_def[of s']
        write_commit_is_snoc[OF WCommit(2,1)[simplified]]
        write_commit_get_view[OF WCommit(2,1)[simplified]]
        get_view_inv[of s "WCommit x1 x2 x3 x4 x5 x6 x7" s' cl]
      apply (auto simp add: View_RYW_def kvs_of_s_defs vl_writers_def split: ver_state.split_asm)
      apply (metis reach.reach_trans reach_co_not_no_ver reach_trans.hyps(1))
      subgoal apply (simp add: tps_trans_all_defs get_view_def split: if_split_asm)
        using CO_Sub_Wtxn_Cts_def[of s k]
        by (smt (verit) in_mono reach_co_sub_wtxn_cts)+
      subgoal
        apply (simp add: tps_trans_defs)
        using Committed_Abs_in_CO_def[of s k] CO_Sub_Wtxn_Cts_def[of s k]
        apply (simp add: is_committed_in_kvs_def get_view_def)
        by (metis (no_types, lifting) in_mono is_committed.simps(1))
      done
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case using CO_not_No_Ver_def[of s]
      apply (auto simp add: View_RYW_def kvs_of_s_defs vl_writers_def split: ver_state.split_asm)
      apply (simp_all add: tps_trans_defs get_view_def)
      by (meson CO_has_Cts_def domI reach_co_has_cts)+
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case using CO_not_No_Ver_def[of s]
      apply (auto simp add: View_RYW_def kvs_of_s_defs vl_writers_def split: ver_state.split_asm)
      apply (auto simp add: tps_trans_defs get_view_def)
      by (meson CO_has_Cts_def reach_co_has_cts)+
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case using CO_not_No_Ver_def[of s]
      apply (auto simp add: View_RYW_def kvs_of_s_defs vl_writers_def split: ver_state.split_asm)
      apply (auto simp add: tps_trans_defs get_view_def)
      by (meson CO_has_Cts_def reach_co_has_cts)+
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case using CO_not_No_Ver_def[of s]
      apply (auto simp add: View_RYW_def kvs_of_s_defs vl_writers_def split: ver_state.split_asm)
      apply (auto simp add: tps_trans_defs get_view_def)
      by (meson CO_has_Cts_def reach_co_has_cts)+
  qed
qed


subsubsection \<open>View Wellformedness\<close>

definition FTid_notin_Get_View where
  "FTid_notin_Get_View s cl \<longleftrightarrow>
    (\<forall>n cl' k. (n > cl_sn (cls s cl) \<longrightarrow> Tn (Tn_cl n cl) \<notin> get_view s cl' k))"

lemmas FTid_notin_Get_ViewI = FTid_notin_Get_View_def[THEN iffD2, rule_format]
lemmas FTid_notin_Get_ViewE[elim] = FTid_notin_Get_View_def[THEN iffD1, elim_format, rule_format]

lemma reach_ftid_notin_get_view [simp]: "reach tps_s s \<Longrightarrow> FTid_notin_Get_View s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: FTid_notin_Get_View_def tps_s_defs get_view_def)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RDone x1 x2 x3 x4 x5)
    then show ?case
      apply (simp add: FTid_notin_Get_View_def tps_trans_defs get_view_def)
      using Suc_lessD by blast
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      by (auto simp add: FTid_notin_Get_View_def tps_trans_all_defs get_view_def set_insort_key)
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case
      apply (simp add: FTid_notin_Get_View_def tps_trans_defs get_view_def)
      using Suc_lessD by blast
  qed (auto simp add: FTid_notin_Get_View_def tps_trans_defs get_view_def)
qed

lemma reach_kvs_expands [simp]:
  assumes "state_trans s e s'"
    and "reach tps_s s"
  shows "kvs_of_s s \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s kvs_of_s s'"
  using assms kvs_of_s_inv[of s e s']
proof (induction e)
  case (RDone x1 x2 x3 x4 x5)
  then show ?case
    by (auto simp add: tps_trans_defs kvs_expands_def vlist_order_def version_order_def kvs_of_s_defs
        view_atomic_def full_view_def split: ver_state.split)
next
  case (WCommit x1 x2 x3 x4 x5 x6 x7)
  then show ?case using t_is_fresh[of s] write_commit_kvs_of_s[of s _ x2]
    apply (auto simp add: tps_trans_defs)
    by (meson kvs_expands_update_kv)
qed auto


definition Views_of_s_Wellformed where
  "Views_of_s_Wellformed s cl \<longleftrightarrow> (view_wellformed (kvs_of_s s) (views_of_s s cl))"

lemmas Views_of_s_WellformedI = Views_of_s_Wellformed_def[THEN iffD2, rule_format]
lemmas Views_of_s_WellformedE[elim] = Views_of_s_Wellformed_def[THEN iffD1, elim_format, rule_format]

lemma reach_views_of_s_wellformed [simp]: "reach tps_s s \<Longrightarrow> Views_of_s_Wellformed s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Views_of_s_Wellformed_def tps_s_defs view_of_def views_of_s_def index_of_T0_init
        view_wellformed_defs full_view_def get_view_def kvs_of_s_def)
next
  case (reach_trans s e s')
  hence "view_wellformed (kvs_of_s s') (views_of_s s cl)"
    using kvs_expands_view_wellformed reach_kvs_expands tps_trans
      Views_of_s_Wellformed_def by metis
  then show ?case using reach_trans kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2 x3 x4 x5)
    then have reach_s': "reach tps_s s'" by blast
    show ?case using RInvoke views_of_s_inv[of s "RInvoke _ _ _ _ _"]
    proof (cases "cl = x1")
      case True
      then show ?thesis
      proof (auto simp add: Views_of_s_Wellformed_def view_wellformed_def)
        show "view_in_range (kvs_of_s s') (views_of_s s' x1)"
          apply (auto simp add: view_in_range_defs)
          using zero_in_views_of_s[OF reach_s'] apply (simp add: tps_trans_defs)
          using views_of_s_in_range[OF reach_s'] by (simp add: full_view_def length_cts_order)
      next
        show "view_atomic (kvs_of_s s') (views_of_s s' x1)"
        proof (auto simp add: views_of_s_def view_atomic_def view_of_def full_view_def)
          fix k k' i' t
          assume a: "i' < length (kvs_of_s s' k')" "t \<in> get_view s' x1 k" "t \<in> set (cts_order s' k)"
            "v_writer (kvs_of_s s' k ! index_of (cts_order s' k) t) = v_writer (kvs_of_s s' k' ! i')"
          then have "t \<in> get_view s' x1 k'" using RInvoke
              v_writer_kvs_of_s_nth[OF RInvoke(3)] cts_order_inv[of s "RInvoke _ _ _ _ _"]
              index_of_p[of "cts_order s k"] CO_Distinct_def[of s]
            by (simp add: get_view_def length_cts_order)
          then show "\<exists>t. i' = index_of (cts_order s' k') t \<and> t \<in> get_view s' x1 k' \<and> t \<in> set (cts_order s' k')"
            using a v_writer_kvs_of_s_nth[OF RInvoke(3), of "index_of (cts_order s' k) t" k]
            apply (intro exI[where x=t], auto)
            subgoal using RInvoke
              v_writer_kvs_of_s_nth[OF RInvoke(3)] cts_order_inv[of s "RInvoke _ _ _ _ _"]
              index_of_p[of "cts_order s k"] CO_Distinct_def[of s]
              index_of_nth[of "cts_order s' k'" i']
              by (simp add: get_view_def length_cts_order)
            by (metis Committed_Abs_in_CO_def Get_View_Committed_def reach_cmt_abs_in_co
                reach_get_view_committed reach_s')
        qed
      qed
    qed (simp add: Views_of_s_Wellformed_def)
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then have reach_s': "reach tps_s s'" by blast
    show ?case using WCommit views_of_s_inv[of s "WCommit _ _ _ _ _ _ _"]
    proof (cases "cl = x1")
      case True
      then show ?thesis
      proof (auto simp add: Views_of_s_Wellformed_def view_wellformed_def)
        show "view_in_range (kvs_of_s s') (views_of_s s' x1)"
          apply (auto simp add: view_in_range_defs)
          using zero_in_views_of_s[OF reach_s'] apply (simp add: tps_trans_defs)
          using views_of_s_in_range[OF reach_s'] by (simp add: full_view_def length_cts_order)
      next
        show "view_atomic (kvs_of_s s') (views_of_s s' x1)"
        proof (auto simp add: views_of_s_def view_atomic_def view_of_def full_view_def)
          fix k k' i' t
          assume a: "i' < length (kvs_of_s s' k')" "t \<in> get_view s' x1 k" "t \<in> set (cts_order s' k)"
            "v_writer (kvs_of_s s' k ! index_of (cts_order s' k) t) = v_writer (kvs_of_s s' k' ! i')"
          then obtain i where i_: "t = cts_order s' k ! i" "i < length (cts_order s' k)"
            by (metis in_set_conv_nth)
          then have i_t: "v_writer (kvs_of_s s' k ! i) = t"
            using a v_writer_kvs_of_s_nth[OF reach_s'] by auto
          then have i'_t: "v_writer (kvs_of_s s' k' ! i') = t"
            using a i_ index_of_nth[of "cts_order s' k"] CO_Distinct_def[of s' k] reach_s' by auto
          then have t_in_co: "t \<in> set (cts_order s' k')"
            by (metis a(1) length_cts_order nth_mem reach_s' v_writer_kvs_of_s_nth)
          then have "t \<in> get_view s' x1 k'" using a
            by (auto simp add: get_view_def)
          then show "\<exists>t. i' = index_of (cts_order s' k') t \<and> t \<in> get_view s' x1 k' \<and> t \<in> set (cts_order s' k')"
            using a t_in_co v_writer_kvs_of_s_nth[OF WCommit(3), of "index_of (cts_order s' k) t" k]
            apply (intro exI[where x=t], auto)
            using WCommit
              v_writer_kvs_of_s_nth[OF WCommit(3)]
              v_writer_kvs_of_s_nth[OF reach_s']
              index_of_nth[of "cts_order s' k'" i'] CO_Distinct_def[of s'] i'_t
              apply (simp add: get_view_def length_cts_order)
              by (metis reach_co_distinct reach_s')
        qed
      qed
    qed (simp add: Views_of_s_Wellformed_def)
  qed (auto simp add: Views_of_s_Wellformed_def tps_trans_defs views_of_s_def get_view_def)
qed


subsection \<open>Fp Property\<close>

definition Rtxn_Fp_Inv where
  "Rtxn_Fp_Inv s cl k \<longleftrightarrow> (\<forall>t cclk keys kv_map v.
    cl_state (cls s cl) = RtxnInProg cclk keys kv_map \<and> kv_map k = Some v \<and>
    t = read_at (svr_state (svrs s k)) (gst (cls s cl)) cl \<longrightarrow>
    (\<exists>cts sclk lst rs. svr_state (svrs s k) t = Commit cts sclk lst v rs))"

lemmas Rtxn_Fp_InvI = Rtxn_Fp_Inv_def[THEN iffD2, rule_format]
lemmas Rtxn_Fp_InvE[elim] = Rtxn_Fp_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_fp [simp]: "reach tps_s s \<Longrightarrow> Rtxn_Fp_Inv s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rtxn_Fp_Inv_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      using Fresh_rd_notin_other_rs_def[of s]
      apply (simp add: Rtxn_Fp_Inv_def tps_trans_defs)
      by (smt map_upd_Some_unfold option.discI txn_state.inject(1) txn_state.simps(17))
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      apply (auto simp add: Rtxn_Fp_Inv_def tps_trans_defs add_to_readerset_pres_read_at)
      by (meson add_to_readerset_commit')
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case by (auto simp add: Rtxn_Fp_Inv_def tps_trans_defs prepare_write_pres_read_at)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then have gst_lt: "gst (cls s cl) < x4"
      using Gst_lt_Cl_Cts_def[of s]
      apply (simp add: tps_trans_defs)
      by (metis txid0.collapse)
    then have "\<And>cclk keys kv_map. cl_state (cls s cl) = RtxnInProg cclk keys kv_map \<Longrightarrow>
         get_cl_w (Tn x2) \<noteq> cl" using CommitW
      by (auto simp add: tps_trans_defs)
    then show ?case
      using CommitW gst_lt commit_write_pres_read_at[of "svr_state (svrs s k)"]
      by (auto simp add: Rtxn_Fp_Inv_def tps_trans_defs)
  qed (auto simp add: Rtxn_Fp_Inv_def tps_trans_defs)
qed

lemma v_value_last_version:
  assumes "reach tps_s s"
    and "svr_state (svrs s k)(cts_order s k ! Max (views_of_s s cl k)) = Commit cts sclk lst v rs"
  shows "v = v_value (last_version (kvs_of_s s k) (views_of_s s cl k))"
  using assms Max_views_of_s_in_range[OF assms(1), of cl k]
  by (auto simp add: kvs_of_s_defs)


subsection \<open>Refinement Proof\<close>

definition invariant_list where
  "invariant_list s \<equiv> (\<forall>cl k. Sqn_Inv_c s cl \<and> Sqn_Inv_nc s cl \<and> View_Closed s cl
    \<and> Views_of_s_Wellformed s cl \<and> Rtxn_Fp_Inv s cl k \<and> CO_Distinct s k
    \<and> T0_in_CO s k \<and> T0_First_in_CO s k \<and> View_Init s cl k \<and> FTid_notin_Get_View s cl)"

lemma invariant_listE [elim]: 
  "\<lbrakk> invariant_list s; 
     \<lbrakk> \<And>cl. Sqn_Inv_c s cl; \<And>cl. Sqn_Inv_nc s cl;
       \<And>cl k. Rtxn_Fp_Inv s cl k; \<And>k. CO_Distinct s k;
       \<And>k. T0_in_CO s k; \<And>k. T0_First_in_CO s k; FTid_notin_Get_View s cl \<rbrakk>
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
                       version_init_def get_view_def view_of_def index_of_T0_init[simplified])
next
  fix gs a and gs' :: "'v global_conf"
  assume p: "tps_s: gs\<midarrow>a\<rightarrow> gs'" and reach_s: "reach tps_s gs" and "reach ET_CC.ET_ES (sim gs)"
  then have I: "invariant_list gs" and reach_s': "reach tps_s gs'" by auto
  show "ET_CC.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  using p I reach_s kvs_of_s_inv[of gs a gs']
  proof (induction a)
    case (RInvoke cl keys sn u' clk)
    then show ?case
    proof -
      {
        assume vext: \<open>read_invoke_s cl keys sn u' clk gs gs'\<close>
        then have u'_: "u' = views_of_s gs' cl"
          by (simp add: views_of_s_def tps_trans_defs get_view_def)
        have \<open>ET_CC.ET_trans_and_fp 
                (kvs_of_s gs, views_of_s gs)
                 (ETViewExt cl u')
                (kvs_of_s gs', views_of_s gs')\<close>
        proof (rule ET_CC.ET_view_ext_rule)
          show \<open>views_of_s gs cl \<sqsubseteq> u'\<close> using vext reach_s
            apply (auto simp add: tps_trans_defs get_view_def views_of_s_def
                        intro!: view_of_deps_mono)
            using Gst_le_Min_Lst_map_def[of gs cl]
            by auto
        next
          show \<open>view_wellformed (kvs_of_s gs) u'\<close> using vext u'_
            by (metis state_trans.simps(1) RInvoke.prems(4) Views_of_s_Wellformed_def
                commit_ev.simps(3) reach_s reach_s' reach_views_of_s_wellformed)
        next
          show \<open>view_wellformed (kvs_of_s gs) (views_of_s gs cl)\<close>
            using reach_s reach_views_of_s_wellformed by auto
        next
          show \<open>kvs_of_s gs' = kvs_of_s gs\<close>
            by (simp add: RInvoke.prems(4) reach_s vext)
        next
          show \<open>views_of_s gs' = (views_of_s gs)(cl := u')\<close> using vext
            by (auto simp add: tps_trans_defs views_of_s_def get_view_def)
        qed
      }
      then show ?thesis using RInvoke
        by (auto simp only: ET_CC.trans_ET_ES_eq tps_trans state_trans.simps sim_def med.simps)
    qed
  next
    case (RDone cl kv_map sn u'' clk)
    then show ?case
    proof -
      {
        assume cmt: \<open>read_done_s cl kv_map sn u'' clk gs gs'\<close>
        have \<open>ET_CC.ET_trans_and_fp 
                (kvs_of_s gs, views_of_s gs)
                 (ET cl sn u'' (read_only_fp kv_map))
                (kvs_of_s gs', views_of_s gs')\<close>
        proof (rule ET_CC.ET_trans_rule [where u'="views_of_s gs' cl"])
          show \<open>views_of_s gs cl \<sqsubseteq> u''\<close> using cmt
            by (auto simp add: tps_trans_defs views_of_s_def view_of_deps_mono)
        next
          show \<open>ET_CC.canCommit (kvs_of_s gs) u'' (read_only_fp kv_map)\<close> using cmt I
            by (auto simp add: tps_trans_defs closed_closed'[OF reach_s] ET_CC.canCommit_def
                invariant_list_def)
        next
          show \<open>vShift_MR_RYW (kvs_of_s gs) u'' (kvs_of_s gs') (views_of_s gs' cl)\<close>
            using cmt I reach_s
          proof (intro vShift_MR_RYW_I)
            show "u'' \<sqsubseteq> views_of_s gs' cl" (* MR *)
              using cmt I reach_s
                get_view_inv[OF reach_s, of "RDone cl kv_map sn u'' clk", simplified]
              by (auto simp add: tps_trans_defs views_of_s_def)
          next
            fix t k i (* RYW.1: reflexive case *)
            assume a: "t \<in> kvs_txids (kvs_of_s gs')" "t \<notin> kvs_txids (kvs_of_s gs)"
              "i < length (kvs_of_s gs' k)" "t = v_writer (kvs_of_s gs' k ! i)"
            then show "i \<in> views_of_s gs' cl k"
              using cmt reach_s
              apply (auto simp add: read_done_kvs_of_s dest!: v_writer_in_kvs_txids)
              by (metis a(3) full_view_elemI full_view_update_kv read_done_kvs_of_s
                  read_only_fp_no_writes update_kv_v_writer_old)
          next
            fix t k i (* RYW.2: SO case *)
            assume a: "t \<in> kvs_txids (kvs_of_s gs')" "t \<notin> kvs_txids (kvs_of_s gs)"
              "i < length (kvs_of_s gs' k)" "(v_writer (kvs_of_s gs' k ! i), t) \<in> SO"
            then have "i < length (cts_order gs' k)"
              by (auto simp add: length_cts_order)
            then show "i \<in> views_of_s gs' cl k" using a cmt reach_s
                View_RYW_def[of gs cl k]
                kvs_txids_update_kv_read_only_concrete[OF reach_s]
                views_of_s_inv[OF reach_s, of "RDone cl kv_map sn u'' clk"]
                cts_order_inv[OF reach_s, of "RDone cl kv_map sn u'' clk"]
                v_writer_kvs_of_s_nth[OF reach_s' \<open>i < length (cts_order gs' k)\<close>]
              apply (auto simp add: read_done_kvs_of_s views_of_s_def view_of_def SO_def SO0_def
                  vl_writers_def dest: v_writer_in_kvs_txids split: if_split_asm)
              subgoal for n
                using index_of_nth[of "cts_order gs k" i] CO_Distinct_def[of gs]
                apply (intro exI[where x="Tn (Tn_cl n cl)"], simp)
                by (metis nth_mem v_writer_set_cts_order_eq).
          qed
        next
          show \<open>view_wellformed (kvs_of_s gs) u''\<close> using cmt I
            by (simp add: tps_trans_defs invariant_list_def views_of_s_def
                Views_of_s_Wellformed_def)
        next
          show \<open>view_wellformed (kvs_of_s gs') (views_of_s gs' cl)\<close>
            by (metis Views_of_s_Wellformed_def p reach_s reach_trans reach_views_of_s_wellformed)
        next
          show \<open>view_wellformed (kvs_of_s gs) (views_of_s gs cl)\<close> using cmt I
            by (auto simp add: tps_trans_defs invariant_list_def)
        next
          show \<open>Tn_cl sn cl \<in> next_txids (kvs_of_s gs) cl\<close> using cmt I
            by (auto simp add: read_done_s_def read_done_G_s_def read_done_G_def t_is_fresh)
        next
          show \<open>fp_property (read_only_fp kv_map) (kvs_of_s gs) u''\<close>
            using cmt reach_s
            apply (auto simp add: tps_trans_defs fp_property_def view_snapshot_def)
            subgoal for k
              using Rtxn_Fp_Inv_def[of gs cl k] Rtxn_Reads_Max_def[of gs] v_value_last_version
              by (auto simp add: views_of_s_def).
        next
          show \<open>kvs_of_s gs' = update_kv (Tn_cl sn cl) (read_only_fp kv_map) u'' (kvs_of_s gs)\<close>
            using cmt apply (auto simp add: read_done_s_def read_done_G_s_def)
            by (metis cmt reach_s read_done_kvs_of_s)
        next
          show \<open>views_of_s gs' = (views_of_s gs)(cl := views_of_s gs' cl)\<close> using cmt
            by (auto simp add: tps_trans_defs views_of_s_def get_view_def)
        qed
      }
      then show ?thesis using RDone
        by (auto simp only: ET_CC.trans_ET_ES_eq tps_trans state_trans.simps sim_def med.simps)
    qed
  next
    case (WCommit cl kv_map cts sn u'' clk mmap)
    then show ?case
    proof -
      {
        assume cmt: \<open>write_commit_s cl kv_map cts sn u'' clk mmap gs gs'\<close>
        have \<open>ET_CC.ET_trans_and_fp 
                (kvs_of_s gs, views_of_s gs)
                 (ET cl sn u'' (write_only_fp kv_map))
                (kvs_of_s gs', views_of_s gs')\<close>
        proof (rule ET_CC.ET_trans_rule [where u'="views_of_s gs' cl"])
          show \<open>views_of_s gs cl \<sqsubseteq> u''\<close> using cmt
            by (auto simp add: tps_trans_defs get_view_def views_of_s_def view_of_deps_mono)
        next
          show \<open>ET_CC.canCommit (kvs_of_s gs) u'' (write_only_fp kv_map)\<close> using cmt I
            by (auto simp add: tps_trans_defs closed_closed'[OF reach_s] ET_CC.canCommit_def
                invariant_list_def)
        next
          show \<open>vShift_MR_RYW (kvs_of_s gs) u'' (kvs_of_s gs') (views_of_s gs' cl)\<close> 
          proof (intro vShift_MR_RYW_I)
            show "u'' \<sqsubseteq> views_of_s gs' cl" (* MR *)
              using cmt I reach_s
                reach_s'[THEN reach_co_distinct]
                write_commit_get_view[OF reach_s cmt]
                write_commit_is_snoc[OF reach_s cmt]
              by (auto simp add: tps_trans_all_defs CO_Distinct_def views_of_s_def intro: view_of_mono)
          next
            fix t k i (* RYW.1: reflexive case *)
            assume "t \<in> kvs_txids (kvs_of_s gs')" "t \<notin> kvs_txids (kvs_of_s gs)"
              "i < length (kvs_of_s gs' k)" "t = v_writer (kvs_of_s gs' k ! i)"
            then show "i \<in> views_of_s gs' cl k"
              using cmt I reach_s
              apply (auto simp add: write_commit_kvs_of_s views_of_s_def write_commit_view_of
                         dest: v_writer_in_kvs_txids split: if_split_asm)
              by (metis full_view_elemI length_cts_order less_SucE update_kv_v_writer_old v_writer_in_kvs_txids)
          next
            fix t k i (* RYW.2: SO case *)
            assume a: "t \<in> kvs_txids (kvs_of_s gs')" "t \<notin> kvs_txids (kvs_of_s gs)"
              "i < length (kvs_of_s gs' k)" "(v_writer (kvs_of_s gs' k ! i), t) \<in> SO"
            then show "i \<in> views_of_s gs' cl k" using cmt I reach_s
            proof (cases "i = length (cts_order gs k)")
              case True
              then show ?thesis using a(3) cmt reach_s
              apply (auto simp add: write_commit_kvs_of_s write_commit_get_view views_of_s_def view_of_def)
              subgoal by (simp add: length_cts_order)
              subgoal using CO_Distinct_def[of gs' k] reach_co_distinct[OF reach_s']
                write_commit_is_snoc[OF reach_s cmt]
              apply (auto simp add: tps_trans_all_defs)
              apply (intro exI[where x="get_wtxn gs cl"])
                apply (auto intro!: the_equality[symmetric])
                by (metis (no_types, lifting) distinct_insort length_cts_order length_insort
                    nth_append_length nth_distinct_injective)
              done
            next
              case False
              then have "i < length (kvs_of_s gs k)" "i < length (cts_order gs k)" using a(3) cmt reach_s
                by (auto simp add: write_commit_kvs_of_s length_cts_order split: if_split_asm)
              then show ?thesis using a cmt reach_s reach_s'
              using View_RYW_def[of gs cl k]
              apply (auto simp add: write_commit_cts_order_update write_commit_kvs_of_s
                  write_commit_get_view views_of_s_def view_of_def SO_def SO0_def
                  kvs_txids_update_kv vl_writers_def
                  dest: v_writer_in_kvs_txids split: if_split_asm)
              subgoal for n
                using index_of_nth[of "cts_order gs k" i] CO_Distinct_def[of gs]
                apply (intro exI[where x="Tn (Tn_cl n cl)"], simp add: v_writer_kvs_of_s_nth)
                by (metis nth_mem v_writer_set_cts_order_eq)
              subgoal for n
                using CO_Distinct_def[of gs' k]
                  write_commit_is_snoc[OF reach_s cmt, of k]
                  update_kv_v_writer_old[of i "kvs_of_s gs"]
                apply (auto simp add: full_view_def)
                apply (intro exI[where x="Tn (Tn_cl n cl)"] conjI the_equality[symmetric])
                apply (auto simp add: v_writer_kvs_of_s_nth v_writer_set_cts_order_eq nth_append
                            dest: nth_mem)
                by (smt (verit, best) length_insort less_Suc_eq nless_le nth_append 
                        nth_append_length nth_distinct_injective 
                        nth_mem write_commit_cts_order_update wtxn_cts_tn_le_cts)
              done
            qed
          qed
        next
          show \<open>view_wellformed (kvs_of_s gs) u''\<close> using cmt I
            by (simp add: tps_trans_defs invariant_list_def views_of_s_def
                Views_of_s_Wellformed_def)
        next
          show \<open>view_wellformed (kvs_of_s gs') (views_of_s gs' cl)\<close>
            by (metis (no_types, lifting) Views_of_s_Wellformed_def p reach_s reach_trans
                      reach_views_of_s_wellformed)
        next
          show \<open>view_wellformed (kvs_of_s gs) (views_of_s gs cl)\<close> using cmt I
            by (auto simp add: tps_trans_defs invariant_list_def)
        next
          show \<open>Tn_cl sn cl \<in> next_txids (kvs_of_s gs) cl\<close> using cmt I
            by (auto simp add: write_commit_s_def write_commit_G_s_def write_commit_G_def t_is_fresh)
        next
          show \<open>fp_property (write_only_fp kv_map) (kvs_of_s gs) u''\<close>
            by (simp add: fp_property_write_only_fp)
        next
          show \<open>kvs_of_s gs' = update_kv (Tn_cl sn cl) (write_only_fp kv_map) u'' (kvs_of_s gs)\<close> 
            using cmt apply (simp add: write_commit_s_def write_commit_G_s_def)
            by (metis cmt reach_s write_commit_kvs_of_s)
        next
          show \<open>views_of_s gs' = (views_of_s gs)(cl := views_of_s gs' cl)\<close> using cmt
            apply (auto simp add: write_commit_s_def, intro ext)
            by (metis tps_trans WCommit.prems(1) fun_upd_apply reach_s v_ext_ev.simps(2) views_of_s_inv)
        qed
      }
      then show ?thesis using WCommit
        by (auto simp only: ET_CC.trans_ET_ES_eq tps_trans state_trans.simps sim_def med.simps)
    qed
  qed (auto simp add: sim_def views_of_s_def get_view_def tps_trans_defs invariant_list_def)
qed

end