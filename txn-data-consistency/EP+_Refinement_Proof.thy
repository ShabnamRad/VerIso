section \<open>Eiger Port Plus Protocol Satisfying CCv (Causal+) - Proofs and lemmas\<close>

theory "EP+_Refinement_Proof"
  imports "EP+_Sorted" "EP+_Trace"
begin


subsection \<open>View update lemmas\<close>

lemma get_view_update_cls:
  "cl' \<noteq> cl \<Longrightarrow>
   get_view (s\<lparr>cls := (cls s)(cl := X) \<rparr>) cl' = get_view s cl'"
  by (auto simp add: get_view_def)

lemma get_view_update_cls_rtxn_rts:
  "cl' \<noteq> cl \<Longrightarrow>
   get_view (s\<lparr>cls := (cls s)(cl := X), rtxn_rts := Y \<rparr>) cl' = get_view s cl'"
  by (auto simp add: get_view_def)

lemma get_view_update_svr_wtxns_dom:
   "wtxns_dom new_svr_state = wtxns_dom (svr_state (svrs s k)) \<Longrightarrow> 
    get_view (s\<lparr>svrs := (svrs s)
                   (k := svrs s k
                      \<lparr>svr_state := new_svr_state,
                       svr_clock := clk \<rparr>)\<rparr>) cl 
 = get_view s cl"
  by (auto simp add: get_view_def ext)


lemma get_view_update_cls_wtxn_cts_cts_order:
  "\<lbrakk> cl' \<noteq> cl; wtxn_cts s (get_wtxn s cl) = None; Y > gst (cls s cl') \<rbrakk> \<Longrightarrow>
   get_view (s\<lparr> cls := (cls s)(cl := X),
                wtxn_cts := (wtxn_cts s) (get_wtxn s cl \<mapsto> Y),
                cts_order := Z \<rparr>) cl'
  = get_view s cl'"
  by (auto simp add: get_view_def)


lemmas get_view_update_lemmas = 
  get_view_update_cls get_view_update_cls_rtxn_rts get_view_update_cls_wtxn_cts_cts_order
  get_view_update_svr_wtxns_dom

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
    case (RInvoke x1 x2 x3 x4)
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

definition CO_is_Cmt_Abs where
  "CO_is_Cmt_Abs s k \<longleftrightarrow> (\<forall>t. t \<in> set (cts_order s k) \<longrightarrow>
    (\<exists>cts sts lst v rs. svr_state (svrs s k) t = Commit cts sts lst v rs) \<or> 
    ((\<exists>pd ts v. svr_state (svrs s k) t = Prep pd ts v) \<and> 
     (\<exists>cts kv_map. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map \<and> k \<in> dom kv_map)))"

lemmas CO_is_Cmt_AbsI = CO_is_Cmt_Abs_def[THEN iffD2, rule_format]
lemmas CO_is_Cmt_AbsE[elim] = CO_is_Cmt_Abs_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_is_cmt_abs [simp]: "reach tps_s s \<Longrightarrow> CO_is_Cmt_Abs s k"
  apply (simp add: CO_is_Cmt_Abs_def)
  apply rule subgoal for t apply (cases t)
    apply (metis Init_Ver_Inv_def reach_tps reach_init_ver_inv)
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
    apply (metis reach_tps reach_init_ver_inv)
    by (metis CO_Tn_is_Cmt_Abs_def[of s] Wtxn_State_Cts_def WtxnCommit_Wtxn_Cts_def reach_tps
        reach_co_tn_is_cmt_abs reach_svr_state_cts reach_wtxncommit_wtxn_cts txid0.exhaust).

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
  "Committed_Abs_in_CO s k \<longleftrightarrow> (\<forall>t.
    (\<exists>cts sts lst v rs. svr_state (svrs s k) t = Commit cts sts lst v rs) \<or> 
    ((\<exists>pd ts v. svr_state (svrs s k) t = Prep pd ts v) \<and>
     (\<exists>cts kv_map. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map)) \<longrightarrow>
    t \<in> set (cts_order s k))"

lemmas Committed_Abs_in_COI = Committed_Abs_in_CO_def[THEN iffD2, rule_format]
lemmas Committed_Abs_in_COE[elim] = Committed_Abs_in_CO_def[THEN iffD1, elim_format, rule_format]

lemma reach_cmt_abs_in_co [simp]: "reach tps_s s \<Longrightarrow> Committed_Abs_in_CO s k"
  apply (simp add: Committed_Abs_in_CO_def)
  apply rule subgoal for t apply (cases t, blast)
  by (metis Prep_is_Curr_wt_def[of s k] Committed_Abs_Tn_in_CO_def get_cl_w.simps(2) txid0.collapse
      reach_tps get_sn_w.simps(2) is_prepared.simps(1) reach_cmt_abs_tn_in_co reach_prep_is_curr_wt).


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
      apply (auto simp add: tps_trans_defs)
      by (metis (lifting) get_cl_w.simps(2) txn_state.distinct(11) ver_state.distinct(3)
          ver_state.distinct(5))
    then have map_pres: "\<And>X.
      map (unique_ts ((wtxn_cts s) (get_wtxn s x1 \<mapsto> X))) (cts_order s k) =
      map (unique_ts (wtxn_cts s)) (cts_order s k)"
      by (auto simp add: unique_ts_def)
    then show ?case using WCommit
      by (simp add: CO_Sorted_def tps_trans_all_defs sorted_insort_key map_pres)
  qed (auto simp add: CO_Sorted_def tps_trans_defs)
qed



subsection \<open>UpdateKV for wtxn\<close>

lemma sorted_insort_key_is_snoc:
  "sorted (map f l) \<Longrightarrow> \<forall>x \<in> set l. f x < f t \<Longrightarrow> insort_key f t l = l @ [t]"
  by (induction l, auto)

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
    apply (auto simp add: tps_trans_defs)
    by (metis (lifting) get_cl_w.simps(2) txn_state.distinct(11) ver_state.distinct(3)
        ver_state.distinct(5))
  obtain \<tau> where tr_s: "tps_s: state_init \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s" using assms(2)
    by (metis (full_types) ES.select_convs(1) reach_trace_equiv tps_s_def)
  then have "tps_s: state_init \<midarrow>\<langle>\<tau> @ [WCommit cl kv_map cts sn u'' clk mmap]\<rangle>\<rightarrow> s'"
    using assms(3) by (simp add: trace_snoc)
  then have tr:
    "tps: state_init \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s"
    "tps: state_init \<midarrow>\<langle>\<tau> @ [WCommit cl kv_map cts sn u'' clk mmap]\<rangle>\<rightarrow> s'"
    by (simp_all add: tr_s tps_s_tr_sub_tps)
  obtain cts' where has_cts: "wtxn_cts s (Tn t') = Some cts'"
    using assms(1,2) CO_is_Cmt_Abs_def[of s k] Wtxn_State_Cts_def[of s k]
    by auto
  obtain kv_map' u''' clk' mmap'
    where "WCommit (get_cl t') kv_map' cts' (get_sn t') u''' clk' mmap' \<in> set \<tau>"
    using wtxn_cts_WC_in_\<tau>[OF tr(1), of "get_sn t'" "get_cl t'"]
    by (metis (full_types) ES.select_convs(1) has_cts tps_def txid0.collapse)
  then obtain j where j_:
    "\<tau> ! j = WCommit (get_cl t') kv_map' cts' (get_sn t') u''' clk' mmap'" "j < length \<tau>"
    by (meson in_set_conv_nth)
  then show ?thesis
  proof (cases "get_cl t' = cl")
    case True
    then have "(\<tau> @ [WCommit cl kv_map cts sn u'' clk mmap]): j \<prec> length \<tau>" using j_
      apply (intro r_into_trancl)
      by (auto simp add: cl_ord_def nth_append intro!: causal_dep0I_cl)
    then show ?thesis using assms True
      apply (auto simp add: unique_ts_def ects_def less_prod_def)
        using notin apply presburger
        using j_ has_cts  WCommit_cts_causal_dep_gt_past[OF tr(2), of "length \<tau>" j]
        by (auto simp add: nth_append less_prod_def tps_def)
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
  assumes "write_commit cl kv_map commit_t sn u'' clk mmap gs gs'" 
  and "kv_map k = Some v" 
  shows "txn_to_vers gs k (get_wtxn gs cl) = new_vers (Tn (Tn_cl sn cl)) v"
  using assms
  by (auto simp add: write_commit_def write_commit_G_def txn_to_vers_def
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
  apply (auto simp add: kvs_of_s_def update_kv_write_only write_commit_txn_to_vers_pres
    write_commit_cts_order_update write_commit_txn_to_vers_get_wtxn split: option.split)
  apply (simp add: tps_trans_defs txn_to_vers_def split: ver_state.split)
  by (metis (lifting) domI option.inject ver_state.distinct(1,5) ver_state.inject(1))


lemma write_commit_views_of_s:
  assumes "write_commit_s cl kv_map cts sn u'' clk mmap s s'"
  shows "views_of_s s' = (\<lambda>cl'. view_of
    (ext_corder (get_wtxn s cl) kv_map (unique_ts ((wtxn_cts s) (get_wtxn s cl \<mapsto> cts))) (cts_order s))    
    (if cl' = cl
     then (\<lambda>k. if kv_map k = None
               then get_view s cl k
               else insert (get_wtxn s cl) (get_view s cl k)) 
     else get_view s cl'))"
  using assms write_commit_cts_order_update[OF assms]
  apply (auto simp add: views_of_s_def)
  apply (rule ext) unfolding ext_corder_def
  apply (intro arg_cong[where f="view_of (\<lambda>k. if kv_map k = None then cts_order s k
                       else insort_key (unique_ts ((wtxn_cts s)(get_wtxn s cl \<mapsto> cts))) (get_wtxn s cl)
                             (cts_order s k))"])
  apply (auto simp add: get_view_def)
  subgoal sorry
  apply (auto simp add: tps_trans_defs)
  oops

lemmas write_commit_update_simps = 
  write_commit_txn_to_vers_pres write_commit_cts_order_update write_commit_kvs_of_s
  (*write_commit_views_of_s*)


(***************************************)

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
          v_readerset = {t. \<exists>rts rlst. rs t = Some (rts, rlst) \<and> get_sn t < cl_sn (cls s (get_cl t))}\<rparr>"], simp)
       by (rule bexI[where x=t], auto)
     done
   done



subsection \<open>Simulation realtion lemmas\<close>

lemma kvs_of_s_init:
  "kvs_of_s (state_init) = (\<lambda>k. [\<lparr>v_value = undefined, v_writer = T0, v_readerset = {}\<rparr>])"
  by (simp add: kvs_of_s_defs tps_s_defs)

lemma kvs_of_s_inv:
  assumes "state_trans s e s'"
    and "reach tps_s s"
    and "\<not>commit_ev e"
  shows "kvs_of_s s' = kvs_of_s s"
  using assms(1, 3)
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
      using assms(2) Fresh_wr_notin_rs_def reach_fresh_wr_notin_rs
      by (smt reach_tps insert_commute insert_compr mem_Collect_eq not_None_eq singleton_conv2 txid0.collapse).
next
  case (RegR svr t t_wr gst_ts)
  then show ?case       \<comment> \<open>extends readerset; ok since committed reads remain the same\<close>
    by (auto 3 4 simp add: kvs_of_s_defs tps_trans_defs add_to_readerset_def split: ver_state.split)
next
  case (PrepW svr t v)  \<comment> \<open>goes to Prep state; not yet added to abstract state (client not committed)\<close>
  then show ?case using assms(2) CO_not_No_Ver_def reach_co_not_no_ver
    apply (auto simp add: kvs_of_s_defs, intro ext)
    by (auto simp add: tps_trans_defs split: ver_state.split)
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
    case (RDone x1 x2 x3 x4 x5)
    hence sqn_added: "get_sqns (kvs_of_s s') x1 = get_sqns (kvs_of_s s) x1 \<union> {cl_sn (cls s x1)}" sorry
    from RDone have "cl \<noteq> x1 \<longrightarrow> get_sqns (kvs_of_s s') cl = get_sqns (kvs_of_s s) cl"
      apply (simp add: read_done_def read_done_U_def) sorry
    then show ?case using RDone sqn_added by (auto simp add: Sqn_Inv_nc_def tps_trans_defs)
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    hence "cl \<noteq> x1" unfolding Sqn_Inv_nc_def
      apply (auto simp add: Sqn_Inv_nc_def tps_trans_defs) sorry
    with WCommit have "get_sqns (kvs_of_s s') cl = get_sqns (kvs_of_s s) cl"
      apply (auto simp add: write_commit_kvs_of_s update_kv_defs) sorry
    then show ?case using WCommit
      by (auto simp add: Sqn_Inv_nc_def tps_trans_defs)
  next
    case (WDone x1 x2 x3 x4 x5)
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
    case (RDone x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Sqn_Inv_c_def)
      by (metis (full_types) Sqn_Inv_nc_def gt_ex nless_le reach.reach_trans reach_sql_inv_nc
          reach_trans.hyps(1) txn_state.inject(3))+
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Sqn_Inv_c_def)
      by (metis Sqn_Inv_nc_def less_or_eq_imp_le reach.reach_trans reach_sql_inv_nc
          reach_trans.hyps(1) txn_state.inject(3))
  qed (auto simp add: Sqn_Inv_c_def tps_trans_defs)
qed

lemma t_is_fresh:
  assumes "Sqn_Inv_c s cl" and "Sqn_Inv_nc s cl"
    and "cl_state (cls s cl) \<in> {WtxnPrep kv_map, RtxnInProg cclk keys kv_map}"
  shows "get_txn s cl \<in> next_txids (kvs_of_s s) cl"
  using assms by (auto simp add: kvs_of_s_defs next_txids_def)

subsection \<open>Kvt_map values of read_done\<close>
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
    case (RInvoke x1 x2 x3 x4)
    then show ?case apply (auto simp add: Rtxn_IdleK_notin_rs_def tps_trans_defs)
      using Fresh_wr_notin_rs_def[of s]
      by (metis insertCI reach_tps reach_fresh_wr_notin_rs)
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case 
      by (auto simp add: Rtxn_IdleK_notin_rs_def tps_trans_defs add_to_readerset_def
               split: ver_state.split)
  qed (auto simp add: Rtxn_IdleK_notin_rs_def tps_trans_defs, blast?)
qed

definition Rtxn_RegK_Kvtm_Cmt_in_rs where
  "Rtxn_RegK_Kvtm_Cmt_in_rs s cl \<longleftrightarrow> (\<forall>k cclk keys kv_map v.
    cl_state (cls s cl) = RtxnInProg cclk keys kv_map \<and> kv_map k = Some v \<longrightarrow>
    (\<exists>t cts sts lst rs rts rlst. svr_state (svrs s k) t = Commit cts sts lst v rs \<and> rs (get_txn s cl) = Some (rts, rlst)))"

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

subsection \<open>Timestamp relations\<close>

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
      Prep pd ts v \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = {}\<rparr>
    | Commit cts sts lst v rs \<Rightarrow> \<lparr>v_value = v, v_writer = t,
        v_readerset = {t. \<exists>rts rlst. (t, rts, rlst) \<in> rs \<and> get_sn t < cl_sn (cls s (get_cl t))}\<rparr>) ` set (cts_order s k) =
   {t \<in> set (cts_order s k). \<exists>pd ts v cts sts lst rs.
        svr_state (svrs s k) t \<in> {Prep pd ts v, Commit cts sts lst v rs}}"
  using assms
  by (auto simp add: image_iff CO_not_No_Ver_def split: ver_state.split)

lemma v_readerset_kvs_of_s_k:
  assumes "\<forall>k. CO_not_No_Ver s k"
    and "t_wr \<in> set (cts_order s k)"
  shows "v_readerset (case svr_state (svrs s k) t_wr of
      Prep pd ts v \<Rightarrow> \<lparr>v_value = v, v_writer = t_wr, v_readerset = {}\<rparr>
    | Commit cts sts lst v rs \<Rightarrow> \<lparr>v_value = v, v_writer = t_wr,
        v_readerset = {t. \<exists>rts rlst. (t, rts, rlst) \<in> rs \<and> get_sn t < cl_sn (cls s (get_cl t))}\<rparr>) = 
   {t. \<exists>cts sts lst v rs rts rlst. svr_state (svrs s k) t_wr = Commit cts sts lst v rs \<and>
      (t, rts, rlst) \<in> rs \<and> get_sn t < cl_sn (cls s (get_cl t))}"
  using assms
  by (auto split: ver_state.split)

lemma v_readerset_kvs_of_s:
  assumes "\<forall>k. CO_not_No_Ver s k"
  shows "(\<Union>k. \<Union>t_wr\<in>set (cts_order s k). v_readerset (case svr_state (svrs s k) t_wr of
      Prep pd ts v \<Rightarrow> \<lparr>v_value = v, v_writer = t_wr, v_readerset = {}\<rparr>
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
    and "cl_state (cls s cl) = RtxnInProg cclk keys kv_map"
  shows "closed' (kvs_of_s s') (cl_ctx (cls s cl) \<union> get_ctx s cl keys) (R_CC (kvs_of_s s'))"
  using assms
  by (auto simp add: closed'_def visTx'_union_distr visTx'_same_writers[of "kvs_of_s s'"] finite_read_wtxns
    Finite_Keys_def intro: closed_general_union_V_extend_N_extend_rel[where Y="read_wtxns s cl keys"]) old lemmas*)
                                                            
\<comment> \<open>write_commit closedness (canCommit)\<close>
lemma write_commit_WR_onK:
  assumes "write_commit cl kv_map commit_t sn u'' clk mmap s s'"
  shows "R_onK WR (kvs_of_s s') = R_onK WR (kvs_of_s s)"
  apply (auto simp add: R_onK_def WR_def) sorry

lemma write_commit_same_rel:
  assumes "write_commit cl kv_map commit_t sn u'' clk mmap s s'"
  shows "R_CC (kvs_of_s s') = R_CC (kvs_of_s s)"
  using assms
  by (auto simp add: R_CC_def write_commit_WR_onK)

lemma "dom kv_map \<noteq> {} \<Longrightarrow> snd ` (\<Union>k\<in>dom kv_map. {(k, t)}) = {t}"
  apply (auto simp add: image_def)
  by (metis domIff insertI1 sndI)

lemma write_commit_ctx_closed:    (* HERE *)
  assumes "write_commit cl kv_map commit_t sn u'' clk mmap s s'"
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
     (*using add_to_readerset_v_writer_img[of ] apply (simp add: txid_defs) sorry \<comment> \<open>Continue here!\<close>*)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case sorry
  qed (auto simp add: RO_WO_Inv_def tps_trans_defs)
qed


subsection \<open>View Invariants\<close>

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
    case (RInvoke x1 x2 x3 x4)
    then show ?case apply (simp add: View_Init_def tps_trans_defs get_view_def)
      by (meson Gst_le_Min_Lst_map_def linorder_not_le order.strict_trans2
          reach_tps reach_gst_le_min_lst_map reach_gst_lt_cl_cts)
  qed (auto simp add: View_Init_def tps_trans_defs get_view_def)
qed


definition Get_View_Committed where
  "Get_View_Committed s cl k \<longleftrightarrow> (\<forall>t. t \<in> get_view s cl k  \<longrightarrow>
    (is_committed (svr_state (svrs s k) t) \<or> 
    (\<exists>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<and> k \<in> dom kv_map \<and> t = get_wtxn s cl)))"

lemmas Get_View_CommittedI = Get_View_Committed_def[THEN iffD2, rule_format]
lemmas Get_View_CommittedE[elim] = Get_View_Committed_def[THEN iffD1, elim_format, rule_format]

lemma reach_get_view_committed[simp]:
  "reach tps_s s \<Longrightarrow> Get_View_Committed s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Get_View_Committed_def tps_s_defs get_view_def)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RInvoke x1 x2 x3 x4)
    then show ?case apply (auto simp add: Get_View_Committed_def tps_trans_defs get_view_def) sorry
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Get_View_Committed_def tps_trans_defs get_view_def) sorry
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Get_View_Committed_def tps_trans_defs get_view_def) sorry
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Get_View_Committed_def tps_trans_defs get_view_def) sorry
  qed (auto simp add: Get_View_Committed_def tps_trans_defs get_view_def)
qed

(* Closedness inv
definition Deps_Closed where
  "Deps_Closed s cl \<longleftrightarrow> (closed' (kvs_of_s s) (get_view s cl) (R_CC (kvs_of_s s)) \<and> 
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
    case (RDone x1 x2 x3 x4 x5)
    then show ?case using read_done_ctx_closed get_ctx_closed
      apply (auto simp add: Deps_Closed_def tps_trans_defs) sorry
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Deps_Closed_def tps_trans_defs) sorry
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case sorry
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case sorry
  qed (auto simp add: Deps_Closed_def tps_trans_defs)
qed
*)


subsection \<open>View Shift\<close>

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
    by (induction e) (auto simp add: Cl_WtxnCommit_Get_View_def tps_trans_defs get_view_def)
qed

lemma read_commit_added_txid:
  assumes "read_done cl kv_map sn u clk s s'"
    and "Tn (Tn_cl sn' cl) \<in> (kvs_txids (kvs_of_s s') - kvs_txids (kvs_of_s s))"
  shows "sn' = sn"
  using assms
  apply (auto simp add: read_done_def kvs_of_s_defs txid_defs split: ver_state.split) sorry

subsection \<open>Fp Property\<close>

\<comment> \<open>Fingerprint content invariant and Lemmas for proving the fp_property\<close>

definition RegR_Fp_Inv where
  "RegR_Fp_Inv s k \<longleftrightarrow> (\<forall>t cclk keys kv_map cts sts lst v rs.
    cl_state (cls s (get_cl t)) = RtxnInProg cclk keys kv_map \<and> k \<in> keys \<and> kv_map k = None \<and>
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
    case (RInvoke x1 x2 x3 x4)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs) sorry
  next
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs) sorry
  next
    case (RDone x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs) sorry
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs) sorry
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs) sorry
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs) sorry
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: RegR_Fp_Inv_def tps_trans_defs) sorry
  qed (auto simp add: RegR_Fp_Inv_def tps_trans_defs get_view_def)
qed

(* more inv to show v_value v_writer kvs_of_s commit_t kv_map relation*)

definition Rtxn_Fp_Inv where
  "Rtxn_Fp_Inv s cl \<longleftrightarrow> (\<forall>k cclk keys kv_map v.
    cl_state (cls s cl) = RtxnInProg cclk keys kv_map \<and> kv_map k = Some v \<longrightarrow>
     v = v_value ((kvs_of_s s k) ! Max (view_of (cts_order s) (get_view s cl) k)))"

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
    case (RDone x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case sorry
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case sorry
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case sorry
  qed (auto simp add: Rtxn_Fp_Inv_def tps_trans_defs view_of_def get_view_def)
qed


subsection \<open>Proofs in progress\<close>

(**************************************)
(**************************************)

(* lemmas about lists *)

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


(* 
  lemmas about views 
*)

lemma get_view_cls_update:
 "\<forall>k\<in>dom kv_map. \<forall>t\<in>set (cts_order gs k). unique_ts (wtxn_cts gs) t < (cts, cl) \<Longrightarrow>
   cts > gst (cls gs cl') \<Longrightarrow>
    get_view (gs\<lparr>cls := (cls gs)(cl := cls gs cl\<lparr>cl_state := X, cl_clock := Y\<rparr>),
                  wtxn_cts := (wtxn_cts gs)(get_wtxn gs cl \<mapsto> cts),
                  cts_order := new_cord \<rparr>) cl'
  = get_view gs cl'"
  apply (auto simp add: get_view_def; rule ext, auto) oops

lemma views_of_s_cls_update:  (* STILL NEEDED? *)
  "\<forall>k\<in>dom kv_map. \<forall>t\<in>set (cts_order gs k). unique_ts (wtxn_cts gs) t < (cts, cl) \<Longrightarrow>
   views_of_s (gs\<lparr>cls := (cls gs)(cl := cls gs cl\<lparr>cl_state := X, cl_clock := Y\<rparr>),
                  wtxn_cts := (wtxn_cts gs)(get_wtxn gs cl \<mapsto> cts),
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


lemma view_of_deps_mono:
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
    by (meson kvs_expands_through_update)
qed auto


lemma write_commit_views_of_s_other_cl_inv:
  assumes "reach tps_s s"
    and "write_commit_s cl kv_map cts sn u'' clk mmap s s'"
    and "cl' \<noteq> cl"
  shows "views_of_s s' cl' = views_of_s s cl'"
proof -
  have wtxn_None: "wtxn_cts s (get_wtxn s cl) = None"
    using assms(1,2) Wtxn_Cts_Tn_None_def[of s cl]
    by (auto simp add: tps_trans_defs)
  have reach_s': "reach tps_s s'" using assms(1,2)
    by (metis tps_trans state_trans.simps(5) reach_trans)
  obtain k pd ts v where
    "svr_state (svrs s k) (get_wtxn s cl) = Prep pd ts v \<and> k \<in> dom kv_map"
    using assms(1,2) Dom_Kv_map_Not_Emp_def[of s]
    apply (simp add: tps_trans_defs)
    by (meson domIff)
  then have "gst (cls s cl') < Max {get_ts (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map}"
    using assms Gst_lt_Cl_Cts_def[of s' cl' k] reach_s'
    apply (auto simp add: tps_trans_defs split: if_split_asm)
    by blast
  then have gv: "get_view s' cl' = get_view s cl'" using assms
    apply (auto simp add: get_view_def tps_trans_defs)
    using wtxn_None by blast
  show ?thesis unfolding views_of_s_def gv
  proof (intro view_of_prefix)
    fix k
    show "prefix (cts_order s k) (cts_order s' k)"
      using assms(2) write_commit_is_snoc[OF assms(1,2), of k]
      by (auto simp add: tps_trans_all_defs)
  next
    fix k
    show "distinct (cts_order s' k)" 
    using assms CO_Distinct_def reach_co_distinct
    by (metis state_trans.simps(5) tps_trans reach_trans)
  next
    fix k
    show "(set (cts_order s' k) - set (cts_order s k)) \<inter> get_view s cl' k = {}"
      using assms(2) write_commit_is_snoc[OF assms(1,2), of k]
      by (auto simp add: get_view_def wtxn_None tps_trans_all_defs)
  qed
qed


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
    case (RInvoke x1 x2 x3 x4)
  then show ?case sorry
next
  case (RDone x1 x2 x3 x4 x5)
    hence "view_wellformed (kvs_of_s s') (views_of_s s cl)" apply simp
    using kvs_expanded_view_wellformed by blast
    then show ?case using RDone
    apply (auto simp add: Views_of_s_Wellformed_def) sorry
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case
      apply (simp add: Views_of_s_Wellformed_def tps_trans_defs views_of_s_def get_view_def) sorry
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Views_of_s_Wellformed_def tps_trans_defs
          add_to_readerset_def split: ver_state.split) sorry
  next
    case (PrepW x1 x2 x3 x4 x5)    then show ?case apply (auto simp add: Views_of_s_Wellformed_def tps_trans_defs views_of_s_def get_view_def) sorry
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Views_of_s_Wellformed_def tps_trans_defs views_of_s_def get_view_def) sorry
  qed (auto simp add: Views_of_s_Wellformed_def tps_trans_defs views_of_s_def get_view_def)
qed


(**************************************)
(**************************************)

subsection \<open>Refinement Proof\<close>

definition invariant_list where
  "invariant_list s \<equiv> (\<forall>cl k. Sqn_Inv_c s cl \<and> Sqn_Inv_nc s cl
    \<and> Views_of_s_Wellformed s cl \<and> Rtxn_Fp_Inv s cl \<and> CO_Distinct s k
    \<and> T0_in_CO s k \<and> T0_First_in_CO s k \<and> View_Init s cl k \<and> FTid_notin_Get_View s cl)"

lemma invariant_listE [elim]: 
  "\<lbrakk> invariant_list s; 
     \<lbrakk> \<And>cl. Sqn_Inv_c s cl; \<And>cl. Sqn_Inv_nc s cl;
       \<And>cl. Rtxn_Fp_Inv s cl; \<And>k. CO_Distinct s k;
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
                       version_init_def get_view_def view_of_def the_T0)
next
  fix gs a and gs' :: "'v global_conf"
  assume p: "tps_s: gs\<midarrow>a\<rightarrow> gs'" and reach_s: "reach tps_s gs" and "reach ET_CC.ET_ES (sim gs)"
  then have I: "invariant_list gs" and reach_s': "reach tps_s gs'" by auto
  show "ET_CC.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  using p I reach_s kvs_of_s_inv[of gs a gs']
  proof (induction a)
    case (RInvoke cl keys sn clk)
    then show ?case
    proof -
      {
        assume vext: \<open>read_invoke cl keys sn clk gs gs'\<close>
        have \<open>ET_CC.ET_trans_and_fp 
                (kvs_of_s gs, views_of_s gs)
                 (ETViewExt cl)
                (kvs_of_s gs', views_of_s gs')\<close>
        proof (rule ET_CC.ET_view_ext_rule [where u'="views_of_s gs' cl"])
          show \<open>views_of_s gs cl \<sqsubseteq> views_of_s gs' cl\<close> using vext reach_s
            apply (auto simp add: tps_trans_defs get_view_def views_of_s_def
                        intro!: view_of_deps_mono)
            using Gst_le_Min_Lst_map_def[of gs cl]
            by auto
        next
          show \<open>view_wellformed (kvs_of_s gs) (views_of_s gs' cl)\<close> using vext
            by (metis state_trans.simps(1) RInvoke.prems(4) Views_of_s_Wellformed_def
                commit_ev.simps(3) reach_s reach_s' reach_views_of_s_wellformed)
        next
          show \<open>view_wellformed (kvs_of_s gs) (views_of_s gs cl)\<close>
            using reach_s reach_views_of_s_wellformed by auto
        next
          show \<open>kvs_of_s gs' = kvs_of_s gs\<close>
            by (simp add: RInvoke.prems(4) reach_s vext)
        next
          show \<open>views_of_s gs' = (views_of_s gs)(cl := views_of_s gs' cl)\<close> using vext
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
            by (simp add: tps_trans_defs invariant_list_def views_of_s_def
                Views_of_s_Wellformed_def)
        next
          show \<open>view_wellformed (kvs_of_s gs') (views_of_s gs' cl)\<close> using I
            by (metis Views_of_s_Wellformed_def p reach_s reach_trans reach_views_of_s_wellformed)
        next
          show \<open>view_wellformed (kvs_of_s gs) (views_of_s gs cl)\<close> using cmt I
            by (auto simp add: tps_trans_defs invariant_list_def)
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
 \<forall>k\<in>dom kv_map. \<exists>pd ts v. svr_state (svrs gs k) (get_wtxn gs cl) = Prep pd ts v \<and> kv_map k = Some v;
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
            apply (auto simp add: write_commit_s_def) apply (rule ext)
            by (smt (verit) cmt fun_upd_apply reach_s write_commit_views_of_s_other_cl_inv)
        qed
      }
      then show ?thesis using WCommit
        by (auto simp only: ET_CC.trans_ET_ES_eq tps_trans state_trans.simps sim_def med.simps)
    qed
  qed (auto simp add: sim_def views_of_s_def get_view_def tps_trans_defs invariant_list_def)
qed

end