section \<open>2PC-2PL: Refinement Proof\<close>

theory Serializable_2PC_2PL_Proof
  imports Serializable_2PC_2PL_State_Updates
begin


subsection \<open>Basic lemmas [MOVE!]\<close>

(* To: State_Updates (?) *)

lemma kvs_of_gs_init [simp]: "kvs_of_gs gs_init = kvs_init"
  by (simp add: kvs_of_gs_def gs_init_def kvs_init_defs update_kv_key_reads_all_txn_def 
                eligible_reads_def)


subsection \<open>Sequence number invariant\<close>

subsection \<open>Lemmas\<close>

lemma not_no_lock_equiv_non_empty_fp:
  assumes
    "\<forall>k. is_locked (svr_state (svrs s k) t)"
    "\<And>k. WLockFpInv s k" "\<And>k. RLockFpInv s k" "\<And>k. NoLockFpInv s k"
  shows
    "(\<exists>k. svr_state (svrs s k) t \<noteq> no_lock) \<longleftrightarrow> (\<exists>k. svr_fp (svrs s k) t \<noteq> (\<lambda>x. None))"
  using assms 
  by (auto) (meson RLockFpInv_def WLockFpInv_def, blast)

lemma get_sqns_cl_commit:   (* used in SqnInv proof below *)
  assumes 
    "sn = cl_sn (cls s cl)" 
    "F = (\<lambda>k. svr_fp (svrs s k) (get_txn cl s))"
    "\<forall>k. is_locked (svr_state (svrs s k) (get_txn cl s))"
    "cl_state (cls s cl) = cl_prepared"
    "cl_state (cls s' cl) = cl_committed"
    "cl_sn (cls s' cl) = cl_sn (cls s cl)" 
    "svr_cl_cl'_unchanged cl s s'" 
    "invariant_list_kvs s"
  shows "get_sqns (kvs_of_gs s') cl' =
         (if cl = cl' \<and> (\<exists>k. svr_state (svrs s k) (get_txn cl s) \<noteq> no_lock) 
          then insert (cl_sn (cls s cl)) (get_sqns (kvs_of_gs s) cl')
          else get_sqns (kvs_of_gs s) cl')" 
  using assms
  apply (subst kvs_of_gs_cl_commit_unfolded)
  apply (simp_all add: split del: if_split)
  apply (subst get_sqns_update_kv)
  subgoal for k
    by (simp add: cl_commit_def full_view_elemD)
  subgoal 
    by (simp add: not_no_lock_equiv_non_empty_fp)
  done


subsection \<open>Invariant\<close>

definition SqnInv where
  "SqnInv s \<longleftrightarrow> (\<forall>cl.
    (cl_state (cls s cl) \<noteq> cl_committed \<longrightarrow> (\<forall>sn \<in> get_sqns (kvs_of_gs s) cl. sn < cl_sn (cls s cl))) \<and>
    (cl_state (cls s cl) = cl_committed \<longrightarrow> (\<forall>sn \<in> get_sqns (kvs_of_gs s) cl. sn \<le> cl_sn (cls s cl))))"

lemmas SqnInvI = SqnInv_def[THEN iffD2, rule_format]
lemmas SqnInvE[elim] = SqnInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_sql_inv [simp, dest]:
  assumes "reach tps s"
  shows "SqnInv s"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: tps_def intro!: SqnInvI)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_gs_not_cl_commit_inv[of s e s'] 
  proof (induction e)
    case (Prepare x1 x2)
    then show ?case 
      by (auto simp add: SqnInv_def tps_trans_defs svr_unchanged_defs)
  next
    case (RLock x1 x2 x3)
    then show ?case 
      by (auto simp add: SqnInv_def tps_trans_defs svr_unchanged_defs)
  next
    case (WLock x1 x2 x3 x4)
    then show ?case
      by (auto simp add: SqnInv_def tps_trans_defs svr_unchanged_defs)
  next
    case (NoLock x1 x2)
    then show ?case
      by (auto simp add: SqnInv_def tps_trans_defs svr_unchanged_defs)
  next
    case (NOK x1 x2)
    then show ?case 
      by (auto simp add: SqnInv_def tps_trans_defs svr_unchanged_defs)
  next
    case (Commit x1 x2)
    then show ?case
      by (auto simp add: SqnInv_def tps_trans_defs svr_unchanged_defs)
  next
    case (Abort x1 x2)
    then show ?case 
      by (auto simp add: SqnInv_def tps_trans_defs svr_unchanged_defs)
  next
    case (User_Commit cl)
    then show ?case
      apply (auto simp add: SqnInv_def tps_trans_defs cl_unchanged_defs)
       apply (metis state_cl.distinct(3))
      by (metis state_cl.distinct(7))
  next
    case (Cl_Commit cl sn u'' F)
    then have "invariant_list_kvs s" by simp
    then show ?case using Cl_Commit 
      apply (auto simp add: tps_trans_defs cl_unchanged_defs get_sqns_cl_commit intro!: SqnInvI)
      by (auto simp add: SqnInv_def split: if_split_asm) 
         (metis order_less_imp_le)+
  next
    case (Cl_Abort x)
    then show ?case 
      apply (auto simp add: SqnInv_def tps_trans_defs cl_unchanged_defs)
       apply (metis state_cl.distinct(7)) 
      by (metis state_cl.distinct(11))
  next
    case (Cl_ReadyC x)
    then show ?case 
      apply (auto simp add: SqnInv_def tps_trans_defs cl_unchanged_defs)
       apply (metis less_Suc_eq_le) 
      by (metis state_cl.distinct(3))
  next
    case (Cl_ReadyA x)
    then show ?case 
      apply (auto simp add: SqnInv_def tps_trans_defs cl_unchanged_defs)
       apply (metis less_Suc_eq state_cl.distinct(11)) 
      by (metis state_cl.distinct(3))
  qed (auto simp add: SqnInv_def tps_trans_defs svr_unchanged_defs)  (* only skip *)
qed


subsubsection \<open>Consequences: fresh txids\<close>

lemma txid_is_fresh:
  assumes "SqnInv s"
    and "cl_state (cls s cl) = cl_prepared"
  shows "get_txn cl s \<in> next_txids (kvs_of_gs s) cl"
  using assms by (auto simp add: kvs_of_gs_def next_txids_def SqnInv_def)

lemma cl_commit_fresh_txid:
  assumes "cl_commit cl sn u'' F s s'" "SqnInv s"
  shows "Tn_cl sn cl \<in> next_txids (kvs_of_gs s) cl"
  using assms
  by (auto simp add: cl_commit_def intro: txid_is_fresh)



subsection \<open>View well-formedness invariant\<close>

subsubsection \<open>Lemmas\<close>

lemma cl_view_init [simp]: "cl_view (cls gs_init cl) = (\<lambda>k. 1)"
  by (simp add: gs_init_def)

lemma cl_view_inv:
  assumes "gs_trans s e s'"
    and "not_cl_commit e"
  shows "cl_view (cls s' cl) = cl_view (cls s cl)"
  using assms 
  by (induction e) (auto simp add: tps_trans_defs unchanged_defs dest: eq_for_all_cl)

lemma cl_commit_cl_view_update:
  assumes "cl_commit cl sn u'' F s s'"
  shows "cl_view (cls s' cl') = 
           (if cl' = cl 
            then length \<circ> update_kv (Tn_cl sn cl) F (view_of_cl_view u'') (kvs_of_gs s) 
            else cl_view (cls s cl'))"
  using assms
  by (auto simp add: cl_commit_def cl_unchanged_defs)


(* lemmas about views_of_gs *)

lemma views_of_gs_init [simp]: "views_of_gs gs_init cl = view_init"
  by (simp add: views_of_gs_def view_of_cl_view_def view_init_def lessThan_Suc)

lemma views_of_gs_inv:
  assumes "gs_trans s e s'"
    and "not_cl_commit e"
  shows "views_of_gs s' cl = views_of_gs s cl"
  using assms 
  by (simp add: views_of_gs_def cl_view_inv)


(* lemmas about view_of_cl_view *)

lemma view_of_cl_view_monotonic:
  "u \<le> u' \<Longrightarrow> view_of_cl_view u \<sqsubseteq> view_of_cl_view u'"
  by (simp add: view_of_cl_view_def view_order_def le_funD)



(* view update under cl_commit *)

lemma cl_commit_views_of_gs_update:
  assumes "cl_commit cl sn u'' F s s'" 
  shows 
    "views_of_gs s' = 
      (\<lambda>cl'. if cl' = cl 
             then full_view \<circ> update_kv (Tn_cl sn cl) F (view_of_cl_view u'') (kvs_of_gs s) 
             else views_of_gs s cl')"
  using assms
  by (auto simp add: views_of_gs_def cl_commit_cl_view_update)


subsection \<open>Invariant\<close>

definition KVSView where
  "KVSView s \<longleftrightarrow> (\<forall>cl. view_wellformed (kvs_of_gs s) (views_of_gs s cl))"

lemmas KVSViewI = KVSView_def[THEN iffD2, rule_format]
lemmas KVSViewE[elim] = KVSView_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_view [simp, dest]:
  assumes "reach tps s" 
  shows "KVSView s"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (simp add: KVSView_def tps_def)
next
  case (reach_trans s e s')
  then show ?case
  proof (cases "not_cl_commit e")
    case True
    then show ?thesis using reach_trans 
      by (intro KVSViewI) (auto simp add: kvs_of_gs_not_cl_commit_inv views_of_gs_inv)
  next
    case False 
    then show ?thesis using reach_trans 
      by (intro KVSViewI)
         (auto 4 3 simp add: kvs_of_gs_cl_commit cl_commit_views_of_gs_update 
                   intro!: view_wellformed_update_kv cl_commit_fresh_txid 
                   dest!: update_kv_empty)
  qed
qed

subsubsection \<open>Consequences\<close>

definition TMFullView where
  "TMFullView s \<longleftrightarrow> (\<forall>cl. cl_view (cls s cl) \<le> length o kvs_of_gs s)"

lemmas TMFullViewI = TMFullView_def[THEN iffD2, rule_format]
lemmas TMFullViewE[elim] = TMFullView_def[THEN iffD1, elim_format, rule_format]

lemma KVSView_implies_TMFullView [simp, intro]: "KVSView s \<Longrightarrow> TMFullView s"
  by (auto simp add: KVSView_def TMFullView_def view_wellformed_def view_in_range_defs 
                     full_view_def le_funI view_of_cl_view_def views_of_gs_def)

lemma TMFullView_abstract_view: 
  "TMFullView s \<Longrightarrow> views_of_gs s cl \<sqsubseteq> (full_view o kvs_of_gs s)"
  by (auto simp add: views_of_gs_def simp flip: view_of_cl_view_length
           intro: view_of_cl_view_monotonic)



subsection \<open>Refinement Proof\<close>

text \<open>List of all EP+ invariants\<close>

definition invariant_list where   (* chsp removed: KVSGSNonEmp, TMFullView (both derivable) *)
  "invariant_list s \<longleftrightarrow> invariant_list_kvs s \<and> KVSView s \<and> SqnInv s"

lemmas invariant_listI = invariant_list_def[THEN iffD2, rule_format]

lemma invariant_listE [elim]: 
 "\<lbrakk> invariant_list s; \<lbrakk> invariant_list_kvs s; KVSView s; SqnInv s \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add: invariant_list_def)


subsubsection \<open>Lemmas for proving @{term "ET_SER.canCommit"}\<close>

lemma cl_commit_canCommit:
  assumes 
    "cl_commit cl sn u'' F gs gs'"
    "invariant_list gs"
  shows 
    "ET_SER.canCommit (kvs_of_gs gs) (view_of_cl_view u'') F"
  using assms
  by (auto simp add: cl_commit_def full_view_satisfies_ET_SER_canCommit)


subsubsection \<open>Lemmas for proving @{term "fp_property"}\<close>

lemma last_ver_v_update_kv_key_reads_all_txn:
  "last_ver_v (update_kv_key_reads_all_txn tCls tSvrs tFk vl) = last_ver_v vl"
  by (auto simp add: update_kv_key_reads_all_txn_def Let_def )
     (metis list_update_nonempty max_in_full_view v_value_inv_under_readerset_update)

lemma last_ver_v_update_kv_key_writes_all_txn:
  assumes "\<And>t. \<lbrakk> tCls t = cl_committed; tSvrs t = write_lock \<rbrakk> \<Longrightarrow> tFk (the_wr_t tSvrs) W = None" 
  shows "last_ver_v (update_kv_key_writes_all_txn tCls tSvrs tFk vl) = last_ver_v vl"
  using assms
  by (auto simp add: update_kv_key_writes_all_txn_def )

lemma last_ver_v_update_kv_all_txn:
  assumes "\<And>t. \<lbrakk> tCls t = cl_committed; tSvrs t = write_lock \<rbrakk> \<Longrightarrow> tFk (the_wr_t tSvrs) W = None" 
  shows "last_ver_v (update_kv_all_txn tCls tSvrs tFk vl) = last_ver_v vl"
  using assms
  by (auto simp add: update_kv_all_txn_def last_ver_v_update_kv_key_writes_all_txn 
                     last_ver_v_update_kv_key_reads_all_txn)

lemma view_snapshot_full_view_eq: 
  assumes 
    "cl_state (cls gs cl) = cl_prepared" 
    "is_locked (svr_state (svrs gs k) (get_txn cl gs))"
    "svr_fp (svrs gs k) (get_txn cl gs) R = Some v"
    "invariant_list gs"
  shows 
    "view_snapshot (kvs_of_gs gs) (full_view \<circ> kvs_of_gs gs) k = v"
  using assms
  apply (auto simp add: view_snapshot_def kvs_of_gs_def cl_commit_def)
  subgoal 
    apply (frule RLockFpContentInvD, auto)
    apply (subst last_ver_v_update_kv_all_txn, auto)
    by (meson RLockInv_def invariant_listE)
  subgoal
    apply (frule WLockFpContentInvD, auto)
    apply (subst last_ver_v_update_kv_all_txn, auto)
    by (metis WLockInv_def invariant_list_def state_cl.distinct(7) txid0.sel(2))
  subgoal 
    by (drule NoLockFpInvD, auto)
  done

lemma cl_commit_fp_property:
  assumes 
    "cl_commit cl sn u'' F gs gs'"
    "invariant_list gs"
  shows 
    "fp_property F (kvs_of_gs gs) (view_of_cl_view u'')"
  using assms
  by (auto simp add: fp_property_def cl_commit_def view_snapshot_full_view_eq)


subsubsection \<open>Refinement proof proper\<close>

lemma tps_refines_et_es: "tps \<sqsubseteq>\<^sub>med ET_SER.ET_ES"
proof (intro simulate_ES_fun_with_invariant[where I="invariant_list"])
  fix gs0 :: "'v global_conf"
  assume p: "init tps gs0"
  then show "init ET_SER.ET_ES (sim gs0)"
    by (auto simp add: ET_SER.ET_ES_defs tps_defs sim_defs update_kv_all_defs view_of_cl_view_def
                       full_view_def kvs_init_def v_list_init_def eligible_reads_def lessThan_Suc)
next
  fix gs a and gs' :: "'v global_conf"
  assume p: "tps: gs\<midarrow>a\<rightarrow> gs'" and inv: "invariant_list gs"
  then show "ET_SER.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  using kvs_of_gs_not_cl_commit_inv[of gs a gs'] cl_view_inv[of gs a gs'] 
  proof (induction a)
    case (Cl_Commit cl sn u'' F)
    show ?case 
    proof -
      { 
        assume cmt: \<open>cl_commit cl sn u'' F gs gs'\<close> and I: \<open>invariant_list gs\<close>
        have \<open>ET_SER.ET_trans_and_fp 
                (kvs_of_gs gs, views_of_gs gs) (ET cl sn (view_of_cl_view u'') F) 
                (kvs_of_gs gs', views_of_gs gs')\<close>

          thm ET_SER.ET_trans_rule
          term "view_of_cl_view (cl_view (cls gs' cl))"
          term "full_view o kvs_of_gs gs'"

        proof (rule ET_SER.ET_trans_rule [where u'="view_of_cl_view (cl_view (cls gs' cl))"])
          show \<open>views_of_gs gs cl \<sqsubseteq> view_of_cl_view u''\<close> using cmt I
            by (auto simp add: cl_commit_def intro!: TMFullView_abstract_view)  (* uses KVSView *)
        next 
          show \<open>ET_SER.canCommit (kvs_of_gs gs) (view_of_cl_view u'') F\<close> using cmt I 
            by (intro cl_commit_canCommit) 
        next 
          show \<open>view_wellformed (kvs_of_gs gs) (view_of_cl_view u'')\<close> using cmt I
            by (auto simp add: cl_commit_def)
        next 
          show \<open>view_wellformed (kvs_of_gs gs') (view_of_cl_view (cl_view (cls gs' cl)))\<close> using cmt I
            by (auto 4 3 simp add: kvs_of_gs_cl_commit cl_commit_cl_view_update 
                         dest!: update_kv_empty)
        next 
          show \<open>view_wellformed (kvs_of_gs gs) (views_of_gs gs cl)\<close> using I 
            thm KVSView_def
            by (auto 4 3)   (* This is invariant KVSView; should go by auto w/o any modifiers. *)
        next 
          show \<open>Tn_cl sn cl \<in> next_txids (kvs_of_gs gs) cl\<close> using cmt I
            by (auto simp add: cl_commit_fresh_txid) 
        next 
          show \<open>fp_property F (kvs_of_gs gs) (view_of_cl_view u'')\<close> using cmt I
            by (intro cl_commit_fp_property)    
        next 
          show \<open>kvs_of_gs gs' = update_kv (Tn_cl sn cl) F (view_of_cl_view u'') (kvs_of_gs gs)\<close> 
            using cmt I
            by (auto 4 3 intro: kvs_of_gs_cl_commit)
        next 
          show \<open>views_of_gs gs' = (views_of_gs gs)(cl := view_of_cl_view (cl_view (cls gs' cl)))\<close> 
            using cmt I
            by (auto simp add: cl_commit_cl_view_update cl_commit_views_of_gs_update)
        qed simp
      }
      then show ?thesis using Cl_Commit
        by (simp only: ET_SER.trans_ET_ES_eq tps_trans gs_trans.simps sim_def med.simps)
    qed
  qed (auto simp add: sim_defs invariant_list_def)
qed (simp add: invariant_list_def)


end
