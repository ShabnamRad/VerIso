section \<open>2PC-2PL: Refinement Proof\<close>

theory Serializable_2PC_2PL_Proof
  imports Serializable_2PC_2PL_State_Updates
begin

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

lemma get_sqns_cl_commit:   \<comment> \<open>used in SqnInv proof below\<close>
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
    by (simp add: KVSNonEmp_def full_view_elemD kvs_of_gs_def)
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
  assumes "reach tpl s"
  shows "SqnInv s"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: tpl_def intro!: SqnInvI)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_gs_not_cl_commit_inv[of s e s'] 
  proof (induction e)
    case (User_Commit cl)
    then show ?case
      apply (auto simp add: SqnInv_def tpl_trans_defs cl_unchanged_defs)
       apply (metis state_cl.distinct(3))
      by (metis state_cl.distinct(7))
  next
    case (Cl_Commit cl sn u'' F)
    then have "invariant_list_kvs s" by simp
    then show ?case using Cl_Commit 
      apply (auto simp add: tpl_trans_defs cl_unchanged_defs get_sqns_cl_commit intro!: SqnInvI)
      by (auto simp add: SqnInv_def split: if_split_asm) 
         (metis order_less_imp_le)+
  next
    case (Cl_Abort x)
    then show ?case 
      apply (auto simp add: SqnInv_def tpl_trans_defs cl_unchanged_defs)
       apply (metis state_cl.distinct(7)) 
      by (metis state_cl.distinct(11))
  next
    case (Cl_ReadyC x)
    then show ?case 
      apply (auto simp add: SqnInv_def tpl_trans_defs cl_unchanged_defs)
       apply (metis less_Suc_eq_le) 
      by (metis state_cl.distinct(3))
  next
    case (Cl_ReadyA x)
    then show ?case 
      apply (auto simp add: SqnInv_def tpl_trans_defs cl_unchanged_defs)
       apply (metis less_Suc_eq state_cl.distinct(11)) 
      by (metis state_cl.distinct(3))
  qed (auto simp add: SqnInv_def tpl_trans_defs svr_unchanged_defs)
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


subsection \<open>Refinement Proof\<close>

text \<open>List of all EP+ invariants\<close>

definition invariant_list where
  "invariant_list s \<longleftrightarrow> invariant_list_kvs s \<and> SqnInv s"

lemmas invariant_listI[intro] = invariant_list_def[THEN iffD2, rule_format]

lemma invariant_listE [elim]: 
 "\<lbrakk> invariant_list s; \<lbrakk> invariant_list_kvs s; SqnInv s \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add: invariant_list_def)


subsubsection \<open>Lemmas for proving @{term "ET_SER.canCommit"}\<close>

lemma cl_commit_canCommit:
  assumes 
    "cl_commit cl sn u'' F gs gs'"
    "invariant_list gs"
  shows 
    "ET_SER.canCommit (kvs_of_gs gs) u'' F"
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
    "fp_property F (kvs_of_gs gs) u''"
  using assms
  by (auto simp add: fp_property_def cl_commit_def view_snapshot_full_view_eq)


subsubsection \<open>Refinement proof proper\<close>

lemma tpl_refines_sser: "tpl \<sqsubseteq>\<^bsub>[sim,med]\<^esub> ET_SER.ET_ES"   
proof (intro simulate_ES_fun_h)
  fix gs0 :: "'v global_conf"
  assume p: "init tpl gs0"
  then show "init ET_SER.ET_ES (sim gs0)"
    by (auto simp add: ET_SER.ET_ES_defs tpl_defs sim_defs update_kv_all_defs
                       full_view_def kvs_init_def v_list_init_def eligible_reads_def lessThan_Suc)
next
  fix gs e and gs' :: "'v global_conf"
  assume p: "tpl: gs\<midarrow>e\<rightarrow> gs'" and reach: "reach tpl gs"
  then have reach': "reach tpl gs'" by auto  
  with reach have I: "invariant_list gs" and I':"invariant_list gs'" by auto
  show "ET_SER.ET_ES: sim gs\<midarrow>med e\<rightarrow> sim gs'"
  proof (cases "not_cl_commit e")
    case True
    then show ?thesis using p reach
      by (auto simp add: sim_def views_of_gs_def kvs_of_gs_not_cl_commit_inv)
  next
    case False
    then show ?thesis using p
    proof -
      { 
        fix cl sn u'' F
        assume cmt: \<open>cl_commit cl sn u'' F gs gs'\<close> 
        have \<open>ET_SER.ET_trans_and_fp 
                (kvs_of_gs gs, views_of_gs gs) (ET cl sn u'' F) 
                (kvs_of_gs gs', views_of_gs gs')\<close>
        proof (rule ET_SER.ET_trans_rule [where u'="view_init"])
          show \<open>views_of_gs gs cl \<sqsubseteq> u''\<close> using cmt I
            by (auto 4 3 simp add: cl_commit_def views_of_gs_def)
        next 
          show \<open>ET_SER.canCommit (kvs_of_gs gs) u'' F\<close> using cmt I 
            by (intro cl_commit_canCommit) 
        next 
          show \<open>view_wellformed (kvs_of_gs gs) u''\<close> using cmt I
            by (auto simp add: cl_commit_def)
        next 
          show \<open>view_wellformed (kvs_of_gs gs') view_init\<close> using cmt I'
            by (auto simp add: KVS_T0_init_implies_kvs_T0_init)
        next 
          show \<open>view_wellformed (kvs_of_gs gs) (views_of_gs gs cl)\<close> using I 
            by (auto simp add: views_of_gs_def KVS_T0_init_implies_kvs_T0_init)
        next 
          show \<open>Tn_cl sn cl \<in> next_txids (kvs_of_gs gs) cl\<close> using cmt I
            by (auto simp add: cl_commit_fresh_txid) 
        next 
          show \<open>fp_property F (kvs_of_gs gs) u''\<close> using cmt I
            by (intro cl_commit_fp_property)    
        next 
          show \<open>kvs_of_gs gs' = update_kv (Tn_cl sn cl) F u'' (kvs_of_gs gs)\<close> 
            using cmt I
            by (auto 4 3 intro: kvs_of_gs_cl_commit)
        next
          show \<open>views_of_gs gs' = (views_of_gs gs)(cl := view_init)\<close> 
            using cmt I
            by (auto simp add: views_of_gs_def)
        qed simp
      }
      then show ?thesis using p False
        by (clarsimp simp add: sim_def)
    qed
  qed
qed


end
