section \<open>Tapir Falsification\<close>

theory "Tapir_Falsification"
  imports "Tapir"
begin

subsection \<open>Lemmas and Invariants\<close>

lemma update_kv_all_txn_v_value_inv:
  assumes "i \<in> full_view vl"
  shows "v_value (update_kv_all_txn tStm tSkm tFk vl ! i) = v_value (vl ! i)"
  using assms
  by (auto simp add: update_kv_all_defs update_kv_key_writes_simps nth_append full_view_def
           split: option.split)

lemma update_kv_key_reads_all_txn_length [simp]:
  "length (update_kv_key_reads_all_txn tStm tSkm tFk vl) = length vl"
  by (auto simp add: update_kv_key_reads_all_defs)

lemma writer_update_before:
  assumes "reach tapir s"
    and "cl_state (cls s cl) = cl_prepared ts"
    and "svr_state (svrs s k) (get_txn cl s) = occ_s"
  shows "update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k)) tFk vl =
         update_kv_key_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k)) tFk vl"
  using assms
  (*by (auto 4 3 simp add: update_kv_all_defs split: option.split)*) oops

lemma svr_vl_kvs_eq_length:
  assumes "reach tapir s"
    and "cl_state (cls s cl) = cl_prepared ts"
    and "svr_state (svrs s k) (get_txn cl s) = occ_s"
  shows "length (kvs_of_gs s k) = length (svr_vl (svrs s k))"
  using assms
  apply (auto simp add: kvs_of_gs_def update_kv_all_defs)
  (*by (metis assms(1) update_kv_key_reads_all_txn_length writer_update_before)*) oops

lemma svr_vl_kvs_eq_lv:
  assumes "reach tapir s"
    and "cl_state (cls s cl) = cl_prepared ts"
    and "svr_state (svrs s k) (get_txn cl s) = occ_s"
  shows "v_value (last_version (kvs_of_gs s k) (full_view (kvs_of_gs s k))) =
         v_value (last_version (svr_vl (svrs s k)) (full_view (svr_vl (svrs s k))))"
  using assms (*svr_vl_kvs_eq_length[of s]
    update_kv_all_txn_v_value_inv[of "Max {..<length (svr_vl (svrs s k))}" "svr_vl (svrs s k)"]
  apply (auto simp add: full_view_def kvs_of_gs_def KVSNonEmp_def)
  apply (metis full_view_def lessThan_iff max_in_full_view)
  by (metis full_view_def lessThan_iff max_in_full_view)*) oops

subsection \<open>Refinement Attempt\<close>

lemma tps_refines_et_es: "tapir \<sqsubseteq>\<^sub>med ET_SER.ET_ES"
proof (intro simulate_ES_fun)
  fix gs0 :: "'v global_conf"
  assume p: "init tapir gs0"
  then show "init ET_SER.ET_ES (sim gs0)"
    by (auto simp add: ET_SER.ET_ES_defs tapir_defs sim_defs kvs_init_def v_list_init_def 
                       version_init_def update_kv_all_defs eligible_reads_def)
next
  fix gs a and gs' :: "'v global_conf"
  assume p: "tapir: gs\<midarrow>a\<rightarrow> gs'" and reach_s: "reach tapir gs" and "reach ET_SER.ET_ES (sim gs)"
  then have (*I: "invariants_list gs" and *) reach_s': "reach tapir gs'" by auto
  with p show "ET_SER.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  proof (induction a)
    case (Cl_Commit cl sn u'' F ts)
    show ?case 
    proof -
      { 
        assume cmt: \<open>cl_commit cl sn u'' F ts gs gs'\<close> (*and I: \<open>invariant_list gs\<close>*)
        have \<open>ET_SER.ET_trans_and_fp 
                (kvs_of_gs gs, views_of_gs gs) (ET cl sn u'' F) (kvs_of_gs gs', views_of_gs gs')\<close>
        proof (rule ET_SER.ET_trans_rule [where u'="full_view o (updated_kvs gs cl ts)"])
          show \<open>views_of_gs gs cl \<sqsubseteq> u''\<close> using cmt (* I
            apply (auto 4 3 simp add: cl_commit_def views_of_gs_def)*) sorry
        next 
          show \<open>ET_SER.canCommit (kvs_of_gs gs) u'' F\<close> using cmt (* I 
            by (auto simp add: cl_commit_def full_view_satisfies_ET_SER_canCommit)*) sorry
        next 
          show \<open>view_wellformed (kvs_of_gs gs) u''\<close> using cmt (* I
            by (auto 4 4 simp add: cl_commit_def full_view_wellformed)*) sorry
        next 
          show \<open>view_wellformed (kvs_of_gs gs') (full_view o (updated_kvs gs cl ts))\<close> using cmt (*I
          proof - 
            have "KVSGSNonEmp gs'" using cmt I
              by (simp add: cl_commit_def KVSGSNonEmp_def KVSNonEmp_def invariant_list_def 
                            sim_defs(2) unchanged_defs(4))
            then show ?thesis 
              by (auto simp add: full_view_wellformed)
          qed*) sorry
        next 
          show \<open>view_wellformed (kvs_of_gs gs) (views_of_gs gs cl)\<close> (*using I
            by (auto 4 3 simp add: views_of_gs_def)*) sorry
        next 
          show \<open>Tn_cl sn cl \<in> next_txids (kvs_of_gs gs) cl\<close> using cmt (*I
            by (auto simp add: cl_commit_def t_is_fresh)*) sorry
        next 
          show \<open>fp_property F (kvs_of_gs gs) u''\<close> using cmt
            apply (auto simp add: cl_commit_def fp_property_def view_snapshot_def)
              (* Invariant: there is no timestamp inversion *)
            subgoal for k a b
              (*apply (cases "svr_state (svrs gs k) (get_txn cl gs) = no_lock")
              subgoal by (auto simp add: NoLockFpInv_def invariant_list_def)
              subgoal by (smt (verit) RLockFpContentInv_def WLockFpContentInv_def
                                      empty_iff insertCI insertE invariant_listE o_apply 
                                      option.distinct(1) option.inject svr_vl_kvs_eq_lv) 
              done*) sorry
            sorry
        next 
          show \<open>kvs_of_gs gs' = update_kv (Tn_cl sn cl) F u'' (kvs_of_gs gs)\<close> using cmt (*I
            by (auto 4 3 simp add: cl_commit_def kvs_of_gs_def update_kv_def 
                                   kvs_of_gs_cl_commit svr_cl_cl'_unchanged_def)*) sorry
        next 
          show \<open>views_of_gs gs' = (views_of_gs gs)(cl := full_view o (updated_kvs gs cl ts))\<close> using cmt (*I
            apply (auto simp add: cl_commit_def views_of_gs_def)
            apply (rule ext)
            by (auto simp add: cl_unchanged_defs intro: updated_is_kvs_of_gs')*) sorry
        qed simp
      }
      then show ?thesis using Cl_Commit
        by (simp only: ET_SER.trans_ET_ES_eq tapir_trans s_trans.simps sim_def med.simps)
    qed
  next
    case (Cl_Prep x1 x2)
    then show ?case apply (auto simp add: sim_defs tapir_trans_defs)
      apply (rule ext)                
      apply (auto simp add: update_kv_all_defs eligible_reads_def)
      by (smt (verit) Collect_cong state_cl.distinct(4) version.cases version.update_convs(3))+
  next
    case (Cl_Abort x)
    then show ?case apply (auto simp add: sim_defs tapir_trans_defs)
      apply (rule ext)                
      apply (auto simp add: update_kv_all_defs eligible_reads_def)
      by (smt (verit) Collect_cong state_cl.distinct(7) version.cases version.update_convs(3))+
  next
    case (Cl_ReadyA x)
    then show ?case apply (auto simp add: sim_defs tapir_trans_defs)
      apply (rule ext)                
      apply (auto simp add: update_kv_all_defs eligible_reads_def)
      by (smt (verit) Collect_cong state_cl.distinct(11) version.cases version.update_convs(3))+
  next
    case (TryPrep x1 x2 x3)
    then show ?case sorry
  next
    case (OCCCheck x1 x2 x3)
    then show ?case sorry
  next
    case (Commit x1 x2)
    then show ?case sorry
  next
    case (Abort x1 x2)
    then show ?case sorry
  next
    case (Cl_ReadyC x)
    then show ?case sorry
  qed simp                            
qed

end
