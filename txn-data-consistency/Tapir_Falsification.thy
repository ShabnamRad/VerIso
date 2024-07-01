section \<open>Tapir Falsification\<close>

theory "Tapir_Falsification"
  imports "Tapir"
begin

subsection \<open>Lemmas and Invariants\<close>

lemma ext_map_neqE:
  "\<lbrakk>(\<lambda>k. map (\<lambda>t. P k t) (l k)) \<noteq> (\<lambda>k. map (\<lambda>t. Q k t) (l k)); \<exists>k t. P k t \<noteq> Q k t \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis"
proof -
  assume a1: "(\<lambda>k. map (P k) (l k)) \<noteq> (\<lambda>k. map (Q k) (l k))"
  assume a2: "\<exists>k t. P k t \<noteq> Q k t \<Longrightarrow> thesis"
  obtain aa :: 'a where
    "map (P aa) (l aa) \<noteq> map (Q aa) (l aa)"
    using a1 by metis
  then show ?thesis
    using a2 by metis
qed




subsection \<open>Refinement Attempt\<close>

lemma tps_refines_et_es: "tapir \<sqsubseteq>\<^sub>med ET_SER.ET_ES"
proof (intro simulate_ES_fun)
  fix gs0 :: "'v global_conf"
  assume p: "init tapir gs0"
  then show "init ET_SER.ET_ES (sim gs0)"
    by (auto simp add: ET_SER.ET_ES_defs tapir_defs sim_defs kvs_init_def v_list_init_def 
                       version_init_def)
next
  fix gs a and gs' :: "'v global_conf"
  assume p: "tapir: gs\<midarrow>a\<rightarrow> gs'" and reach_s: "reach tapir gs" and "reach ET_SER.ET_ES (sim gs)"
  then have (*I: "invariants_list gs" and *) reach_s': "reach tapir gs'" by auto
  with p show "ET_SER.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  proof (induction a)
    case (Cl_Commit cl sn u'' F ts  r_map w_map)
    show ?case 
    proof -
      { 
        assume cmt: \<open>cl_commit cl sn u'' F ts r_map w_map gs gs'\<close> (*and I: \<open>invariant_list gs\<close>*)
        have \<open>ET_SER.ET_trans_and_fp 
                (kvs_of_s gs, views_of_s gs) (ET cl sn u'' F) (kvs_of_s gs', views_of_s gs')\<close>
        proof (rule ET_SER.ET_trans_rule [where u'="full_view o (kvs_of_s gs')"])
          show \<open>views_of_s gs cl \<sqsubseteq> u''\<close> using cmt (* I
            apply (auto 4 3 simp add: cl_commit_def views_of_gs_def)*) sorry
        next 
          show \<open>ET_SER.canCommit (kvs_of_s gs) u'' F\<close> using cmt (* I 
            by (auto simp add: cl_commit_def full_view_satisfies_ET_SER_canCommit)*) sorry
        next 
          show \<open>view_wellformed (kvs_of_s gs) u''\<close> using cmt (* I
            by (auto 4 4 simp add: cl_commit_def full_view_wellformed)*) sorry
        next 
          show \<open>view_wellformed (kvs_of_s gs') (full_view o (kvs_of_s gs'))\<close> using cmt (*I
          proof - 
            have "KVSGSNonEmp gs'" using cmt I
              by (simp add: cl_commit_def KVSGSNonEmp_def KVSNonEmp_def invariant_list_def 
                            sim_defs(2) unchanged_defs(4))
            then show ?thesis 
              by (auto simp add: full_view_wellformed)
          qed*) sorry
        next 
          show \<open>view_wellformed (kvs_of_s gs) (views_of_s gs cl)\<close> (*using I
            by (auto 4 3 simp add: views_of_gs_def)*) sorry
        next 
          show \<open>Tn_cl sn cl \<in> next_txids (kvs_of_s gs) cl\<close> using cmt (*I
            by (auto simp add: cl_commit_def t_is_fresh)*) sorry
        next 
          show \<open>fp_property F (kvs_of_s gs) u''\<close>
          proof -
            have a: "\<And>k v. F k R = Some v \<Longrightarrow>
              \<exists>t. svr_state (svrs gs k) (get_wtxn gs cl) = occ_s (Some (v, t)) (F k W)"
              using cmt
              apply (auto simp add: cl_commit_def)
              by (smt UnI1 UnI2 eq_fst_iff map_option_eq_Some option.distinct(1))
            show ?thesis using cmt
              apply (auto simp add: cl_commit_def fp_property_def view_snapshot_def)
              subgoal for k v
                using a[of k v] apply auto sorry.
              (* Invariant: there is no timestamp inversion *)
              (*apply (cases "svr_state (svrs gs k) (get_txn cl gs) = no_lock")
              subgoal by (auto simp add: NoLockFpInv_def invariant_list_def)
              subgoal by (smt (verit) RLockFpContentInv_def WLockFpContentInv_def
                                      empty_iff insertCI insertE invariant_listE o_apply 
                                      option.distinct(1) option.inject svr_vl_kvs_eq_lv) 
              done*)
          qed
        next 
          show \<open>kvs_of_s gs' = update_kv (Tn_cl sn cl) F u'' (kvs_of_s gs)\<close> using cmt (*I
            by (auto 4 3 simp add: cl_commit_def kvs_of_gs_def update_kv_def 
                                   kvs_of_gs_cl_commit svr_cl_cl'_unchanged_def)*) sorry
        next 
          show \<open>views_of_s gs' = (views_of_s gs)(cl := full_view o (kvs_of_s gs'))\<close> using cmt (*I
            apply (auto simp add: cl_commit_def views_of_gs_def)
            apply (rule ext)
            by (auto simp add: cl_unchanged_defs intro: updated_is_kvs_of_gs')*) sorry
        qed simp
      }
      then show ?thesis using Cl_Commit
        by (simp only: ET_SER.trans_ET_ES_eq tapir_trans s_trans.simps sim_def med.simps)
    qed
  next
    case (Cl_Prep x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: sim_def tapir_trans_defs)
      by (rule ext, auto simp add: sim_defs split: svr_state.split)+
  next
    case (Cl_Read_Resp x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: sim_def tapir_trans_defs)
      by (rule ext, auto simp add: sim_defs split: svr_state.split)+
  next
    case (Cl_Abort x)
    then show ?case
      apply (auto simp add: sim_def tapir_trans_defs)
      by (rule ext, auto simp add: sim_defs split: svr_state.split)+
  next
    case (Cl_ReadyC x1 x2)
    then show ?case
      apply (auto simp add: sim_defs tapir_trans_defs)
      apply (rule ext, auto simp add: sim_defs split: svr_state.split) sorry
  next
    case (Cl_ReadyA x1 x2)
    then show ?case
      apply (auto simp add: sim_def tapir_trans_defs)
      by (rule ext, auto simp add: sim_defs split: svr_state.split)+
  next
    case (Prep x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: sim_defs tapir_trans_defs)
      subgoal apply (elim ext_map_neqE, auto)
        (*apply (auto simp add: sim_defs split: svr_state.split_asm option.split_asm)
        apply (smt (verit) fun_upd_other fun_upd_same svr_conf.select_convs(1) svr_conf.surjective
            svr_conf.update_convs(1) svr_state.distinct(13) svr_state.distinct(3))
        apply (smt (verit) fun_upd_other fun_upd_same svr_conf.select_convs(1) svr_conf.surjective
            svr_conf.update_convs(1) svr_state.distinct(17) svr_state.distinct(7))*) sorry
      sorry
  next
    case (OCCCheck x1 x2 x3 x4 x5 x6)
    then show ?case sorry
  next
    case (CommitR x1 x2 x3 x4)
    then show ?case sorry
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case sorry
  next
    case (Abort x1 x2)
    then show ?case sorry
  qed simp                            
qed

end
