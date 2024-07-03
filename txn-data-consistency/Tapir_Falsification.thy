section \<open>Tapir Falsification\<close>

theory "Tapir_Falsification"
  imports "Tapir"
begin

subsection \<open>Lemmas and Invariants\<close>

lemma cl_commit_svrs_unchanged [dest]:
  "s' = s \<lparr>cls := (cls s) (x1 := cls s x1 \<lparr>cl_state := A, cl_view := B\<rparr>), commit_order := C\<rparr>
    \<Longrightarrow> svrs s' = svrs s" by auto

lemma occ_check_res:
  "occ_check k t ts rto wvo s \<in> {aborted, prepared ts rto wvo}"
  by (simp add: occ_check_def)

lemma read_resp_abs_committed_reads_inv:
  assumes "svr_state (svrs s k) (Tn t) = idle"
  shows
    "abs_committed_reads (s \<lparr>svrs := (svrs s)
      (k := svrs s k \<lparr>svr_state := (svr_state (svrs s k)) (Tn t := read X)\<rparr>)\<rparr>) k' t_wr =
     abs_committed_reads s k' t_wr"
  using assms
  by (auto simp add: abs_committed_reads_def read_resp_def)

definition Svr_Ver_Ord_Non_Emp where
  "Svr_Ver_Ord_Non_Emp s k \<longleftrightarrow> svr_ver_order (svrs s k) \<noteq> []"
                                                           
lemmas Svr_Ver_Ord_Non_EmpI = Svr_Ver_Ord_Non_Emp_def[THEN iffD2, rule_format]
lemmas Svr_Ver_Ord_Non_EmpE[elim] = Svr_Ver_Ord_Non_Emp_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_svr_ver_ord_non_emp [simp, dest]: "reach tapir s \<Longrightarrow> Svr_Ver_Ord_Non_Emp s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Svr_Ver_Ord_Non_Emp_def tapir_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Svr_Ver_Ord_Non_Emp_def tapir_trans_defs)
qed

definition Svr_Ver_Ord_Cmt where
  "Svr_Ver_Ord_Cmt s k \<longleftrightarrow> (\<forall>t \<in> set (svr_ver_order (svrs s k)).
    (\<exists>ts rto v. svr_state (svrs s k) t = committed ts rto (Some v)))"
                                                           
lemmas Svr_Ver_Ord_CmtI = Svr_Ver_Ord_Cmt_def[THEN iffD2, rule_format]
lemmas Svr_Ver_Ord_CmtE[elim] = Svr_Ver_Ord_Cmt_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_svr_ver_ord_cmt [simp, dest]: "reach tapir s \<Longrightarrow> Svr_Ver_Ord_Cmt s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Svr_Ver_Ord_Cmt_def tapir_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Svr_Ver_Ord_Cmt_def tapir_trans_defs)
qed

definition Read_Twr_Cmt where
  "Read_Twr_Cmt s k \<longleftrightarrow> (\<forall>t t_wr ts wvo.
    svr_state (svrs s k) t \<in> {read (Some t_wr),
                              prepared ts (Some t_wr) wvo,
                              committed ts (Some t_wr) wvo} \<longrightarrow> 
    (\<exists>ts' rto' v. svr_state (svrs s k) t_wr = committed ts' rto' (Some v)))"
                                                           
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
    then show ?case using Svr_Ver_Ord_Non_Emp_def[of s k] Svr_Ver_Ord_Cmt_def[of s k]
      apply (simp add: Read_Twr_Cmt_def tapir_trans_defs)
      by (smt last_in_set option.discI option.inject svr_state.distinct(5))
  next
    case (Prep x1 x2 x3 x4 x5a)
    then show ?case
      apply (simp add: Read_Twr_Cmt_def tapir_trans_defs)
      by (smt Read_Twr_Cmt_def all_not_in_conv fun_upd_apply insert_iff occ_check_res
          reach_trans.IH svr_state.distinct(9,11,13,15,17,19) svr_state.inject(2))
  next
    case (Commit x1 x2 x3 x4 x5a)
    then show ?case
      apply (auto simp add: Read_Twr_Cmt_def tapir_trans_defs)
      by (metis svr_state.distinct(15))+
  next
    case (Abort x1 x2)
    then show ?case
      apply (simp add: Read_Twr_Cmt_def tapir_trans_defs)
      by (metis svr_state.distinct(15) svr_state.distinct(19))
  qed (auto simp add: Read_Twr_Cmt_def tapir_trans_defs)
qed

subsection \<open>Refinement Attempt\<close>

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
  then have (*I: "invariants_list gs" and *) reach_s': "reach tapir gs'" by auto
  with p show "ET_SER.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  proof (induction a)
    case (Cl_Commit cl sn u'' F ts r_map w_map)
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
            have a: "\<And>k t. r_map k = Some t \<Longrightarrow>
              \<exists>ts rto v. svr_state (svrs gs k) t = committed ts rto (Some v)"
              using cmt reach_s Read_Twr_Cmt_def[of gs]
              apply (auto simp add: cl_commit_def)
              by (metis (no_types, lifting) Un_iff domI)
            show ?thesis using cmt
              apply (auto simp add: cl_commit_def fp_property_def view_snapshot_def)
              subgoal for k t_wr
                using a[of k t_wr] apply auto
            (* Invariant: there is no timestamp inversion *)
            (*apply (cases "svr_state (svrs gs k) (get_txn cl gs) = no_lock")
            subgoal by (auto simp add: NoLockFpInv_def invariant_list_def)
            subgoal by (smt (verit) RLockFpContentInv_def WLockFpContentInv_def
                                    empty_iff insertCI insertE invariant_listE o_apply 
                                    option.distinct(1) option.inject svr_vl_kvs_eq_lv) 
            done*) sorry sorry
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
    then show ?case sorry
  next
    case (Commit x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (Abort x1 x2)
    then show ?case sorry
  qed simp                            
qed

end
