theory "EP+_TCCv_update_kv_invs"
  imports "EP+_TCCv_proof"
begin

lemma map_list_update:
  "i < length l \<Longrightarrow> distinct l \<Longrightarrow>
   (map f l) [i := (map f l ! i) \<lparr>v_readerset := x\<rparr>] =
    map (f (l ! i := (f (l ! i)) \<lparr>v_readerset := x\<rparr>)) l"
  by (smt (verit) fun_upd_apply length_list_update length_map nth_eq_iff_index_eq
      nth_equalityI nth_list_update nth_map)

lemma view_of_in_range:
  assumes "i \<in> view_of (commit_order s) ctx k"
    and "CO_Distinct s k"
  shows "i < length (commit_order s k)"
  using assms
  apply (auto simp add: view_of_def Image_def CO_Distinct_def)
  by (smt (verit, best) distinct_Ex1 the1_equality)

lemma finite_view_of:
  "finite (view_of (commit_order s) ctx k)"
  by (simp add: view_of_def)

lemma view_of_non_emp:
  assumes "T0_in_CO s k"
    and "View_Init s cl"
  shows "view_of (commit_order s) (cl_ctx (cls s cl) \<union> u) k \<noteq> {}"
  using assms
  by (auto simp add: view_of_def)

lemma Max_view_of_in_range:
  assumes "view_of (commit_order s) ctx k \<noteq> {}"
    and "finite (view_of (commit_order s) ctx k)"
    and "CO_Distinct s k"
  shows "Max (view_of (commit_order s) ctx k) < length (commit_order s k)"
  using assms
  by (simp add: view_of_in_range)

lemma theI_of_ctx_in_CO:
  assumes "i = index_of (commit_order s k) t"
    and "t \<in> set (commit_order s k)"
    and "CO_Distinct s k"
  shows "commit_order s k ! i = t"
  using assms
  by (smt (verit, del_insts) CO_Distinct_def distinct_Ex1 theI_unique)

lemma view_of_committed:
  assumes "cl_state (cls s cl) = RtxnInProg keys kv_map"
    and "CO_Distinct s k"
    and "Ctx_Committed s"
    and "Get_Ctx_Commited s k"
    and "i \<in> view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s cl keys) k"
  shows "is_committed (svr_state (svrs s k) (commit_order s k ! i))"
  using assms Ctx_Committed_def[of s] theI_of_ctx_in_CO[of i s]
  apply (auto simp add: view_of_def Image_def)
    apply (metis (mono_tags) txn_state.distinct(9))
  using Get_Ctx_Commited_def[of s k]
  by (meson is_committed.elims(2))

lemma not_last_version_not_read:
  assumes "cl_state (cls s cl) = RtxnInProg (dom kv_map) kv_map"
    and "t_wr \<in> set (commit_order s k)"
    and "t_wr \<noteq> commit_order s k ! Max (view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s cl (dom kv_map)) k)"
    and "svr_state (svrs s k) t_wr = Commit cts sts lst v rs"
  shows "(get_txn s cl, rts, rlst) \<notin> rs"
  using assms
  apply (auto simp add: ) oops

definition Rtxn_Once_in_rs' where
  "Rtxn_Once_in_rs' s k \<longleftrightarrow> (\<forall>t.
    (\<forall>t' cts sts lst v rs. svr_state (svrs s k) t' = Commit cts sts lst v rs \<longrightarrow> t \<notin> rs) \<or> 
    (\<exists>!t'. \<exists>cts sts lst v rs. svr_state (svrs s k) t' = Commit cts sts lst v rs \<and> t \<in> rs))"

inductive ver_step :: "'v ver_state \<Rightarrow> 'v ver_state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>v" 60) where
  "ver_step v v" |
  "ver_step No_Ver (Prep pts v)" |
  "ver_step (Prep pts v) (Commit cts sts lst v {})" |
  "rs' = insert t rs \<Longrightarrow> ver_step (Commit cts sts lst v rs) (Commit cts sts lst v rs')"

lemma ver_step_inv:
  assumes "state_trans_h s e s'"
  shows "\<forall>t. svr_state (svrs s k) t \<rightarrow>\<^sub>v svr_state (svrs s' k) t"
  using assms
proof (induction e)
  case (RegR x1 x2 x3 x4)
  then show ?case by (auto simp add: tps_trans_defs add_to_readerset_def
   intro: ver_step.intros split: ver_state.split)
next
  case (CommitW x1 x2 x3 x4)
  then show ?case by (auto simp add: tps_trans_defs intro: ver_step.intros)
qed (auto simp add: tps_trans_defs intro: ver_step.intros)

lemma rtxn_get_ctx:
  assumes "state_trans_h s e s'"
    and "Gst_Lt_Cts s cl"
    and "\<And>k. Init_Ver_Inv s k"
    and "cl_state (cls s cl) = RtxnInProg keys kv_map"
    and "cl_state (cls s' cl) = RtxnInProg keys kv_map'"
  shows "get_ctx s' cl keys = get_ctx s cl keys"
  using assms Gst_Lt_Cts_def[of s cl]
proof (induction e)
  case (WCommit x1 x2 x3 x4 x5)
  then show ?case
    apply (auto simp add: tps_trans_defs get_ctx_defs split: if_split_asm) sorry
next
  case (RegR x1 x2 x3 x4)
  then show ?case
    by (auto simp add: tps_trans_defs get_ctx_defs add_to_readerset_pres_read_at
        split: if_split_asm, metis+)
next
  case (PrepW x1 x2 x3)
  then show ?case
    apply (auto simp add: tps_trans_defs get_ctx_def prepare_write_pres_read_at
                split: if_split_asm)
    using Init_Ver_Inv_def[of s x1] sorry
next
  case (CommitW x1 x2 x3 x4)
  then show ?case sorry
qed (auto simp add: tps_trans_defs get_ctx_defs)
  

definition Rtxn_Once_in_rs where
  "Rtxn_Once_in_rs s k \<longleftrightarrow> (\<forall>t_rd t_wr cts sts lst v rs rts rlst. 
    svr_state (svrs s k) t_wr = Commit cts sts lst v rs \<and> (t_rd, rts, rlst) \<in> rs \<longrightarrow>
    (\<exists>i. is_done s t_rd \<and> t_wr = commit_order s k ! i \<and> i \<in> view_of (commit_order s) (cl_ctx (cls s (get_cl t_rd))) k) \<or>
    (\<exists>keys kv_map. is_curr_t s t_rd \<and> cl_state (cls s (get_cl t_rd)) = RtxnInProg keys kv_map \<and>
    t_wr = commit_order s k ! Max (view_of (commit_order s) (cl_ctx (cls s (get_cl t_rd)) \<union>
      get_ctx s (get_cl t_rd) keys) k)))"

lemmas Rtxn_Once_in_rsI = Rtxn_Once_in_rs_def[THEN iffD2, rule_format]
lemmas Rtxn_Once_in_rsE[elim] = Rtxn_Once_in_rs_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_once_in_rs [simp]: "reach tps_h s \<Longrightarrow> Rtxn_Once_in_rs s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Rtxn_Once_in_rs_def tps_defs split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case using rtxn_get_ctx[of s e s']
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (auto simp add: Rtxn_Once_in_rs_def tps_trans_defs)
      apply blast
      apply blast
      apply (metis txn_state.distinct(1))
      apply (metis txn_state.distinct(1))
      apply blast
      apply blast
      apply (smt (verit))
      by (smt (verit))
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (auto simp add: Rtxn_Once_in_rs_def tps_trans_defs)
      apply blast
      apply blast
      apply (metis txn_state.inject(1))
      apply (metis txn_state.inject(1))
      apply blast
      apply blast
      apply (smt (verit))
      by (smt (verit))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: Rtxn_Once_in_rs_def tps_trans_defs)
      using FTid_notin_rs_def
      apply (metis Nat.not_less_eq reach_ftid_notin_rs txid0.exhaust txid0.sel(1) txid0.sel(2))
      using FTid_notin_rs_def sorry
  next
    case (WInvoke x1 x2)
    then show ?case apply (simp add: Rtxn_Once_in_rs_def tps_trans_defs)
      by (smt (verit) txn_state.distinct(1))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Rtxn_Once_in_rs_def tps_trans_defs)
      apply (metis (no_types, lifting) txn_state.distinct(7)) sorry
  next
    case (WDone x1 x2)
    then show ?case using FTid_notin_rs_def
      apply (auto simp add: Rtxn_Once_in_rs_def tps_trans_defs)
      apply (metis (no_types, lifting) less_Suc_eq)
      apply (metis (no_types, lifting) txn_state.distinct(9))
      apply blast
      apply blast
      apply (smt (verit))
      by (smt (verit))
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (auto simp add: Rtxn_Once_in_rs_def tps_trans_defs)
      subgoal for keys kv_map t_rd t_wr cts v rs
        apply (cases "get_cl t_rd = get_cl x2"; cases "cl_state (cls s (get_cl t_rd))")
        apply auto
        using Fresh_wr_notin_rs_def[of s "get_cl x2"]
        add_to_readerset_commit_subset[of "svr_state (svrs s x1)" x2 "svr_clock (svrs s x1)" "svr_lst (svrs s x1)"
         "read_at (svr_state (svrs s x1)) (gst (cls s (get_cl x2))) (get_cl x2)" t_wr cts v rs] sorry sorry
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Rtxn_Once_in_rs_def tps_trans_defs) sorry
  next
    case (CommitW x1 x2 x3 x4)
    then show ?case apply (simp add: Rtxn_Once_in_rs_def tps_trans_defs) sorry
  qed simp
qed

lemma read_done_h_kvs_of_s:
  assumes "read_done_h cl kv_map sn u'' s s'"
    and "cl_state (cls s cl) = RtxnInProg (dom kv_map) kv_map"
    and "\<And>k. commit_order s' k = commit_order s k"
    and "\<And>k. CO_Distinct s k"
    and "\<And>k. CO_not_No_Ver s k"
    and "\<And>k. T0_in_CO s k"
    and "View_Init s cl"
    and "Rtxn_IdleK_notin_rs s cl"
    and "\<And>k. Rtxn_Once_in_rs s k"
    and "Ctx_Committed s"
    and "\<And>k. Get_Ctx_Commited s k"
  shows "kvs_of_s s' = update_kv (Tn_cl sn cl)
          (read_only_fp kv_map)
          (view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s cl (dom kv_map)))
          (kvs_of_s s)"
  using assms
  apply (auto simp add: update_kv_defs)
  apply (rule ext) subgoal for k apply (cases "kv_map k")
  subgoal apply (auto simp add: read_done_h_def read_done_U_def kvs_of_s_defs split: ver_state.split)
    by (smt (verit, best) Rtxn_IdleK_notin_rs_def domIff less_antisym txid0.collapse)
  subgoal for v
    apply (auto simp add: Let_def kvs_of_s_def)
    apply (subst map_list_update)
    subgoal by (meson Max_in finite_view_of view_of_in_range view_of_non_emp)
    subgoal by blast
    subgoal apply (auto simp add: txn_to_vers_def)
        subgoal \<comment> \<open>t_wr' = commit_order ! Max (view_of ...)\<close>
          using Max_view_of_in_range[of s "cl_ctx (cls s cl) \<union> get_ctx s cl (dom kv_map)" k]
            view_of_committed[of s cl "dom kv_map" kv_map k 
          "Max (view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s cl (dom kv_map)) k)"]
          finite_view_of[of s "cl_ctx (cls s cl) \<union> get_ctx s cl (dom kv_map)" k]
          view_of_non_emp[of s k cl "get_ctx s cl (dom kv_map)"]
        apply simp using CO_not_No_Ver_def[of s k]
         (*apply (auto simp add: read_done_h_def split: ver_state.split)
          apply (metis not_less_less_Suc_eq txid0.exhaust_sel)
        using Rtxn_RegK_Kvtm_Cmt_in_rs_def[of s cl]*) sorry
        subgoal for t_wr_old \<comment> \<open>t_wr' \<noteq> commit_order ! Max (view_of ...)\<close>
         apply (auto simp add: read_done_h_def read_done_U_def split: ver_state.split)
          subgoal for cts' sts' lst' v' rs' t_rd
           apply (cases "get_sn t_rd = cl_sn (cls s cl)", simp_all)
           apply (cases t_rd, auto)
           using Rtxn_Once_in_rs_def
           by (metis assms(2) less_irrefl_nat txid0.sel(1) txid0.sel(2) txn_state.inject(1)).
       done.
     done.

end