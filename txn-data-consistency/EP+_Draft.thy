theory "EP+_Draft"
  imports "EP+_Refinement_Proof"
begin

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

lemma view_of_committed_in_kvs:
  assumes "cl_state (cls s cl) = RtxnInProg cclk keys kv_map"
    and "reach tps_s s"
    and "i \<in> view_of (cts_order s) (get_view s cl) k"
    and "t_wr = cts_order s k ! i"
  shows "is_committed_in_kvs s k t_wr"
  using assms Get_View_Committed_def[of s cl k] theI_of_ctx_in_CO[of i s]
  by (auto simp add: view_of_def)

lemma not_last_version_not_read:
  assumes "cl_state (cls s cl) = RtxnInProg cclk (dom kv_map) kv_map"
    and "t_wr \<in> set (cts_order s k)"
    and "t_wr \<noteq> cts_order s k ! Max (view_of (cts_order s) (get_view s cl) k)"
    and "svr_state (svrs s k) t_wr = Commit cts sts lst v rs"
  shows "rs (get_txn s cl) = None"
  using assms oops

definition Rtxn_Once_in_rs' where
  "Rtxn_Once_in_rs' s k \<longleftrightarrow> (\<forall>t.
    (\<forall>t' cts sts lst v rs. svr_state (svrs s k) t' = Commit cts sts lst v rs \<longrightarrow> t \<notin> dom rs) \<or> 
    (\<exists>!t'. \<exists>cts sts lst v rs. svr_state (svrs s k) t' = Commit cts sts lst v rs \<and> t \<in> dom rs))"

inductive ver_step :: "'v ver_state \<Rightarrow> 'v ver_state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>v" 60) where
  "ver_step v v" |
  "ver_step No_Ver (Prep pdts pts v)" |
  "ver_step (Prep pdts pts v) (Commit cts sts lst v rs_emp)" |
  "rs' = rs (t \<mapsto> (x, y)) \<Longrightarrow> ver_step (Commit cts sts lst v rs) (Commit cts sts lst v rs')"

lemma ver_step_inv:
  assumes "state_trans s e s'"
  shows "\<forall>t. svr_state (svrs s k) t \<rightarrow>\<^sub>v svr_state (svrs s' k) t"
  using assms
proof (induction e)
  case (RegR x1 x2 x3 x4 x5 x6 x7)
  then show ?case by (auto simp add: tps_trans_defs add_to_readerset_def
   intro: ver_step.intros split: ver_state.split)
next
  case (CommitW x1 x2 x3 x4 x5 x6 x7)
  then show ?case by (auto simp add: tps_trans_defs intro: ver_step.intros)
qed (auto simp add: tps_trans_defs intro: ver_step.intros)

lemma rtxn_get_view:
  assumes "state_trans s e s'"
    and "reach tps_s s"
    and "cl_state (cls s cl) = RtxnInProg cclk keys kv_map"
    and "cl_state (cls s' cl) = RtxnInProg cclk keys kv_map'"
  shows "get_view s' cl = get_view s cl"
  using assms Gst_lt_Cts_def[of s cl]
proof (induction e)
  case (WCommit x1 x2 x3 x4 x5 x6 x7)
  then show ?case
    apply (auto simp add: tps_trans_defs get_view_def split: if_split_asm)
    apply (intro ext Collect_eqI) sorry
qed (auto simp add: tps_trans_defs get_view_def)
  

definition Rtxn_Once_in_rs where
  "Rtxn_Once_in_rs s k \<longleftrightarrow> (\<forall>t_rd t_wr cts sts lst v rs rts rlst. 
    svr_state (svrs s k) t_wr = Commit cts sts lst v rs \<and> rs t_rd = Some (rts, rlst) \<longrightarrow>
    (\<exists>i. is_done s t_rd \<and> t_wr = cts_order s k ! i \<and> i \<in> view_of (cts_order s) (get_view s (get_cl t_rd)) k) \<or>
    (\<exists>cclk keys kv_map. is_curr_t s t_rd \<and> cl_state (cls s (get_cl t_rd)) = RtxnInProg cclk keys kv_map \<and>
    t_wr = cts_order s k ! Max (view_of (cts_order s) (get_view s (get_cl t_rd)) k)))"

lemmas Rtxn_Once_in_rsI = Rtxn_Once_in_rs_def[THEN iffD2, rule_format]
lemmas Rtxn_Once_in_rsE[elim] = Rtxn_Once_in_rs_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_once_in_rs [simp]: "reach tps s \<Longrightarrow> Rtxn_Once_in_rs s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Rtxn_Once_in_rs_def tps_defs split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case using rtxn_get_view[of s e s']
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (auto simp add: Rtxn_Once_in_rs_def tps_trans_defs get_view_def)
      apply blast sorry
  next
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Rtxn_Once_in_rs_def tps_trans_defs) sorry
  next
    case (RDone x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: Rtxn_Once_in_rs_def tps_trans_defs get_view_def)
      using FTid_notin_rs_def sorry
  next
    case (WInvoke x1 x2 x3 x4)
    then show ?case apply (simp add: Rtxn_Once_in_rs_def tps_trans_defs get_view_def)
      (*by (smt (verit) txn_state.distinct(1))*) sorry
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case  sorry
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case using FTid_notin_rs_def
      apply (auto simp add: Rtxn_Once_in_rs_def tps_trans_defs get_view_def)
      apply (metis (no_types, lifting) less_Suc_eq)
      by (metis (no_types, lifting) txn_state.distinct(9))
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: Rtxn_Once_in_rs_def tps_trans_defs get_view_def)
      subgoal for keys kv_map cts' ts' lst' v' rs' t_rd t_wr cts v rs
        apply (cases "get_cl t_rd = get_cl x2"; cases "cl_state (cls s (get_cl t_rd))")
        apply auto
        using Fresh_wr_notin_rs_def[of s "get_cl x2"]
        add_to_readerset_commit_subset[of "svr_state (svrs s x1)" x2 "svr_clock (svrs s x1)" "svr_lst (svrs s x1)"
         "read_at (svr_state (svrs s x1)) (gst (cls s (get_cl x2))) (get_cl x2)" t_wr cts v rs] sorry sorry
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case sorry
  qed
qed


lemma update_kv_key_read_only:
  "update_kv_key t (case_op_type ro None) uk vl = 
   (case ro of None \<Rightarrow> vl
    | Some v \<Rightarrow> (let lv = last_version vl uk in
                  vl[Max uk := lv\<lparr>v_readerset := insert t (v_readerset lv)\<rparr>]))"
  by (auto simp add: update_kv_key_def split: option.split)

lemma update_kv_read_only:
  "update_kv t (read_only_fp kv_map) u K k = 
   (case kv_map k of
     None \<Rightarrow> K k |
     Some v \<Rightarrow> (let lv = last_version (K k) (u k) in
                (K k) [Max (u k) := lv\<lparr>v_readerset := insert t (v_readerset lv)\<rparr>]))"
  by (simp add: update_kv_def read_only_fp_def update_kv_key_read_only)

lemma read_done_txn_to_vers_update:
  assumes "reach tps_s s"
    "read_done_s cl kv_map sn u'' clk s s'"
  shows "txn_to_vers s' k =
    (case kv_map k of
      None \<Rightarrow> txn_to_vers s k |
      Some _ \<Rightarrow> (txn_to_vers s k)
          (cts_order s k ! Max (view_of (cts_order s) (get_view s cl) k) :=
            txn_to_vers s k (cts_order s k ! Max (view_of (cts_order s) (get_view s cl) k))
              \<lparr>v_readerset := insert (get_txn s cl)
                (v_readerset (last_version (map (txn_to_vers s k) (cts_order s k))
                  (view_of (cts_order s) (get_view s cl) k)))\<rparr>))"
proof (cases "kv_map k")
  case None
  then show ?thesis using assms
    apply (auto simp add: tps_trans_defs txn_to_vers_def; intro ext)
    apply (auto split: ver_state.split)
    using Rtxn_IdleK_notin_rs_def[of s]
    by (metis domIff less_SucE option.discI reach_rtxn_idle_k_notin_rs txid0.collapse)
next
  case (Some a)
  then have "{t. t \<in> get_view s cl k \<and> t \<in> set (cts_order s k)} \<noteq> {}"
    apply (simp add: get_view_def)
    by (metis T0_in_CO_def Wtxn_Cts_T0_def assms(1) domI le_0_eq linorder_le_cases option.sel
        reach_t0_in_co reach_tps reach_wtxn_cts_t0)
  then have max_in_range: "Max (view_of (cts_order s) (get_view s cl) k) < length (cts_order s k)"
    using assms(1) CO_Distinct_def[of s k] index_of_nth[of "cts_order s k"]
    by (auto simp add: view_of_def in_set_conv_nth)
  have "is_committed_in_kvs s k (cts_order s k ! Max (view_of (cts_order s) (get_view s cl) k))"
    using assms CO_is_Cmt_Abs_def[of s k]
      view_of_committed_in_kvs[of s cl _ _ _ "Max (view_of (cts_order s) (get_view s cl) k)" k]
    by (auto simp add: tps_trans_defs finite_view_of view_of_non_emp)
  then show ?thesis using assms Some max_in_range
    apply (auto simp add: tps_trans_defs txn_to_vers_def; intro ext)
    subgoal for _ t sorry
      (*apply (auto split: ver_state.split)
      apply (metis less_antisym txid0.collapse)
      subgoal sorry
      sorry.*)
    sorry
qed


lemma read_done_kvs_of_s:
  assumes "reach tps_s s"
    "read_done_s cl kv_map sn u'' clk s s'"
  shows "kvs_of_s s' = update_kv (Tn_cl sn cl)
                          (read_only_fp kv_map)
                          (view_of (cts_order s) (get_view s cl))
                          (kvs_of_s s)"
  using assms
  apply (auto simp add: update_kv_defs)
  apply (rule ext)
  subgoal for k
    apply (cases "kv_map k")
    subgoal apply (auto simp add: tps_trans_defs kvs_of_s_defs split: ver_state.split)
      by (smt Rtxn_IdleK_notin_rs_def reach_rtxn_idle_k_notin_rs domIff less_antisym
          txid0.collapse option.discI)
    subgoal for v
      apply (auto simp add: Let_def kvs_of_s_def)
      apply (subst map_list_update)
      subgoal by (metis Max_views_of_s_in_range views_of_s_def)
      subgoal using reach_co_distinct by auto
      subgoal apply (auto simp add: tps_trans_defs txn_to_vers_def)
          subgoal \<comment> \<open>t_wr' = cts_order ! Max (view_of ...)\<close>
            using Max_views_of_s_in_range[of s cl k]
              (*view_of_committed_in_kvs[of s cl cclk "dom kv_map" kv_map k 
            "Max (view_of (cts_order s) (get_view s cl) k)"]*)
            finite_view_of[of s "get_view s cl" k]
            view_of_non_emp[of s k cl]
          apply simp using CO_not_No_Ver_def[of s k]
           (* apply (auto simp add: read_done_def split: ver_state.split)
            apply (metis not_less_less_Suc_eq txid0.exhaust_sel)
          using Rtxn_RegK_Kvtm_Cmt_in_rs_def[of s cl]*) sorry
          subgoal for t_wr_old \<comment> \<open>t_wr' \<noteq> cts_order ! Max (view_of ...)\<close>
           apply (auto simp add: read_done_def read_done_U_def split: ver_state.split)
            subgoal for cts' sts' lst' v' rs' t_rd
             apply (cases "get_sn t_rd = cl_sn (cls s cl)", simp_all)
             apply (cases t_rd, auto)
             using Rtxn_Once_in_rs_def 
             by (smt reach_tps reach_rtxn_once_in_rs less_irrefl_nat txid0.sel(1) txid0.sel(2)).
         done.
       done.

(*
  using assms
  apply (intro ext)
  apply (simp add: kvs_of_s_def update_kv_read_only read_done_txn_to_vers_update)
  apply (auto simp add: tps_trans_defs Let_def split: option.split)
  apply (subst map_list_update)
  subgoal by (metis Max_views_of_s_in_range views_of_s_def)
  subgoal using reach_co_distinct by auto
  by metis*)

end