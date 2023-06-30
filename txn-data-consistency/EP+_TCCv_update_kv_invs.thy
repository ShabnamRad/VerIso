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
    and "ctx `` {k} \<subseteq> set (commit_order s k)"
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
    and "ctx `` {k} \<subseteq> set (commit_order s k)"
    and "CO_Distinct s k"
  shows "Max (view_of (commit_order s) ctx k) < length (commit_order s k)"
  using assms
  by (simp add: view_of_in_range)

lemma theI_of_ctx_in_CO:
  assumes "i = (THE i. i < length (commit_order s k) \<and> commit_order s k ! i = t)"
    and "t \<in> set (commit_order s k)"
    and "CO_Distinct s k"
  shows "commit_order s k ! i = t"
  using assms
  by (smt (verit, del_insts) CO_Distinct_def distinct_Ex1 theI_unique)

lemma ctx_get_ctx_subset_co:
  assumes "cl_state (cls s cl) = RtxnInProg keys kvt_map"
    and "Cl_Ctx_Sub_CO s k"
    and "Get_Ctx_Sub_CO s k"
  shows "(cl_ctx (cls s cl) \<union> get_ctx s kvt_map) `` {k} \<subseteq> set (commit_order s k)"
  using assms Cl_Ctx_Sub_CO_def Get_Ctx_Sub_CO_def
  by blast

lemma view_of_committed:
  assumes "cl_state (cls s cl) = RtxnInProg keys kvt_map" 
    and "CO_Distinct s k"
    and "Ctx_Committed s"
    and "Deps_Committed s"
    and "i \<in> view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s kvt_map) k"
  shows "\<exists>cts v rs deps. svr_state (svrs s k) (commit_order s k ! i) = Commit cts v rs deps"
  using assms Ctx_Committed_def[of s] Deps_Committed_def[of s] theI_of_ctx_in_CO[of i s]
  apply (auto simp add: view_of_def Image_def get_ctx_def)
  apply (metis (mono_tags, opaque_lifting) is_committed.elims(2) txn_state.distinct(9))
  by (meson is_committed.elims(2))

lemma not_last_version_not_read:
  assumes "cl_state (cls s cl) = RtxnInProg (dom kvt_map) kvt_map"
    and "t_wr \<in> set (commit_order s k)"
    and "t_wr \<noteq> commit_order s k ! Max (view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s kvt_map) k)"
    and "svr_state (svrs s k) t_wr = Commit cts v rs deps"
  shows "get_txn s cl \<notin> rs"
  using assms
  apply (auto simp add: ) oops

definition Rtxn_Once_in_rs' where
  "Rtxn_Once_in_rs' s k \<longleftrightarrow> (\<forall>t.
    (\<forall>t' cts v rs deps. svr_state (svrs s k) t' = Commit cts v rs deps \<longrightarrow> t \<notin> rs) \<or> 
    (\<exists>!t'. \<exists>cts v rs deps. svr_state (svrs s k) t' = Commit cts v rs deps \<and> t \<in> rs))"

inductive ver_grows :: "'v ver_state \<Rightarrow> 'v ver_state \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>v" 60) where
  "ver_grows v v" |
  "ver_grows No_Ver (Prep pts v)" |
  "ver_grows No_Ver (Commit cts v rs deps)" |
  "ver_grows (Prep pts v) (Commit cts v rs deps)" |
  "rs \<subseteq> rs' \<Longrightarrow> ver_grows (Commit cts v rs deps) (Commit cts v rs' deps)"

lemma ver_grows_inv:
  assumes "state_trans s e s'"
  shows "\<forall>t. svr_state (svrs s k) t \<sqsubseteq>\<^sub>v svr_state (svrs s' k) t"
  using assms
proof (induction e)
  case (RegR x1 x2 x3 x4)
  then show ?case by (auto simp add: tps_trans_defs add_to_readerset_def
   intro: ver_grows.intros split: ver_state.split)
next
  case (CommitW x1 x2 x3 x4 x5)
  then show ?case apply (auto simp add: tps_trans_defs intro: ver_grows.intros)
    by (metis is_prepared.elims(2) ver_grows.intros(4) ver_state.sel(3))
qed (auto simp add: tps_trans_defs intro: ver_grows.intros)

inductive committed_ver_grows :: "'v ver_state \<Rightarrow> 'v ver_state \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>c\<^sub>v" 60) where
  "committed_ver_grows v v" |
  "rs \<subseteq> rs' \<Longrightarrow> committed_ver_grows (Commit cts v rs deps) (Commit cts v rs' deps)"

lemma rtxn_committed_ver_grows:
  assumes "state_trans s e s'"
    and "\<forall>k t v. e \<noteq> PrepW k t v"
    and "\<forall>k t v cts deps. e \<noteq> CommitW k t v cts deps"
  shows "committed_ver_grows (svr_state (svrs s k) t) (svr_state (svrs s' k) t)"
  using assms
proof (induction e)
  case (RegR x1 x2 x3 x4)
  then show ?case by (auto simp add: tps_trans_defs add_to_readerset_def
   intro: committed_ver_grows.intros split: ver_state.split)
qed (auto simp add: tps_trans_defs intro: committed_ver_grows.intros)

lemma rtxn_get_ctx:
  assumes "state_trans s e s'"
    and "\<forall>k t v. e \<noteq> PrepW k t v"
    and "\<forall>k t v cts deps. e \<noteq> CommitW k t v cts deps"
  shows "get_ctx s' kvt_map = get_ctx s kvt_map"
  using assms
  apply (auto simp add: get_ctx_def)
  apply (smt (verit) committed_ver_grows.cases insertCI rtxn_committed_ver_grows ver_state.inject(2))
  apply (smt (verit) committed_ver_grows.simps insert_iff rtxn_committed_ver_grows ver_state.inject(2))
  apply (smt (verit) committed_ver_grows.simps insertCI rtxn_committed_ver_grows ver_state.inject(2))
  by (smt (verit) committed_ver_grows.simps insert_iff rtxn_committed_ver_grows ver_state.inject(2))

lemma rtxn_get_ctx_pres:
  assumes "\<And>k t. ver_grows (svr_state (svrs s k) t) (svr_state (svrs s' k) t)"
  shows "get_ctx s' kvt_map = get_ctx s kvt_map"
  using assms
  oops
  

definition Rtxn_Once_in_rs where
  "Rtxn_Once_in_rs s cl \<longleftrightarrow> (\<forall>k t_wr cts v rs deps. 
    svr_state (svrs s k) t_wr = Commit cts v rs deps \<and> get_txn s cl \<in> rs \<longrightarrow>
    (\<exists>keys kvt_map. cl_state (cls s cl) = RtxnInProg keys kvt_map \<and>
    t_wr = commit_order s k ! Max (view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s kvt_map) k)))"

lemmas Rtxn_Once_in_rsI = Rtxn_Once_in_rs_def[THEN iffD2, rule_format]
lemmas Rtxn_Once_in_rsE[elim] = Rtxn_Once_in_rs_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_once_in_rs [simp]: "reach tps s \<Longrightarrow> Rtxn_Once_in_rs s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Rtxn_Once_in_rs_def tps_defs split: if_split_asm)
next
  case (reach_trans s e s')
  then show ?case using rtxn_get_ctx[of s e s']
  proof (induction)
    case (RInvoke x1 x2)
    then show ?case apply (auto simp add: Rtxn_Once_in_rs_def tps_trans_defs)
      by blast
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (auto simp add: Rtxn_Once_in_rs_def tps_trans_defs) sorry
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: Rtxn_Once_in_rs_def tps_trans_defs)
      using FTid_notin_rs_def by blast
  next
    case (WInvoke x1 x2)
    then show ?case apply (simp add: Rtxn_Once_in_rs_def tps_trans_defs)
      by (metis txn_state.distinct(1))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Rtxn_Once_in_rs_def tps_trans_defs) sorry
  next
    case (WDone x1 x2)
    then show ?case apply (auto simp add: Rtxn_Once_in_rs_def tps_trans_defs)
      using FTid_notin_rs_def by blast
  next
    case (RegR x1 x2 x3 x4)
    then show ?case apply (auto simp add: Rtxn_Once_in_rs_def tps_trans_defs)
      subgoal for t_wr keys kvt_map cts v rs deps
        apply (cases "cl = get_cl x2", simp_all)
        apply (cases "cl_state (cls s cl)", simp_all)
      subgoal for keys'
        using Fresh_wr_notin_rs_def[of s "get_cl x2"]
        add_to_readerset_commit_subset[of "svr_state (svrs s x1)" x2
         "read_at (svr_state (svrs s x1)) (gst (cls s (get_cl x2))) (get_cl x2)" t_wr cts v rs deps]
        apply auto sorry sorry sorry
  next
    case (PrepW x1 x2 x3)
    then show ?case apply (simp add: Rtxn_Once_in_rs_def tps_trans_defs) sorry
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Rtxn_Once_in_rs_def tps_trans_defs) sorry
  qed simp
qed

lemma read_done_kvs_of_s:
  assumes "read_done cl kvt_map sn u'' s s'"
    and "cl_state (cls s cl) = RtxnInProg (dom kvt_map) kvt_map"
    and "\<forall>k. commit_order s' k = commit_order s k"
    and "\<forall>k. CO_Distinct s k"
    and "\<forall>k. Cl_Ctx_Sub_CO s k"
    and "\<forall>k. Get_Ctx_Sub_CO s k"
    and "\<forall>k. T0_in_CO s k"
    and "View_Init s cl"
    and "Rtxn_IdleK_notin_rs s cl"
    and "\<And>k. Rtxn_Once_in_rs s k"
    and "Ctx_Committed s"
    and "Deps_Committed s"
  shows "kvs_of_s s' = update_kv (Tn_cl sn cl)
          (\<lambda>k. case_op_type (map_option fst (kvt_map k)) None)
          (view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s kvt_map))
          (kvs_of_s s)"
  using assms
  apply (auto simp add: update_kv_defs)
  apply (rule ext) subgoal for k apply (cases "map_option fst (kvt_map k)")
  subgoal apply (auto simp add: read_done_def kvs_of_s_defs split: ver_state.split)
    by (smt (verit, best) Rtxn_IdleK_notin_rs_def domIff less_antisym txid0.collapse)
  subgoal for v
    apply (auto simp add: Let_def kvs_of_s_def)
    apply (subst map_list_update)
    subgoal by (meson Max_in ctx_get_ctx_subset_co finite_view_of view_of_in_range view_of_non_emp)
    subgoal by blast
    subgoal for t_wr apply (auto simp add: txn_to_vers_def)
        subgoal \<comment> \<open>t_wr' = commit_order ! Max (view_of ...)\<close>
          using Max_view_of_in_range[of s "cl_ctx (cls s cl) \<union> get_ctx s kvt_map" k]
            view_of_committed[of s cl "dom kvt_map" kvt_map k 
          "Max (view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s kvt_map) k)"]
          ctx_get_ctx_subset_co[of s cl "dom kvt_map" kvt_map k]
          finite_view_of[of s "cl_ctx (cls s cl) \<union> get_ctx s kvt_map" k]
          view_of_non_emp[of s k cl "get_ctx s kvt_map"]
        apply simp
         (*apply (auto simp add: read_done_def split: ver_state.split)
         apply (metis not_less_less_Suc_eq txid0.exhaust_sel)
        using Rtxn_RegK_in_rs_def[of s] Kvt_map_t_Committed_def[of s]*) sorry
        subgoal for t_wr' \<comment> \<open>t_wr' \<noteq> commit_order ! Max (view_of ...)\<close>
         apply (auto simp add: read_done_def split: ver_state.split)
          subgoal for cts' v' rs' deps' t_rd
           apply (cases "get_sn t_rd = cl_sn (cls s cl)", simp_all)
           apply (cases t_rd, auto)
           using Rtxn_Once_in_rs_def by (smt (z3) txn_state.inject(1)).
       done.
     done.

end