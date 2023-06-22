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

lemma read_done_kvs_of_s:
  assumes "read_done cl kvt_map sn u'' s s'"
    and "cl_state (cls s cl) = RtxnInProg (dom kvt_map) kvt_map"
    and "\<forall>k. commit_order s' k = commit_order s k"
    and "\<forall>k. CO_Distinct s k"
    and "\<forall>k. CO_not_No_Ver s k"
    and "\<forall>k. Cl_Ctx_Sub_CO s k"
    and "\<forall>k. Get_Ctx_Sub_CO s k"
    and "\<forall>k. T0_in_CO s k"
    and "View_Init s cl"
    and "Rtxn_IdleK_notin_rs s cl"
    and "Rtxn_RegK_in_rs s cl"
    and "Kvt_map_t_Committed s cl"
    and "Ctx_Committed s"
    and "Deps_Committed s"
  shows "kvs_of_s s' = update_kv (Tn_cl sn cl)
          (\<lambda>k. case_op_type (map_option fst (kvt_map k)) None)
          (view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s kvt_map))
          (kvs_of_s s)"
  using assms
  apply (auto simp add: update_kv_defs update_kv_writes_def update_kv_key_reads_def)
  apply (rule ext) apply (auto split: option.split)
  subgoal apply (auto simp add: read_done_def kvs_of_s_defs split: ver_state.split)
    by (smt (verit, best) Rtxn_IdleK_notin_rs_def domIff less_antisym txid0.collapse)
  subgoal for k v t_wr
    apply (auto simp add: Let_def last_version_def kvs_of_s_def)
    apply (subst map_list_update)
    subgoal by (meson Max_in ctx_get_ctx_subset_co finite_view_of view_of_in_range view_of_non_emp)
    subgoal by blast
    subgoal apply (auto simp add: txn_to_vers_def)
      subgoal using Max_view_of_in_range[of s "cl_ctx (cls s cl) \<union> get_ctx s kvt_map" k]
            view_of_committed[of s cl "dom kvt_map" kvt_map k 
          "Max (view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s kvt_map) k)"]
          ctx_get_ctx_subset_co[of s cl "dom kvt_map" kvt_map k]
          finite_view_of[of s "cl_ctx (cls s cl) \<union> get_ctx s kvt_map" k]
          view_of_non_emp[of s k cl "get_ctx s kvt_map"]
        apply simp
         (*apply (auto simp add: read_done_def split: ver_state.split)
         apply (metis not_less_less_Suc_eq txid0.exhaust_sel)
        using Rtxn_RegK_in_rs_def[of s] Kvt_map_t_Committed_def[of s]*) sorry
       subgoal for t_wr' using CO_not_No_Ver_def [of s k]
         apply (auto simp add: read_done_def split: ver_state.split)
         subgoal for cts' v' rs' deps' t_rd
           apply (cases "get_sn t_rd = cl_sn (cls s (get_cl t_rd))", simp_all)
           apply (cases t_rd, auto) sorry
         . . . .

end