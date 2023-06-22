theory "EP+_TCCv_update_kv_invs"
  imports "EP+_TCCv_proof"
begin

lemma map_list_update:
  "i < length (corder k) \<Longrightarrow> distinct (corder k) \<Longrightarrow>
   (map f (corder k)) [i := x] = map (f ((corder k) ! i := x)) (corder k)"
  by (smt (verit) fun_upd_apply length_list_update length_map nth_eq_iff_index_eq
      nth_equalityI nth_list_update nth_map)

lemma view_of_in_range:
  assumes "i \<in> view_of corder ctx k"
    and "ctx `` {k} \<subseteq> set (corder k)"
    and "distinct (corder k)"
  shows "i < length (corder k)"
  using assms
  apply (auto simp add: view_of_def Image_def)
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
  assumes "view_of corder ctx k \<noteq> {}"
    and "finite (view_of corder ctx k)"
    and "ctx `` {k} \<subseteq> set (corder k)"
    and "distinct (corder k)"
  shows "Max (view_of corder ctx k) < length (corder k)"
  using assms
  by (simp add: view_of_in_range)


lemma read_done_kvs_of_s:
  assumes "read_done cl kvt_map sn u'' s s'"
    and "\<forall>k. CO_Distinct s k"
    and "\<forall>k. Cl_Ctx_Sub_CO s k"
    and "\<forall>k. Get_Ctx_Sub_CO s k"
    and "\<forall>k. T0_in_CO s k"
    and "View_Init s cl"
    and "Rtxn_IdleK_notin_rs s cl"
    and "Rtxn_RegK_in_rs s cl"
  shows "kvs_of_s s' = update_kv (Tn_cl sn cl)
          (\<lambda>k. case_op_type (map_option fst (kvt_map k)) None)
          (view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s kvt_map))
          (kvs_of_s s)"
  using assms
  apply (auto simp add: update_kv_defs update_kv_writes_def update_kv_key_reads_def)
  apply (rule ext) apply (auto split: option.split)
  subgoal apply (auto simp add: read_done_def kvs_of_s_def split: ver_state.split)
    by (smt (verit, best) Rtxn_IdleK_notin_rs_def domIff less_antisym txid0.collapse)
  subgoal for k
    apply (auto simp add: Let_def last_version_def kvs_of_s_def)
    apply (subst map_list_update, auto)
    using Max_view_of_in_range[of "commit_order s" "cl_ctx (cls s cl) \<union> get_ctx s kvt_map" k]
      finite_view_of[of s] view_of_non_emp[of s] CO_Distinct_def Get_Ctx_Sub_CO_def Cl_Ctx_Sub_CO_def
     apply (simp_all add: read_done_def)
     apply blast
    apply (auto)
    subgoal sorry
    apply (auto split:ver_state.split)
    subgoal for t cts v rs deps t'
      using Rtxn_RegK_in_rs_def[of s "get_cl t'"] oops

end