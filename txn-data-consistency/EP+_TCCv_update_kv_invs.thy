theory "EP+_TCCv_update_kv_invs"
  imports "EP+_TCCv_proof"
begin

lemma read_done_kvs_of_s:
  assumes "read_done cl kvt_map sn u'' s s'"
    and "\<forall>k. Commit_Order_Sound' s k"
    and "\<forall>k. Commit_Order_Sound' s' k"
    and "Rtxn_IdleK_notin_rs s cl"
    and "Rtxn_RegK_in_rs s cl"
  shows "kvs_of_s s' = update_kv (get_txn s cl)
    (\<lambda>k. case_op_type (map_option fst (kvt_map k)) None)
    (view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s kvt_map))
    (kvs_of_s s)"
  using assms
  apply (auto simp add: update_kv_defs update_kv_writes_def update_kv_reads_def)
  apply (rule ext) apply (auto split: option.split ver_state.split)
  subgoal apply (auto simp add: Commit_Order_Sound'_def read_done_def kvs_of_s_def
        split: ver_state.split)
    by (smt (verit, best) Rtxn_IdleK_notin_rs_def domIff less_antisym txid0.collapse)
  subgoal apply (auto simp add: Commit_Order_Sound'_def read_done_def Let_def kvs_of_s_def) oops

end