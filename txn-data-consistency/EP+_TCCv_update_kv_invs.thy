theory "EP+_TCCv_update_kv_invs"
  imports "EP+_TCCv_proof"
begin


lemma v_writer_kvs_of_s:
  assumes "\<forall>k. Commit_Order_Sound' s k"
  shows "v_writer ` (\<lambda>t. case svr_state (svrs s k) t of
      Prep ts v \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = {}\<rparr>
    | Commit cts v rs deps \<Rightarrow> \<lparr>v_value = v, v_writer = t,
        v_readerset = {t \<in> rs. get_sn t < cl_sn (cls s (get_cl t))}\<rparr>) ` set (commit_order s k) =
   {t \<in> set (commit_order s k). \<exists>ts v cts rs deps. svr_state (svrs s k) t \<in> {Prep ts v, Commit cts v rs deps}}"
  using assms
  by (auto simp add: image_iff Commit_Order_Sound'_def split: ver_state.split)

lemma v_readerset_kvs_of_s_k:
  assumes "\<forall>k. Commit_Order_Sound' s k"
    and "t_wr \<in> set (commit_order s k)"
  shows "v_readerset (case svr_state (svrs s k) t_wr of
      Prep ts v \<Rightarrow> \<lparr>v_value = v, v_writer = t_wr, v_readerset = {}\<rparr>
    | Commit cts v rs deps \<Rightarrow> \<lparr>v_value = v, v_writer = t_wr,
        v_readerset = {t \<in> rs. get_sn t < cl_sn (cls s (get_cl t))}\<rparr>) = 
   {t. \<exists>cts v rs deps. svr_state (svrs s k) t_wr = Commit cts v rs deps \<and>
      t \<in> rs \<and> get_sn t < cl_sn (cls s (get_cl t))}"
  using assms
  by (auto split: ver_state.split)

lemma v_readerset_kvs_of_s:
  assumes "\<forall>k. Commit_Order_Sound' s k"
  shows "(\<Union>k. \<Union>t_wr\<in>set (commit_order s k). v_readerset (case svr_state (svrs s k) t_wr of
      Prep ts v \<Rightarrow> \<lparr>v_value = v, v_writer = t_wr, v_readerset = {}\<rparr>
    | Commit cts v rs deps \<Rightarrow> \<lparr>v_value = v, v_writer = t_wr,
        v_readerset = {t \<in> rs. get_sn t < cl_sn (cls s (get_cl t))}\<rparr>)) = 
   {t. \<exists>k. \<exists>t_wr \<in> set (commit_order s k).
      \<exists>cts v rs deps. svr_state (svrs s k) t_wr = Commit cts v rs deps \<and>
      t \<in> rs \<and> get_sn t < cl_sn (cls s (get_cl t))}"
  using assms
  apply (auto simp add: v_readerset_kvs_of_s_k)
  by blast+

lemma read_done_same_writers:
  assumes "read_done cl kvt_map sn u'' s s'"
    and "\<forall>k. Commit_Order_Sound' s k"
    and "\<forall>k. Commit_Order_Sound' s' k"
  shows "kvs_writers (kvs_of_s s') = kvs_writers (kvs_of_s s)"
  using assms
  apply (simp add: kvs_writers_def vl_writers_def kvs_of_s_def v_writer_kvs_of_s Commit_Order_Sound'_def)
  by (simp add: read_done_def)

definition Rtxn_IdleK_notin_rs where
  "Rtxn_IdleK_notin_rs s cl \<longleftrightarrow> (\<forall>k keys kvt_map t cts v rs deps.
    cl_state (cls s cl) = RtxnInProg keys kvt_map \<and> k \<notin> keys \<and>
    svr_state (svrs s k) t = Commit cts v rs deps \<longrightarrow> get_txn s cl \<notin> rs)"

lemmas Rtxn_IdleK_notin_rsI = Rtxn_IdleK_notin_rs_def[THEN iffD2, rule_format]
lemmas Rtxn_IdleK_notin_rsE[elim] = Rtxn_IdleK_notin_rs_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_idle_k_notin_rs [simp]: "reach tps s \<Longrightarrow> Rtxn_IdleK_notin_rs s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rtxn_IdleK_notin_rs_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (auto simp add: Rtxn_IdleK_notin_rs_def tps_trans_defs)
      using Fresh_wr_notin_rs_def[of s]
      by (metis dual_order.eq_iff insertCI reach_fresh_wr_notin_rs txid0.sel(1) txid0.sel(2))
  next
    case (RegR x1 x2 x3 x4)
    then show ?case by (auto simp add: Rtxn_IdleK_notin_rs_def tps_trans_defs add_to_readerset_def
          split: ver_state.split, blast+)
  qed (auto simp add: Rtxn_IdleK_notin_rs_def tps_trans_defs, (blast+)?)
qed

definition Rtxn_RegK_in_rs where
  "Rtxn_RegK_in_rs s cl \<longleftrightarrow> (\<forall>k keys kvt_map t cts v rs deps.
    cl_state (cls s cl) = RtxnInProg keys kvt_map \<and> kvt_map k = Some (v, t) \<and>
    svr_state (svrs s k) t = Commit cts v rs deps \<longrightarrow> get_txn s cl \<in> rs)"

lemmas Rtxn_RegK_in_rsI = Rtxn_RegK_in_rs_def[THEN iffD2, rule_format]
lemmas Rtxn_RegK_in_rsE[elim] = Rtxn_RegK_in_rs_def[THEN iffD1, elim_format, rule_format]

lemma reach_rtxn_reg_k_in_rs [simp]: "reach tps s \<Longrightarrow> Rtxn_RegK_in_rs s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: Rtxn_RegK_in_rs_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (Read x1 x2 x3 x4)
    then show ?case apply (auto simp add: Rtxn_RegK_in_rs_def tps_trans_defs)
      by (metis old.prod.inject option.inject ver_state.inject(2))
  next
    case (RegR x1 x2 x3 x4)
    then show ?case by (auto simp add: Rtxn_RegK_in_rs_def tps_trans_defs add_to_readerset_def
          split: ver_state.split; blast)
  next
    case (PrepW x1 x2 x3)
    then show ?case by (simp add: Rtxn_RegK_in_rs_def tps_trans_defs, blast)
  next
    case (CommitW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Rtxn_RegK_in_rs_def tps_trans_defs)
      by (metis Kvt_map_t_Committed_def is_prepared.simps(3) reach_kvt_map_t_committed)
  qed (auto simp add: Rtxn_RegK_in_rs_def tps_trans_defs)
qed
lemma insert_Diff_if': "a \<notin> c \<Longrightarrow> insert a (b - c) = insert a b - c"
  by (simp add: insert_Diff_if)

lemma read_done_new_read:
  assumes "read_done cl kvt_map sn u'' s s'"
    and "\<forall>k. Commit_Order_Sound' s k"
    and "\<forall>k. Commit_Order_Sound' s' k"
    and "Finite_Dom_Kvt_map s cl"
    and "Rtxn_RegK_in_rs s cl"
    and "Tn (get_txn s cl) \<notin> kvs_writers (kvs_of_s s)"
  shows "read_only_Txs (kvs_of_s s') = insert (Tn (get_txn s cl)) (read_only_Txs (kvs_of_s s))"
  using assms
  apply (simp add: read_only_Txs_def read_done_same_writers insert_Diff_if')
  apply (rule arg_cong[where f="\<lambda>m. m - _"])
  apply (simp add: kvs_readers_def vl_readers_def kvs_of_s_def v_readerset_kvs_of_s)
  apply (auto simp add: read_done_def image_insert[symmetric] simp del: image_insert)
  using image_eqI apply blast
  apply (smt (z3) image_eqI insertCI less_SucE mem_Collect_eq txid0.collapse)
  using image_eqI apply blast
  subgoal apply (rule image_eqI, auto)
    apply (cases "dom kvt_map = {}", auto simp add: ex_in_conv[symmetric] simp del: dom_eq_empty_conv) (* rtxn_regk ?*) sorry
  by (smt (verit) image_eqI less_Suc_eq mem_Collect_eq)

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