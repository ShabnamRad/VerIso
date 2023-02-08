section \<open>Eiger Port+ Refinement Proof Invariants (and important lemmas)\<close>

theory CCv_Eiger_Port_modified_Invariants
  imports CCv_Eiger_Port_modified
begin

\<comment> \<open>Lemmas about simulation functions\<close>

lemma pending_rtxn_inv:
  assumes "\<forall>keys kv_map. txn_state (cls s cl) \<noteq> RtxnInProg keys kv_map"
    and "\<forall>keys kv_map. txn_state (cls s' cl) \<noteq> RtxnInProg keys kv_map"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "pending_rtxn s' t = pending_rtxn s t"
  oops

lemma pending_rtxn_added:
  assumes "txn_state (cls s cl) = Idle"
    and "txn_state (cls s' cl) = RtxnInProg keys kv_map"
    and "txn_sn (cls s' cl) = txn_sn (cls s cl)"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "Collect (pending_rtxn s') = insert (get_txn_cl s cl) (Collect (pending_rtxn s))"
  oops

lemma pending_rtxn_removed:
  assumes "txn_state (cls s cl) = RtxnInProg keys kv_map"
    and "txn_state (cls s' cl) = Idle"
    and "txn_sn (cls s' cl) = txn_sn (cls s cl)"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "Collect (pending_rtxn s') = Set.remove (get_txn_cl s cl) (Collect (pending_rtxn s))"
  oops

lemma pending_wtxn_cl_ev_inv:
  assumes "\<forall>kv_map. txn_state (cls s cl) \<noteq> WtxnPrep kv_map"
    and "\<forall>kv_map. txn_state (cls s' cl) \<noteq> WtxnPrep kv_map"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "pending_wtxn s' t = pending_wtxn s t"
  oops

lemma pending_wtxn_svr_ev_inv:
  assumes "cls s' = cls s"
  shows "pending_wtxn s' t = pending_wtxn s t"
  oops

lemma pending_wtxn_added:
  assumes "txn_state (cls s cl) = Idle"
    and "txn_state (cls s' cl) = WtxnPrep kv_map"
    and "txn_sn (cls s' cl) = txn_sn (cls s cl)"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "Collect (pending_wtxn s') = insert (Tn (get_txn_cl s cl)) (Collect (pending_wtxn s))"
  oops

lemma pending_wtxn_removed:
  assumes "txn_state (cls s cl) = WtxnPrep kv_map"
    and "txn_state (cls s' cl) = WtxnCommit gts cts kv_map"
    and "txn_sn (cls s' cl) = txn_sn (cls s cl)"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "Collect (pending_wtxn s') = Set.remove (Tn (get_txn_cl s cl)) (Collect (pending_wtxn s))"
  oops

lemma indices_map_get_ver_committed_rd [simp]:
  "indices_map (map (get_ver_committed_rd s) vl) i = indices_map vl i"
  oops

lemma dom_indices_map:
  "dom (indices_map vl i) = v_writer ` set (vl)"
  oops

lemma insert_in_vl_ver_features:
  "f ` set (insert_in_vl vl (Some ver)) = insert (f ver) (f ` set vl)"
  oops

lemma commit_all_in_vl_length:
  "length (commit_all_in_vl s vl1 vl2) = length vl1 + length vl2"
  oops

lemma commit_all_in_vl_writers:
  "v_writer ` set (commit_all_in_vl s vl1 vl2) = v_writer ` set vl1 \<union> v_writer ` set vl2"
  oops

lemma commit_all_in_vl_readersets:
  "v_readerset ` (set (commit_all_in_vl s vl1 vl2)) = v_readerset ` set vl1 \<union> v_readerset ` set vl2"
  oops

lemma commit_all_in_vl_append:
  "commit_all_in_vl s vl_c (vl @ [ver]) =
  insert_in_vl (commit_all_in_vl s vl_c vl) (Some (committed_ver ver (get_glts s ver) 0))"
  oops

lemma get_vl_pre_committed_writers:
  "v_writer ` set (get_vl_pre_committed s vl) = v_writer ` {x \<in> set vl. \<not>v_is_pending x \<or> \<not> pending_wtxn s (v_writer x)}"
  oops

lemma get_vl_pre_committed_readersets:
  "v_readerset ` (set (get_vl_pre_committed s vl)) \<subseteq> v_readerset ` (set vl)"
  oops

lemma pending_wtxns_empty:
  "pending_wtxns s k = {} \<longleftrightarrow> (\<forall>t. wtxn_state (svrs s k) t \<in> {Ready, Commit})"
  oops

lemma pending_wtxns_non_empty:
  assumes "wtxn_state (svrs s k) t \<noteq> Ready"
    and "wtxn_state (svrs s k) t \<noteq> Commit"
  shows "pending_wtxns s k \<noteq> {}"
  oops

\<comment> \<open>Lemmas for unchanged elements in svrs\<close>

lemma DS_eq_all_k:
  assumes "DS (svrs s' k) = DS (svrs s k)"
    and "other_insts_unchanged k (svrs s) (svrs s')"
  shows "\<forall>k. DS (svrs s' k) = DS (svrs s k)"
  oops

lemma eq_for_all_k: 
  assumes "f (svrs s' k) = f (svrs s k)"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> svrs s' k' = svrs s k'"
  shows "\<forall>k. f (svrs s' k) = f (svrs s k)"
  oops

lemma eq_for_all_k_t: 
  assumes "f (svrs s' k) t = f (svrs s k) t"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> svrs s' k' = svrs s k'"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> f (svrs s' k) t' = f (svrs s k) t'"
  shows "\<forall>k. f (svrs s' k) = f (svrs s k)"
  oops

lemma eq_for_all_cl:
  assumes "f (cls s' cl) = f (cls s cl)"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "\<forall>cl. f (cls s' cl) = f (cls s cl)"
  oops

subsection \<open>Monotonic lemmas and inequality of timestamps invariants\<close>

lemma glts_monotonic:
  assumes "state_trans s e s'"
  shows "global_time s' \<ge> global_time s"
  oops

lemma clock_monotonic:
  assumes "state_trans s e s'"
  shows "clock (svrs s' svr) \<ge> clock (svrs s svr)"
  oops

lemma cl_clock_monotonic:
  assumes "state_trans s e s'"
  shows "cl_clock (cls s' cl) \<ge> cl_clock (cls s cl)"
  oops

definition PendingWtxnsUB where
  "PendingWtxnsUB s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns s svr. ts \<le> clock (svrs s svr))"

definition FinitePendingInv where
  "FinitePendingInv s svr \<longleftrightarrow> finite (pending_wtxns s svr)"

definition ClockLstInv where
  "ClockLstInv s \<longleftrightarrow> (\<forall>svr. lst (svrs s svr) \<le> clock (svrs s svr))"

definition PendingWtxnsLB where
  "PendingWtxnsLB s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns s svr. lst (svrs s svr) \<le> ts)"

lemma min_pending_wtxns_monotonic:
  assumes "state_trans s e s'"
    and "pending_wtxns s k \<noteq> {}"
    and "pending_wtxns s' k \<noteq> {}"
    and "PendingWtxnsUB s k" and "FinitePendingInv s k"
  shows "Min (pending_wtxns s k) \<le> Min (pending_wtxns s' k)"
  oops

lemma lst_monotonic:
  assumes "state_trans s e s'"
    and "ClockLstInv s" and "FinitePendingInv s svr"
    and "PendingWtxnsLB s svr" and "PendingWtxnsUB s svr"
  shows "lst (svrs s' svr) \<ge> lst (svrs s svr)"
  oops

lemma gst_monotonic:
  assumes "state_trans s e s'"
  shows "gst (cls s' cl) \<ge> gst (cls s cl)"
  oops

\<comment> \<open>Invariants about kvs, global ts and init version v0\<close>

definition KVSNonEmp where
  "KVSNonEmp s \<longleftrightarrow> (\<forall>k. DS (svrs s k) \<noteq> [])"

definition GltsNotZero where
  "GltsNotZero s \<longleftrightarrow> global_time s > 0"

definition CommitGltsNotZero where
  "CommitGltsNotZero s cl \<longleftrightarrow> (\<forall>gts cts kv_map. txn_state (cls s cl) = WtxnCommit gts cts kv_map \<longrightarrow> gts > 0)"

definition InitVerInv where
  "InitVerInv s k \<longleftrightarrow> v_writer (DS (svrs s k) ! 0) = T0 \<and> v_glts (DS (svrs s k) ! 0) = 0 \<and>
    \<not>v_is_pending (DS (svrs s k) ! 0)"

definition KVSNotAllPending where
  "KVSNotAllPending s k \<longleftrightarrow>  \<not>v_is_pending (DS (svrs s k) ! 0)"

lemma get_vl_committed_length_inv:
  assumes "KVSNonEmp s"
    and "KVSNotAllPending s k"
  shows "length (get_vl_committed_wr (DS (svrs s k))) > 0"
  oops

definition KVSSNonEmp where
  "KVSSNonEmp s \<longleftrightarrow> (\<forall>k. kvs_of_s s k \<noteq> [])"

\<comment> \<open>To make sure get_glts works\<close>
definition ReadyToCommitVer where (*Not yet proven*)
  "ReadyToCommitVer s k \<longleftrightarrow>
    (\<forall>cl v n. v \<in> set (get_vl_ready_to_commit_wr s (DS (svrs s k)))\<and> v_writer v = Tn (Tn_cl n cl) \<longrightarrow>
    (\<exists>glts cts kv_map. txn_state (cls s cl) =  WtxnCommit glts cts kv_map))"


\<comment> \<open>Invariant about future and past transactions svrs\<close>

definition FutureTIDInv where
  "FutureTIDInv s cl \<longleftrightarrow> (\<forall>n k. n > txn_sn (cls s cl) \<longrightarrow> wtxn_state (svrs s k) (Tn_cl n cl) = Ready)"

definition ReadOnlyTxn where
  "ReadOnlyTxn s \<longleftrightarrow> (\<forall>cl svr ks vs. txn_state (cls s cl) \<in> {Idle, RtxnInProg ks vs}
    \<longrightarrow> wtxn_state (svrs s svr) (get_txn_cl s cl) = Ready)"

definition WriteTxnIdleSvr where
  "WriteTxnIdleSvr s \<longleftrightarrow>
    (\<forall>cl k gts cts kv_map. txn_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit gts cts kv_map}
        \<and> kv_map k = None \<longrightarrow> wtxn_state (svrs s k) (get_txn_cl s cl) = Ready)"

definition PastTIDInv where
  "PastTIDInv s cl \<longleftrightarrow> (\<forall>n k. n < txn_sn (cls s cl) \<longrightarrow> wtxn_state (svrs s k) (Tn_cl n cl) \<in> {Ready, Commit})"

lemma other_sn_idle:  
  assumes "FutureTIDInv s cl" and "PastTIDInv s cl"
    and "get_cl_txn t = cl" and "get_sn_txn t \<noteq> txn_sn (cls s cl)"
  shows "\<And>k. wtxn_state (svrs s k) t \<in> {Ready, Commit}"
  oops

definition FutureTidRdDS where (* Not yet proven *)
  "FutureTidRdDS s cl \<longleftrightarrow> (\<forall>n k. \<forall>ver \<in> set (DS (svrs s k)). n > txn_sn (cls s cl) \<longrightarrow> Tn_cl n cl \<notin> v_readerset ver)"

definition FutureTidWrDS where
  "FutureTidWrDS s cl \<longleftrightarrow> (\<forall>n k. n > txn_sn (cls s cl) \<longrightarrow> Tn (Tn_cl n cl) \<notin> v_writer ` set (DS (svrs s k)))"

\<comment> \<open>t is not in the v_readerset in the beginning of the transaction\<close>
definition FreshReadTxnInv where (* Not yet proven *)
  "FreshReadTxnInv s cl \<longleftrightarrow> (txn_state (cls s cl) = Idle
    \<longrightarrow> (\<forall>k. get_txn_cl s cl \<notin> \<Union> (v_readerset ` set (DS (svrs s k)))))"

definition FreshWriteTxnInv where
  "FreshWriteTxnInv s cl \<longleftrightarrow>
    (\<forall>keys kv_map k. txn_state (cls s cl) \<in> {Idle, RtxnInProg keys kv_map} \<longrightarrow>
      Tn (get_txn_cl s cl) \<notin> v_writer ` set (DS (svrs s k)))"

abbreviation invariant_list_kvs where
  "invariant_list_kvs s \<equiv> \<forall>cl k. FutureTIDInv s cl \<and> PastTIDInv s cl \<and> KVSNonEmp s \<and>
    KVSNotAllPending s k \<and> FreshReadTxnInv s cl"

lemma kvs_of_s_inv: (* Not yet proven *)
  assumes "state_trans s e s'"
    and "invariant_list_kvs s"
    and "not_committing_ev e"
  shows "kvs_of_s s' = kvs_of_s s"
  oops

lemma writers_inv_not_commit_write:
  assumes "state_trans s e s'"
    and "\<And>cl kv_map cts sn u. \<not>write_commit cl kv_map cts sn u s s'"
  shows "v_writer ` set (get_vl_pre_committed s' (DS (svrs s' svr))) =
  v_writer ` set (get_vl_pre_committed s (DS (svrs s svr)))"
  oops


definition NoPendingInView where (* Not yet proven *)
  "NoPendingInView s \<longleftrightarrow> (\<forall>cl k. cl_view (cls s cl) k \<subseteq> v_writer ` set (get_vl_pre_committed s (DS (svrs s k))))"

lemma in_view_index_not_none:
  assumes "x \<in> cl_view (cls s cl) k"
    and "NoPendingInView s"
  shows "x \<in> dom (get_indices_map (kvs_of_s s k))"
  oops

lemma map_extend_subset:
  assumes "k \<notin> dom m1"
    and "m2 = [k \<mapsto> v] ++ m1"
  shows "m1 \<subseteq>\<^sub>m m2"
  oops

lemma prefix_update_get_indices_map:
  shows "indices_map (vl1 @ [ver]) i = [v_writer ver \<mapsto> (i + length vl1)] ++ indices_map vl1 i"
  oops

lemma prefix_subset_indices_map:
  assumes "v_writer ver \<notin> v_writer ` set vl1"
  shows "indices_map vl1 i \<subseteq>\<^sub>m indices_map (vl1 @ [ver]) i"
  oops

lemma read_commit_indices_map_grows: (* Not yet proven *)
  assumes "read_done cl kv_map sn u s s'"
  shows "get_indices_map (kvs_of_s s k) \<subseteq>\<^sub>m get_indices_map (kvs_of_s s' k)"
  oops

definition OnlyPendingVer where (* Not yet proven *)
  "OnlyPendingVer s cl k \<longleftrightarrow>
  (\<forall>t. \<forall>ver \<in> set (DS (svrs s k)). v_is_pending ver \<and> is_txn_writer t ver \<longrightarrow> t = Tn (get_txn_cl s cl))"

definition CurrentVerPending where (* Not yet proven *)
  "CurrentVerPending s cl k \<longleftrightarrow>
    (\<forall>kvm keys ver. txn_state (cls s cl) \<in> {Idle, WtxnPrep kvm, RtxnInProg keys kvm} \<and> 
    find (is_txn_writer (Tn (get_txn_cl s cl))) (DS (svrs s k)) = Some ver \<longrightarrow> v_is_pending ver)"

lemma write_commit_not_add_to_ready:
  assumes "find (is_txn_writer (Tn (get_txn_cl s cl))) (DS (svrs s k)) = None"
    and "txn_sn (cls s' cl) = txn_sn (cls s cl)"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "get_vl_ready_to_commit_wr s' (DS (svrs s' k)) = get_vl_ready_to_commit_wr s (DS (svrs s k))"
  oops

lemma write_commit_adds_one_to_ready:
  assumes "find (is_txn_writer (Tn (get_txn_cl s cl))) (DS (svrs s k)) = Some ver"
    and "txn_state (cls s cl) = WtxnPrep kv_map"
    and "txn_state (cls s' cl) = WtxnCommit (global_time s) cts kv_map"
    and "txn_sn (cls s' cl) = txn_sn (cls s cl)"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "\<exists>ver \<in> set (DS (svrs s' k)). get_vl_ready_to_commit_wr s' (DS (svrs s' k)) =
                                      get_vl_ready_to_commit_wr s (DS (svrs s k)) @ [ver]"
  oops

lemma assumes "ver \<in> set (get_vl_ready_to_commit_wr s (DS (svrs s k)))"
    and "find (is_txn_writer (Tn (get_txn_cl s cl))) (DS (svrs s k)) = None"
    and "txn_state (cls s cl) = WtxnPrep kv_map"
    and "txn_state (cls s' cl) = WtxnCommit (global_time s) cts kv_map"
    and "txn_sn (cls s' cl) = txn_sn (cls s cl)"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "get_glts s' ver = get_glts s ver"
  oops

lemma write_commit_indices_map_grows:
  assumes "write_commit cl kv_map cts sn u s s'"
  shows "get_indices_map (kvs_of_s s k) \<subseteq>\<^sub>m get_indices_map (kvs_of_s s' k)"
  oops

subsection\<open>View invariants\<close>

lemma cl_view_inv:
  assumes "state_trans s e s'"
    and "not_committing_ev e"
  shows "cl_view (cls s' cl) = cl_view (cls s cl)"
  oops

lemma views_of_s_inv:
  assumes "state_trans s e s'"
    and "invariant_list_kvs s"
    and "not_committing_ev e"
  shows "views_of_s s' cl = views_of_s s cl"
  oops

lemma read_commit_views_of_s_other_cl_inv:
  assumes "read_done cl kv_map sn u s s'"
    and "NoPendingInView s"
    and "cl' \<noteq> cl"
  shows "views_of_s s' cl' = views_of_s s cl'"
  oops

lemma write_commit_views_of_s_other_cl_inv:
  assumes "write_commit cl kv_map cts sn u s s'"
    and "NoPendingInView s"
    and "cl' \<noteq> cl"
  shows "views_of_s s' cl' = views_of_s s cl'"
  oops

end
