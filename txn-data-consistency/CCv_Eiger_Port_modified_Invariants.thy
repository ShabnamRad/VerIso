section \<open>Eiger Port+ Refinement Proof Invariants (and important lemmas)\<close>

theory CCv_Eiger_Port_modified_Invariants
  imports CCv_Eiger_Port_modified
begin

\<comment> \<open>Invariants about kv store\<close>
definition KVSNonEmp where
  "KVSNonEmp s \<longleftrightarrow> (\<forall>k. DS (svrs s k) \<noteq> [])"

definition KVSNotAllPending where
  "KVSNotAllPending s k \<longleftrightarrow> (\<exists>i. i < length (DS (svrs s k)) \<and> \<not>v_is_pending (DS (svrs s k) ! i))"

definition KVSSNonEmp where
  "KVSSNonEmp s \<longleftrightarrow> (\<forall>k. kvs_of_s s k \<noteq> [])"

\<comment> \<open>Invariant about future and past transactions svrs\<close>

definition FutureTIDInv where
  "FutureTIDInv s cl \<longleftrightarrow> (\<forall>n k. n > txn_sn (cls s cl) \<longrightarrow> wtxn_state (svrs s k) (Tn_cl n cl) = Ready)"

definition PastTIDInv where
  "PastTIDInv s cl \<longleftrightarrow> (\<forall>n k. n < txn_sn (cls s cl) \<longrightarrow> wtxn_state (svrs s k) (Tn_cl n cl) \<in> {Ready, Commit})"

lemma other_sn_idle:  
  assumes "FutureTIDInv s cl" and "PastTIDInv s cl"
    and "get_cl_txn t = cl" and "get_sn_txn t \<noteq> txn_sn (cls s cl)"
  shows "\<And>k. wtxn_state (svrs s k) t \<in> {Ready, Commit}"
  oops

abbreviation not_committing_ev where
  "not_committing_ev e \<equiv> \<forall>cl kv_map cts sn u. e \<noteq> RDone cl kv_map sn u \<and> e \<noteq> WCommit cl kv_map cts sn u"

abbreviation invariant_list_kvs where
  "invariant_list_kvs s \<equiv> \<forall>cl k. FutureTIDInv s cl \<and> PastTIDInv s cl \<and> KVSNonEmp s \<and> KVSNotAllPending s k"
                                                               
subsection \<open>Refinement Proof\<close>

lemma pending_rtxn_inv:
  assumes "\<forall>keys kv_map. txn_state (cls s cl) \<noteq> RtxnInProg keys kv_map"
    and "\<forall>keys kv_map. txn_state (cls s' cl) \<noteq> RtxnInProg keys kv_map"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "pending_rtxn s' t = pending_rtxn s t"
  oops

lemma pending_wtxn_inv:
  assumes "\<forall>kv_map. txn_state (cls s cl) \<noteq> WtxnPrep kv_map"
    and "\<forall>kv_map. txn_state (cls s' cl) \<noteq> WtxnPrep kv_map"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "pending_wtxn s' t = pending_wtxn s t"
  oops

lemma kvs_of_s_inv:
  assumes "state_trans s e s'"
    and "invariant_list_kvs s"
    and "not_committing_ev e"
  shows "kvs_of_s s' = kvs_of_s s"
  oops

lemma finite_pending_wtxns: 
  assumes "pending_wtxns (svrs s' k) t = Some x"
    and "\<forall>k'. finite (ran (pending_wtxns (svrs s k')))"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> pending_wtxns (svrs s' k') = pending_wtxns (svrs s k')"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> pending_wtxns (svrs s' k) t' = pending_wtxns (svrs s k) t'"
  shows "\<forall>k. finite (ran (pending_wtxns (svrs s' k)))"
  oops

definition FinitePendingInv where
  "FinitePendingInv s svr \<longleftrightarrow> finite (ran (pending_wtxns (svrs s svr)))"

lemma clock_monotonic:
  assumes "state_trans s e s'"
  shows "clock (svrs s' svr) \<ge> clock (svrs s svr)"
  oops

definition PendingWtsInv where
  "PendingWtsInv s \<longleftrightarrow> (\<forall>svr. \<forall>ts \<in> ran (pending_wtxns (svrs s svr)). ts \<le> clock (svrs s svr))"

definition ClockLstInv where
  "ClockLstInv s \<longleftrightarrow> (\<forall>svr. lst (svrs s svr) \<le> clock (svrs s svr))"

lemma lst_monotonic:
  assumes "state_trans s e s'"
  shows "lst (svrs s' svr) \<ge> lst (svrs s svr)"
  oops

lemma gst_monotonic:
  assumes "state_trans s e s'"
  shows "gst (cls s' cl) \<ge> gst (cls s cl)"
  oops

lemma tm_view_inv:
  assumes "state_trans s e s'"
    and "not_committing_ev e"
  shows "cl_view (cls s' cl) = cl_view (cls s cl)"
  oops

end
