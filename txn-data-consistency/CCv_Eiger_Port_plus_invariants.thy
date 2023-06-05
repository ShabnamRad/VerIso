section \<open>Eiger Port Plus Protocol Satisfying CCv (Causal+) - Proofs and lemmas\<close>

theory CCv_Eiger_Port_plus_invariants
  imports CCv_Eiger_Port_plus
begin

section \<open>Lemmas about the functions\<close>


subsection \<open>wtxns_dom lemmas\<close>
subsection \<open>wtxns_vran lemmas\<close>
subsection \<open>wtxns_rsran lemmas\<close>

subsection \<open>Helper functions lemmas: arg_max, add_to_readerset, pending_wtxns_ts\<close>

lemma view_of_prefix:
  assumes "\<And>k. prefix (corder k) (corder' k)"
    and "\<And>k. distinct (corder' k)"
    and "\<And>k. u `` {k} \<subseteq> set (corder k)"
  shows "view_of corder u = view_of corder' u" oops

lemma get_ctx_step:
  assumes "txn_state (cls s cl) = RtxnInProg keys kvt_map"
    and "kvt_map k = None"
    and "txn_state (cls s' cl) = RtxnInProg keys (kvt_map (k \<mapsto> (v, t)))"
    and "wtxn_state (svrs s k) t = Commit cts v rs deps"
    and "\<And>k t. wtxn_state (svrs s' k) t = wtxn_state (svrs s k) t"
  shows "get_ctx s' (kvt_map (k \<mapsto> (v, t))) = get_ctx s kvt_map \<union> (insert (k, t) deps)" oops

subsection  \<open>Extra: general lemmas: find, min, append\<close>

subsection \<open>monotonic lemmas and inequality of timestamps invariants\<close>

lemma clock_monotonic:
  "state_trans s e s' \<Longrightarrow> clock (svrs s' svr) \<ge> clock (svrs s svr)" oops

lemma cl_clock_monotonic:
  "state_trans s e s' \<Longrightarrow> cl_clock (cls s' cl) \<ge> cl_clock (cls s cl)" oops

definition Pend_Wt_UB where
  "Pend_Wt_UB s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns_ts (wtxn_state (svrs s svr)). ts \<le> clock (svrs s svr))"

definition Finite_Pend_Inv where
  "Finite_Pend_Inv s svr \<longleftrightarrow> finite (pending_wtxns_ts (wtxn_state (svrs s svr)))"

definition Clk_le_Lst where
  "Clk_le_Lst s k \<longleftrightarrow> lst (svrs s k) \<le> clock (svrs s k)"

definition Pend_Wt_LB where
  "Pend_Wt_LB s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns_ts (wtxn_state (svrs s svr)). lst (svrs s svr) \<le> ts)"

lemma min_pending_wtxns_monotonic:
  assumes "state_trans s e s'"
    and "pending_wtxns_ts (wtxn_state (svrs s k)) \<noteq> {}"
    and "pending_wtxns_ts (wtxn_state (svrs s' k)) \<noteq> {}"
    and "Pend_Wt_UB s k" and "Finite_Pend_Inv s k"
  shows "Min (pending_wtxns_ts (wtxn_state (svrs s k))) \<le>
         Min (pending_wtxns_ts (wtxn_state (svrs s' k)))" oops


lemma lst_monotonic:
  assumes "state_trans s e s'"
    and "Clk_le_Lst s svr" and "Finite_Pend_Inv s svr"
    and "Pend_Wt_LB s svr"
  shows "lst (svrs s' svr) \<ge> lst (svrs s svr)" oops

definition Lst_map_le_Lst where
  "Lst_map_le_Lst s cl k \<longleftrightarrow> (lst_map (cls s cl) k \<le> lst (svrs s k))"

lemma lst_map_monotonic:
  assumes "state_trans s e s'"
    and "Lst_map_le_Lst s cl k"
  shows "lst_map (cls s cl) k \<le> lst_map (cls s' cl) k" oops

definition Finite_Dom_Kv_map where
  "Finite_Dom_Kv_map s cl \<longleftrightarrow>
    (\<forall>kv_map cts deps. txn_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map deps} \<longrightarrow>
      finite (dom (kv_map)))"

definition Finite_Lst_map_Ran where
  "Finite_Lst_map_Ran s cl \<longleftrightarrow> finite (range (lst_map (cls s cl)))"

lemma lst_map_min_monotonic:
  assumes "state_trans s e s'"
    and "\<And>k. Lst_map_le_Lst s cl k"
    and "Finite_Lst_map_Ran s cl"
    and "Finite_Lst_map_Ran s' cl"
  shows "Min (range (lst_map (cls s cl))) \<le> Min (range (lst_map (cls s' cl)))" oops

definition Gst_le_Min_Lst_map where
  "Gst_le_Min_Lst_map s cl \<longleftrightarrow> (gst (cls s cl) \<le> Min (range (lst_map (cls s cl))))"

lemma gst_monotonic:
  assumes "state_trans s e s'"
    and "Gst_le_Min_Lst_map s cl"
  shows "gst (cls s' cl) \<ge> gst (cls s cl)" oops

definition Gst_le_Lst_map where
  "Gst_le_Lst_map s cl k \<longleftrightarrow> (gst (cls s cl) \<le> lst_map (cls s cl) k)"

definition Pend_Wt_Inv where
  "Pend_Wt_Inv s k \<longleftrightarrow> (\<forall>prep_t. prep_t \<in> pending_wtxns_ts (wtxn_state (svrs s k))
    \<longleftrightarrow> (\<exists>t v. wtxn_state (svrs s k) t = Prep prep_t v))"

definition Lst_Lt_Pts where
  "Lst_Lt_Pts s k \<longleftrightarrow> (\<forall>t prep_t v. wtxn_state (svrs s k) t = Prep prep_t v \<longrightarrow> lst (svrs s k) \<le> prep_t)"

definition Finite_Wtxns_Dom where
  "Finite_Wtxns_Dom s k \<longleftrightarrow> finite (wtxns_dom (wtxn_state (svrs s k)))"

definition Finite_Wtxns_rsran where
  "Finite_Wtxns_rsran s k \<longleftrightarrow> finite (wtxns_rsran (wtxn_state (svrs s k)))"


subsection \<open>Invariants about kvs, global ts and init version v0\<close>

definition Kvs_Not_Emp where
  "Kvs_Not_Emp s \<longleftrightarrow> (\<forall>k. wtxn_state (svrs s k) \<noteq> wtxns_emp)"

definition Commit_Order_T0 where
  "Commit_Order_T0 s k \<longleftrightarrow> T0 \<in> set (commit_order s k)"

definition KvsOfS_Not_Emp where
  "KvsOfS_Not_Emp s \<longleftrightarrow> (\<forall>k. kvs_of_s s k \<noteq> [])"

definition Init_Ver_Inv where
  "Init_Ver_Inv s k \<longleftrightarrow> (\<exists>rs. wtxn_state (svrs s k) T0 = Commit 0 undefined rs {})"


subsection \<open>Invariant about server and client state relations and (future and past) transactions ids\<close>

\<comment> \<open>Value of rtxn_rts for current and future transaction ids\<close>
definition CFTid_Rtxn_Inv where
  "CFTid_Rtxn_Inv s cl \<longleftrightarrow> (\<forall>n. n \<ge> txn_sn (cls s cl) \<longrightarrow> rtxn_rts s (Tn_cl n cl) = None)"

\<comment> \<open>Value of wtxn_state for future transaction ids\<close>
definition FTid_Wtxn_Inv where
  "FTid_Wtxn_Inv s cl \<longleftrightarrow> (\<forall>n k. n > txn_sn (cls s cl) \<longrightarrow> wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver)"

\<comment> \<open>Next 4 invariants: txn_state + txn_sn \<longrightarrow> wtxn_state\<close>
definition Cl_Rtxn_Inv where
  "Cl_Rtxn_Inv s \<longleftrightarrow> (\<forall>cl k keys kvm. txn_state (cls s cl) \<in> {Idle, RtxnInProg keys kvm}
    \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) = No_Ver)"

definition Cl_Wtxn_Idle_Svr where
  "Cl_Wtxn_Idle_Svr s \<longleftrightarrow>
    (\<forall>cl k cts kv_map deps. txn_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map deps}
        \<and> kv_map k = None \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) = No_Ver)"

definition Cl_Prep_Inv where
  "Cl_Prep_Inv s \<longleftrightarrow> (\<forall>cl k kvm. \<exists>prep_t v. txn_state (cls s cl) = WtxnPrep kvm
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) \<in> {No_Ver, Prep prep_t v}) \<and>
    (k \<notin> dom kvm \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) = No_Ver))"

definition Cl_Commit_Inv where
  "Cl_Commit_Inv s \<longleftrightarrow> (\<forall>cl k cts kvm deps. \<exists>prep_t v rs. txn_state (cls s cl) = WtxnCommit cts kvm deps
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) \<in> {Prep prep_t v, Commit cts v rs deps}) \<and>
    (kvm k = None \<longrightarrow> wtxn_state (svrs s k) (get_wtxn_cl s cl) = No_Ver))"

\<comment> \<open>Next 2 invariants: wtxn_state \<longrightarrow> txn_state\<close>
definition Svr_Prep_Inv where
  "Svr_Prep_Inv s \<longleftrightarrow> (\<forall>k t ts v. wtxn_state (svrs s k) t = Prep ts v  \<and> is_curr_wt s t \<longrightarrow>
    (\<exists>cts kv_map deps.
      txn_state (cls s (get_cl_wtxn t)) \<in> {WtxnPrep  kv_map, WtxnCommit cts kv_map deps} \<and>
      k \<in> dom kv_map))"

definition Svr_Commit_Inv where
  "Svr_Commit_Inv s \<longleftrightarrow> (\<forall>k t cts v rs deps. 
    wtxn_state (svrs s k) t = Commit cts v rs deps \<and> is_curr_wt s t \<longrightarrow> 
      (\<exists>kv_map. txn_state (cls s (get_cl_wtxn t)) = WtxnCommit cts kv_map deps \<and> k \<in> dom kv_map))"

\<comment> \<open>Values of wtxn_state and rtxn_rts for past transaction ids\<close>
definition PTid_Inv where
  "PTid_Inv s cl \<longleftrightarrow> (\<forall>k. \<forall>n < txn_sn (cls s cl).
   (wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver) \<or>
   (rtxn_rts s (Tn_cl n cl) = None \<and> 
    (\<exists>cts v rs deps. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts v rs deps)))"

lemma other_sn_idle:  
  assumes "FTid_Wtxn_Inv s cl" and "PTid_Inv s cl"
    and "get_cl_txn t = cl" and "get_sn_txn t \<noteq> txn_sn (cls s cl)"
  shows "\<And>k. \<exists>cts v rs deps. wtxn_state (svrs s k) (Tn t) \<in> {No_Ver, Commit cts v rs deps}" oops

definition Rtxn_Wtxn_No_Ver where
  "Rtxn_Wtxn_No_Ver s cl \<longleftrightarrow>
    (\<forall>n ts. rtxn_rts s (Tn_cl n cl) = Some ts \<longrightarrow> (\<forall>k. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver))"

definition Wtxn_Rtxn_None where
  "Wtxn_Rtxn_None s k \<longleftrightarrow>
    (\<forall>cl n ts v cts rs deps. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) \<in> {Prep ts v, Commit cts v rs deps}
       \<longrightarrow> rtxn_rts s (Tn_cl n cl) = None)"

definition WtxnCommit_Wtxn_Cts where
  "WtxnCommit_Wtxn_Cts s cl \<longleftrightarrow> (\<forall>cts kv_map deps. txn_state (cls s cl) = WtxnCommit cts kv_map deps
    \<longrightarrow> wtxn_cts s (get_wtxn_cl s cl) = Some cts)"

definition Wtxn_State_Cts where
  "Wtxn_State_Cts s k \<longleftrightarrow>
    (\<forall>t cts v rs ts kv_map deps. (wtxn_state (svrs s k) t = Commit cts v rs deps) \<or> 
      (wtxn_state (svrs s k) t = Prep ts v \<and> is_curr_wt s t \<and>
       txn_state (cls s (get_cl_wtxn t)) = WtxnCommit cts kv_map deps)
      \<longrightarrow> wtxn_cts s t = Some cts)"

definition FTid_notin_rs where
  "FTid_notin_rs s cl \<longleftrightarrow> (\<forall>k n t cts v rs deps. n > txn_sn (cls s cl) \<and>
    wtxn_state (svrs s k) t = Commit cts v rs deps \<longrightarrow> Tn_cl n cl \<notin> rs)"

definition FTid_not_wr where
  "FTid_not_wr s cl \<longleftrightarrow> (\<forall>n k. n > txn_sn (cls s cl) \<longrightarrow> Tn (Tn_cl n cl) \<notin> wtxns_dom (wtxn_state (svrs s k)))"

definition Fresh_wr_notin_rs where
  "Fresh_wr_notin_rs s k \<longleftrightarrow> (\<forall>t t' cts kv_map deps cts' v' rs' deps'.
    txn_state (cls s (get_cl_txn t')) \<in> {Idle, WtxnPrep kv_map, WtxnCommit cts kv_map deps} \<and>
    get_sn_txn t' \<ge> txn_sn (cls s (get_cl_txn t')) \<and>
    wtxn_state (svrs s k) t = Commit cts' v' rs' deps' \<longrightarrow> t' \<notin> rs')"

definition Fresh_wr_notin_Wts_dom where
  "Fresh_wr_notin_Wts_dom s cl \<longleftrightarrow> (\<forall>keys kv_map k. txn_state (cls s cl) \<in> {Idle, RtxnInProg keys kv_map} \<longrightarrow>
    Tn (get_txn_cl s cl) \<notin> wtxns_dom (wtxn_state (svrs s k)))"

definition Rtxn_rts_le_Gst where
  "Rtxn_rts_le_Gst s cl \<longleftrightarrow> (\<forall>n ts. rtxn_rts s (Tn_cl n cl) = Some ts \<longrightarrow> ts \<le> gst (cls s cl))"

subsection \<open>Gst, Cts, Pts relations\<close>

definition Gst_le_Pts where
  "Gst_le_Pts s cl \<longleftrightarrow> (\<forall>k prep_t v. 
      wtxn_state (svrs s k) (get_wtxn_cl s cl) = Prep prep_t v \<longrightarrow> gst (cls s cl) \<le> prep_t)"

definition Gst_Lt_Cts where
  "Gst_Lt_Cts s cl \<longleftrightarrow> (\<forall>k cts v rs deps. 
      wtxn_state (svrs s k) (get_wtxn_cl s cl) = Commit cts v rs deps \<longrightarrow> gst (cls s cl) < cts)" (*RInvoke & CommitW*)

definition Gst_Lt_Cl_Cts where
  "Gst_Lt_Cl_Cts s cl \<longleftrightarrow> (\<forall>cl' cts kv_map deps. txn_state (cls s cl') = WtxnCommit cts kv_map deps
    \<longrightarrow> gst (cls s cl) < cts)" (*RInvoke & CommitW*)


subsection \<open>Invariants about commit order\<close>

abbreviation is_committed_in_kvs where
  "is_committed_in_kvs s k t \<equiv> 
    is_committed (wtxn_state (svrs s k) t)  \<or> 
    (is_prepared (wtxn_state (svrs s k) t) \<and> \<comment> \<open>is_curr_wt s t \<and>\<close>
     (\<exists>cts kv_map deps. txn_state (cls s (get_cl_wtxn t)) = WtxnCommit cts kv_map deps))"

definition Commit_Order_Tid where
  "Commit_Order_Tid s cl \<longleftrightarrow> (case txn_state (cls s cl) of
    WtxnCommit cts kv_map deps \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (commit_order s k) \<longrightarrow> n \<le> txn_sn (cls s cl))
  | _ \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (commit_order s k) \<longrightarrow> n < txn_sn (cls s cl)))"

definition Commit_Order_Distinct where
  "Commit_Order_Distinct s k \<longleftrightarrow> distinct (commit_order s k)"

definition Commit_Order_Sound where
  "Commit_Order_Sound s k \<longleftrightarrow> (\<forall>n cl. Tn (Tn_cl n cl) \<in> set (commit_order s k) \<longrightarrow>
    (\<exists>cts v rs deps. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts v rs deps) \<or> 
    ((\<exists>ts v. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Prep ts v) \<and> 
     (\<exists>cts kv_map deps. txn_state (cls s cl) = WtxnCommit cts kv_map deps \<and> 
      txn_sn (cls s cl) = n \<and> k \<in> dom kv_map)))"

definition Commit_Order_Sound' where
  "Commit_Order_Sound' s k \<longleftrightarrow> (\<forall>t \<in> set (commit_order s k). wtxn_state (svrs s k) t \<noteq> No_Ver)"

definition Commit_Order_Sound'' where
  "Commit_Order_Sound'' s k \<longleftrightarrow> (\<forall>t \<in> set (commit_order s k). \<exists>cts. wtxn_cts s t = Some cts)"

definition Commit_Order_Complete where
  "Commit_Order_Complete s k \<longleftrightarrow> (\<forall>n cl.
    (\<exists>cts v rs deps. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts v rs deps) \<or> 
    ((\<exists>ts v. wtxn_state (svrs s k) (Tn (Tn_cl n cl)) = Prep ts v) \<and> 
     (\<exists>cts kv_map deps. txn_state (cls s cl) = WtxnCommit cts kv_map deps \<and> txn_sn (cls s cl) = n)) \<longrightarrow>
    Tn (Tn_cl n cl) \<in> set (commit_order s k))"

definition Commit_Order_Sorted where
  "Commit_Order_Sorted s k \<longleftrightarrow> (\<forall>i < length (commit_order s k). \<forall>i' < length (commit_order s k).
    i < i' \<longrightarrow> the (wtxn_cts s (commit_order s k ! i)) \<le> the (wtxn_cts s (commit_order s k ! i')))" (*WCommit*)


subsection \<open>kvs_of_s preserved through non-commit\<close>

abbreviation invariant_list_kvs where
  "invariant_list_kvs s \<equiv> \<forall>k. Commit_Order_Sound' s k \<and>  Fresh_wr_notin_rs s k"

abbreviation not_committing_ev where
  "not_committing_ev e \<equiv> \<forall>cl kvt_map kv_map cts sn u. e \<noteq> RDone cl kvt_map sn u \<and>
    e \<noteq> WCommit cl kv_map cts sn u"

lemma kvs_of_s_inv:
  assumes "state_trans s e s'"
    and "invariant_list_kvs s"
    and "not_committing_ev e"
  shows "kvs_of_s s' = kvs_of_s s" oops


subsection \<open>Transaction ID Freshness\<close>

definition Sqn_Inv_nc where
  "Sqn_Inv_nc s cl \<longleftrightarrow> (\<forall>cts kvm deps. txn_state (cls s cl) \<noteq> WtxnCommit cts kvm deps
    \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m < txn_sn (cls s cl)))" (* commit events *)

definition Sqn_Inv_c where
  "Sqn_Inv_c s cl \<longleftrightarrow> (\<forall>cts kvm deps. txn_state (cls s cl) = WtxnCommit cts kvm deps
    \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m \<le> txn_sn (cls s cl)))"

lemma t_is_fresh:
  assumes "Sqn_Inv_c s cl" and "Sqn_Inv_nc s cl"
    and "txn_state (cls s cl) \<in> {WtxnPrep kv_map, RtxnInProg keys kvt_map}"
  shows "get_txn_cl s cl \<in> next_txids (kvs_of_s s) cl" oops

subsection \<open>At functions point to committed versions\<close>

lemma at_is_committed:
  assumes "Init_Ver_Inv s k"
  shows "is_committed ((wtxn_state (svrs s k)) (at (wtxn_state (svrs s k)) rts))" oops

lemma newest_own_write_is_committed:
  assumes "Finite_Wtxns_Dom s k"and "newest_own_write (wtxn_state (svrs s k)) ts cl = Some t"
  shows "is_committed (wtxn_state (svrs s k) t)" oops

lemma read_at_is_committed:
  assumes "Init_Ver_Inv s k" and "Finite_Wtxns_Dom s k"
  shows "is_committed (wtxn_state (svrs s k) (read_at (wtxn_state (svrs s k)) rts cl))" oops

subsection \<open>Timestamp relations\<close>

definition Disjoint_RW where
  "Disjoint_RW s \<longleftrightarrow> ((\<Union>k. wtxns_dom (wtxn_state (svrs s k))) \<inter> Tn ` (\<Union>k. wtxns_rsran (wtxn_state (svrs s k))) = {})" (* not proven *)

definition Disjoint_RW' where
  "Disjoint_RW' s \<longleftrightarrow> (kvs_writers (kvs_of_s s) \<inter> Tn ` kvs_readers (kvs_of_s s) = {})" (* not proven *)

definition RO_has_rts where
  "RO_has_rts s \<longleftrightarrow> (\<forall>t. Tn t \<in> read_only_Txs (kvs_of_s s) \<longrightarrow> (\<exists>rts. rtxn_rts s t = Some rts))" (* not proven *)

definition SO_ROs where
  "SO_ROs s \<longleftrightarrow> (\<forall>r1 r2 rts1 rts2. (Tn r1, Tn r2) \<in> SO \<and>
    rtxn_rts s r1 = Some rts1 \<and> rtxn_rts s r2 = Some rts2 \<longrightarrow> rts1 \<le> rts2)"

definition SO_RO_WR where
  "SO_RO_WR s \<longleftrightarrow> (\<forall>r w rts cts. (Tn r, w) \<in> SO \<and>
    rtxn_rts s r = Some rts \<and> wtxn_cts s w = Some cts \<longrightarrow> rts \<le> cts)" (* commit events*)


subsection \<open>CanCommit\<close>

lemmas canCommit_defs = ET_CC.canCommit_def closed_def R_CC_def R_onK_def

lemma the_T0: "(THE i. i = 0 \<and> [T0] ! i = T0) = 0" by auto

lemma visTx_visTx': "\<comment> \<open>\<forall>k t. (k, t) \<in> u \<longrightarrow> t \<in> set (commit_order s k) \<Longrightarrow>\<close>
  visTx (kvs_of_s s) (view_of (commit_order s) u) = visTx' (kvs_of_s s) u" oops (* not proven *)

lemma closed_closed': "\<comment> \<open>\<forall>k t. (k, t) \<in> u \<longrightarrow> t \<in> set (commit_order s k) \<Longrightarrow>\<close>
  closed (kvs_of_s s) (view_of (commit_order s) u) r = closed' (kvs_of_s s) u r" oops

lemma visTx'_subset_writers:
  "visTx' (kvs_of_s s) (get_view s cl) \<subseteq> kvs_writers (kvs_of_s s)" oops

lemma visTx'_cl_ctx_subset_writers:
  "visTx' (kvs_of_s s) (cl_ctx (cls s cl)) \<subseteq> kvs_writers (kvs_of_s s)" oops

lemma visTx'_deps_subset_writers: 
  "wtxn_state (svrs s k) t = Commit cts v rs deps
    \<Longrightarrow> visTx' (kvs_of_s s) deps \<subseteq> kvs_writers (kvs_of_s s)" oops

lemma visTx'_cl_deps_subset_writers: 
  "txn_state (cls s cl) = WtxnCommit cts kvm deps
    \<Longrightarrow> visTx' (kvs_of_s s) deps \<subseteq> kvs_writers (kvs_of_s s)" oops

lemma "kvs_writers (kvs_of_s s) \<subseteq> (\<Union>k. wtxns_dom (wtxn_state (svrs s k)))"(* not proven *)
  oops

lemma "kvs_readers (kvs_of_s s) \<subseteq> (\<Union>k. wtxns_rsran (wtxn_state (svrs s k)))"(* not proven *)
  oops

definition closed_general :: "'v set \<Rightarrow> 'v rel \<Rightarrow> 'v set \<Rightarrow> bool" where
  "closed_general vis r r_only \<equiv> vis = ((r^*) `` (vis)) - r_only"

lemma closed'_generalize: "closed' K u r = closed_general (visTx' K u) (r^-1) (read_only_Txs K)" oops

lemma union_closed_general:
  "closed_general vis r r_only \<Longrightarrow> closed_general vis' r r_only
    \<Longrightarrow> closed_general (vis \<union> vis') r r_only" oops

lemma visTx_union_distr: "visTx' K (u \<union> u') = visTx' K u \<union> visTx' K u'" oops

lemma union_closed: "closed' K u r \<Longrightarrow> closed' K u' r \<Longrightarrow> closed' K (u \<union> u') r" oops

lemma visTx'_insert:
  "snd t \<in> kvs_writers K \<Longrightarrow> visTx' K (insert t u) = insert (snd t) (visTx' K u)" oops

lemma insert_t_closed_general:
  "t \<notin> vis \<Longrightarrow> t \<notin> r_only \<Longrightarrow> (\<And>x. (t, x) \<in> r^* \<Longrightarrow> x \<in> vis \<or> x \<in> r_only \<or> x = t)
    \<Longrightarrow> closed_general vis r r_only \<Longrightarrow> closed_general (insert t vis) r r_only" oops

lemma insert_t_closed:
  "get_wtxn_cl s cl \<in> kvs_writers K \<Longrightarrow> closed' K (cl_ctx (cls s cl)) r \<Longrightarrow>
    closed' K (insert (k, get_wtxn_cl s cl) (cl_ctx (cls s cl))) r" oops (* not proven *)

definition RO_le_gst :: "'v state \<Rightarrow> cl_id \<Rightarrow> txid set" where
  "RO_le_gst s cl \<equiv> {t \<in> read_only_Txs (kvs_of_s s). \<exists>t'. t = Tn t' \<and> the (rtxn_rts s t') \<le> gst (cls s cl)}"

definition RO_WO_Inv where
  "RO_WO_Inv s \<longleftrightarrow> (\<Union>k. wtxns_dom (wtxn_state (svrs s k))) \<inter> Tn ` (\<Union>k. wtxns_rsran (wtxn_state (svrs s k))) = {}" (* server events*)


subsection \<open>Ctx Invariants\<close>

\<comment> \<open>deps are committed\<close>
definition Ctx_Committed where
  "Ctx_Committed s \<longleftrightarrow> (\<forall>cl k t. (k, t) \<in> cl_ctx (cls s cl) \<longrightarrow>
    is_committed (wtxn_state (svrs s k) t) \<or> 
    (\<exists>cts kvm deps. txn_state (cls s cl) = WtxnCommit cts kvm deps \<and>
      k \<in> dom kvm \<and> t = get_wtxn_cl s cl))"

definition Deps_Committed where
  "Deps_Committed s \<longleftrightarrow> (\<forall>k t k' t' cts v rs deps. wtxn_state (svrs s k) t = Commit cts v rs deps \<and>
    (k', t') \<in> deps \<longrightarrow> is_committed (wtxn_state (svrs s k') t'))"

definition Cl_Deps_Committed where
  "Cl_Deps_Committed s \<longleftrightarrow> (\<forall>cl k t cts kv_map deps. txn_state (cls s cl) = WtxnCommit cts kv_map deps \<and>
    (k, t) \<in> deps \<longrightarrow> is_committed (wtxn_state (svrs s k) t))"

definition Cl_Ctx_Sub_CO where
  "Cl_Ctx_Sub_CO s k \<longleftrightarrow> (\<forall>cl t. (k, t) \<in> cl_ctx (cls s cl) \<longrightarrow> t \<in> set (commit_order s k))"

definition Deps_Closed where
  "Deps_Closed s cl \<longleftrightarrow> (closed' (kvs_of_s s) (cl_ctx (cls s cl)) (R_CC (kvs_of_s s)) \<and> 
    (\<forall>k t cts v rs kv_map deps. wtxn_state (svrs s k) t = Commit cts v rs deps \<or>
      txn_state (cls s cl) = WtxnCommit cts kv_map deps \<longrightarrow>
      closed' (kvs_of_s s) deps (R_CC (kvs_of_s s))))" (* not proven *)


subsection \<open>view wellformed\<close>

lemma v_writer_set_commit_order_eq:
  assumes "Commit_Order_Sound' s k"                   
  shows "v_writer ` set (kvs_of_s s k) = set (commit_order s k)" oops

lemma reach_kvs_expands [simp]:
  assumes "state_trans s e s'" and "\<And>cl. Sqn_Inv_c s cl" and "\<And>cl. Sqn_Inv_nc s cl"
    and "\<And>cl. PTid_Inv s cl" and "\<And>cl. FTid_Wtxn_Inv s cl"
    and "Kvs_Not_Emp s" and "\<And>cl k. Fresh_rd_notin_rs s cl k"
  shows "kvs_of_s s \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s kvs_of_s s'" oops (* WCommit subcases *)

lemma visTx_in_kvs_of_s_writers[simp]:
  "reach tps s \<Longrightarrow>
   visTx (kvs_of_s s) ((view_of (commit_order s) (get_view s cl))) \<subseteq> kvs_writers (kvs_of_s s)" oops


subsection \<open>View invariants\<close>

lemma write_commit_views_of_s_other_cl_inv:
  assumes "write_commit cl kv_map cts sn u s s'"
    and "cl' \<noteq> cl"
  shows "views_of_s s' cl' = views_of_s s cl'" oops (* not proven *)

definition Views_of_s_Wellformed where
  "Views_of_s_Wellformed s cl \<longleftrightarrow> (view_wellformed (kvs_of_s s) (views_of_s s cl))" (* commit events *)

subsection \<open>View Shift\<close>

lemma get_view_grows:
  assumes "state_trans s e s'" and "Gst_le_Min_Lst_map s cl"
  shows "(\<lambda>k. get_view s cl `` {k}) \<sqsubseteq> (\<lambda>k. get_view s' cl `` {k})" oops

definition Cl_Ctx_WtxnCommit where
  "Cl_Ctx_WtxnCommit s cl \<longleftrightarrow>
    (\<forall>cts kv_map deps k. txn_state (cls s cl) = WtxnCommit cts kv_map deps \<and> k \<in> dom kv_map \<longrightarrow>
      (k, get_wtxn_cl s cl) \<in> cl_ctx (cls s cl))"

lemma read_commit_added_txid:
  assumes "read_done cl kv_map sn u s s'"
    and "Tn (Tn_cl sn' cl) \<in> (kvs_txids (kvs_of_s s') - kvs_txids (kvs_of_s s))"
  shows "sn' = sn" oops (* not proven *)

subsection \<open>View Grows\<close>

lemma view_grows_view_of: "a \<subseteq> b \<Longrightarrow> view_of corder a \<sqsubseteq> view_of corder b" oops

section \<open>Fp Property\<close>

\<comment> \<open>Fingerprint content invariant and Lemmas for proving the fp_property\<close>

definition RegR_Fp_Inv where
  "RegR_Fp_Inv s k \<longleftrightarrow> (\<forall>t keys kv_map cts v rs deps.
    txn_state (cls s (get_cl_txn t)) = RtxnInProg keys kv_map \<and> k \<in> keys \<and> kv_map k = None \<and>
    wtxn_state (svrs s k) (read_at (wtxn_state (svrs s k)) (gst (cls s (get_cl_txn t))) (get_cl_txn t))
       = Commit cts v rs deps \<longrightarrow>
    v = v_value (last_version (kvs_of_s s k)
      (view_of (commit_order s) (get_view s (get_cl_txn t)) k)))"
 (* not proven *)

definition Rtxn_Fp_Inv where
  "Rtxn_Fp_Inv s cl \<longleftrightarrow> (\<forall>k t keys kvt_map v.
    txn_state (cls s cl) = RtxnInProg keys kvt_map \<and> kvt_map k = Some (v, t) \<longrightarrow>
     v = v_value (last_version (kvs_of_s s k)
      (view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s kvt_map) k)))"
(* not proven *)
  

subsection \<open>Refinement Proof\<close>
abbreviation invariant_list where
  "invariant_list s \<equiv> (\<forall>cl k. invariant_list_kvs s \<and> Sqn_Inv_c s cl \<and> Sqn_Inv_nc s cl
    \<and> Views_of_s_Wellformed s cl \<and> Rtxn_Fp_Inv s cl \<and> Commit_Order_Distinct s k \<and> Ctx_Committed s)"

end
