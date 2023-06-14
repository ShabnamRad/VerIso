section \<open>Eiger Port Plus Protocol Satisfying CCv (Causal+) - Proofs and lemmas\<close>

theory "EP+_TCCv_invariants"
  imports "EP+_TCCv"
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
  assumes "cl_state (cls s cl) = RtxnInProg keys kvt_map"
    and "kvt_map k = None"
    and "cl_state (cls s' cl) = RtxnInProg keys (kvt_map (k \<mapsto> (v, t)))"
    and "svr_state (svrs s k) t = Commit cts v rs deps"
    and "\<And>k t. svr_state (svrs s' k) t = svr_state (svrs s k) t"
  shows "get_ctx s' (kvt_map (k \<mapsto> (v, t))) = get_ctx s kvt_map \<union> (insert (k, t) deps)" oops

subsection  \<open>Extra: general lemmas: find, min, append\<close>

subsection \<open>monotonic lemmas and inequality of timestamps invariants\<close>

lemma svr_clock_monotonic:
  "state_trans s e s' \<Longrightarrow> svr_clock (svrs s' svr) \<ge> svr_clock (svrs s svr)" oops

lemma cl_clock_monotonic:
  "state_trans s e s' \<Longrightarrow> cl_clock (cls s' cl) \<ge> cl_clock (cls s cl)" oops

definition Pend_Wt_UB where
  "Pend_Wt_UB s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns_ts (svr_state (svrs s svr)). ts \<le> svr_clock (svrs s svr))"

definition Finite_Pend_Inv where
  "Finite_Pend_Inv s svr \<longleftrightarrow> finite (pending_wtxns_ts (svr_state (svrs s svr)))"

definition Clk_le_Lst where
  "Clk_le_Lst s k \<longleftrightarrow> lst (svrs s k) \<le> svr_clock (svrs s k)"

definition Pend_Wt_LB where
  "Pend_Wt_LB s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns_ts (svr_state (svrs s svr)). lst (svrs s svr) \<le> ts)"

lemma min_pending_wtxns_monotonic:
  assumes "state_trans s e s'"
    and "pending_wtxns_ts (svr_state (svrs s k)) \<noteq> {}"
    and "pending_wtxns_ts (svr_state (svrs s' k)) \<noteq> {}"
    and "Pend_Wt_UB s k" and "Finite_Pend_Inv s k"
  shows "Min (pending_wtxns_ts (svr_state (svrs s k))) \<le>
         Min (pending_wtxns_ts (svr_state (svrs s' k)))" oops


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
    (\<forall>kv_map cts deps. cl_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map deps} \<longrightarrow>
      finite (dom (kv_map)))"

definition Finite_Dom_Kvt_map where
  "Finite_Dom_Kvt_map s cl \<longleftrightarrow>
    (\<forall>keys kvt_map. cl_state (cls s cl) = RtxnInProg keys kvt_map \<longrightarrow>
      finite (dom (kvt_map)) \<and> keys \<noteq> {})"

definition Finite_t_Ran_Kvt_map where
  "Finite_t_Ran_Kvt_map s cl \<longleftrightarrow>
    (\<forall>keys kvt_map. cl_state (cls s cl) = RtxnInProg keys kvt_map \<longrightarrow>
      finite (snd ` ran (kvt_map)))"

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
  "Pend_Wt_Inv s k \<longleftrightarrow> (\<forall>prep_t. prep_t \<in> pending_wtxns_ts (svr_state (svrs s k))
    \<longleftrightarrow> (\<exists>t v. svr_state (svrs s k) t = Prep prep_t v))"

definition Lst_Lt_Pts where
  "Lst_Lt_Pts s k \<longleftrightarrow> (\<forall>t prep_t v. svr_state (svrs s k) t = Prep prep_t v \<longrightarrow> lst (svrs s k) \<le> prep_t)"

definition Finite_Wtxns_Dom where
  "Finite_Wtxns_Dom s k \<longleftrightarrow> finite (wtxns_dom (svr_state (svrs s k)))"

definition Finite_Wtxns_rsran where
  "Finite_Wtxns_rsran s k \<longleftrightarrow> finite (wtxns_rsran (svr_state (svrs s k)))"


subsection \<open>Invariants about kvs, global ts and init version v0\<close>

definition Kvs_Not_Emp where
  "Kvs_Not_Emp s \<longleftrightarrow> (\<forall>k. svr_state (svrs s k) \<noteq> wtxns_emp)"

definition T0_in_CO where
  "T0_in_CO s k \<longleftrightarrow> T0 \<in> set (commit_order s k)"

definition KvsOfS_Not_Emp where
  "KvsOfS_Not_Emp s \<longleftrightarrow> (\<forall>k. kvs_of_s s k \<noteq> [])"

definition Init_Ver_Inv where
  "Init_Ver_Inv s k \<longleftrightarrow> (\<exists>rs. svr_state (svrs s k) T0 = Commit 0 undefined rs {})"


subsection \<open>Invariant about server and client state relations and (future and past) transactions ids\<close>

\<comment> \<open>Value of rtxn_rts for current and future transaction ids\<close>
definition CFTid_Rtxn_Inv where
  "CFTid_Rtxn_Inv s cl \<longleftrightarrow> (\<forall>n. n \<ge> cl_sn (cls s cl) \<longrightarrow> rtxn_rts s (Tn_cl n cl) = None)"

\<comment> \<open>Value of svr_state for future transaction ids\<close>
definition FTid_Wtxn_Inv where
  "FTid_Wtxn_Inv s cl \<longleftrightarrow> (\<forall>n k. n > cl_sn (cls s cl) \<longrightarrow> svr_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver)"

\<comment> \<open>Next 4 invariants: cl_state + cl_sn \<longrightarrow> svr_state\<close>
definition Cl_Rtxn_Inv where
  "Cl_Rtxn_Inv s \<longleftrightarrow> (\<forall>cl k keys kvm. cl_state (cls s cl) \<in> {Idle, RtxnInProg keys kvm}
    \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver)"

definition Cl_Wtxn_Idle_Svr where
  "Cl_Wtxn_Idle_Svr s \<longleftrightarrow>
    (\<forall>cl k cts kv_map deps. cl_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map deps}
        \<and> kv_map k = None \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver)"

definition Cl_Prep_Inv where
  "Cl_Prep_Inv s \<longleftrightarrow> (\<forall>cl k kvm. \<exists>prep_t v. cl_state (cls s cl) = WtxnPrep kvm
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) \<in> {No_Ver, Prep prep_t v}) \<and>
    (k \<notin> dom kvm \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver))"

definition Cl_Commit_Inv where
  "Cl_Commit_Inv s \<longleftrightarrow> (\<forall>cl k cts kvm deps. \<exists>prep_t v rs. cl_state (cls s cl) = WtxnCommit cts kvm deps
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) \<in> {Prep prep_t v, Commit cts v rs deps}) \<and>
    (kvm k = None \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver))"

\<comment> \<open>Next 2 invariants: svr_state \<longrightarrow> cl_state\<close>
definition Prep_is_Curr_wt where
  "Prep_is_Curr_wt s k \<longleftrightarrow> (\<forall>t. is_prepared (svr_state (svrs s k) t) \<longrightarrow> is_curr_wt s t)"

definition Svr_Prep_Inv where
  "Svr_Prep_Inv s \<longleftrightarrow> (\<forall>k t ts v. svr_state (svrs s k) t = Prep ts v \<longrightarrow>
    (\<exists>cts kv_map deps.
      cl_state (cls s (get_cl_w t)) \<in> {WtxnPrep  kv_map, WtxnCommit cts kv_map deps} \<and>
      k \<in> dom kv_map))"

definition Svr_Commit_Inv where
  "Svr_Commit_Inv s \<longleftrightarrow> (\<forall>k t cts v rs deps. 
    svr_state (svrs s k) t = Commit cts v rs deps \<and> is_curr_wt s t \<longrightarrow> 
      (\<exists>kv_map. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map deps \<and> k \<in> dom kv_map))"

\<comment> \<open>Values of svr_state and rtxn_rts for past transaction ids\<close>
definition PTid_Inv where
  "PTid_Inv s cl \<longleftrightarrow> (\<forall>k. \<forall>n < cl_sn (cls s cl).
   (svr_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver) \<or>
   (rtxn_rts s (Tn_cl n cl) = None \<and> 
    (\<exists>cts v rs deps. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts v rs deps)))"

lemma other_sn_idle:  
  assumes "FTid_Wtxn_Inv s cl" and "PTid_Inv s cl"
    and "get_cl t = cl" and "get_sn t \<noteq> cl_sn (cls s cl)"
  shows "\<And>k. \<exists>cts v rs deps. svr_state (svrs s k) (Tn t) \<in> {No_Ver, Commit cts v rs deps}" oops

definition Rtxn_Wtxn_No_Ver where
  "Rtxn_Wtxn_No_Ver s cl \<longleftrightarrow>
    (\<forall>n ts. rtxn_rts s (Tn_cl n cl) = Some ts \<longrightarrow> (\<forall>k. svr_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver))"

definition Wtxn_Rtxn_None where
  "Wtxn_Rtxn_None s k \<longleftrightarrow>
    (\<forall>cl n ts v cts rs deps. svr_state (svrs s k) (Tn (Tn_cl n cl)) \<in> {Prep ts v, Commit cts v rs deps}
       \<longrightarrow> rtxn_rts s (Tn_cl n cl) = None)"

definition WtxnCommit_Wtxn_Cts where
  "WtxnCommit_Wtxn_Cts s cl \<longleftrightarrow> (\<forall>cts kv_map deps. cl_state (cls s cl) = WtxnCommit cts kv_map deps
    \<longrightarrow> wtxn_cts s (get_wtxn s cl) = Some cts)"

definition Wtxn_State_Cts where
  "Wtxn_State_Cts s k \<longleftrightarrow> (\<forall>t cts v rs deps ts kv_map.
    svr_state (svrs s k) t = Commit cts v rs deps \<or>
   (svr_state (svrs s k) t = Prep ts v \<and> cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map deps)
      \<longrightarrow> wtxn_cts s t = Some cts)"

definition FTid_notin_rs where
  "FTid_notin_rs s cl \<longleftrightarrow> (\<forall>k n t cts v rs deps. n > cl_sn (cls s cl) \<and>
    svr_state (svrs s k) t = Commit cts v rs deps \<longrightarrow> Tn_cl n cl \<notin> rs)"

definition FTid_not_wr where
  "FTid_not_wr s cl \<longleftrightarrow> (\<forall>n k. n > cl_sn (cls s cl) \<longrightarrow> Tn (Tn_cl n cl) \<notin> wtxns_dom (svr_state (svrs s k)))"

definition Fresh_wr_notin_rs where
  "Fresh_wr_notin_rs s k \<longleftrightarrow> (\<forall>t t' cts kv_map deps cts' v' rs' deps'.
    cl_state (cls s (get_cl t')) \<in> {Idle, WtxnPrep kv_map, WtxnCommit cts kv_map deps} \<and>
    get_sn t' \<ge> cl_sn (cls s (get_cl t')) \<and>
    svr_state (svrs s k) t = Commit cts' v' rs' deps' \<longrightarrow> t' \<notin> rs')"

definition Fresh_wr_notin_Wts_dom where
  "Fresh_wr_notin_Wts_dom s cl \<longleftrightarrow> (\<forall>keys kv_map k. cl_state (cls s cl) \<in> {Idle, RtxnInProg keys kv_map} \<longrightarrow>
    Tn (get_txn s cl) \<notin> wtxns_dom (svr_state (svrs s k)))"

definition Rtxn_rts_le_Gst where
  "Rtxn_rts_le_Gst s cl \<longleftrightarrow> (\<forall>n ts. rtxn_rts s (Tn_cl n cl) = Some ts \<longrightarrow> ts \<le> gst (cls s cl))"

subsection \<open>Gst, Cts, Pts relations\<close>

definition Gst_le_Pts where
  "Gst_le_Pts s cl \<longleftrightarrow> (\<forall>k prep_t v. 
      svr_state (svrs s k) (get_wtxn s cl) = Prep prep_t v \<longrightarrow> gst (cls s cl) \<le> prep_t)"

definition Gst_Lt_Cts where
  "Gst_Lt_Cts s cl \<longleftrightarrow> (\<forall>k cts v rs deps. 
      svr_state (svrs s k) (get_wtxn s cl) = Commit cts v rs deps \<longrightarrow> gst (cls s cl) < cts)" (*RInvoke & CommitW*)

definition Gst_Lt_Cl_Cts where
  "Gst_Lt_Cl_Cts s cl \<longleftrightarrow> (\<forall>cl' cts kv_map deps. cl_state (cls s cl') = WtxnCommit cts kv_map deps
    \<longrightarrow> gst (cls s cl) < cts)" (*RInvoke & CommitW*)


subsection \<open>Invariants about commit order\<close>

abbreviation is_committed_in_kvs where
  "is_committed_in_kvs s k t \<equiv> 
    is_committed (svr_state (svrs s k) t)  \<or> 
    (is_prepared (svr_state (svrs s k) t) \<and> \<comment> \<open>is_curr_wt s t \<and>\<close>
     (\<exists>cts kv_map deps. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map deps))"

definition CO_Tid where
  "CO_Tid s cl \<longleftrightarrow> (case cl_state (cls s cl) of
    WtxnCommit cts kv_map deps \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (commit_order s k) \<longrightarrow> n \<le> cl_sn (cls s cl))
  | _ \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (commit_order s k) \<longrightarrow> n < cl_sn (cls s cl)))"

definition CO_Distinct where
  "CO_Distinct s k \<longleftrightarrow> distinct (commit_order s k)"

definition CO_Tn_is_Cmt_Abs where
  "CO_Tn_is_Cmt_Abs s k \<longleftrightarrow> (\<forall>n cl. Tn (Tn_cl n cl) \<in> set (commit_order s k) \<longrightarrow>
    (\<exists>cts v rs deps. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts v rs deps) \<or> 
    ((\<exists>ts v. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Prep ts v) \<and> 
     (\<exists>cts kv_map deps. cl_state (cls s cl) = WtxnCommit cts kv_map deps \<and> 
      cl_sn (cls s cl) = n \<and> k \<in> dom kv_map)))"

definition CO_not_No_Ver where
  "CO_not_No_Ver s k \<longleftrightarrow> (\<forall>t \<in> set (commit_order s k). svr_state (svrs s k) t \<noteq> No_Ver)"

definition CO_has_Cts where
  "CO_has_Cts s k \<longleftrightarrow> (\<forall>t \<in> set (commit_order s k). \<exists>cts. wtxn_cts s t = Some cts)"

definition Committed_Abs_Tn_in_CO where
  "Committed_Abs_Tn_in_CO s k \<longleftrightarrow> (\<forall>n cl.
    (\<exists>cts v rs deps. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts v rs deps) \<or> 
    ((\<exists>ts v. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Prep ts v) \<and> 
     (\<exists>cts kv_map deps. cl_state (cls s cl) = WtxnCommit cts kv_map deps \<and> cl_sn (cls s cl) = n)) \<longrightarrow>
    Tn (Tn_cl n cl) \<in> set (commit_order s k))"

definition Committed_Abs_in_CO where
  "Committed_Abs_in_CO s k \<longleftrightarrow> (\<forall>t.
    (\<exists>cts v rs deps. svr_state (svrs s k) t = Commit cts v rs deps) \<or> 
    ((\<exists>ts v. svr_state (svrs s k) t = Prep ts v) \<and>
     (\<exists>cts kv_map deps. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map deps)) \<longrightarrow>
    t \<in> set (commit_order s k))"

definition CO_Sorted where
  "CO_Sorted s k \<longleftrightarrow> (\<forall>i < length (commit_order s k). \<forall>i' < length (commit_order s k).
    i < i' \<longrightarrow> the (wtxn_cts s (commit_order s k ! i)) \<le> the (wtxn_cts s (commit_order s k ! i')))" (*WCommit*)


subsection \<open>kvs_of_s through events\<close>

lemma write_commit_kvs_of_s:
  assumes "write_commit cl kv_map commit_t sn u'' s s'"
  shows"kvs_of_s s' = update_kv (Tn_cl sn cl)
         (\<lambda>k. case_op_type None (kv_map k))
         (view_of (commit_order s) (cl_ctx (cls s cl)))
         (kvs_of_s s)" oops

abbreviation invariant_list_kvs where
  "invariant_list_kvs s \<equiv> \<forall>k. CO_not_No_Ver s k \<and>  Fresh_wr_notin_rs s k"

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
  "Sqn_Inv_nc s cl \<longleftrightarrow> (\<forall>cts kvm deps. cl_state (cls s cl) \<noteq> WtxnCommit cts kvm deps
    \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m < cl_sn (cls s cl)))" (* commit events *)

definition Sqn_Inv_c where
  "Sqn_Inv_c s cl \<longleftrightarrow> (\<forall>cts kvm deps. cl_state (cls s cl) = WtxnCommit cts kvm deps
    \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m \<le> cl_sn (cls s cl)))"

lemma t_is_fresh:
  assumes "Sqn_Inv_c s cl" and "Sqn_Inv_nc s cl"
    and "cl_state (cls s cl) \<in> {WtxnPrep kv_map, RtxnInProg keys kvt_map}"
  shows "get_txn s cl \<in> next_txids (kvs_of_s s) cl" oops

subsection \<open>At functions point to committed versions\<close>

lemma at_is_committed:
  assumes "Init_Ver_Inv s k"
  shows "is_committed ((svr_state (svrs s k)) (at (svr_state (svrs s k)) rts))" oops

lemma newest_own_write_is_committed:
  assumes "Finite_Wtxns_Dom s k"and "newest_own_write (svr_state (svrs s k)) ts cl = Some t"
  shows "is_committed (svr_state (svrs s k) t)" oops

lemma read_at_is_committed:
  assumes "Init_Ver_Inv s k" and "Finite_Wtxns_Dom s k"
  shows "is_committed (svr_state (svrs s k) (read_at (svr_state (svrs s k)) rts cl))" oops

definition Kvt_map_t_Committed where
  "Kvt_map_t_Committed s cl \<longleftrightarrow> (\<forall>keys kvt_map k v t. cl_state (cls s cl) = RtxnInProg keys kvt_map
    \<and> kvt_map k = Some (v, t) \<longrightarrow> (\<exists>cts rs deps. svr_state (svrs s k) t = Commit cts v rs deps))"


subsection \<open>Kvt_map values meaning for read_done\<close>
definition Rtxn_IdleK_notin_rs where
  "Rtxn_IdleK_notin_rs s cl \<longleftrightarrow> (\<forall>k keys kvt_map t cts v rs deps.
    cl_state (cls s cl) = RtxnInProg keys kvt_map \<and> k \<notin> keys \<and>
    svr_state (svrs s k) t = Commit cts v rs deps \<longrightarrow> get_txn s cl \<notin> rs)"

definition Rtxn_RegK_in_rs where
  "Rtxn_RegK_in_rs s cl \<longleftrightarrow> (\<forall>k keys kvt_map t cts v rs deps.
    cl_state (cls s cl) = RtxnInProg keys kvt_map \<and> kvt_map k = Some (v, t) \<and>
    svr_state (svrs s k) t = Commit cts v rs deps \<longrightarrow> get_txn s cl \<in> rs)"


subsection \<open>Timestamp relations\<close>

definition Disjoint_RW where
  "Disjoint_RW s \<longleftrightarrow> ((\<Union>k. wtxns_dom (svr_state (svrs s k))) \<inter> Tn ` (\<Union>k. wtxns_rsran (svr_state (svrs s k))) = {})" (* not proven *)

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

subsection \<open>Closedness\<close>
lemma visTx'_union_distr: "visTx' K (u\<^sub>1 \<union> u\<^sub>2) = visTx' K u\<^sub>1 \<union> visTx' K u\<^sub>2"
  by (auto simp add: visTx'_def)

lemma visTx'_Union_distr: "visTx' K (\<Union>i\<in>I. u i) = (\<Union>i\<in>I. visTx' K (u i))"
  by (auto simp add: visTx'_def)

lemma visTx'_same_writers: "kvs_writers K' = kvs_writers K \<Longrightarrow> visTx' K' u = visTx' K u"
  by (simp add: visTx'_def)

lemma union_closed':
  assumes "closed' K u\<^sub>1 r"
    and "closed' K u\<^sub>2 r"
    and "kvs_writers K' = kvs_writers K" 
    and "read_only_Txs K \<subseteq> read_only_Txs K'"
  shows "closed' K' (u\<^sub>1 \<union> u\<^sub>2) r"
  using assms
  by (auto simp add: closed'_def visTx'_union_distr visTx'_same_writers[of K']
           intro: closed_general_set_union_closed)

lemma Union_closed':
  assumes "\<And>i. i \<in> I \<Longrightarrow> closed' K (u i) r"
    and "finite I" 
    and "kvs_writers K' = kvs_writers K" 
    and "read_only_Txs K \<subseteq> read_only_Txs K'"
  shows "closed' K' (\<Union>i\<in>I. u i) r"
  using assms                                  
  apply (simp add: closed'_def visTx'_Union_distr visTx'_same_writers[of K'])
  apply (rule closed_general_set_Union_closed)
  apply auto
  done

lemma union_closed'_extend_rel:
  assumes "closed' K u\<^sub>1 r"
    and "closed' K u\<^sub>2 r"
    and "kvs_writers K' = kvs_writers K" 
    and "read_only_Txs K \<subseteq> read_only_Txs K'"
    and "x \<notin> (r\<inverse>)\<^sup>* `` (visTx' K u\<^sub>1 \<union> visTx' K u\<^sub>2)"
    and "r' = (\<Union>y\<in>Y. {(y, x)}) \<union> r"
    and "finite Y"
  shows "closed' K' (u\<^sub>1 \<union> u\<^sub>2) r'"
  using assms
  by (auto simp add: closed'_def visTx'_union_distr visTx'_same_writers[of K']
      intro: closed_general_union_V_extend_N_extend_rel)


lemma visTx'_new_writer: "kvs_writers K' = insert t (kvs_writers K) \<Longrightarrow>
  snd ` t_wr_deps = {t} \<Longrightarrow> visTx' K' (u \<union> t_wr_deps) = insert t (visTx' K u)"
  by (auto simp add: visTx'_def)

lemma insert_wr_t_closed':
  assumes "closed' K u r"
    and "closed_general {t} (r\<inverse>) (visTx' K u \<union> read_only_Txs K)"
    and "read_only_Txs K' = read_only_Txs K"
    and "kvs_writers K' = insert t (kvs_writers K)"
    and "snd ` t_wr_deps = {t}"
  shows "closed' K' (u \<union> t_wr_deps) r"
  using assms
  by (auto simp add: closed'_def visTx'_new_writer intro: closed_general_set_union_closed)

\<comment> \<open>insert (k, t) in version's deps - used in get_ctx\<close>
lemma visTx'_observes_t:
  "t \<in> kvs_writers K \<Longrightarrow> visTx' K (insert (k, t) deps) = insert t (visTx' K deps)"
  by (simp add: visTx'_def)

lemma insert_kt_to_deps_closed':
  assumes "closed' K deps r"
    and "t \<in> kvs_writers K"
    and "closed_general {t} (r\<inverse>) (visTx' K deps \<union> read_only_Txs K)"
  shows "closed' K (insert (k, t) deps) r"
  using assms
  by (auto simp add: closed'_def visTx'_observes_t intro: closed_general_set_union_closed)


\<comment> \<open>concrete read_done closedness\<close>

\<comment> \<open>premises\<close>
lemma get_ctx_reformulate:
  assumes "cl_state (cls s cl) = RtxnInProg keys kvt_map"
    and "Kvt_map_t_Committed s cl"
  shows "get_ctx s kvt_map = (\<Union>k\<in>dom kvt_map. (let t = snd (the (kvt_map k)) in 
    insert (k, t) (get_dep_set (svr_state (svrs s k) t))))" oops
  
lemma get_ctx_closed:
  assumes "\<And>k. k \<in> dom kvt_map \<Longrightarrow> let t = snd (the (kvt_map k)) in
      closed' K (insert (k, t) (get_dep_set (svr_state (svrs s k) t))) r"
    and "cl_state (cls s cl) = RtxnInProg keys kvt_map"
    and "Kvt_map_t_Committed s cl"
    and "Finite_Dom_Kvt_map s cl"
  shows "closed' K (get_ctx s kvt_map) r" oops

lemma read_done_same_writers:
  assumes "read_done cl kvt_map sn u'' s s'"
    and "\<forall>k. CO_not_No_Ver s k"
    and "\<forall>k. CO_not_No_Ver s' k"
  shows "kvs_writers (kvs_of_s s') = kvs_writers (kvs_of_s s)" oops

lemma read_done_new_read:
  assumes "read_done cl kvt_map sn u'' s s'"
    and "\<forall>k. CO_not_No_Ver s k"
    and "\<forall>k. CO_not_No_Ver s' k"
    and "\<forall>k. Committed_Abs_in_CO s k"
    and "\<forall>k. T0_in_CO s k"
    and "Finite_Dom_Kvt_map s cl"
    and "Kvt_map_t_Committed s cl"
    and "Rtxn_RegK_in_rs s cl"
    and "Tn (get_txn s cl) \<notin> kvs_writers (kvs_of_s s)"
  shows "read_only_Txs (kvs_of_s s') = insert (Tn (get_txn s cl)) (read_only_Txs (kvs_of_s s))" oops

lemma read_done_WR_onK:
  assumes "read_done cl kvt_map sn u'' s s'"
  shows "R_onK WR (kvs_of_s s') = (\<Union>y\<in>snd ` ran kvt_map. {(y, Tn (get_txn s cl))}) \<union> R_onK WR (kvs_of_s s)" oops
(* not proven *)

lemma read_done_extend_rel:
  assumes "read_done cl kvt_map sn u'' s s'"
  shows "R_CC (kvs_of_s s') = (\<Union>y\<in>snd ` ran kvt_map. {(y, Tn (get_txn s cl))}) \<union> R_CC (kvs_of_s s)" oops

\<comment> \<open>read_done closedness (canCommit)\<close>
lemma read_done_ctx_closed:
  assumes "closed' (kvs_of_s s) (cl_ctx (cls s cl)) (R_CC (kvs_of_s s))"
    and "closed' (kvs_of_s s) (get_ctx s kvt_map) (R_CC (kvs_of_s s))"
    and "kvs_writers (kvs_of_s s') = kvs_writers (kvs_of_s s)"
    and "read_only_Txs (kvs_of_s s') = insert (Tn (get_txn s cl)) (read_only_Txs (kvs_of_s s))"
    and "Tn (get_txn s cl) \<notin> ((R_CC (kvs_of_s s))\<inverse>)\<^sup>* `` (visTx' (kvs_of_s s) (cl_ctx (cls s cl) \<union> get_ctx s kvt_map))"
    and "R_CC (kvs_of_s s') = (\<Union>y\<in>snd ` ran kvt_map. {(y, Tn (get_txn s cl))}) \<union> R_CC (kvs_of_s s)"
    and "Finite_t_Ran_Kvt_map s cl"
    and "cl_state (cls s cl) = RtxnInProg keys kvt_map"
  shows "closed' (kvs_of_s s') (cl_ctx (cls s cl) \<union> get_ctx s kvt_map) (R_CC (kvs_of_s s'))" oops                        


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
  "svr_state (svrs s k) t = Commit cts v rs deps
    \<Longrightarrow> visTx' (kvs_of_s s) deps \<subseteq> kvs_writers (kvs_of_s s)" oops

lemma visTx'_cl_deps_subset_writers: 
  "cl_state (cls s cl) = WtxnCommit cts kvm deps
    \<Longrightarrow> visTx' (kvs_of_s s) deps \<subseteq> kvs_writers (kvs_of_s s)" oops

lemma "kvs_writers (kvs_of_s s) \<subseteq> (\<Union>k. wtxns_dom (svr_state (svrs s k)))"(* not proven *)
  oops

lemma "kvs_readers (kvs_of_s s) \<subseteq> (\<Union>k. wtxns_rsran (svr_state (svrs s k)))"(* not proven *)
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
  "get_wtxn s cl \<in> kvs_writers K \<Longrightarrow> closed' K (cl_ctx (cls s cl)) r \<Longrightarrow>
    closed' K (insert (k, get_wtxn s cl) (cl_ctx (cls s cl))) r" oops (* not proven *)

definition RO_le_gst :: "'v global_conf \<Rightarrow> cl_id \<Rightarrow> txid set" where
  "RO_le_gst s cl \<equiv> {t \<in> read_only_Txs (kvs_of_s s). \<exists>t'. t = Tn t' \<and> the (rtxn_rts s t') \<le> gst (cls s cl)}"

definition RO_WO_Inv where
  "RO_WO_Inv s \<longleftrightarrow> (\<Union>k. wtxns_dom (svr_state (svrs s k))) \<inter> Tn ` (\<Union>k. wtxns_rsran (svr_state (svrs s k))) = {}" (* server events*)


subsection \<open>Ctx Invariants\<close>

definition View_Init where
  "View_Init s cl \<longleftrightarrow> (\<forall>k. (k, T0) \<in> cl_ctx (cls s cl))"

\<comment> \<open>deps are committed\<close>
definition Ctx_Committed where
  "Ctx_Committed s \<longleftrightarrow> (\<forall>cl k t. (k, t) \<in> cl_ctx (cls s cl) \<longrightarrow>
    is_committed (svr_state (svrs s k) t) \<or> 
    (\<exists>cts kvm deps. cl_state (cls s cl) = WtxnCommit cts kvm deps \<and>
      k \<in> dom kvm \<and> t = get_wtxn s cl))"

definition Deps_Committed where
  "Deps_Committed s \<longleftrightarrow> (\<forall>k t k' t' cts v rs deps. svr_state (svrs s k) t = Commit cts v rs deps \<and>
    (k', t') \<in> deps \<longrightarrow> is_committed (svr_state (svrs s k') t'))"

definition Cl_Deps_Committed where
  "Cl_Deps_Committed s \<longleftrightarrow> (\<forall>cl k t cts kv_map deps. cl_state (cls s cl) = WtxnCommit cts kv_map deps \<and>
    (k, t) \<in> deps \<longrightarrow> is_committed (svr_state (svrs s k) t))"

definition Cl_Ctx_Sub_CO where
  "Cl_Ctx_Sub_CO s k \<longleftrightarrow> (\<forall>cl t. (k, t) \<in> cl_ctx (cls s cl) \<longrightarrow> t \<in> set (commit_order s k))"

definition Get_Ctx_Sub_CO where
  "Get_Ctx_Sub_CO s k \<longleftrightarrow> (\<forall>cl t keys kvt_map. cl_state (cls s cl) = RtxnInProg keys kvt_map \<and>
    (k, t) \<in> get_ctx s kvt_map \<longrightarrow> t \<in> set (commit_order s k))"

definition Deps_Closed where
  "Deps_Closed s cl \<longleftrightarrow> (closed' (kvs_of_s s) (cl_ctx (cls s cl)) (R_CC (kvs_of_s s)) \<and> 
    (\<forall>k t cts v rs kv_map deps. svr_state (svrs s k) t = Commit cts v rs deps \<or>
      cl_state (cls s cl) = WtxnCommit cts kv_map deps \<longrightarrow>
      closed' (kvs_of_s s) deps (R_CC (kvs_of_s s))))" (* not proven *)


subsection \<open>view wellformed\<close>

lemma v_writer_set_commit_order_eq:
  assumes "CO_not_No_Ver s k"                   
  shows "v_writer ` set (kvs_of_s s k) = set (commit_order s k)" oops

lemma reach_kvs_expands [simp]:
  assumes "state_trans s e s'" and "\<And>cl. Sqn_Inv_c s cl" and "\<And>cl. Sqn_Inv_nc s cl"
    and "\<And>cl. PTid_Inv s cl" and "\<And>cl. FTid_Wtxn_Inv s cl"
    and "Kvs_Not_Emp s" and "invariant_list_kvs s"
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
    (\<forall>cts kv_map deps k. cl_state (cls s cl) = WtxnCommit cts kv_map deps \<and> k \<in> dom kv_map \<longrightarrow>
      (k, get_wtxn s cl) \<in> cl_ctx (cls s cl))"

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
    cl_state (cls s (get_cl t)) = RtxnInProg keys kv_map \<and> k \<in> keys \<and> kv_map k = None \<and>
    svr_state (svrs s k) (read_at (svr_state (svrs s k)) (gst (cls s (get_cl t))) (get_cl t))
       = Commit cts v rs deps \<longrightarrow>
    v = v_value (last_version (kvs_of_s s k)
      (view_of (commit_order s) (get_view s (get_cl t)) k)))"
 (* not proven *)

definition Rtxn_Fp_Inv where
  "Rtxn_Fp_Inv s cl \<longleftrightarrow> (\<forall>k t keys kvt_map v.
    cl_state (cls s cl) = RtxnInProg keys kvt_map \<and> kvt_map k = Some (v, t) \<longrightarrow>
     v = v_value (last_version (kvs_of_s s k)
      (view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s kvt_map) k)))"
(* not proven *)
  

subsection \<open>Refinement Proof\<close>
abbreviation invariant_list where
  "invariant_list s \<equiv> (\<forall>cl k. invariant_list_kvs s \<and> Sqn_Inv_c s cl \<and> Sqn_Inv_nc s cl
    \<and> Views_of_s_Wellformed s cl \<and> Rtxn_Fp_Inv s cl \<and> CO_Distinct s k \<and> Ctx_Committed s)"

end
