section \<open>Eiger Port Plus Protocol Satisfying CCv (Causal+) - Proofs and lemmas\<close>

theory "EP+_TCCv_Invariants"
  imports "EP+_Sorted"
begin

subsection \<open>wtxns lemmas\<close>


subsubsection \<open>wtxns_dom lemmas\<close>
subsubsection \<open>wtxns_vran lemmas\<close>
subsubsection \<open>wtxns_rsran lemmas\<close>

subsection \<open>Helper functions lemmas: arg_max, add_to_readerset, pending_wtxns_ts\<close>

lemma view_of_prefix:
  assumes "\<And>k. prefix (corder k) (corder' k)"
    and "\<And>k. distinct (corder' k)"
    and "\<And>k. (set (corder' k) - set (corder k)) \<inter> u k = {}"
  shows "view_of corder u = view_of corder' u" oops


subsection \<open>Extra: general lemmas: find, min, append\<close>

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
  "Clk_le_Lst s k \<longleftrightarrow> svr_lst (svrs s k) \<le> svr_clock (svrs s k)"

definition Pend_Wt_LB where
  "Pend_Wt_LB s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns_ts (svr_state (svrs s svr)). svr_lst (svrs s svr) \<le> ts)"

lemma min_pending_wtxns_monotonic:
  assumes "state_trans s e s'"
    and "pending_wtxns_ts (svr_state (svrs s k)) \<noteq> {}"
    and "pending_wtxns_ts (svr_state (svrs s' k)) \<noteq> {}"
    and "reach tps_s s"
  shows "Min (pending_wtxns_ts (svr_state (svrs s k))) \<le>
         Min (pending_wtxns_ts (svr_state (svrs s' k)))" oops

lemma svr_lst_monotonic:
  assumes "state_trans s e s'"
    and "reach tps_s s"
  shows "svr_lst (svrs s' svr) \<ge> svr_lst (svrs s svr)" oops

definition Rlst_le_Lst where
  "Rlst_le_Lst s k \<longleftrightarrow> (\<forall>t_wr cts ts lst v rs rlst rts t.
    svr_state (svrs s k) t_wr = Commit cts ts lst v rs \<and> rs t = Some (rts, rlst)
      \<longrightarrow> rlst \<le> svr_lst (svrs s k))"

definition Get_lst_le_Lst where
  "Get_lst_le_Lst s k \<longleftrightarrow> (\<forall>t cts sts lst v rs.
    svr_state (svrs s k) t = Commit cts sts lst v rs \<longrightarrow> lst \<le> svr_lst (svrs s k))"

definition Lst_map_le_Lst where
  "Lst_map_le_Lst s cl k \<longleftrightarrow> (lst_map (cls s cl) k \<le> svr_lst (svrs s k))"

definition Rlst_ge_Lst_map where
  "Rlst_ge_Lst_map s cl k \<longleftrightarrow> (\<forall>t cts ts lst v rs rlst rts.
    svr_state (svrs s k) t = Commit cts ts lst v rs \<and> rs (get_txn s cl) = Some (rts, rlst)
      \<longrightarrow> lst_map (cls s cl) k \<le> rlst)" (* not proven *)

definition Get_lst_ge_Lst_map where
  "Get_lst_ge_Lst_map s cl k \<longleftrightarrow> (\<forall>cts ts lst v rs.
    svr_state (svrs s k) (get_wtxn s cl) = Commit cts ts lst v rs \<longrightarrow> lst_map (cls s cl) k \<le> lst)" (* not proven *)

lemma lst_map_monotonic:
  assumes "state_trans s e s'"
    and "reach tps_s s"
  shows "lst_map (cls s cl) k \<le> lst_map (cls s' cl) k" oops

definition Finite_Dom_Kv_map where
  "Finite_Dom_Kv_map s cl \<longleftrightarrow>
    (\<forall>kv_map cts. cl_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map} \<longrightarrow>
      finite (dom (kv_map)))"

definition Finite_Dom_Kv_map_rd where
  "Finite_Dom_Kv_map_rd s cl \<longleftrightarrow>
    (\<forall>keys kv_map. cl_state (cls s cl) = RtxnInProg keys kv_map \<longrightarrow>
      finite (dom (kv_map)) \<and> keys \<noteq> {})"

definition Finite_t_Ran_Kvt_map where
  "Finite_t_Ran_Kvt_map s cl \<longleftrightarrow>
    (\<forall>keys kv_map. cl_state (cls s cl) = RtxnInProg keys kv_map \<longrightarrow>
      finite (snd ` ran (kv_map)))"

definition Finite_Lst_map_Ran where
  "Finite_Lst_map_Ran s cl \<longleftrightarrow> finite (range (lst_map (cls s cl)))"

lemma lst_map_min_monotonic:
  assumes "state_trans s e s'"
    and "reach tps_s s"
  shows "Min (range (lst_map (cls s cl))) \<le> Min (range (lst_map (cls s' cl)))" oops

definition Gst_le_Min_Lst_map where
  "Gst_le_Min_Lst_map s cl \<longleftrightarrow> (gst (cls s cl) \<le> Min (range (lst_map (cls s cl))))"

lemma gst_monotonic:
  assumes "state_trans s e s'"
    and "reach tps_s s"
  shows "gst (cls s' cl) \<ge> gst (cls s cl)" oops

definition Gst_le_Lst_map where
  "Gst_le_Lst_map s cl k \<longleftrightarrow> (gst (cls s cl) \<le> lst_map (cls s cl) k)"

definition Pend_Wt_Inv where
  "Pend_Wt_Inv s k \<longleftrightarrow> (\<forall>prep_t. prep_t \<in> pending_wtxns_ts (svr_state (svrs s k))
    \<longleftrightarrow> (\<exists>t v. svr_state (svrs s k) t = Prep prep_t v))"

definition Lst_Lt_Pts where
  "Lst_Lt_Pts s k \<longleftrightarrow> (\<forall>t prep_t v. svr_state (svrs s k) t = Prep prep_t v \<longrightarrow> svr_lst (svrs s k) \<le> prep_t)"

definition Finite_Wtxns_Dom where
  "Finite_Wtxns_Dom s k \<longleftrightarrow> finite (wtxns_dom (svr_state (svrs s k)))"

definition Finite_Wtxns_rsran where
  "Finite_Wtxns_rsran s k \<longleftrightarrow> finite (wtxns_rsran (svr_state (svrs s k)))"


subsection \<open>Invariants about kvs, global ts and init version v0\<close>

definition T0_in_CO where
  "T0_in_CO s k \<longleftrightarrow> T0 \<in> set (cts_order s k)"

definition T0_First_in_CO where
  "T0_First_in_CO s k \<longleftrightarrow> cts_order s k ! 0 = T0"

definition KvsOfS_Not_Emp where
  "KvsOfS_Not_Emp s \<longleftrightarrow> (\<forall>k. kvs_of_s s k \<noteq> [])"

definition Init_Ver_Inv where
  "Init_Ver_Inv s k \<longleftrightarrow> (\<exists>rs. svr_state (svrs s k) T0 = Commit 0 0 0 undefined rs)"


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
    (\<forall>cl k cts kv_map. cl_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map}
        \<and> kv_map k = None \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver)"

definition Cl_Prep_Inv where
  "Cl_Prep_Inv s \<longleftrightarrow> (\<forall>cl k kvm. \<exists>prep_t v. cl_state (cls s cl) = WtxnPrep kvm
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) \<in> {No_Ver, Prep prep_t v}) \<and>
    (k \<notin> dom kvm \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver))"

definition Cl_Commit_Inv where
  "Cl_Commit_Inv s \<longleftrightarrow> (\<forall>cl k cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<longrightarrow>
    (\<forall>v. kv_map k = Some v \<longrightarrow>
      (\<exists>prep_t sts lst rs. svr_state (svrs s k) (get_wtxn s cl) \<in> {Prep prep_t v, Commit cts sts lst v rs})) \<and>
    (kv_map k = None \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver))"

\<comment> \<open>Next 2 invariants: svr_state \<longrightarrow> cl_state\<close>
definition Prep_is_Curr_wt where
  "Prep_is_Curr_wt s k \<longleftrightarrow> (\<forall>t. is_prepared (svr_state (svrs s k) t) \<longrightarrow> is_curr_wt s t)"

definition Svr_Prep_Inv where
  "Svr_Prep_Inv s \<longleftrightarrow> (\<forall>k t ts v. svr_state (svrs s k) t = Prep ts v \<longrightarrow>
    (\<exists>cts kv_map.
      cl_state (cls s (get_cl_w t)) \<in> {WtxnPrep  kv_map, WtxnCommit cts kv_map} \<and>
      k \<in> dom kv_map))"

definition Svr_Commit_Inv where
  "Svr_Commit_Inv s \<longleftrightarrow> (\<forall>k t cts sts lst v rs. 
    svr_state (svrs s k) t = Commit cts sts lst v rs \<and> is_curr_wt s t \<longrightarrow> 
      (\<exists>kv_map. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map \<and> k \<in> dom kv_map))"

\<comment> \<open>Values of svr_state and rtxn_rts for past transaction ids\<close>
definition PTid_Inv where
  "PTid_Inv s cl \<longleftrightarrow> (\<forall>k. \<forall>n < cl_sn (cls s cl).
   (svr_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver) \<or>
   (rtxn_rts s (Tn_cl n cl) = None \<and> 
    (\<exists>cts sts lst v rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts sts lst v rs)))"

lemma other_sn_idle:  
  assumes "FTid_Wtxn_Inv s cl" and "PTid_Inv s cl"
    and "get_cl t = cl" and "get_sn t \<noteq> cl_sn (cls s cl)"
  shows "\<And>k. \<exists>cts sts lst v rs. svr_state (svrs s k) (Tn t) \<in> {No_Ver, Commit cts sts lst v rs}" oops

definition Rtxn_Wtxn_No_Ver where
  "Rtxn_Wtxn_No_Ver s cl \<longleftrightarrow>
    (\<forall>n ts. rtxn_rts s (Tn_cl n cl) = Some ts \<longrightarrow> (\<forall>k. svr_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver))"

definition Wtxn_Rtxn_None where
  "Wtxn_Rtxn_None s k \<longleftrightarrow>
    (\<forall>cl n ts v cts sts lst rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) \<in> {Prep ts v, Commit cts sts lst v rs}
       \<longrightarrow> rtxn_rts s (Tn_cl n cl) = None)"

definition Wtxn_Cts_T0 where
  "Wtxn_Cts_T0 s k \<longleftrightarrow> wtxn_cts s T0 = Some 0"

definition Wtxn_Cts_Tn_None where
  "Wtxn_Cts_Tn_None s \<longleftrightarrow> (\<forall>cts kv_map keys n cl. 
    (cl_state (cls s cl) \<in> {Idle, WtxnPrep kv_map} \<and> n \<ge> cl_sn (cls s cl)) \<or>
    (cl_state (cls s cl) \<in> {RtxnInProg keys kv_map, WtxnCommit cts kv_map} \<and> n > cl_sn (cls s cl))
     \<longrightarrow> wtxn_cts s (Tn (Tn_cl n cl)) = None)"

definition Wtxn_Cts_None where
  "Wtxn_Cts_None s \<longleftrightarrow> (\<forall>cts kv_map keys t. t \<noteq> T0 \<and> (
    (cl_state (cls s (get_cl_w t)) \<in> {Idle, WtxnPrep kv_map} \<and>
        get_sn_w t \<ge> cl_sn (cls s (get_cl_w t))) \<or>
    (cl_state (cls s (get_cl_w t)) \<in> {RtxnInProg keys kv_map, WtxnCommit cts kv_map} \<and>
        get_sn_w t > cl_sn (cls s (get_cl_w t))))
     \<longrightarrow> wtxn_cts s t = None)"

definition WtxnCommit_Wtxn_Cts where
  "WtxnCommit_Wtxn_Cts s cl \<longleftrightarrow> (\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map
    \<longrightarrow> wtxn_cts s (get_wtxn s cl) = Some cts)"

definition Wtxn_State_Cts where
  "Wtxn_State_Cts s k \<longleftrightarrow> (\<forall>t cts sts lst v rs ts kv_map.
    svr_state (svrs s k) t = Commit cts sts lst v rs \<or>
   (svr_state (svrs s k) t = Prep ts v \<and> cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map)
      \<longrightarrow> wtxn_cts s t = Some cts)"

definition FTid_notin_rs where
  "FTid_notin_rs s cl \<longleftrightarrow> (\<forall>k n t cts sts lst v rs. n > cl_sn (cls s cl) \<and>
    svr_state (svrs s k) t = Commit cts sts lst v rs \<longrightarrow> rs (Tn_cl n cl) = None)"

definition FTid_not_wr where
  "FTid_not_wr s cl \<longleftrightarrow> (\<forall>n k. n > cl_sn (cls s cl) \<longrightarrow> Tn (Tn_cl n cl) \<notin> wtxns_dom (svr_state (svrs s k)))"

definition Fresh_wr_notin_rs where
  "Fresh_wr_notin_rs s cl \<longleftrightarrow> (\<forall>k t cts kv_map cts' sts' lst' v' rs'.
    cl_state (cls s cl) \<in> {Idle, WtxnPrep kv_map, WtxnCommit cts kv_map} \<and>
    svr_state (svrs s k) t = Commit cts' sts' lst' v' rs' \<longrightarrow> rs' (get_txn s cl) = None)"

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
  "Gst_Lt_Cts s cl \<longleftrightarrow> (\<forall>k cts sts lst v rs. 
      svr_state (svrs s k) (get_wtxn s cl) = Commit cts sts lst v rs \<longrightarrow> gst (cls s cl) < cts)" (*RInvoke & CommitW*)

definition Gst_Lt_Cl_Cts where
  "Gst_Lt_Cl_Cts s cl \<longleftrightarrow> (\<forall>cl' cts kv_map. cl_state (cls s cl') = WtxnCommit cts kv_map
    \<longrightarrow> gst (cls s cl) < cts)" (*RInvoke & CommitW*)


subsection \<open>Commit Order Invariants\<close>

abbreviation is_committed_in_kvs where
  "is_committed_in_kvs s k t \<equiv> 
    is_committed (svr_state (svrs s k) t)  \<or> 
    (is_prepared (svr_state (svrs s k) t) \<and> \<comment> \<open>is_curr_wt s t \<and>\<close>
     (\<exists>cts kv_map. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map))"

definition CO_Tid where
  "CO_Tid s cl \<longleftrightarrow> (case cl_state (cls s cl) of
    WtxnCommit cts kv_map \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow> n \<le> cl_sn (cls s cl))
  | _ \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow> n < cl_sn (cls s cl)))"

definition CO_Distinct where
  "CO_Distinct s k \<longleftrightarrow> distinct (cts_order s k)"

definition CO_Tn_is_Cmt_Abs where
  "CO_Tn_is_Cmt_Abs s k \<longleftrightarrow> (\<forall>n cl. Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow>
    (\<exists>cts sts lst v rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts sts lst v rs) \<or> 
    ((\<exists>ts v. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Prep ts v) \<and> 
     (\<exists>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<and> 
      cl_sn (cls s cl) = n \<and> k \<in> dom kv_map)))"

definition CO_is_Cmt_Abs where
  "CO_is_Cmt_Abs s k \<longleftrightarrow> (\<forall>t. t \<in> set (cts_order s k) \<longrightarrow>
    (\<exists>cts sts lst v rs. svr_state (svrs s k) t = Commit cts sts lst v rs) \<or> 
    ((\<exists>ts v. svr_state (svrs s k) t = Prep ts v) \<and> 
     (\<exists>cts kv_map. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map \<and> k \<in> dom kv_map)))"

definition CO_not_No_Ver where
  "CO_not_No_Ver s k \<longleftrightarrow> (\<forall>t \<in> set (cts_order s k). svr_state (svrs s k) t \<noteq> No_Ver)"

definition CO_has_Cts where
  "CO_has_Cts s k \<longleftrightarrow> (\<forall>t \<in> set (cts_order s k). \<exists>cts. wtxn_cts s t = Some cts)"

definition Committed_Abs_Tn_in_CO where
  "Committed_Abs_Tn_in_CO s k \<longleftrightarrow> (\<forall>n cl.
    (\<exists>cts sts lst v rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts sts lst v rs) \<or> 
    ((\<exists>ts v. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Prep ts v) \<and> 
     (\<exists>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<and> cl_sn (cls s cl) = n)) \<longrightarrow>
    Tn (Tn_cl n cl) \<in> set (cts_order s k))"

definition Committed_Abs_in_CO where
  "Committed_Abs_in_CO s k \<longleftrightarrow> (\<forall>t.
    (\<exists>cts sts lst v rs. svr_state (svrs s k) t = Commit cts sts lst v rs) \<or> 
    ((\<exists>ts v. svr_state (svrs s k) t = Prep ts v) \<and>
     (\<exists>cts kv_map. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map)) \<longrightarrow>
    t \<in> set (cts_order s k))"

definition CO_Sorted where
  "CO_Sorted s k \<longleftrightarrow> (\<forall>i < length (cts_order s k). \<forall>i' < length (cts_order s k).
    i < i' \<longrightarrow> the (wtxn_cts s (cts_order s k ! i)) \<le> the (wtxn_cts s (cts_order s k ! i')))" (*WCommit*)


subsection \<open>Simulation relation lemmas\<close>

lemma kvs_of_s_init:
  "kvs_of_s (state_init) = (\<lambda>k. [\<lparr>v_value = undefined, v_writer = T0, v_readerset = {}\<rparr>])" oops

abbreviation not_committing_ev where
  "not_committing_ev e \<equiv> \<forall>cl kv_map cts sn u'' clk. e \<noteq> RDone cl kv_map sn u'' clk \<and>
    e \<noteq> WCommit cl kv_map cts sn u'' clk"   

lemma kvs_of_s_inv:
  assumes "state_trans s e s'"
    and "reach tps_s s"
    and "not_committing_ev e"
  shows "kvs_of_s s' = kvs_of_s s" oops


subsection \<open>Transaction ID Freshness\<close>

definition Sqn_Inv_nc where
  "Sqn_Inv_nc s cl \<longleftrightarrow> (\<forall>cts kv_map. cl_state (cls s cl) \<noteq> WtxnCommit cts kv_map
     \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m < cl_sn (cls s cl)))"

definition Sqn_Inv_c where
  "Sqn_Inv_c s cl \<longleftrightarrow> (\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map
     \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m \<le> cl_sn (cls s cl)))"

lemma t_is_fresh:
  assumes "Sqn_Inv_c s cl" and "Sqn_Inv_nc s cl"
    and "cl_state (cls s cl) \<in> {WtxnPrep kv_map, RtxnInProg keys kv_map}"
  shows "get_txn s cl \<in> next_txids (kvs_of_s s) cl" oops

subsection \<open>committed At functions\<close>

lemma at_is_committed:
  assumes "Init_Ver_Inv s k"
  shows "is_committed ((svr_state (svrs s k)) (at (svr_state (svrs s k)) rts))" oops

lemma newest_own_write_is_committed:
  assumes "Finite_Wtxns_Dom s k"and "newest_own_write (svr_state (svrs s k)) ts cl = Some t"
  shows "is_committed (svr_state (svrs s k) t)" oops

lemma read_at_is_committed:
  assumes "Init_Ver_Inv s k" and "Finite_Wtxns_Dom s k"
  shows "is_committed (svr_state (svrs s k) (read_at (svr_state (svrs s k)) rts cl))" oops


subsection \<open>Kvt_map values of read_done\<close>
definition Rtxn_IdleK_notin_rs where
  "Rtxn_IdleK_notin_rs s cl \<longleftrightarrow> (\<forall>k keys kv_map t cts sts lst v rs.
    cl_state (cls s cl) = RtxnInProg keys kv_map \<and> k \<notin> keys \<and>
    svr_state (svrs s k) t = Commit cts sts lst v rs \<longrightarrow> rs (get_txn s cl) = None)"

definition Rtxn_RegK_Kvtm_Cmt_in_rs where
  "Rtxn_RegK_Kvtm_Cmt_in_rs s cl \<longleftrightarrow> (\<forall>k keys kv_map v.
    cl_state (cls s cl) = RtxnInProg keys kv_map \<and> kv_map k = Some v \<longrightarrow>
    (\<exists>t cts sts lst rs rts rlst. svr_state (svrs s k) t = Commit cts sts lst v rs
      \<and> rs (get_txn s cl) = Some (rts, rlst)))"


subsection \<open>Timestamp relations\<close>

definition Disjoint_RW where
  "Disjoint_RW s \<longleftrightarrow> ((\<Union>k. wtxns_dom (svr_state (svrs s k))) \<inter> Tn ` (\<Union>k. wtxns_rsran (svr_state (svrs s k))) = {})" (* not proven *)

(*definition Disjoint_RW' where
  "Disjoint_RW' s \<longleftrightarrow> (kvs_writers (kvs_of_s s) \<inter> Tn ` kvs_readers (kvs_of_s s) = {})" (* not proven *)*)

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
  visTx' K' (insert t u) = insert t (visTx' K u)" oops

lemma insert_wr_t_closed':
  assumes "closed' K u r"
    and "closed_general {t} (r\<inverse>) (visTx' K u \<union> read_only_Txs K)"
    and "read_only_Txs K' = read_only_Txs K"
    and "kvs_writers K' = insert t (kvs_writers K)"
  shows "closed' K' (insert t u) r" oops

\<comment> \<open>insert (k, t) in version's deps - used in get_ctx\<close>
lemma visTx'_observes_t:
  "t \<in> kvs_writers K \<Longrightarrow> visTx' K (insert t deps) = insert t (visTx' K deps)" oops

lemma insert_kt_to_deps_closed':
  assumes "closed' K deps r"
    and "t \<in> kvs_writers K"
    and "closed_general {t} (r\<inverse>) (visTx' K deps \<union> read_only_Txs K)"
  shows "closed' K (insert t deps) r" oops


\<comment> \<open>concrete read_done closedness\<close>

\<comment> \<open>premises\<close>
  
lemma get_ctx_closed:
  assumes "\<And>k. k \<in> dom kv_map \<Longrightarrow>
      let t = read_at (svr_state (svrs s k)) (gst (cls s cl)) cl in
      closed' K (insert t (get_dep_set (svr_state (svrs s k) t))) r"
    and "cl_state (cls s cl) = RtxnInProg (dom kv_map) kv_map"
    and "Rtxn_RegK_Kvtm_Cmt_in_rs s cl"
    and "Finite_Dom_Kv_map_rd s cl"
  shows "closed' K (get_ctx s cl (dom kv_map)) r" oops

lemma v_writer_kvs_of_s:
  assumes "\<forall>k. CO_not_No_Ver s k"
  shows "v_writer ` (\<lambda>t. case svr_state (svrs s k) t of
      Prep ts v \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = {}\<rparr>
    | Commit cts sts lst v rs \<Rightarrow> \<lparr>v_value = v, v_writer = t,
        v_readerset = {t. \<exists>rts rlst. rs t = Some (rts, rlst) \<and> get_sn t < cl_sn (cls s (get_cl t))}\<rparr>) ` set (cts_order s k) =
   {t \<in> set (cts_order s k). \<exists>ts v cts sts lst rs.
        svr_state (svrs s k) t \<in> {Prep ts v, Commit cts sts lst v rs}}" oops

lemma v_readerset_kvs_of_s_k:
  assumes "\<forall>k. CO_not_No_Ver s k"
    and "t_wr \<in> set (cts_order s k)"
  shows "v_readerset (case svr_state (svrs s k) t_wr of
      Prep ts v \<Rightarrow> \<lparr>v_value = v, v_writer = t_wr, v_readerset = {}\<rparr>
    | Commit cts sts lst v rs \<Rightarrow> \<lparr>v_value = v, v_writer = t_wr,
        v_readerset = {t. \<exists>rts rlst. rs t = Some (rts, rlst) \<and> get_sn t < cl_sn (cls s (get_cl t))}\<rparr>) = 
   {t. \<exists>cts sts lst v rs rts rlst. svr_state (svrs s k) t_wr = Commit cts sts lst v rs \<and>
      rs t = Some (rts, rlst) \<and> get_sn t < cl_sn (cls s (get_cl t))}" oops

lemma v_readerset_kvs_of_s:
  assumes "\<forall>k. CO_not_No_Ver s k"
  shows "(\<Union>k. \<Union>t_wr\<in>set (cts_order s k). v_readerset (case svr_state (svrs s k) t_wr of
      Prep ts v \<Rightarrow> \<lparr>v_value = v, v_writer = t_wr, v_readerset = {}\<rparr>
    | Commit cts sts lst v rs \<Rightarrow> \<lparr>v_value = v, v_writer = t_wr,
        v_readerset = {t. \<exists>rts rlst. rs t = Some (rts, rlst) \<and> get_sn t < cl_sn (cls s (get_cl t))}\<rparr>)) = 
   {t. \<exists>k. \<exists>t_wr \<in> set (cts_order s k).
      \<exists>cts sts lst v rs rts rlst. svr_state (svrs s k) t_wr = Commit cts sts lst v rs \<and>
      rs t = Some (rts, rlst) \<and> get_sn t < cl_sn (cls s (get_cl t))}" oops

lemma read_done_same_writers:
  assumes "read_done cl kv_map sn u'' clk s s'"
    and "\<forall>k. CO_not_No_Ver s k"
    and "\<forall>k. CO_not_No_Ver s' k"
  shows "kvs_writers (kvs_of_s s') = kvs_writers (kvs_of_s s)" oops

lemma read_done_new_read:
  assumes "read_done cl kv_map sn u'' clk s s'"
    and "\<forall>k. CO_not_No_Ver s k"
    and "\<forall>k. CO_not_No_Ver s' k"
    and "\<forall>k. Committed_Abs_in_CO s k"
    and "\<forall>k. T0_in_CO s k"
    and "Finite_Dom_Kv_map_rd s cl"
    and "Rtxn_RegK_Kvtm_Cmt_in_rs s cl"
    and "Rtxn_RegK_Kvtm_Cmt_in_rs s cl"
    and "Tn (get_txn s cl) \<notin> kvs_writers (kvs_of_s s)"
  shows "read_only_Txs (kvs_of_s s') = insert (Tn (get_txn s cl)) (read_only_Txs (kvs_of_s s))" oops

lemma read_done_WR_onK:
  assumes "read_done cl kv_map sn u'' clk s s'"
  shows "R_onK WR (kvs_of_s s') = (\<Union>y\<in>snd ` ran kv_map. {(y, Tn (get_txn s cl))}) \<union> R_onK WR (kvs_of_s s)" oops
(* not proven *)

lemma read_done_extend_rel:
  assumes "read_done cl kv_map sn u'' clk s s'"
  shows "R_CC (kvs_of_s s') = (\<Union>y\<in>snd ` ran kv_map. {(y, Tn (get_txn s cl))}) \<union> R_CC (kvs_of_s s)" oops

\<comment> \<open>read_done closedness (canCommit)\<close>
lemma read_done_ctx_closed:
  assumes "closed' (kvs_of_s s) (cl_ctx (cls s cl)) (R_CC (kvs_of_s s))"
    and "closed' (kvs_of_s s) (get_ctx s cl keys) (R_CC (kvs_of_s s))"
    and "kvs_writers (kvs_of_s s') = kvs_writers (kvs_of_s s)"
    and "read_only_Txs (kvs_of_s s') = insert (Tn (get_txn s cl)) (read_only_Txs (kvs_of_s s))"
    and "Tn (get_txn s cl) \<notin> ((R_CC (kvs_of_s s))\<inverse>)\<^sup>* ``
      (visTx' (kvs_of_s s) (cl_ctx (cls s cl) \<union> get_ctx s cl keys))"
    and "R_CC (kvs_of_s s') = (\<Union>y\<in>snd ` ran kv_map. {(y, Tn (get_txn s cl))}) \<union> R_CC (kvs_of_s s)"
    and "Finite_t_Ran_Kvt_map s cl"
    and "cl_state (cls s cl) = RtxnInProg keys kv_map"
  shows "closed' (kvs_of_s s') (cl_ctx (cls s cl) \<union> get_ctx s cl keys) (R_CC (kvs_of_s s'))" oops

\<comment> \<open>write_commit closedness (canCommit)\<close>
lemma write_commit_WR_onK:
  assumes "write_commit cl kv_map commit_t sn u'' clk s s'"
  shows "R_onK WR (kvs_of_s s') = R_onK WR (kvs_of_s s)" oops (* not proven *)

lemma write_commit_same_rel:
  assumes "write_commit cl kv_map commit_t sn u'' clk s s'"
  shows "R_CC (kvs_of_s s') = R_CC (kvs_of_s s)" oops

lemma write_commit_ctx_closed:
  assumes "write_commit cl kv_map commit_t sn u'' clk s s'"
    and "closed' (kvs_of_s s) (cl_ctx (cls s cl)) (R_CC (kvs_of_s s))"
    and "closed_general {get_wtxn s cl} ((R_CC (kvs_of_s s))\<inverse>)
          (visTx' (kvs_of_s s) (cl_ctx (cls s cl)) \<union> read_only_Txs (kvs_of_s s))"
    and "read_only_Txs (kvs_of_s s') = read_only_Txs (kvs_of_s s)"
    and "kvs_writers (kvs_of_s s') = insert (get_wtxn s cl) (kvs_writers (kvs_of_s s))"
  shows "closed' (kvs_of_s s') (insert (get_wtxn s cl) (cl_ctx (cls s cl))) (R_CC (kvs_of_s s'))"
  oops (* not proven *)


subsection \<open>CanCommit\<close>

lemma the_T0: "(THE i. i = 0 \<and> [T0] ! i = T0) = 0" oops

lemmas canCommit_defs = ET_CC.canCommit_def R_CC_def R_onK_def

(*
lemma visTx_visTx': "\<comment> \<open>\<forall>k t. (k, t) \<in> u \<longrightarrow> t \<in> set (cts_order s k) \<Longrightarrow>\<close>
  visTx (kvs_of_s s) (view_of (cts_order s) u) = visTx' (kvs_of_s s) u" oops (* not proven *)

lemma closed_closed': "\<comment> \<open>\<forall>k t. (k, t) \<in> u \<longrightarrow> t \<in> set (cts_order s k) \<Longrightarrow>\<close>
  closed (kvs_of_s s) (view_of (cts_order s) u) r = closed' (kvs_of_s s) u r" oops
*)

lemma visTx'_cl_ctx_subset_writers:
  "visTx' (kvs_of_s s) (cl_ctx (cls s cl)) \<subseteq> kvs_writers (kvs_of_s s)" oops

lemma visTx'_wtxn_deps_subset_writers: 
  "wtxn_deps s t = deps \<Longrightarrow> visTx' (kvs_of_s s) deps \<subseteq> kvs_writers (kvs_of_s s)" oops

lemma "kvs_writers (kvs_of_s s) \<subseteq> (\<Union>k. wtxns_dom (svr_state (svrs s k)))"(* not proven *)
  oops

lemma "kvs_readers (kvs_of_s s) \<subseteq> (\<Union>k. wtxns_rsran (svr_state (svrs s k)))"(* not proven *)
  oops

definition RO_le_gst :: "'v global_conf \<Rightarrow> cl_id \<Rightarrow> txid set" where
  "RO_le_gst s cl \<equiv> {t \<in> read_only_Txs (kvs_of_s s). \<exists>t'. t = Tn t' \<and> the (rtxn_rts s t') \<le> gst (cls s cl)}"

definition RO_WO_Inv where
  "RO_WO_Inv s \<longleftrightarrow> (\<Union>k. wtxns_dom (svr_state (svrs s k))) \<inter> Tn ` (\<Union>k. wtxns_rsran (svr_state (svrs s k))) = {}" (* server events*)


subsection \<open>View Invariants\<close>

definition View_Init where
  "View_Init s cl k \<longleftrightarrow> (T0 \<in> get_view s cl k)"

definition Get_View_Committed where
  "Get_View_Committed s cl k \<longleftrightarrow> (\<forall>t. t \<in> get_view s cl k  \<longrightarrow>
    (is_committed (svr_state (svrs s k) t) \<or> 
    (\<exists>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<and> k \<in> dom kv_map \<and> t = get_wtxn s cl)))" (* not proven *)

(* Closedness inv
definition Deps_Closed where
  "Deps_Closed s cl \<longleftrightarrow> (closed' (kvs_of_s s) (cl_ctx (cls s cl)) (R_CC (kvs_of_s s)) \<and> 
    (\<forall>k t cts sts lst v rs kv_map deps. svr_state (svrs s k) t = Commit cts sts lst v rs \<or>
      cl_state (cls s cl) = WtxnCommit cts kv_map \<longrightarrow>
      closed' (kvs_of_s s) deps (R_CC (kvs_of_s s))))" (* not proven *)
*)

subsection \<open>View Shift\<close>

definition Cl_WtxnCommit_Get_View where
  "Cl_WtxnCommit_Get_View s cl \<longleftrightarrow>
    (\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<longrightarrow>
      (\<forall>k \<in> dom kv_map. get_wtxn s cl \<in> get_view s cl k))"

lemma read_commit_added_txid:
  assumes "read_done cl kv_map sn u clk s s'"
    and "Tn (Tn_cl sn' cl) \<in> (kvs_txids (kvs_of_s s') - kvs_txids (kvs_of_s s))"
  shows "sn' = sn" oops (* not proven *)

subsection \<open>Fp Property\<close>

\<comment> \<open>Fingerprint content invariant and Lemmas for proving the fp_property\<close>

definition RegR_Fp_Inv where
  "RegR_Fp_Inv s k \<longleftrightarrow> (\<forall>t keys kv_map cts sts lst v rs.
    cl_state (cls s (get_cl t)) = RtxnInProg keys kv_map \<and> k \<in> keys \<and> kv_map k = None \<and>
    svr_state (svrs s k) (read_at (svr_state (svrs s k)) (gst (cls s (get_cl t))) (get_cl t))
       = Commit cts sts lst v rs \<longrightarrow>
    v = v_value ((kvs_of_s s k) !
      Max (view_of (cts_order s) (get_view s (get_cl t)) k)))"
(* not proven *)


definition Rtxn_Fp_Inv where
  "Rtxn_Fp_Inv s cl \<longleftrightarrow> (\<forall>k keys kv_map v.
    cl_state (cls s cl) = RtxnInProg keys kv_map \<and> kv_map k = Some v \<longrightarrow>
     v = v_value ((kvs_of_s s k) !
        Max (view_of (cts_order s) (get_view s cl) k)))"
(* not proven *)

subsection\<open>Proofs in progress\<close>


\<comment> \<open>lemmas about lists\<close>
lemma distinct_prefix: "\<lbrakk> distinct xs; prefix xs' xs \<rbrakk> \<Longrightarrow> distinct xs'" oops

lemma nth_eq_prefix: "\<lbrakk> i < length xs; prefix xs ys \<rbrakk> \<Longrightarrow> xs ! i = ys ! i" oops

lemma nth_distinct_injective:
  "\<lbrakk> xs ! i = xs ! j; i < length xs; j < length xs; distinct xs \<rbrakk> \<Longrightarrow> i = j" oops


\<comment> \<open>lemma about THE\<close>
lemma the_the_equality:
  "\<lbrakk> P a; \<And>y. P y \<Longrightarrow> y = a; \<And>x. Q x \<longleftrightarrow> P x \<rbrakk> \<Longrightarrow> (THE x. P x) = (THE x. Q x)" oops


\<comment> \<open>lemmas about views\<close>
lemma views_of_s_cls_update:  \<comment> \<open>STILL NEEDED?\<close>
  "views_of_s (gs\<lparr>cls := (cls gs)(cl := new_cls), wtxn_cts := X, cts_order := new_cmtord \<rparr>) cl' = 
   view_of new_cmtord (cl_ctx (if cl' = cl then new_cls else (cls gs cl')))" oops


lemma view_of_deps_mono:
  assumes "\<forall>k. u k \<subseteq> u' k"
  shows "view_of cord u \<sqsubseteq> view_of cord u'" oops

lemma view_of_mono: 
  assumes "\<forall>k. u k \<subseteq> u' k" and "\<And>k. prefix (cord k) (cord' k)" "\<And>k. distinct (cord' k)" 
  shows "view_of cord u \<sqsubseteq> view_of cord' u'" oops

(*
lemma view_of_ext_corder_cl_ctx:  
  assumes "\<And>k. distinct (ext_corder (get_wtxn gs cl) kv_map (cts_order gs) k)"
  shows "view_of (cts_order gs) (cl_ctx (cls gs cl)) \<sqsubseteq> 
         view_of (ext_corder (get_wtxn gs cl) kv_map (cts_order gs)) 
                 (insert (get_wtxn gs cl) (cl_ctx (cls gs cl)))" oops
*)

\<comment> \<open>more lemmas about view updates\<close>
(*lemma view_of_update:
  assumes 
    "i = length (cord k)"  
    "cord' k = cord k @ [t]"
    "t \<notin> set (cord k)"
    "t \<in> deps"
  shows "i \<in> view_of cord' deps k" oops*)

\<comment> \<open>lemmas related to commit order (CO)\<close>

lemma length_cts_order: "length (cts_order gs k) = length (kvs_of_s gs k)" oops

lemma v_writer_txn_to_vers_inverse_on_CO:
  assumes "CO_not_No_Ver gs k" "t \<in> set (cts_order gs k)"
  shows "v_writer (txn_to_vers gs k t) = t" oops


lemma set_cts_order_incl_kvs_writers:
  assumes "CO_not_No_Ver gs k"
  shows "set (cts_order gs k) \<subseteq> kvs_writers (kvs_of_s gs)" oops

lemma set_cts_order_incl_kvs_tids:
  assumes "CO_not_No_Ver gs k"
  shows "set (cts_order gs k) \<subseteq> kvs_txids (kvs_of_s gs)" oops


subsubsection \<open>Write commit guard properties\<close>

lemma write_commit_txn_to_vers_get_wtxn:
  assumes "write_commit cl kv_map cts sn u'' clk gs gs'" 
  and "kv_map k = Some v" 
  shows "txn_to_vers gs k (get_wtxn gs cl) = new_vers (Tn (Tn_cl sn cl)) v" oops

lemma write_commit_seqn:    \<comment> \<open> NOT USED? \<close>
  assumes "write_commit cl kv_map cts sn u'' clk gs gs'" 
  shows "sn = cl_sn (cls gs cl)" oops


subsubsection \<open>Write commit update properties\<close>

lemma write_commit_txn_to_vers_pres:
  assumes "write_commit cl kv_map cts sn u'' clk gs gs'"
  shows "txn_to_vers gs' k = txn_to_vers gs k" oops


lemma write_commit_cts_order_update:
  assumes "write_commit cl kv_map cts sn u'' clk gs gs'"
  shows "cts_order gs' k = 
         (if kv_map k = None then cts_order gs k else cts_order gs k @ [get_wtxn gs cl])" oops


lemma write_commit_kvs_of_s:
  assumes "write_commit cl kv_map commit_t sn u'' clk s s'"
  shows "kvs_of_s s' = update_kv (Tn_cl sn cl)
                          (write_only_fp kv_map)
                          (view_of (cts_order s) (cl_ctx (cls s cl)))
                          (kvs_of_s s)" oops

(*lemma write_commit_views_of_s:
  assumes "write_commit cl kv_map commit_t sn u'' s s'"
  shows "views_of_s s' = 
         (\<lambda>cl'. view_of (ext_corder (get_wtxn s cl) kv_map (cts_order s))    
                        (if cl' = cl then insert (get_wtxn s cl) (cl_ctx (cls s cl)) 
                         else cl_ctx (cls s cl')))" oops*)

lemma full_view_elem: "i \<in> full_view vl \<longleftrightarrow> i < length vl" oops

lemma length_update_kv_bound:
  "i < length (update_kv t F u K k) \<longleftrightarrow> i < length (K k) \<or> W \<in> dom (F k) \<and> i = length (K k)" oops


subsubsection \<open>View Wellformedness\<close>

definition FTid_notin_Get_View where
  "FTid_notin_Get_View s cl \<longleftrightarrow> (\<forall>n cl' k. (n > cl_sn (cls s cl) \<longrightarrow> Tn (Tn_cl n cl) \<notin> get_view s cl' k) \<and>
    (cl' \<noteq> cl \<longrightarrow> get_wtxn s cl \<notin> get_view s cl' k))"

lemma views_of_s_inv:
  assumes "state_trans s e s'"
    and "reach tps_s s"
    and "\<not>commit_ev e"
  shows "views_of_s s' cl = views_of_s s cl" oops (* not proven *)

lemma read_commit_views_of_s_other_cl_inv:
  assumes "read_done cl kv_map sn u clk s s'"
    and "reach tps_s s"
    and "cl' \<noteq> cl"
  shows "views_of_s s' cl' = views_of_s s cl'" oops (* not proven *)

lemma write_commit_views_of_s_other_cl_inv:
  assumes "write_commit_s cl kv_map cts sn u clk s s'"
    and "reach tps_s s"
    and "cl' \<noteq> cl"
  shows "views_of_s s' cl' = views_of_s s cl'" oops (* not proven *)

lemma reach_kvs_expands [simp]:
  assumes "state_trans s e s'"
    and "reach tps_s s"
  shows "kvs_of_s s \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s kvs_of_s s'" oops

definition Views_of_s_Wellformed where
  "Views_of_s_Wellformed s cl \<longleftrightarrow> (view_wellformed (kvs_of_s s) (views_of_s s cl))" (* commit events *)


subsection \<open>Refinement Proof\<close>
definition invariant_list where
  "invariant_list s \<equiv> (\<forall>cl k. Sqn_Inv_c s cl \<and> Sqn_Inv_nc s cl
    \<and> Views_of_s_Wellformed s cl \<and> Rtxn_Fp_Inv s cl \<and> CO_Distinct s k
    \<and> T0_in_CO s k \<and> T0_First_in_CO s k \<and> View_Init s cl k \<and> FTid_notin_Get_View s cl)"

end
