section \<open>Eiger Port Plus Protocol Satisfying CCv (Causal+) - Proofs and lemmas\<close>

theory "EP+_Invariants"
  imports "EP+_Sorted"
begin

subsection \<open>wtxns lemmas\<close>
subsubsection \<open>wtxns_dom lemmas\<close>
subsubsection \<open>wtxns_vran lemmas\<close>
subsubsection \<open>wtxns_rsran lemmas\<close>

subsection \<open>Helper functions lemmas\<close>

subsection \<open>(New) helper functions lemmas\<close>

\<comment> \<open>index_of\<close>
lemma index_of_nth:
  "distinct xs \<Longrightarrow> i' < length xs \<Longrightarrow> index_of xs (xs ! i') = i'" oops

lemma index_of_append:
  assumes 
    "distinct (xs @ [t'])"
    "t \<in> set xs"
  shows "index_of (xs @ [t']) t = index_of xs t" oops

lemma index_of_neq:
  assumes "distinct xs"
    and "a \<noteq> b"
    and "a \<in> set xs"
    and "b \<in> set xs"
  shows "index_of xs a \<noteq> index_of xs b" oops

lemma the_the_equality:
  "\<lbrakk> P a; \<And>y. P y \<Longrightarrow> y = a; \<And>x. Q x \<longleftrightarrow> P x \<rbrakk> \<Longrightarrow> (THE x. P x) = (THE x. Q x)" oops

\<comment> \<open>lists\<close>
lemma distinct_prefix: "\<lbrakk> distinct xs; prefix xs' xs \<rbrakk> \<Longrightarrow> distinct xs'" oops

lemma nth_eq_prefix: "\<lbrakk> i < length xs; prefix xs ys \<rbrakk> \<Longrightarrow> xs ! i = ys ! i" oops

lemma nth_distinct_injective:
  "\<lbrakk> xs ! i = xs ! j; i < length xs; j < length xs; distinct xs \<rbrakk> \<Longrightarrow> i = j" oops

\<comment> \<open>view_of\<close>
lemma view_of_prefix:
  assumes "\<And>k. prefix (corder k) (corder' k)"
    and "\<And>k. distinct (corder' k)"
    and "\<And>k. (set (corder' k) - set (corder k)) \<inter> u k = {}"
  shows "view_of corder u = view_of corder' u" oops

lemma view_of_deps_mono:
  assumes "\<forall>k. u k \<subseteq> u' k"
  shows "view_of cord u \<sqsubseteq> view_of cord u'" oops

lemma view_of_mono: 
  assumes "\<forall>k. u k \<subseteq> u' k" and "\<And>k. prefix (cord k) (cord' k)" "\<And>k. distinct (cord' k)" 
  shows "view_of cord u \<sqsubseteq> view_of cord' u'" oops

lemma view_of_update:
  assumes 
    "i = length (cord k)"  
    "cord' k = cord k @ [t]"
    "t \<notin> set (cord k)"
    "t \<in> u k"
  shows "i \<in> view_of cord' u k" oops


subsection \<open>Extra: general lemmas\<close>


subsection \<open>Invariants about initializations and finity of kvs and its versions\<close>

definition T0_in_CO where
  "T0_in_CO s k \<longleftrightarrow> T0 \<in> set (cts_order s k)"

definition Kvs_Not_Emp where
  "Kvs_Not_Emp s \<longleftrightarrow> (\<forall>k. svr_state (svrs s k) \<noteq> wtxns_emp)"

definition KvsOfS_Not_Emp where
  "KvsOfS_Not_Emp s \<longleftrightarrow> (\<forall>k. kvs_of_s s k \<noteq> [])"

definition Dom_Kv_map_Not_Emp where
  "Dom_Kv_map_Not_Emp s cl \<longleftrightarrow> 
    (\<forall>kv_map cts. cl_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map} \<longrightarrow>
      dom kv_map \<noteq> {})"

definition Init_Ver_Inv where
  "Init_Ver_Inv s k \<longleftrightarrow> (\<exists>rs. svr_state (svrs s k) T0 = Commit 0 0 0 undefined rs)"

definition Finite_Wtxns_Dom where
  "Finite_Wtxns_Dom s k \<longleftrightarrow> finite (wtxns_dom (svr_state (svrs s k)))"

definition Finite_Wtxns_rsran where
  "Finite_Wtxns_rsran s k \<longleftrightarrow> finite (wtxns_rsran (svr_state (svrs s k)))"

definition Finite_Pend_Inv where
  "Finite_Pend_Inv s svr \<longleftrightarrow> finite (pending_wtxns_ts (svr_state (svrs s svr)))"

definition Finite_Dom_Kv_map where
  "Finite_Dom_Kv_map s cl \<longleftrightarrow>
    (\<forall>kv_map cts. cl_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map} \<longrightarrow>
      finite (dom (kv_map)))"

definition Finite_Keys where
  "Finite_Keys s cl \<longleftrightarrow>
    (\<forall>cclk keys kv_map. cl_state (cls s cl) = RtxnInProg cclk keys kv_map \<longrightarrow> finite keys)"

definition Finite_Dom_Kv_map_rd where
  "Finite_Dom_Kv_map_rd s cl \<longleftrightarrow>
    (\<forall>cclk keys kv_map. cl_state (cls s cl) = RtxnInProg cclk keys kv_map \<longrightarrow>
      finite (dom (kv_map)) \<and> keys \<noteq> {})"

definition Finite_t_Ran_Kvt_map where
  "Finite_t_Ran_Kvt_map s cl \<longleftrightarrow>
    (\<forall>cclk keys kv_map. cl_state (cls s cl) = RtxnInProg cclk keys kv_map \<longrightarrow>
      finite (snd ` ran (kv_map)))"

definition Finite_Lst_map_Ran where
  "Finite_Lst_map_Ran s cl \<longleftrightarrow> finite (range (lst_map (cls s cl)))"

lemma finite_get_ts:
  "reach tps_s s \<Longrightarrow>
   cl_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map} \<Longrightarrow>
   finite {get_ts (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map}" oops


subsection \<open>At functions\<close>

lemma at_is_committed:
  assumes "reach tps s"
  shows "is_committed ((svr_state (svrs s k)) (at (svr_state (svrs s k)) rts))" oops

lemma newest_own_write_is_committed:
  assumes "Finite_Wtxns_Dom s k"
    and "newest_own_write (svr_state (svrs s k)) ts cl = Some t"
  shows "is_committed (svr_state (svrs s k) t)" oops

lemma read_at_is_committed:
  assumes "reach tps s"
  shows "is_committed (svr_state (svrs s k) (read_at (svr_state (svrs s k)) rts cl))" oops


subsection \<open>Invariant about server and client state relations and (future and past) transactions ids\<close>

\<comment> \<open>Value of svr_state for future transaction ids\<close>
definition FTid_Wtxn_Inv where
  "FTid_Wtxn_Inv s cl \<longleftrightarrow> (\<forall>n k. n > cl_sn (cls s cl) \<longrightarrow> svr_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver)"

subsubsection \<open>cl_state + cl_sn \<longrightarrow> svr_state\<close>
definition Cl_Rtxn_Inv where
  "Cl_Rtxn_Inv s \<longleftrightarrow> (\<forall>cl k cclk keys kvm. cl_state (cls s cl) \<in> {Idle, RtxnInProg cclk keys kvm}
    \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) \<in> {No_Ver, Reg})"

definition Cl_Wtxn_Idle_Svr where
  "Cl_Wtxn_Idle_Svr s cl k \<longleftrightarrow> (\<forall>cts kv_map. cl_state (cls s cl) = Idle \<or>
    (cl_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map} \<and> kv_map k = None)
    \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver)"

definition Cl_Prep_Inv where
  "Cl_Prep_Inv s \<longleftrightarrow> (\<forall>cl k kvm. \<exists>pend_t prep_t v. cl_state (cls s cl) = WtxnPrep kvm
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) \<in> {No_Ver, Prep pend_t prep_t v}) \<and>
    (k \<notin> dom kvm \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver))"

definition Cl_Commit_Inv where
  "Cl_Commit_Inv s \<longleftrightarrow> (\<forall>cl k cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<longrightarrow>
    (\<forall>v. kv_map k = Some v \<longrightarrow>
      (\<exists>pend_t prep_t sts lst rs. svr_state (svrs s k) (get_wtxn s cl) \<in>
        {Prep pend_t prep_t v, Commit cts sts lst v rs})) \<and>
    (kv_map k = None \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver))"

subsubsection \<open>svr_state \<longrightarrow> cl_state\<close>
definition Prep_is_Curr_wt where
  "Prep_is_Curr_wt s k \<longleftrightarrow> (\<forall>t. is_prepared (svr_state (svrs s k) t) \<longrightarrow> is_curr_wt s t)"

definition Svr_Prep_Inv where
  "Svr_Prep_Inv s \<longleftrightarrow> (\<forall>k t pd ts v. svr_state (svrs s k) t = Prep pd ts v \<longrightarrow>
    (\<exists>cts kv_map.
      cl_state (cls s (get_cl_w t)) \<in> {WtxnPrep  kv_map, WtxnCommit cts kv_map} \<and>
      k \<in> dom kv_map))"

definition Svr_Commit_Inv where
  "Svr_Commit_Inv s \<longleftrightarrow> (\<forall>k t cts sts lst v rs. 
    svr_state (svrs s k) t = Commit cts sts lst v rs \<and> is_curr_wt s t \<longrightarrow> 
      (\<exists>kv_map. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map \<and> k \<in> dom kv_map))"


subsubsection \<open>fresh/future transactions\<close>
definition CFTid_Rtxn_Inv where
  "CFTid_Rtxn_Inv s cl \<longleftrightarrow> (\<forall>n. n \<ge> cl_sn (cls s cl) \<longrightarrow> rtxn_rts s (Tn_cl n cl) = None)"

definition CTid_Cts where
  "CTid_Cts s cl \<longleftrightarrow> (\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<longrightarrow> 
    cts = Max {get_ts (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map})"

definition FTid_notin_rs where
  "FTid_notin_rs s cl \<longleftrightarrow> (\<forall>k n t cts sts lst v rs. n > cl_sn (cls s cl) \<and>
    svr_state (svrs s k) t = Commit cts sts lst v rs \<longrightarrow> rs (Tn_cl n cl) = None)"

definition FTid_not_wr where
  "FTid_not_wr s cl \<longleftrightarrow> (\<forall>n k. n > cl_sn (cls s cl) \<longrightarrow> Tn (Tn_cl n cl) \<notin> wtxns_dom (svr_state (svrs s k)))"

definition Fresh_wr_notin_Wts_dom where
  "Fresh_wr_notin_Wts_dom s cl \<longleftrightarrow> (\<forall>cclk keys kv_map k. cl_state (cls s cl) \<in> {Idle, RtxnInProg cclk keys kv_map} \<longrightarrow>
    Tn (get_txn s cl) \<notin> wtxns_dom (svr_state (svrs s k)))"

definition Fresh_wr_notin_rs where
  "Fresh_wr_notin_rs s cl \<longleftrightarrow> (\<forall>k t cts kv_map cts' sts' lst' v' rs'.
    svr_state (svrs s k) t = Commit cts' sts' lst' v' rs' \<and>
    cl_state (cls s cl) \<in> {Idle, WtxnPrep kv_map, WtxnCommit cts kv_map}
     \<longrightarrow> rs' (get_txn s cl) = None)"


subsubsection \<open>past transactions\<close>

definition PTid_Inv where
  "PTid_Inv s cl \<longleftrightarrow> (\<forall>k. \<forall>n < cl_sn (cls s cl).
   (svr_state (svrs s k) (Tn (Tn_cl n cl)) \<in> {No_Ver, Reg}) \<or>
   (rtxn_rts s (Tn_cl n cl) = None \<and> 
    (\<exists>cts sts lst v rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts sts lst v rs)))"

lemma other_sn_idle:  
  assumes "FTid_Wtxn_Inv s cl" and "PTid_Inv s cl"
    and "get_cl t = cl" and "get_sn t \<noteq> cl_sn (cls s cl)"
  shows "\<And>k. \<exists>cts sts lst v rs. svr_state (svrs s k) (Tn t) \<in> {No_Ver, Reg, Commit cts sts lst v rs}" oops

definition Rtxn_Wtxn_No_Ver where
  "Rtxn_Wtxn_No_Ver s cl \<longleftrightarrow>
    (\<forall>n ts. rtxn_rts s (Tn_cl n cl) = Some ts \<longrightarrow> (\<forall>k. svr_state (svrs s k) (Tn (Tn_cl n cl)) \<in> {No_Ver, Reg}))"

definition Wtxn_Rtxn_None where
  "Wtxn_Rtxn_None s k \<longleftrightarrow>
    (\<forall>cl n pd ts v cts sts lst rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) \<in> {Prep pd ts v, Commit cts sts lst v rs}
       \<longrightarrow> rtxn_rts s (Tn_cl n cl) = None)"

definition Wtxn_Cts_T0 where
  "Wtxn_Cts_T0 s k \<longleftrightarrow> wtxn_cts s T0 = Some 0"

definition Wtxn_Cts_Tn_None where
  "Wtxn_Cts_Tn_None s cl \<longleftrightarrow> (\<forall>cts kv_map cclk keys n. 
    (cl_state (cls s cl) \<in> {Idle, WtxnPrep kv_map} \<and> n \<ge> cl_sn (cls s cl)) \<or>
    (cl_state (cls s cl) \<in> {RtxnInProg cclk keys kv_map, WtxnCommit cts kv_map} \<and> n > cl_sn (cls s cl))
     \<longrightarrow> wtxn_cts s (Tn (Tn_cl n cl)) = None)"

definition Wtxn_Cts_None where
  "Wtxn_Cts_None s \<longleftrightarrow> (\<forall>cts kv_map cclk keys t. t \<noteq> T0 \<and> (
    (cl_state (cls s (get_cl_w t)) \<in> {Idle, WtxnPrep kv_map} \<and>
        get_sn_w t \<ge> cl_sn (cls s (get_cl_w t))) \<or>
    (cl_state (cls s (get_cl_w t)) \<in> {RtxnInProg cclk keys kv_map, WtxnCommit cts kv_map} \<and>
        get_sn_w t > cl_sn (cls s (get_cl_w t))))
     \<longrightarrow> wtxn_cts s t = None)"

definition WtxnCommit_Wtxn_Cts where
  "WtxnCommit_Wtxn_Cts s cl \<longleftrightarrow> (\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map
    \<longrightarrow> wtxn_cts s (get_wtxn s cl) = Some cts)"

definition Committed_Abs_has_Wtxn_Cts where
  "Committed_Abs_has_Wtxn_Cts s k \<longleftrightarrow> (\<forall>t cts sts lst v rs pd ts kv_map.
    svr_state (svrs s k) t = Commit cts sts lst v rs \<or>
   (svr_state (svrs s k) t = Prep pd ts v \<and> cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map)
      \<longrightarrow> wtxn_cts s t = Some cts)"


subsection \<open>monotonic lemmas and inequality of timestamps invariants\<close>

lemma svr_clock_monotonic:
  "state_trans s e s' \<Longrightarrow> svr_clock (svrs s' svr) \<ge> svr_clock (svrs s svr)" oops

definition Cl_Clk_le_Prep where
  "Cl_Clk_le_Prep s cl \<longleftrightarrow>
    (\<forall>kv_map k v. cl_state (cls s cl) = WtxnPrep kv_map \<and> kv_map k = Some v \<and>
     is_prepared (svr_state (svrs s k) (get_wtxn s cl)) \<longrightarrow>
     cl_clock (cls s cl) \<le> get_ts (svr_state (svrs s k) (get_wtxn s cl)))"

lemma cl_clock_monotonic:
  "state_trans s e s' \<Longrightarrow> cl_clock (cls s' cl) \<ge> cl_clock (cls s cl)" oops

definition Pend_le_Clk where
  "Pend_le_Clk s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns_ts (svr_state (svrs s svr)). ts \<le> svr_clock (svrs s svr))"

definition Prep_le_Clk where
  "Prep_le_Clk s svr \<longleftrightarrow>
    (\<forall>t pd ts v. svr_state (svrs s svr) t = Prep pd ts v \<longrightarrow> ts \<le> svr_clock (svrs s svr))"

definition Pend_lt_Prep where
  "Pend_lt_Prep s svr \<longleftrightarrow>
    (\<forall>t pd ts v. svr_state (svrs s svr) t = Prep pd ts v \<longrightarrow> pd < ts)"

definition Lst_le_Clk where
  "Lst_le_Clk s k \<longleftrightarrow> svr_lst (svrs s k) \<le> svr_clock (svrs s k)"

definition Lst_le_Pend where
  "Lst_le_Pend s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns_ts (svr_state (svrs s svr)). svr_lst (svrs s svr) \<le> ts)"

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

definition Prep_le_Cl_Cts where
  "Prep_le_Cl_Cts s cl \<longleftrightarrow> (\<forall>cts kv_map k pend_t prep_t v. 
      cl_state (cls s cl) = WtxnCommit cts kv_map \<and>
      svr_state (svrs s k) (get_wtxn s cl) = Prep pend_t prep_t v \<longrightarrow> prep_t \<le> cts)"

definition Lst_map_le_Get_lst where
  "Lst_map_le_Get_lst s cl k \<longleftrightarrow> (\<forall>cts ts lst v rs.
    svr_state (svrs s k) (get_wtxn s cl) = Commit cts ts lst v rs \<longrightarrow> lst_map (cls s cl) k \<le> lst)"

definition Fresh_rd_notin_other_rs where
  "Fresh_rd_notin_other_rs s cl k \<longleftrightarrow> (\<forall>t cclk keys kv_map cts sts lst v rs.
    cl_state (cls s cl) = RtxnInProg cclk keys kv_map \<and>
    svr_state (svrs s k) t = Commit cts sts lst v rs \<and>
    t \<noteq> read_at (svr_state (svrs s k)) (gst (cls s cl)) cl
     \<longrightarrow> rs (get_txn s cl) = None)"

definition Once_in_rs where
  "Once_in_rs s k t \<longleftrightarrow> (\<forall>t_wr cts ts lst v rs m t_wr' cts' ts' lst' v' rs'.
    svr_state (svrs s k) t_wr = Commit cts ts lst v rs \<and> rs t = Some m \<and>
    t_wr' \<noteq> t_wr \<and> svr_state (svrs s k) t_wr' = Commit cts' ts' lst' v' rs' \<longrightarrow> rs' t = None)"

definition Lst_map_le_Rlst where
  "Lst_map_le_Rlst s cl k \<longleftrightarrow> (\<forall>t cts ts lst v rs rlst rts.
    svr_state (svrs s k) t = Commit cts ts lst v rs \<and> rs (get_txn s cl) = Some (rts, rlst)
      \<longrightarrow> lst_map (cls s cl) k \<le> rlst)"

lemma lst_map_monotonic:
  assumes "state_trans s e s'"
    and "reach tps_s s"
  shows "lst_map (cls s cl) k \<le> lst_map (cls s' cl) k" oops

lemma lst_map_min_monotonic:
  assumes "state_trans s e s'"
    and "reach tps_s s"
  shows "Min (range (lst_map (cls s cl))) \<le> Min (range (lst_map (cls s' cl)))" oops

definition Gst_le_Min_Lst_map where
  "Gst_le_Min_Lst_map s cl \<longleftrightarrow> (gst (cls s cl) \<le> Min (range (lst_map (cls s cl))))"

definition Gst_le_Pend_t where
  "Gst_le_Pend_t s cl \<longleftrightarrow> (\<forall>k t pend_t prep_t v. 
      svr_state (svrs s k) t = Prep pend_t prep_t v \<longrightarrow> gst (cls s cl) \<le> pend_t)"

definition Gst_lt_Cl_Cts where
  "Gst_lt_Cl_Cts s cl k \<longleftrightarrow> (\<forall>cl' sn' pd ts v cts kv_map.
    svr_state (svrs s k) (Tn (Tn_cl sn' cl')) = Prep pd ts v \<and>
    cl_state (cls s cl') = WtxnCommit cts kv_map \<and>
    k \<in> dom kv_map
    \<longrightarrow> gst (cls s cl) < cts)"

definition Gst_lt_Cts where
  "Gst_lt_Cts s cl \<longleftrightarrow> (\<forall>k cts sts lst v rs. 
      svr_state (svrs s k) (get_wtxn s cl) = Commit cts sts lst v rs \<longrightarrow> gst (cls s cl) < cts)"

lemma gst_monotonic:
  assumes "state_trans s e s'"
    and "reach tps_s s"
  shows "gst (cls s' cl) \<ge> gst (cls s cl)" oops

definition Rtxn_Rts_le_Gst where
  "Rtxn_Rts_le_Gst s cl \<longleftrightarrow> (\<forall>n ts. rtxn_rts s (Tn_cl n cl) = Some ts \<longrightarrow> ts \<le> gst (cls s cl))"


subsection \<open>Commit Order Invariants\<close>

definition CO_Tid where
  "CO_Tid s cl \<longleftrightarrow> (case cl_state (cls s cl) of
    WtxnCommit cts kv_map \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow> n \<le> cl_sn (cls s cl))
  | _ \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow> n < cl_sn (cls s cl)))"

definition T0_First_in_CO where
  "T0_First_in_CO s k \<longleftrightarrow> cts_order s k ! 0 = T0"

definition CO_Distinct where
  "CO_Distinct s k \<longleftrightarrow> distinct (cts_order s k)"

definition CO_Tn_is_Cmt_Abs where
  "CO_Tn_is_Cmt_Abs s k \<longleftrightarrow> (\<forall>n cl. Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow>
    (\<exists>cts sts lst v rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts sts lst v rs) \<or> 
    ((\<exists>pd ts v. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Prep pd ts v) \<and> 
     (\<exists>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<and> 
      cl_sn (cls s cl) = n \<and> k \<in> dom kv_map)))"

abbreviation is_committed_in_kvs where
  "is_committed_in_kvs s k t \<equiv> 
    is_committed (svr_state (svrs s k) t) \<or> 
    (is_prepared (svr_state (svrs s k) t) \<and>
     (\<exists>cts kv_map. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map \<and> k \<in> dom kv_map))"

definition CO_is_Cmt_Abs where
  "CO_is_Cmt_Abs s k \<longleftrightarrow> (\<forall>t. t \<in> set (cts_order s k) \<longrightarrow> is_committed_in_kvs s k t)"

definition CO_not_No_Ver where
  "CO_not_No_Ver s k \<longleftrightarrow> (\<forall>t \<in> set (cts_order s k).
    svr_state (svrs s k) t \<noteq> No_Ver \<and> svr_state (svrs s k) t \<noteq> Reg)"

definition CO_has_Cts where
  "CO_has_Cts s k \<longleftrightarrow> (\<forall>t \<in> set (cts_order s k). \<exists>cts. wtxn_cts s t = Some cts)"

definition Committed_Abs_Tn_in_CO where
  "Committed_Abs_Tn_in_CO s k \<longleftrightarrow> (\<forall>n cl.
    (\<exists>cts sts lst v rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts sts lst v rs) \<or> 
    ((\<exists>pd ts v. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Prep pd ts v) \<and> 
     (\<exists>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<and> cl_sn (cls s cl) = n)) \<longrightarrow>
    Tn (Tn_cl n cl) \<in> set (cts_order s k))"

definition Committed_Abs_in_CO where
  "Committed_Abs_in_CO s k \<longleftrightarrow> (\<forall>t. is_committed_in_kvs s k t \<longrightarrow> t \<in> set (cts_order s k))"

definition CO_Sub_Wtxn_Cts where
  "CO_Sub_Wtxn_Cts s k \<longleftrightarrow> set (cts_order s k) \<subseteq> dom (wtxn_cts s)"

definition CO_All_k_Wtxn_Cts_Eq where
  "CO_All_k_Wtxn_Cts_Eq s \<longleftrightarrow> dom (wtxn_cts s) = (\<Union>k. set (cts_order s k))"


definition Wtxn_Cts_Tn_is_Abs_Cmt where
  "Wtxn_Cts_Tn_is_Abs_Cmt s cl k \<longleftrightarrow> (\<forall>n cts. wtxn_cts s (Tn (Tn_cl n cl)) = Some cts \<and>
    Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow>
    (\<exists>sts lst v rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts sts lst v rs) \<or> 
    ((\<exists>pd ts v. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Prep pd ts v) \<and> 
     (\<exists>kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<and>
        cl_sn (cls s cl) = n \<and> k \<in> dom kv_map)))"

definition Wtxn_Cts_Tn_is_Abs_Cmt' where
  "Wtxn_Cts_Tn_is_Abs_Cmt' s cl n cts \<longleftrightarrow> (wtxn_cts s (Tn (Tn_cl n cl)) = Some cts \<longrightarrow>
   (\<exists>k. (\<exists>sts lst v rs. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Commit cts sts lst v rs) \<or> 
    ((\<exists>pd ts v. svr_state (svrs s k) (Tn (Tn_cl n cl)) = Prep pd ts v) \<and> 
     (\<exists>kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<and>
        cl_sn (cls s cl) = n \<and> k \<in> dom kv_map))))"

definition CO_Sorted where
  "CO_Sorted s k \<longleftrightarrow> sorted (map (unique_ts (wtxn_cts s)) (cts_order s k))"


\<comment> \<open>commit order lemmas\<close>
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


subsection \<open>UpdateKV for wtxn\<close>

lemma sorted_insort_key_is_snoc:
  "sorted (map f l) \<Longrightarrow> \<forall>x \<in> set l. f x < f t \<Longrightarrow> insort_key f t l = l @ [t]" oops

lemma wtxn_cts_tn_le_cts:
  assumes
    "Tn t' \<in> set (cts_order s k)"
    "reach tps_s s"
    "cl_write_commit_s cl kv_map cts sn u'' clk mmap s s'"
  shows "unique_ts ((wtxn_cts s)(get_wtxn s cl \<mapsto> cts)) (Tn t')
    < unique_ts ((wtxn_cts s)(get_wtxn s cl \<mapsto> cts)) (get_wtxn s cl)" oops

lemma cl_write_commit_is_snoc:
  assumes "reach tps_s s"
    "cl_write_commit_s cl kv_map cts sn u'' clk mmap s s'"
  shows
    "insort_key (unique_ts ((wtxn_cts s) (get_wtxn s cl \<mapsto> cts))) (get_wtxn s cl)
      (cts_order s k) =
      (cts_order s k) @ [get_wtxn s cl]" oops


subsubsection \<open>Write commit guard properties\<close>

lemma cl_write_commit_txn_to_vers_get_wtxn:
  assumes "cl_write_commit_s cl kv_map cts sn u'' clk mmap gs gs'" 
  and "kv_map k = Some v" 
  shows "txn_to_vers gs k (get_wtxn gs cl) = new_vers (Tn (Tn_cl sn cl)) v" oops

subsubsection \<open>Write commit update properties\<close>

lemma cl_write_commit_txn_to_vers_pres:
  assumes "cl_write_commit_s cl kv_map cts sn u'' clk mmap gs gs'"
  shows "txn_to_vers gs' k = txn_to_vers gs k" oops

lemma cl_write_commit_cts_order_update:
  assumes "cl_write_commit_s cl kv_map cts sn u'' clk mmap gs gs'"
  shows "cts_order gs' = (\<lambda>k.
         (if kv_map k = None
          then cts_order gs k
          else insort_key (unique_ts ((wtxn_cts gs) (get_wtxn gs cl \<mapsto> cts))) (get_wtxn gs cl) (cts_order gs k)))" oops

lemma cl_write_commit_kvs_of_s:
  assumes "reach tps_s s"
    "cl_write_commit_s cl kv_map cts sn u'' clk mmap s s'"
  shows "kvs_of_s s' = update_kv (Tn_cl sn cl)
                          (write_only_fp kv_map)
                          (view_of (cts_order s) (get_view s cl))
                          (kvs_of_s s)" oops

lemma cl_write_commit_get_view:
  assumes "reach tps_s s"
    and "cl_write_commit_s cl kv_map cts sn u'' clk mmap s s'"
  shows "get_view s' cl =
    (\<lambda>k. if kv_map k = None
         then get_view s cl k
         else insert (get_wtxn s cl) (get_view s cl k))" oops

lemma cl_write_commit_view_of:
  assumes "reach tps_s s"
    and "cl_write_commit_s cl kv_map cts sn u'' clk mmap s s'"
  shows "view_of (cts_order s') (get_view s' cl) = 
    (\<lambda>k. if kv_map k = None
         then view_of (cts_order s) (get_view s cl) k
         else insert (length (cts_order s k)) (view_of (cts_order s) (get_view s cl) k))" oops
  
lemma full_view_elem: "i \<in> full_view vl \<longleftrightarrow> i < length vl" oops

lemma length_update_kv_bound:
  "i < length (update_kv t F u K k) \<longleftrightarrow> i < length (K k) \<or> W \<in> dom (F k) \<and> i = length (K k)" oops

lemma v_writer_set_cts_order_eq:
  assumes "CO_not_No_Ver s k"                   
  shows "v_writer ` set (kvs_of_s s k) = set (cts_order s k)" oops


subsection \<open>Simulation relation lemmas\<close>

lemma kvs_of_s_init:
  "kvs_of_s (state_init) = (\<lambda>k. [\<lparr>v_value = undefined, v_writer = T0, v_readerset = {}\<rparr>])" oops

lemma kvs_of_s_inv:
  assumes "reach tps_s s"
    and "state_trans s e s'"
    and "\<not>commit_ev e"
  shows "kvs_of_s s' = kvs_of_s s" oops

lemma cts_order_inv:
  assumes "reach tps_s s"
    and "state_trans s e s'"
    and "\<forall>cl kv_map cts sn u'' clk mmap. 
      e \<noteq> WCommit cl kv_map cts sn u'' clk mmap"
  shows "cts_order s' = cts_order s" oops

lemma wtxn_cts_dom_inv:
  assumes "reach tps_s s"
    and "state_trans s e s'"
    and "wtxn_cts s' = wtxn_cts s"
  shows "cts_order s' = cts_order s" oops

lemma get_view_inv:
  assumes "reach tps_s s"
    and "state_trans s e s'"
    and "\<not>v_ext_ev e cl"
  shows "get_view s' cl = get_view s cl" oops

lemma views_of_s_inv:
  assumes "reach tps_s s"
    and "state_trans s e s'"
    and "\<not>v_ext_ev e cl"
  shows "views_of_s s' cl = views_of_s s cl" oops

lemma read_at_inv:
  assumes "reach tps_s s"
    and "state_trans s e s'"
    and "cl_state (cls s cl) = RtxnInProg cclk keys kv_map"
  shows "read_at (svr_state (svrs s' k)) (gst (cls s cl)) cl =
         read_at (svr_state (svrs s k)) (gst (cls s cl)) cl" oops


subsection \<open>UpdateKV for rtxn\<close>

subsubsection \<open>View Invariants\<close>

definition View_Init where
  "View_Init s cl k \<longleftrightarrow> (T0 \<in> get_view s cl k)"

definition Get_View_Committed where
  "Get_View_Committed s cl k \<longleftrightarrow> (\<forall>t. t \<in> get_view s cl k  \<longrightarrow> is_committed_in_kvs s k t)"

subsubsection \<open>view_of, index_of: some more lemmas\<close>

lemma view_of_in_range:
  assumes "i \<in> view_of (cts_order s) u k"
    and "reach tps_s s"
  shows "i < length (cts_order s k)" oops

lemma finite_view_of:
  "finite (view_of (cts_order s) u k)" oops

lemma view_of_non_emp:
  "reach tps_s s \<Longrightarrow> view_of (cts_order s) (get_view s cl) k \<noteq> {}" oops

lemma index_of_T0:
  assumes "reach tps_s s"
  shows "index_of (cts_order s k) T0 = 0" oops

lemma zero_in_view_of:
  assumes "reach tps_s s"
  shows "0 \<in> view_of (cts_order s) (get_view s cl) k" oops

lemma Max_views_of_s_in_range:
  assumes "reach tps_s s"
  shows "Max (views_of_s s cl k) < length (cts_order s k)" oops


subsubsection \<open>Rtxn reads max\<close>

definition Cts_le_Cl_Cts where
  "Cts_le_Cl_Cts s cl k \<longleftrightarrow> (\<forall>sn cts kv_map ts sclk slst v rs.
    cl_state (cls s cl) = WtxnCommit cts kv_map \<and>
    svr_state (svrs s k) (Tn (Tn_cl sn cl)) = Commit ts sclk slst v rs \<longrightarrow>
    (if sn = cl_sn (cls s cl) then ts = cts else ts < cts))"

definition Cl_Curr_Tn_Right where
  "Cl_Curr_Tn_Right s k \<longleftrightarrow> (\<forall>t i j.
    is_curr_t s t \<and> cts_order s k ! j = Tn t \<and> j < i \<and> i < length (cts_order s k) \<longrightarrow>
    get_cl_w (cts_order s k ! i) \<noteq> get_cl t)"

definition Ts_Non_Zero where
  "Ts_Non_Zero s cl k \<longleftrightarrow> (\<forall>sn ts kv_map pd sclk slst v rs.
    cl_state (cls s cl) = WtxnCommit ts kv_map \<or>
    svr_state (svrs s k) (Tn (Tn_cl sn cl)) = Prep pd ts v \<or> 
    svr_state (svrs s k) (Tn (Tn_cl sn cl)) = Commit ts sclk slst v rs \<longrightarrow>
    ts > 0)"

definition Bellow_Gst_Committed where
  "Bellow_Gst_Committed s cl k \<longleftrightarrow> (\<forall>t \<in> set (cts_order s k).
    get_ts (svr_state (svrs s k) t) \<le> gst (cls s cl) \<longrightarrow> is_committed (svr_state (svrs s k) t))"

definition Full_Ts_Inj where
  "Full_Ts_Inj s k \<longleftrightarrow> (\<forall>t t'. t \<noteq> t' \<and>
    is_committed (svr_state (svrs s k) t) \<and> 
    is_committed (svr_state (svrs s k) t')  \<longrightarrow>
    full_ts (svr_state (svrs s k)) t \<noteq> full_ts (svr_state (svrs s k)) t')"

lemma index_of_T0_init: "index_of [T0] T0 = 0" oops

lemma read_at_init:
  "read_at (wtxns_emp(T0 := Commit 0 0 0 undefined (\<lambda>x. None))) 0 cl = T0" oops

lemma wtxn_cts_mono_full_ts:
  assumes "reach tps_s s"
    and "is_committed (svr_state (svrs s k) t)"
    and "is_committed (svr_state (svrs s k) t')"
    and "full_ts (svr_state (svrs s k)) t < full_ts (svr_state (svrs s k)) t'"
  shows "the (wtxn_cts s t) < the (wtxn_cts s t') \<or>
    (the (wtxn_cts s t) = the (wtxn_cts s t') \<and>
      (if t = T0 then 0 else Suc (get_cl_w t)) < (if t' = T0 then 0 else Suc (get_cl_w t')))" oops

lemma get_ts_wtxn_cts_eq:
  assumes "reach tps_s s"
    and "is_committed (svr_state (svrs s k) t)"
  shows "get_ts (svr_state (svrs s k) t) = the (wtxn_cts s t)" oops

lemma get_ts_wtxn_cts_le_rts:
  assumes "reach tps_s s"
    and "t \<in> set (cts_order s k)"
    and "the (wtxn_cts s t) \<le> rts"
  shows "get_ts (svr_state (svrs s k) t) \<le> rts" oops

lemma sorted_wtxn_cts:
  assumes "reach tps_s s"
    and "i < j"
    and "j < length (cts_order s k)"
  shows "the (wtxn_cts s (cts_order s k ! i)) \<le> the (wtxn_cts s (cts_order s k ! j))" oops

lemma index_of_mono_wtxn_cts:
  assumes "reach tps_s s"
    and "t \<in> set (cts_order s k)"
    and "t' \<in> set (cts_order s k)"
    and "the (wtxn_cts s t) < the (wtxn_cts s t')"
  shows "index_of (cts_order s k) t < index_of (cts_order s k) t'" oops

lemma index_of_mono_eq_wtxn_cts:
  assumes "reach tps_s s"
    and "t \<in> set (cts_order s k)"
    and "t' \<in> set (cts_order s k)"
    and "the (wtxn_cts s t) < the (wtxn_cts s t') \<or>
        (the (wtxn_cts s t) = the (wtxn_cts s t') \<and>
          (if t = T0 then 0 else Suc (get_cl_w t)) < (if t' = T0 then 0 else Suc (get_cl_w t')))"
  shows "index_of (cts_order s k) t \<le> index_of (cts_order s k) t'" oops

definition Rtxn_Reads_Max where
  "Rtxn_Reads_Max s cl k \<longleftrightarrow>
   read_at (svr_state (svrs s k)) (gst (cls s cl)) cl =
    (case cl_state (cls s cl) of
      WtxnCommit cts kv_map \<Rightarrow>
        (if is_committed (svr_state (svrs s k) (get_wtxn s cl)) \<or> kv_map k = None
         then cts_order s k ! Max (views_of_s s cl k)
         else cts_order s k ! Max (views_of_s s cl k - {index_of (cts_order s k) (get_wtxn s cl)})) |
      _ \<Rightarrow> cts_order s k ! Max (views_of_s s cl k))"

subsubsection \<open>Kvt_map values of cl_read_done\<close>

definition Rtxn_IdleK_notin_rs where
  "Rtxn_IdleK_notin_rs s cl \<longleftrightarrow> (\<forall>k cclk keys kv_map t cts sts lst v rs.
    cl_state (cls s cl) = RtxnInProg cclk keys kv_map \<and> k \<notin> keys \<and>
    svr_state (svrs s k) t = Commit cts sts lst v rs \<longrightarrow> rs (get_txn s cl) = None)"

definition Rtxn_RegK_Kvtm_Cmt_in_rs where
  "Rtxn_RegK_Kvtm_Cmt_in_rs s cl k \<longleftrightarrow> (\<forall>cclk keys kv_map v.
    cl_state (cls s cl) = RtxnInProg cclk keys kv_map \<and> kv_map k = Some v \<longrightarrow>
    (\<exists>t cts sts lst rs rts rlst. svr_state (svrs s k) t = Commit cts sts lst v rs
      \<and> rs (get_txn s cl) = Some (rts, rlst)))"

subsubsection \<open>Read done update properties\<close>

lemma map_list_update:
  "i < length l \<Longrightarrow> distinct l \<Longrightarrow>
   (map f l) [i := (map f l ! i) \<lparr>v_readerset := x\<rparr>] =
    map (f (l ! i := (f (l ! i)) \<lparr>v_readerset := x\<rparr>)) l" oops

lemma theI_of_ctx_in_CO:
  assumes "i = index_of (cts_order s k) t"
    and "t \<in> set (cts_order s k)"
    and "CO_Distinct s k"
  shows "cts_order s k ! i = t" oops

lemma view_of_committed_in_kvs:
  assumes "cl_state (cls s cl) = RtxnInProg cclk keys kv_map"
    and "reach tps_s s"
    and "i \<in> view_of (cts_order s) (get_view s cl) k"
    and "t_wr = cts_order s k ! i"
  shows "is_committed_in_kvs s k t_wr" oops 

lemma cl_read_done_txn_to_vers_update:
  assumes "reach tps_s s"
    "cl_read_done_s cl kv_map sn u'' clk s s'"
  shows "txn_to_vers s' k =
    (case kv_map k of
      None \<Rightarrow> txn_to_vers s k |
      Some _ \<Rightarrow> (txn_to_vers s k)
          (read_at (svr_state (svrs s k)) (gst (cls s cl)) cl :=
            txn_to_vers s k (read_at (svr_state (svrs s k)) (gst (cls s cl)) cl)
              \<lparr>v_readerset := insert (get_txn s cl)
                (v_readerset (txn_to_vers s k (read_at (svr_state (svrs s k)) (gst (cls s cl)) cl)))\<rparr>))"
  oops

lemma cl_read_done_kvs_of_s:
  assumes "reach tps_s s"
    "cl_read_done_s cl kv_map sn u'' clk s s'"
  shows "kvs_of_s s' = update_kv (Tn_cl sn cl)
                          (read_only_fp kv_map)
                          (view_of (cts_order s) (get_view s cl))
                          (kvs_of_s s)"
  oops


subsection \<open>Transaction ID Freshness\<close>

definition Sqn_Inv_nc where
  "Sqn_Inv_nc s cl \<longleftrightarrow> (\<forall>cts kv_map. cl_state (cls s cl) \<noteq> WtxnCommit cts kv_map
     \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m < cl_sn (cls s cl)))"

definition Sqn_Inv_c where
  "Sqn_Inv_c s cl \<longleftrightarrow> (\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map
     \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m \<le> cl_sn (cls s cl)))"

lemma reach_sql_inv: "reach tps_s s \<Longrightarrow> Sqn_Inv_c s cl \<and> Sqn_Inv_nc s cl" oops

lemma t_is_fresh:
  assumes "reach tps_s s"
    and "cl_state (cls s cl) \<in> {WtxnPrep kv_map, RtxnInProg cclk keys kv_map}"
  shows "get_txn s cl \<in> next_txids (kvs_of_s s) cl" oops


subsection \<open>Views\<close>

subsubsection \<open>View update lemmas\<close>

lemma get_view_update_cls:
  "cl' \<noteq> cl \<Longrightarrow>
   get_view (s\<lparr>cls := (cls s)(cl := X) \<rparr>) cl' = get_view s cl'" oops

lemma get_view_update_cls_rtxn_rts:
  "cl' \<noteq> cl \<Longrightarrow>
   get_view (s\<lparr>cls := (cls s)(cl := X), rtxn_rts := Y \<rparr>) cl' = get_view s cl'" oops

lemma get_view_update_svr_wtxns_dom:
   "wtxns_dom new_svr_state = wtxns_dom (svr_state (svrs s k)) \<Longrightarrow> 
    get_view (s\<lparr>svrs := (svrs s)
                   (k := svrs s k
                      \<lparr>svr_state := new_svr_state,
                       svr_clock := clk \<rparr>)\<rparr>) cl =
    get_view s cl" oops

  
lemma v_writer_kvs_of_s:
  assumes "reach tps_s s"
  shows "v_writer ` set (kvs_of_s s k) = set (cts_order s k)" oops

lemma v_readerset_kvs_of_s:
  assumes "reach tps_s s"
  shows "\<Union> (v_readerset ` set (kvs_of_s s k)) = 
   {t. \<exists>t_wr \<in> set (cts_order s k).
      \<exists>cts sts lst v rs rts rlst. svr_state (svrs s k) t_wr = Commit cts sts lst v rs \<and>
      rs t = Some (rts, rlst) \<and> get_sn t < cl_sn (cls s (get_cl t))}" oops

lemma v_writer_kvs_of_s_nth:
  "reach tps_s s \<Longrightarrow> i < length (cts_order s k) \<Longrightarrow> v_writer (kvs_of_s s k ! i) = cts_order s k ! i" oops

lemma v_readerset_kvs_of_s_nth:
  "reach tps_s s \<Longrightarrow> i < length (cts_order s k) \<Longrightarrow>
    v_readerset (kvs_of_s s k ! i) = get_abst_rs s k (cts_order s k ! i)" oops


subsubsection \<open>View Shift\<close>

definition Cl_WtxnCommit_Get_View where
  "Cl_WtxnCommit_Get_View s cl \<longleftrightarrow>
    (\<forall>cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<longrightarrow>
      (\<forall>k \<in> dom kv_map. get_wtxn s cl \<in> get_view s cl k))"

abbreviation cl_txids :: "cl_id \<Rightarrow> txid set" where
  "cl_txids cl \<equiv> {Tn (Tn_cl sn cl)| sn. True}"

definition View_RYW where
  "View_RYW s cl k \<longleftrightarrow>
    ((vl_writers (kvs_of_s s k) \<inter> cl_txids cl) \<subseteq> get_view s cl k)"
  
  
subsubsection \<open>View Wellformedness\<close>

definition FTid_notin_Get_View where
  "FTid_notin_Get_View s cl \<longleftrightarrow>
    (\<forall>n cl' k. (n > cl_sn (cls s cl) \<longrightarrow> Tn (Tn_cl n cl) \<notin> get_view s cl' k) \<and>
    (cl' \<noteq> cl \<longrightarrow> get_wtxn s cl \<notin> get_view s cl' k))"

lemma reach_kvs_expands [simp]:
  assumes "state_trans s e s'"
    and "reach tps_s s"
  shows "kvs_of_s s \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s kvs_of_s s'" oops

lemma cl_write_commit_views_of_s_other_cl_inv:
  assumes "reach tps_s s"
    and "cl_write_commit_s cl kv_map cts sn u clk mmap s s'"
    and "cl' \<noteq> cl"
  shows "views_of_s s' cl' = views_of_s s cl'" oops

definition Views_of_s_Wellformed where
  "Views_of_s_Wellformed s cl \<longleftrightarrow> (view_wellformed (kvs_of_s s) (views_of_s s cl))"


subsection \<open>Fp Property\<close>

definition Rtxn_Fp_Inv where
  "Rtxn_Fp_Inv s cl k \<longleftrightarrow> (\<forall>t cclk keys kv_map v.
    cl_state (cls s cl) = RtxnInProg cclk keys kv_map \<and> kv_map k = Some v \<and>
    t = read_at (svr_state (svrs s k)) (gst (cls s cl)) cl \<longrightarrow>
    (\<exists>cts sclk lst rs. svr_state (svrs s k) t = Commit cts sclk lst v rs))"


lemma v_value_last_version:
  assumes "reach tps_s s"
    and "svr_state (svrs s k)(cts_order s k ! Max (views_of_s s cl k)) = Commit cts sclk lst v rs"
  shows "v = v_value (last_version (kvs_of_s s k) (views_of_s s cl k))" oops


subsection \<open>Read-Only and Write-Only\<close>

lemma fresh_t_notin_kvs_txids:
  "t \<in> next_txids K cl \<Longrightarrow> Tn t \<notin> kvs_txids K" oops

lemma read_only_Txs_update_kv:
  assumes "(\<And>k. F k R = None \<or> Max (u k) < length (K k))"
    and "(\<forall>k. F k R = None) \<or> (\<forall>k. F k W = None)"
    and "t \<in> next_txids K cl"
  shows "read_only_Txs (update_kv t F u K) = 
   (if \<forall>k. F k R = None then read_only_Txs K else insert (Tn t) (read_only_Txs K))" oops

definition Disjoint_RW where
  "Disjoint_RW s \<longleftrightarrow> (read_only_Txs (kvs_of_s s) = Tn ` kvs_readers (kvs_of_s s))"

lemma kvs_writers_readers_disjoint:
  "reach tps_s s \<Longrightarrow> kvs_writers (kvs_of_s s) \<inter> Tn ` kvs_readers (kvs_of_s s) = {}" oops

definition RO_has_rts where
  "RO_has_rts s \<longleftrightarrow> (\<forall>t. Tn t \<in> read_only_Txs (kvs_of_s s) \<longrightarrow> (\<exists>rts. rtxn_rts s t = Some rts))"

definition SO_Rts_Mono where
  "SO_Rts_Mono s \<longleftrightarrow> (\<forall>r1 r2 rts1 rts2. (Tn r1, Tn r2) \<in> SO \<and>
    rtxn_rts s r1 = Some rts1 \<and> rtxn_rts s r2 = Some rts2 \<longrightarrow> rts1 \<le> rts2)"

definition SO_Cts_Mono where
  "SO_Cts_Mono s \<longleftrightarrow> (\<forall>w1 w2 cts1 cts2. (w1, w2) \<in> SO \<and>
    wtxn_cts s w1 = Some cts1 \<and> wtxn_cts s w2 = Some cts2 \<longrightarrow> cts1 < cts2)"

definition SO_Rts_Cts_Mono where
  "SO_Rts_Cts_Mono s \<longleftrightarrow> (\<forall>t_rd t_wr rts cts. (Tn t_rd, t_wr) \<in> SO \<and>
    rtxn_rts s t_rd = Some rts \<and> wtxn_cts s t_wr = Some cts \<longrightarrow> rts < cts)" (* not proven *)


subsection \<open>Closedness\<close>

lemma visTx'_union_distr: "visTx' K (u\<^sub>1 \<union> u\<^sub>2) = visTx' K u\<^sub>1 \<union> visTx' K u\<^sub>2" oops

lemma visTx'_Union_distr: "visTx' K (\<Union>i\<in>I. u i) = (\<Union>i\<in>I. visTx' K (u i))" oops

lemma visTx'_same_writers: "kvs_writers K' = kvs_writers K \<Longrightarrow> visTx' K' u = visTx' K u" oops

lemma union_closed':
  assumes "closed' K u\<^sub>1 r"
    and "closed' K u\<^sub>2 r"
    and "kvs_writers K' = kvs_writers K" 
    and "read_only_Txs K \<subseteq> read_only_Txs K'"
  shows "closed' K' (u\<^sub>1 \<union> u\<^sub>2) r" oops

lemma Union_closed':
  assumes "\<And>i. i \<in> I \<Longrightarrow> closed' K (u i) r"
    and "finite I" 
    and "kvs_writers K' = kvs_writers K" 
    and "read_only_Txs K \<subseteq> read_only_Txs K'"
  shows "closed' K' (\<Union>i\<in>I. u i) r" oops

lemma union_closed'_extend_rel:
  assumes "closed' K u\<^sub>1 r"
    and "closed' K u\<^sub>2 r"
    and "kvs_writers K' = kvs_writers K" 
    and "read_only_Txs K \<subseteq> read_only_Txs K'"
    and "x \<notin> (r\<inverse>)\<^sup>* `` (visTx' K u\<^sub>1 \<union> visTx' K u\<^sub>2)"
    and "r' = (\<Union>y\<in>Y. {(y, x)}) \<union> r"
    and "finite Y"
  shows "closed' K' (u\<^sub>1 \<union> u\<^sub>2) r'" oops


lemma visTx'_new_writer: "kvs_writers K' = insert t (kvs_writers K) \<Longrightarrow>
  visTx' K' (insert t u) = insert t (visTx' K u)" oops

lemma insert_wr_t_closed':
  assumes "closed' K u r"
    and "closed_general {t} (r\<inverse>) (visTx' K u \<union> read_only_Txs K)"
    and "read_only_Txs K' = read_only_Txs K"
    and "kvs_writers K' = insert t (kvs_writers K)"
  shows "closed' K' (insert t u) r" oops

lemma visTx'_observes_t:
  "t \<in> kvs_writers K \<Longrightarrow> visTx' K (insert t u) = insert t (visTx' K u)" oops

lemma insert_kt_to_u_closed':
  assumes "closed' K u r"
    and "t \<in> kvs_writers K"
    and "closed_general {t} (r\<inverse>) (visTx' K u \<union> read_only_Txs K)"
  shows "closed' K (insert t u) r" oops


\<comment> \<open>cl_read_invoke_s\<close>
definition RO_le_gst :: "'v global_conf \<Rightarrow> cl_id \<Rightarrow> txid set" where
  "RO_le_gst s cl \<equiv> {t \<in> read_only_Txs (kvs_of_s s). \<exists>t'. t = Tn t' \<and> the (rtxn_rts s t') \<le> gst (cls s cl)}"

lemma get_view_incl_kvs_writers:
  assumes "reach tps_s s"
  shows "(\<Union>k. get_view s cl k) \<subseteq> kvs_writers (kvs_of_s s)" oops

abbreviation vis_RO where
  "vis_RO s cl t \<equiv> (\<exists>x. t \<in> get_view s cl x) \<or> t \<in> RO_le_gst s cl"

lemma cl_read_invoke_vis_RO_inv:
  assumes "reach tps_s s"
    and "reach tps_s s'"
    and "(t, t') \<in> (R_CC (kvs_of_s s))\<^sup>+"
    and "kvs_of_s s' = kvs_of_s s"
  shows "vis_RO s' cl t' \<longrightarrow> vis_RO s' cl t" oops (* not proven *)


\<comment> \<open>cl_read_done_s\<close>
lemma cl_read_done_same_writers:
  assumes "reach tps_s s"
    and "cl_read_done_s cl kv_map sn u'' clk s s'"
  shows "kvs_writers (kvs_of_s s') = kvs_writers (kvs_of_s s)" oops

lemma cl_read_done_t_notin_kvs_writers:
  assumes "reach tps_s s"
    and "cl_read_done_s cl kv_map sn u'' clk s s'"
  shows "Tn (get_txn s cl) \<notin> kvs_writers (kvs_of_s s)" oops

lemma cl_read_done_new_read:
  assumes "reach tps_s s"
    and "cl_read_done_s cl kv_map sn u'' clk s s'"
  shows "read_only_Txs (kvs_of_s s') = insert (Tn (get_txn s cl)) (read_only_Txs (kvs_of_s s))" oops

definition wtxns_readable :: "('v, 'm) global_conf_scheme \<Rightarrow> cl_id \<Rightarrow> key set \<Rightarrow> txid set" where
  "wtxns_readable s cl keys \<equiv> {read_at (svr_state (svrs s k)) (gst (cls s cl)) cl | k. k \<in> keys}"

lemma cl_read_done_WR_onK:
  assumes "reach tps_s s"
    and "cl_read_done_s cl kv_map sn u'' clk s s'"
  shows "R_onK WR (kvs_of_s s') = (wtxns_readable s cl (dom kv_map) \<times> {Tn (Tn_cl sn cl)}) \<union> R_onK WR (kvs_of_s s)"oops

lemma cl_read_done_extend_rel:
  assumes "reach tps_s s"
    and "cl_read_done_s cl kv_map sn u'' clk s s'"
  shows "R_CC (kvs_of_s s') = (\<Union>y\<in>snd ` ran kv_map. {(y, Tn (get_txn s cl))}) \<union> R_CC (kvs_of_s s)" oops


lemma cl_read_done_view_closed:
  assumes "closed' (kvs_of_s s) (\<Union>k. get_view s cl' k) (R_CC (kvs_of_s s))"
    and "kvs_writers (kvs_of_s s') = kvs_writers (kvs_of_s s)"
    and "read_only_Txs (kvs_of_s s') = insert (Tn (get_txn s cl)) (read_only_Txs (kvs_of_s s))"
    and "Tn (get_txn s cl) \<notin> ((R_CC (kvs_of_s s))\<inverse>)\<^sup>* ``
      (visTx' (kvs_of_s s) (\<Union>k. get_view s cl' k))"
    and "R_CC (kvs_of_s s') = (wtxns_readable s cl keys \<times> {Tn (get_txn s cl)}) \<union> R_CC (kvs_of_s s)"
    and "Finite_Keys s cl"
    and "cl_state (cls s cl) = RtxnInProg cclk keys kv_map"
  shows "closed' (kvs_of_s s') (\<Union>k. get_view s cl' k) (R_CC (kvs_of_s s'))"
  oops

\<comment> \<open>cl_write_commit_s\<close>
lemma cl_write_commit_WR_onK:
  assumes "reach tps_s s"
    and "cl_write_commit_s cl kv_map commit_t sn u'' clk mmap s s'"
  shows "R_onK WR (kvs_of_s s') = R_onK WR (kvs_of_s s)" oops

lemma cl_write_commit_same_rel:
  assumes "reach tps_s s"
    and "cl_write_commit_s cl kv_map commit_t sn u'' clk mmap s s'"
  shows "R_CC (kvs_of_s s') = R_CC (kvs_of_s s)" oops


lemma cl_write_commit_view_closed:
  assumes "reach tps_s s"
    and "cl_write_commit_s cl kv_map cts sn u'' clk mmap s s'"
    and "closed' (kvs_of_s s) (\<Union>k. get_view s cl' k) (R_CC (kvs_of_s s))"
    and "closed_general {get_wtxn s cl} ((R_CC (kvs_of_s s))\<inverse>)
          (visTx' (kvs_of_s s) (\<Union>k. get_view s cl' k) \<union> read_only_Txs (kvs_of_s s))"
    and "read_only_Txs (kvs_of_s s') = read_only_Txs (kvs_of_s s)"
    and "kvs_writers (kvs_of_s s') = insert (get_wtxn s cl) (kvs_writers (kvs_of_s s))"
  shows "closed' (kvs_of_s s') (insert (get_wtxn s cl) (\<Union>k. get_view s cl' k)) (R_CC (kvs_of_s s'))"
  oops


subsection \<open>CanCommit\<close>

lemma visTx_visTx':
  "visTx (kvs_of_s s) (view_of (cts_order s) u) = visTx' (kvs_of_s s) (\<Union>k. u k)" oops

lemma closed_closed':
  "closed (kvs_of_s s) (view_of (cts_order s) u) r = closed' (kvs_of_s s) (\<Union>k. u k) r" oops

lemma visTx'_subset_writers: 
  "visTx' (kvs_of_s s) u \<subseteq> kvs_writers (kvs_of_s s)" oops

definition PTid_In_KVS where
  "PTid_In_KVS s cl \<longleftrightarrow> (case cl_state (cls s cl) of
    WtxnCommit _ _ \<Rightarrow> (\<forall>n \<le> cl_sn (cls s cl). Tn (Tn_cl n cl) \<in> kvs_txids (kvs_of_s s)) |
    _ \<Rightarrow> (\<forall>n < cl_sn (cls s cl). Tn (Tn_cl n cl) \<in> kvs_txids (kvs_of_s s)))"

lemma SO_in_kvs_txids:
  assumes "reach tps_s s"
    and "Tn (Tn_cl m cl) \<in> kvs_txids (kvs_of_s s)"
    and "n < m"
  shows "Tn (Tn_cl n cl) \<in> kvs_txids (kvs_of_s s)" oops


subsubsection \<open>View Closed\<close>

definition View_Closed where
  "View_Closed s cl \<longleftrightarrow> closed' (kvs_of_s s) (\<Union>k. get_view s cl k) (R_CC (kvs_of_s s))"
  (* not proven: RInvoke, WCommit *)


subsection \<open>Refinement Proof\<close>
definition invariant_list where
  "invariant_list s \<equiv> (\<forall>cl k. Sqn_Inv_c s cl \<and> Sqn_Inv_nc s cl
    \<and> Views_of_s_Wellformed s cl \<and> Rtxn_Fp_Inv s cl k \<and> CO_Distinct s k
    \<and> T0_in_CO s k \<and> T0_First_in_CO s k \<and> View_Init s cl k \<and> FTid_notin_Get_View s cl)"

end
