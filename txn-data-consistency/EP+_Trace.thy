section \<open>lemmas connecting the trace to tps states\<close>

theory "EP+_Trace"
  imports "EP+" Reductions
begin

datatype 'v ev_i = EVI (evi_tr: "'v ev list") (evi_i: nat)

lemma ev_i_eq_iff: "evi1 = evi2 \<longleftrightarrow> evi_tr evi1 = evi_tr evi2 \<and> evi_i evi1 = evi_i evi2"
  using ev_i.expand by auto

definition cl_ord :: "'v ev rel" where
  "cl_ord \<equiv> {(ev1, ev2). ev_cl ev1 \<noteq> None \<and> ev_cl ev1 = ev_cl ev2}"

definition svr_ord :: "'v ev rel" where
  "svr_ord \<equiv> {(ev1, ev2). ev_key ev1 \<noteq> None \<and> ev_key ev1 = ev_key ev2}"

inductive_set txn_ord :: "'v ev rel" where
  "\<lbrakk>t = Tn_cl sn cl; m = clk\<rbrakk> \<Longrightarrow> (RInvoke cl _ sn clk, RegR _ _ _ _ _ _ m) \<in> txn_ord"
| "\<lbrakk>t = Tn_cl sn cl; m = clk\<rbrakk> \<Longrightarrow> (WInvoke cl _ sn clk, PrepW _ _ _ _ m) \<in> txn_ord"
| "\<lbrakk>t = Tn_cl sn cl; m = clk\<rbrakk> \<Longrightarrow> (WCommit cl _ _ sn _ clk _, CommitW _ _ _ _ _ _ m) \<in> txn_ord"
| "\<lbrakk>t = Tn_cl sn cl; m = (clk, lst)\<rbrakk> \<Longrightarrow> (RegR k t _ _ clk lst _, Read cl k _ _ sn _ m) \<in> txn_ord"
| "\<lbrakk>t = Tn_cl sn cl; mmap k = Some clk\<rbrakk> \<Longrightarrow> (PrepW k t _ clk _, WCommit cl _ _ sn _ _ mmap) \<in> txn_ord"
| "\<lbrakk>t = Tn_cl sn cl; mmap k = Some (clk, lst)\<rbrakk> \<Longrightarrow>(CommitW k t _ _ clk lst _, WDone cl _ sn _ mmap) \<in> txn_ord"

definition causal_dep0 :: "'v ev_i \<Rightarrow> 'v ev_i \<Rightarrow> bool" (infix "\<lesssim>\<^sup>0" 65) where
  "evi\<^sub>1 \<lesssim>\<^sup>0 evi\<^sub>2 \<longleftrightarrow>
    evi_tr evi\<^sub>1 = evi_tr evi\<^sub>2 \<and>
    (evi_tr evi\<^sub>1 ! evi_i evi\<^sub>1, evi_tr evi\<^sub>2 ! evi_i evi\<^sub>2) \<in> cl_ord \<union> svr_ord \<union> txn_ord \<and>
    evi_i evi\<^sub>1 < evi_i evi\<^sub>2"

fun causal_dep :: "'v ev_i \<Rightarrow> 'v ev_i \<Rightarrow> bool" (infix "\<lesssim>" 65) where
  "evi\<^sub>1 \<lesssim> evi\<^sub>2 \<longleftrightarrow> (evi\<^sub>1, evi\<^sub>2) \<in> {(x, y). x \<lesssim>\<^sup>0 y}\<^sup>+"

lemma causal_dep0_tr_eq: "x \<lesssim>\<^sup>0 y \<Longrightarrow> evi_tr x = evi_tr y"
  by (simp add: causal_dep0_def)

lemma causal_dep_tr_eq: "x \<lesssim> y \<Longrightarrow> evi_tr x = evi_tr y"
proof -
  assume a: "x \<lesssim> y"
  then show "evi_tr x = evi_tr y"
    apply (induction x y rule: trancl_trans_induct)
    using a causal_dep0_tr_eq by auto
qed

lemma causal_dep0_ind_lt: "x \<lesssim>\<^sup>0 y \<Longrightarrow> evi_i x < evi_i y"
  by (simp add: causal_dep0_def)

lemma causal_dep_ind_lt: "x \<lesssim> y \<Longrightarrow> evi_i x < evi_i y"
proof -
  assume a: "x \<lesssim> y"
  then show "evi_i x < evi_i y"
    apply (induction x y rule: trancl_trans_induct)
    using a causal_dep0_ind_lt by auto
qed

lemma causal_dep0_nth_append:
  "EVI (\<tau> @ e) j \<lesssim>\<^sup>0 EVI (\<tau> @ e) k \<Longrightarrow> k < length \<tau> \<Longrightarrow> EVI \<tau> j \<lesssim>\<^sup>0 EVI \<tau> k"
  by (auto simp add: causal_dep0_def nth_append)

lemma causal_dep_nth_append:
  "EVI (\<tau> @ e) j \<lesssim> EVI (\<tau> @ e) k \<Longrightarrow> k < length \<tau> \<Longrightarrow> EVI \<tau> j \<lesssim> EVI \<tau> k"
proof -
  assume a: "EVI (\<tau> @ e) j \<lesssim> EVI (\<tau> @ e) k" and b: "k < length \<tau>"
  then show "EVI \<tau> j \<lesssim> EVI \<tau> k"
    apply simp
    apply (induction "EVI (\<tau> @ e) j" "EVI (\<tau> @ e) k" arbitrary: k rule: trancl.induct)
    subgoal by (auto simp add: a causal_dep0_nth_append)
    subgoal for b k apply (cases b)
      using causal_dep0_tr_eq[of b "EVI (\<tau> @ e) k"]
        causal_dep0_ind_lt[of b "EVI (\<tau> @ e) k"]
        causal_dep0_nth_append[of \<tau> e _ k] apply auto
      by (metis mem_Collect_eq old.prod.case trancl.simps)
    done
qed

lemma causal_dep0_nth_append_rev:
  "EVI \<tau> j \<lesssim>\<^sup>0 EVI \<tau> k \<Longrightarrow> k < length \<tau> \<Longrightarrow> EVI (\<tau> @ e) j \<lesssim>\<^sup>0 EVI (\<tau> @ e) k"
  by (simp add: causal_dep0_def nth_append)

lemma causal_dep_nth_append_rev:
  "EVI \<tau> j \<lesssim> EVI \<tau> k \<Longrightarrow> k < length \<tau> \<Longrightarrow> EVI (\<tau> @ e) j \<lesssim> EVI (\<tau> @ e) k"
proof -
  assume "EVI \<tau> j \<lesssim> EVI \<tau> k" and "k < length \<tau>"
  then show "EVI (\<tau> @ e) j \<lesssim> EVI (\<tau> @ e) k"
    apply simp
    apply (induction "EVI \<tau> j" "EVI \<tau> k" arbitrary: k rule: trancl.induct)
    subgoal by (auto simp add: causal_dep0_nth_append_rev)
    subgoal for b k apply (cases b)
      using causal_dep0_tr_eq[of b "EVI \<tau> k"]
        causal_dep0_ind_lt[of b "EVI \<tau> k"]
        causal_dep0_nth_append_rev[of \<tau> _ k] apply auto
      by (metis mem_Collect_eq old.prod.case trancl.simps)
    done
qed

lemma causal_dep0_pres:
  assumes
    \<open>EVI \<tau> i \<lesssim>\<^sup>0 EVI \<tau> j\<close>
    \<open>\<tau>' ! i' = \<tau> ! i\<close>
    \<open>\<tau>' ! j' = \<tau> ! j\<close>
    \<open>i' < j'\<close>
  shows "EVI \<tau>' i' \<lesssim>\<^sup>0 EVI \<tau>' j'"
  using assms
  by (simp add: causal_dep0_def)

lemma causal_dep_swap_pres:
  assumes
    \<open>EVI \<tau> i \<lesssim> EVI \<tau> k\<close>
    \<open>\<tau> = l @ e2 # e1 # l'\<close>
    \<open>\<tau>' = l @ e1 # e2 # l'\<close>
    \<open>\<not> EVI \<tau> (length l) \<lesssim> EVI \<tau> (Suc (length l))\<close>
    \<open>i < k\<close>
    \<open>k < length \<tau>\<close>
  shows "EVI \<tau>' i \<lesssim> EVI \<tau>' k"
proof -
  show ?thesis using assms(1)
    apply simp
    apply (induction "EVI \<tau> i" "EVI \<tau> k" arbitrary: k rule: trancl.induct)
    subgoal for k using assms
      apply simp
      apply (cases "i = length l", auto)
      apply (drule causal_dep0_pres)
      subgoal using assms sorry sorry
    subgoal for b k apply (cases b)
      using causal_dep0_tr_eq[of b "EVI \<tau> k"]
        causal_dep0_ind_lt[of b "EVI \<tau> k"] apply auto
        using causal_dep0_pres[of \<tau> _ k \<tau>'] sorry
    done
qed

\<comment> \<open>For events causal dependencies: (ev, index in trace)\<close>
instantiation ev_i :: (type) order
begin

definition
  less_ev_i_def: "x < y \<longleftrightarrow> x \<lesssim> y"

definition
  less_eq_ev_i_def: "x \<le> y = (x = y \<or> x \<lesssim> y)"

instance proof
  fix x y z :: "('a :: type) ev_i"
  show a: "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    apply (auto simp add: less_ev_i_def less_eq_ev_i_def)
    by (meson causal_dep.elims(3) causal_dep_ind_lt dual_order.irrefl trancl_trans)+
  show "x \<le> x"
    by (auto simp add: less_eq_ev_i_def)
  show "\<lbrakk>x \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> x \<le> z"
    apply (auto simp add: less_eq_ev_i_def)
    by (meson trancl_trans)
  show "\<lbrakk>x \<le> y; y \<le> x\<rbrakk> \<Longrightarrow> x = y"
    apply (auto simp add: less_eq_ev_i_def ev_i_eq_iff)
    apply (metis a causal_dep.elims(3) less_eq_ev_i_def less_ev_i_def)
    by (meson a causal_dep.elims(3) less_eq_ev_i_def less_ev_i_def)
qed
end


subsubsection \<open>Invariants\<close>

definition Wtxn_Cts_Tn_None where
  "Wtxn_Cts_Tn_None s \<longleftrightarrow> (\<forall>cts kv_map cclk keys n cl. 
    (cl_state (cls s cl) \<in> {Idle, WtxnPrep kv_map} \<and> n \<ge> cl_sn (cls s cl)) \<or>
    (cl_state (cls s cl) \<in> {RtxnInProg cclk keys kv_map, WtxnCommit cts kv_map} \<and> n > cl_sn (cls s cl))
     \<longrightarrow> wtxn_cts s (Tn (Tn_cl n cl)) = None)"

lemmas Wtxn_Cts_Tn_NoneI = Wtxn_Cts_Tn_None_def[THEN iffD2, rule_format]
lemmas Wtxn_Cts_Tn_NoneE[elim] = Wtxn_Cts_Tn_None_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_cts_tn_none [simp, intro]: "reach tps s \<Longrightarrow> Wtxn_Cts_Tn_None s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Wtxn_Cts_Tn_None_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Wtxn_Cts_Tn_None_def tps_trans_defs)
qed

definition Wtxn_Cts_None where
  "Wtxn_Cts_None s \<longleftrightarrow> (\<forall>cts kv_map cclk keys t. t \<noteq> T0 \<and> (
    (cl_state (cls s (get_cl_w t)) \<in> {Idle, WtxnPrep kv_map} \<and>
        get_sn_w t \<ge> cl_sn (cls s (get_cl_w t))) \<or>
    (cl_state (cls s (get_cl_w t)) \<in> {RtxnInProg cclk keys kv_map, WtxnCommit cts kv_map} \<and>
        get_sn_w t > cl_sn (cls s (get_cl_w t))))
     \<longrightarrow> wtxn_cts s t = None)"

lemmas Wtxn_Cts_NoneI = Wtxn_Cts_None_def[THEN iffD2, rule_format]
lemmas Wtxn_Cts_NoneE[elim] = Wtxn_Cts_None_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_cts_none [simp, intro]: "reach tps s \<Longrightarrow> Wtxn_Cts_None s"
  apply (simp add: Wtxn_Cts_None_def)
  apply rule+ subgoal for cts kv_map cclk keys t apply (cases t)
    apply metis using Wtxn_Cts_Tn_None_def[of s]
    by (smt get_cl_w.simps(2) get_sn_w.simps(2) insert_iff reach_wtxn_cts_tn_none txid0.exhaust).

definition Wtxn_Cts_T0 where
  "Wtxn_Cts_T0 s \<longleftrightarrow> wtxn_cts s T0 = Some 0"

lemmas Wtxn_Cts_T0I = Wtxn_Cts_T0_def[THEN iffD2, rule_format]
lemmas Wtxn_Cts_T0E[elim] = Wtxn_Cts_T0_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_cts_t0 [simp, dest]: "reach tps s \<Longrightarrow> Wtxn_Cts_T0 s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Wtxn_Cts_T0_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Wtxn_Cts_T0_def tps_trans_defs)
qed

definition CO_Tid where
  "CO_Tid s cl \<longleftrightarrow> (case cl_state (cls s cl) of
    WtxnCommit cts kv_map \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow> n \<le> cl_sn (cls s cl))
  | _ \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow> n < cl_sn (cls s cl)))"

lemmas CO_TidI = CO_Tid_def[THEN iffD2, rule_format]
lemmas CO_TidE[elim] = CO_Tid_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_tid[simp]: "reach tps s \<Longrightarrow> CO_Tid s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: CO_Tid_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RDone x1 x2 x3 x4 x5)
    then show ?case apply (simp add: CO_Tid_def tps_trans_defs split: txn_state.split_asm)
      using less_SucI less_Suc_eq_le by blast+
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: CO_Tid_def tps_trans_all_defs set_insort_key split: txn_state.split_asm)
      apply (metis txn_state.distinct(3))
      apply (metis txn_state.distinct(7))
      apply (meson less_or_eq_imp_le)
      by blast
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case apply (simp add: CO_Tid_def tps_trans_defs split: txn_state.split_asm)
      apply (meson less_SucI)+
      by (meson linorder_le_less_linear not_less_eq_eq)
  qed (auto simp add: CO_Tid_def tps_trans_defs split: txn_state.split_asm)
qed

definition Dom_Kv_map_non_Emp where
  "Dom_Kv_map_non_Emp s cl \<longleftrightarrow>
    (\<forall>kv_map cts. cl_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map} \<longrightarrow>
      (\<exists>k v. kv_map k = Some v))"
                                                           
lemmas Dom_Kv_map_non_EmpI = Dom_Kv_map_non_Emp_def[THEN iffD2, rule_format]
lemmas Dom_Kv_map_non_EmpE[elim] = Dom_Kv_map_non_Emp_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_dom_kv_map_non_emp [simp]: "reach tps s \<Longrightarrow> Dom_Kv_map_non_Emp s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Dom_Kv_map_non_Emp_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Dom_Kv_map_non_Emp_def tps_trans_defs)
qed

definition Finite_Dom_Kv_map where
  "Finite_Dom_Kv_map s cl \<longleftrightarrow>
    (\<forall>kv_map cts. cl_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map} \<longrightarrow>
      finite (dom (kv_map)))"
                                                           
lemmas Finite_Dom_Kv_mapI = Finite_Dom_Kv_map_def[THEN iffD2, rule_format]
lemmas Finite_Dom_Kv_mapE[elim] = Finite_Dom_Kv_map_def[THEN iffD1, elim_format, rule_format]
         
lemma reach_finite_dom_kv_map [simp]: "reach tps s \<Longrightarrow> Finite_Dom_Kv_map s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Finite_Dom_Kv_map_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Finite_Dom_Kv_map_def tps_trans_defs)
qed

subsection \<open>Lemmas\<close>

lemma trace_cts_order_tps:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>init tps s\<close>
  shows "Tn (Tn_cl sn cl) \<in> set (cts_order s' k) \<longleftrightarrow>
    (\<exists>kv_map cts u'' clk mmap. k \<in> dom kv_map \<and> WCommit cl kv_map cts sn u'' clk mmap \<in> set \<tau>)"
  using assms(1)
proof (induction \<tau> s' rule: trace.induct)
  case trace_nil
  then show ?case using assms(2) by (simp add: tps_defs)
next
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: tps_trans_all_defs set_insort_key)
      by (metis domIff option.discI)
  qed (auto simp add: tps_trans_defs)
qed

lemma wtxn_cts_immutable:
  assumes
    \<open>wtxn_cts s t = Some c\<close>
    \<open>tps: s \<midarrow>e\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
  shows
    \<open>wtxn_cts s' t = Some c\<close>
  using assms
proof (induction e)
  case (WCommit x1 x2 x3 x4 x5)
  then show ?case apply (simp add: write_commit_def write_commit_U_def write_commit_G_def)
    apply (cases "t = get_wtxn s x1", auto) using Wtxn_Cts_Tn_None_def
    by (metis (lifting) reach_wtxn_cts_tn_none domI domIff insertCI less_imp_neq linorder_not_le)
qed (auto simp add: tps_trans_defs)

lemma WC_in_\<tau>_wtxn_cts:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>WCommit cl kv_map cts sn u'' clk mmap \<in> set \<tau>\<close>
  shows "wtxn_cts s' (Tn (Tn_cl sn cl)) = Some cts"
  using assms
proof (induction \<tau> s' arbitrary: cl kv_map cts sn u'' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: set_insort_key)
      subgoal by (simp add: tps_trans_all_defs) 
      subgoal using wtxn_cts_immutable[of s' "Tn (Tn_cl sn cl)" cts "WCommit x1 x2 x3 x4 x5 x6 x7" s'']
        apply (simp add: trace_is_trace_of_exec_frag reach_last_exec valid_exec_def)
        apply (cases "get_txn s' x1 = Tn_cl sn cl")
        apply (meson valid_exec_frag_append)
        by (auto simp add: tps_trans_all_defs)
      done
  qed (auto simp add: tps_trans_defs)
qed simp

lemma WC_in_\<tau>_kv_map_non_emp:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>WCommit cl kv_map cts sn u'' clk mmap \<in> set \<tau>\<close>
  shows "\<exists>k v. kv_map k = Some v"
  using assms
proof (induction \<tau> s' arbitrary: cl kv_map cts sn u'' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case using Dom_Kv_map_non_Emp_def[of s' x1]
    by (auto simp add: reach_trace_extend tps_trans_defs)
  qed (auto simp add: tps_trans_defs)
qed simp


subsubsection \<open>cl_ord clock invariant\<close>
lemma cl_clock_monotonic:
  "state_trans s e s' \<Longrightarrow> cl_clock (cls s' cl) \<ge> cl_clock (cls s cl)"
  by (induction e) (auto simp add: tps_trans_defs)

lemma last_clk_max_in_cl:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>ev_cl (\<tau> ! i) = Some cl\<close>
    \<open>i < length \<tau>\<close>
  shows \<open>ev_clk (\<tau> ! i) \<le> cl_clock (cls s' cl)\<close>
  using assms
proof (induction \<tau> s' arbitrary: i rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (cases "i = length \<tau>")
    case True
    then show ?thesis using trace_snoc
      by (induction e) (auto simp add: tps_trans_defs)
  next
    case False
    then show ?thesis using trace_snoc
      apply (simp add: nth_append)
      using cl_clock_monotonic le_trans not_less_less_Suc_eq by blast
  qed
qed simp

lemma cl_ord_implies_clk_order:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>(\<tau> ! j, \<tau> ! k) \<in> cl_ord\<close>
    \<open>j < k\<close>
    \<open>k < length \<tau>\<close>
  shows \<open>ev_clk (\<tau> ! j) < ev_clk (\<tau> ! k)\<close>
  using assms
proof (induction \<tau> s' arbitrary: j k rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (cases "k = length \<tau>")
    case True
    then show ?thesis using trace_snoc
      by (induction e)
        (auto simp add: tps_trans_defs nth_append cl_ord_def last_clk_max_in_cl le_imp_less_Suc,
          ((meson last_clk_max_in_cl le_imp_less_Suc le_trans max.coboundedI1)+)?)
  next
    case False
    then show ?thesis using trace_snoc by (simp add: nth_append)
  qed
qed simp


subsubsection \<open>svr_ord clock invariant\<close>
lemma svr_clock_monotonic:
  "state_trans s e s' \<Longrightarrow> svr_clock (svrs s' svr) \<ge> svr_clock (svrs s svr)"
  by (induction e) (auto simp add: tps_trans_defs)

lemma last_clk_max_in_svr:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>ev_key (\<tau> ! i) = Some k\<close>
    \<open>i < length \<tau>\<close>
  shows \<open>ev_clk (\<tau> ! i) \<le> svr_clock (svrs s' k)\<close>
  using assms
proof (induction \<tau> s' arbitrary: i rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (cases "i = length \<tau>")
    case True
    then show ?thesis using trace_snoc
      by (induction e) (auto simp add: tps_trans_defs)
  next
    case False
    then show ?thesis using trace_snoc
      apply (simp add: nth_append)
      using svr_clock_monotonic le_trans not_less_less_Suc_eq by blast
  qed
qed simp

lemma svr_ord_implies_clk_order:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>(\<tau> ! j, \<tau> ! k) \<in> svr_ord\<close>
    \<open>j < k\<close>
    \<open>k < length \<tau>\<close>
  shows \<open>ev_clk (\<tau> ! j) < ev_clk (\<tau> ! k)\<close>
  using assms
proof (induction \<tau> s' arbitrary: j k rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (cases "k = length \<tau>")
    case True
    then show ?thesis using trace_snoc
      by (induction e)
        (auto simp add: tps_trans_defs nth_append svr_ord_def last_clk_max_in_svr le_imp_less_Suc,
          ((meson last_clk_max_in_svr le_imp_less_Suc le_trans max.coboundedI1)+)?)
  next
    case False
    then show ?thesis using trace_snoc by (simp add: nth_append)
  qed
qed simp


subsubsection \<open>txn_ord clock invariant\<close>
lemma helper:
  "x k = Some y \<Longrightarrow> finite (dom x) \<Longrightarrow> f k < Suc (max A (Max {f k |k. k \<in> dom x}))"
  apply (simp add: Setcompr_eq_image)
  by (metis Max.coboundedI domI finite_imageI le_imp_less_Suc max.coboundedI1 max.commute not_in_image)

lemma sc_ord_implies_clk_order:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>(\<tau> ! j, \<tau> ! k) \<in> txn_ord\<close>
    \<open>j < k\<close>
    \<open>k < length \<tau>\<close>
  shows \<open>ev_clk (\<tau> ! j) < ev_clk (\<tau> ! k)\<close>
  using assms
proof (induction \<tau> s' arbitrary: j k rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (cases "k = length \<tau>")
    case True
    then show ?thesis using trace_snoc
    proof (induction e)
      case (Read x1 x2 x3 x4 x5 x6 x7)
      then show ?case 
      proof (cases "\<tau> ! j")
        case (RegR x71 x72 x73 x74 x75 x76 x77)
        then show ?thesis using Read by (simp add: nth_append txn_ord.simps tps_trans_defs)
      qed (simp_all add: nth_append txn_ord.simps)
    next
      case (WCommit x1 x2 x3 x4 x5 x6 x7)
      then show ?case 
      proof (cases "\<tau> ! j")
        case (PrepW x81 x82 x83 x84 x85)
        then show ?thesis using WCommit
          apply (auto simp add: nth_append txn_ord.simps tps_trans_defs)
          using Finite_Dom_Kv_map_def[of s' x1]
            helper[of x2 x81 _ "\<lambda>k. get_ts (svr_state (svrs s' k) (get_wtxn s' x1))"] 
          apply simp
          by (smt not_None_eq option.inject reach_finite_dom_kv_map reach_trace_extend)
      qed (simp_all add: nth_append txn_ord.simps)
    next
      case (WDone x1 x2 x3 x4 x5)
      then show ?case 
      proof (cases "\<tau> ! j")
        case (CommitW x91 x92 x93 x94 x95 x96 x97)
        then show ?thesis using WDone
          apply (cases "x2 x91", auto simp add: nth_append txn_ord.simps tps_trans_defs)
          using Finite_Dom_Kv_map_def[of s' x1]
            helper[of x2 x91 _ "\<lambda>k. get_sclk (svr_state (svrs s' k) (get_wtxn s' x1))"] 
          apply simp
          by (smt (verit) reach_finite_dom_kv_map reach_trace_extend)
         qed (simp_all add: nth_append txn_ord.simps)
    next
      case (RegR x1 x2 x3 x4 x5 x6 x7)
      then show ?case 
      proof (cases "\<tau> ! j")
        case (RInvoke x11 x12 x13 x14)
        then show ?thesis using RegR by (auto simp add: nth_append txn_ord.simps tps_trans_defs)
      qed (simp_all add: nth_append txn_ord.simps)
    next
      case (PrepW x1 x2 x3 x4 x5)
      then show ?case 
      proof (cases "\<tau> ! j")
        case (WInvoke x41 x42 x43 x44)
        then show ?thesis using PrepW by (auto simp add: nth_append txn_ord.simps tps_trans_defs)
      qed (simp_all add: nth_append txn_ord.simps)
    next
      case (CommitW x1 x2 x3 x4 x5 x6 x7)
      then show ?case 
      proof (cases "\<tau> ! j")
        case (WCommit x51 x52 x53 x54 x55 x56 x57)
        then show ?thesis using CommitW by (auto simp add: nth_append txn_ord.simps tps_trans_defs)
      qed (simp_all add: nth_append txn_ord.simps)
    qed (auto simp add: txn_ord.simps)
  next
    case False
    then show ?thesis using trace_snoc by (simp add: nth_append)
  qed
qed simp


subsubsection \<open>causal_dep clock invariant\<close>
lemma causal_dep0_implies_clk_order:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>EVI \<tau> j \<lesssim>\<^sup>0 EVI \<tau> k\<close>
    \<open>k < length \<tau>\<close>
  shows \<open>ev_clk (\<tau> ! j) < ev_clk (\<tau> ! k)\<close>
  using assms
proof (induction \<tau> s' arbitrary: j k rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (cases "k = length \<tau>")
    case True
    then show ?thesis using trace_snoc
        causal_dep0_nth_append[of \<tau>]
        causal_dep0_ind_lt[of "EVI (\<tau> @ [e]) j" "EVI (\<tau> @ [e]) k"]
      apply (auto simp add: causal_dep0_def)
      subgoal by (metis (mono_tags, lifting) cl_ord_implies_clk_order nth_append_length
          trace.trace_snoc trace_snoc.hyps(2) trace_snoc.prems(3)) \<comment> \<open>cl_ord\<close>
      subgoal by (metis (mono_tags, lifting) svr_ord_implies_clk_order nth_append_length
          trace.trace_snoc trace_snoc.hyps(2) trace_snoc.prems(3)) \<comment> \<open>svr_ord\<close>
      subgoal by (metis (no_types, lifting) sc_ord_implies_clk_order nth_append_length
            trace.trace_snoc trace_snoc.hyps(2) trace_snoc.prems(3)) \<comment> \<open>txn_ord\<close>
      done
  next
    case False
    then show ?thesis using trace_snoc
        causal_dep0_nth_append[of \<tau>]
        causal_dep0_ind_lt[of "EVI (\<tau> @ [e]) j" "EVI (\<tau> @ [e]) k"]
      by (simp add: nth_append)
    qed
qed simp


lemma causal_dep_implies_clk_order:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>EVI \<tau> j < EVI \<tau> k\<close>
    \<open>k < length \<tau>\<close>
  shows \<open>ev_clk (\<tau> ! j) < ev_clk (\<tau> ! k)\<close>
  using assms(3-)
  apply (simp add: less_ev_i_def)
  apply (induction "EVI \<tau> j" "EVI \<tau> k" arbitrary: k rule: trancl.induct)
  subgoal using assms(1,2) causal_dep0_implies_clk_order by blast
  subgoal for b k apply (cases b)
    using assms(1,2) causal_dep0_tr_eq[of b "EVI \<tau> k"]
      causal_dep0_ind_lt[of b "EVI \<tau> k"] apply auto
    by (smt (verit, best) add_diff_inverse_nat causal_dep0_implies_clk_order less_SucI
        not_less_eq trans_less_add1)
  done


lemma WCommit_clk_Suc_cts:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>i < length \<tau>\<close>
    \<open>\<tau> ! i = WCommit cl kv_map cts sn u'' clk mmap\<close>
  shows \<open>clk = Suc cts\<close>
  using assms
proof (induction \<tau> s' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6)
    then show ?case
      apply (cases "i = length \<tau>", simp add: tps_trans_defs)
      by (simp add: length_append_singleton not_less_less_Suc_eq nth_append)
  qed (simp_all, (smt ev.distinct less_SucE nth_append nth_append_length)+)
qed simp

lemma WCommit_cts_causal_dep_gt_past:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>k < length \<tau>\<close>
    \<open>\<tau> ! j = WCommit cl kv_map cts sn u'' clk mmap\<close>
    \<open>\<tau> ! k = WCommit cl' kv_map' cts' sn' u''' clk' mmap'\<close>
    \<open>EVI \<tau> j < EVI \<tau> k\<close>
  shows \<open>(cts, Suc cl) < (cts', Suc cl')\<close>
  using assms
proof (induction \<tau> s' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6)
    then show ?case apply (simp add: less_prod_def) using WCommit_clk_Suc_cts
    by (smt (verit) add_less_imp_less_left assms causal_dep_implies_clk_order causal_dep_ind_lt
        ev_clk.simps(5) ev_i.sel(2) less_ev_i_def less_trans_Suc nth_append plus_1_eq_Suc)
  qed (simp_all, (smt (verit) Suc_less_SucD causal_dep_ind_lt causal_dep_nth_append ev.distinct
          ev_i.sel(2) less_ev_i_def less_trans_Suc not_less_less_Suc_eq nth_append nth_append_length')+)
qed simp


end