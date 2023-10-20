section \<open>EP+ Event System for well-sorted executions\<close>

theory "EP+_Sorted"
  imports "EP+" "EP+_Reduction"
begin

\<comment> \<open>Updated Events\<close>

definition read_done_G_s where
  "read_done_G_s cl kv_map sn u'' s \<equiv>
    read_done_G cl kv_map sn s \<and>
    u'' = view_of (cts_order s) (get_view s cl)"

definition read_done_s :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "read_done_s cl kv_map sn u'' s s' \<equiv>
    read_done_G_s cl kv_map sn u'' s \<and>
    s' = read_done_U cl kv_map s"

definition write_commit_G_s where
  "write_commit_G_s cl kv_map cts sn u'' s \<equiv>
    write_commit_G cl kv_map cts sn s \<and>
    u'' = view_of (cts_order s) (get_view s cl) \<and>
    (\<forall>k\<comment>\<open>\<in> dom kv_map\<close>. \<forall>t \<in> set (cts_order s k). ects cts cl \<ge> unique_ts (wtxn_cts s) t)"
  \<comment> \<open>It's actually > but we don't need to enforce it here since \<ge> already works and is what Good_wrt defines\<close>

definition write_commit_s :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> tstmp \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "write_commit_s cl kv_map cts sn u'' s s' \<equiv>
    write_commit_G_s cl kv_map cts sn u'' s \<and> 
    s' = write_commit_U cl kv_map cts s"


subsection \<open>The Event System\<close>

fun state_trans :: "('v, 'm) global_conf_scheme \<Rightarrow> 'v ev \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "state_trans s (RInvoke cl keys sn)           s' \<longleftrightarrow> read_invoke cl keys sn s s'" |
  "state_trans s (Read cl k v t rts rlst sn)    s' \<longleftrightarrow> read cl k v t rts rlst sn s s'" |
  "state_trans s (RDone cl kv_map sn u'')       s' \<longleftrightarrow> read_done_s cl kv_map sn u'' s s'" |
  "state_trans s (WInvoke cl kv_map sn)         s' \<longleftrightarrow> write_invoke cl kv_map sn s s'" |
  "state_trans s (WCommit cl kv_map cts sn u'') s' \<longleftrightarrow> write_commit_s cl kv_map cts sn u'' s s'" |
  "state_trans s (WDone cl kv_map sn)           s' \<longleftrightarrow> write_done cl kv_map sn s s'" |
  "state_trans s (RegR svr t t_wr rts)          s' \<longleftrightarrow> register_read svr t t_wr rts s s'" |
  "state_trans s (PrepW svr t v)                s' \<longleftrightarrow> prepare_write svr t v s s'" |
  "state_trans s (CommitW svr t v cts)          s' \<longleftrightarrow> commit_write svr t v cts s s'" |
  "state_trans s Skip2                          s' \<longleftrightarrow> s' = s"

definition tps_s :: "('v ev, 'v global_conf) ES" where
  "tps_s \<equiv> \<lparr>
    init = \<lambda>s. s = state_init,
    trans = state_trans
  \<rparr>"

lemmas tps_trans_top_defs = 
  read_invoke_def read_def read_done_s_def write_invoke_def write_commit_s_def
  write_done_def register_read_def prepare_write_def commit_write_def

lemmas tps_trans_GU_defs = 
  read_invoke_G_def read_invoke_U_def
  read_G_def read_U_def
  read_done_G_def read_done_U_def read_done_G_s_def
  write_invoke_G_def write_invoke_U_def
  write_commit_G_def write_commit_U_def write_commit_G_s_def
  write_done_G_def write_done_U_def
  register_read_G_def register_read_U_def
  prepare_write_G_def prepare_write_U_def
  commit_write_G_def commit_write_U_def

lemmas tps_trans_defs = tps_trans_top_defs tps_trans_GU_defs

lemmas tps_trans_all_defs = tps_trans_defs ext_corder_def

lemmas tps_s_defs = tps_s_def state_init_def

lemma tps_trans [simp]: "trans tps_s = state_trans" by (simp add: tps_s_def)


subsection \<open>Simulation function\<close>

term "Set.filter (is_done s) rs"

definition txn_to_vers :: "('v, 'm) global_conf_scheme \<Rightarrow> key \<Rightarrow> txid \<Rightarrow> 'v version" where
  "txn_to_vers s k = (\<lambda>t. case svr_state (svrs s k) t of
    Prep ts v \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = {}\<rparr> |
    Commit cts ts lst v rs \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = {t. \<exists>rts rlst. (t, rts, rlst) \<in> rs \<and> is_done s t}\<rparr>)"

definition kvs_of_s :: "'v global_conf \<Rightarrow> 'v kv_store" where
  "kvs_of_s s \<equiv> (\<lambda>k. map (txn_to_vers s k) (cts_order s k))"

lemmas kvs_of_s_defs = kvs_of_s_def txn_to_vers_def

definition views_of_s :: "'v global_conf \<Rightarrow> (cl_id \<Rightarrow> view)" where
  "views_of_s s = (\<lambda>cl. view_of (cts_order s) (get_view s cl))"

definition sim :: "'v global_conf \<Rightarrow> 'v config" where         
  "sim s = (kvs_of_s s, views_of_s s)"

lemmas sim_defs = sim_def kvs_of_s_defs views_of_s_def

subsection \<open>Mediator function\<close>

fun med :: "'v ev \<Rightarrow> 'v label" where
  "med (RDone cl kv_map sn u'') = ET cl sn u'' (read_only_fp kv_map)" |
  "med (WCommit cl kv_map _ sn u'') = ET cl sn u'' (write_only_fp kv_map)" |
  "med _ = ETSkip"

subsection \<open>Reduction: reachable states equivalence\<close>

subsubsection \<open>Invariants\<close>
definition Wtxn_Cts_T0 where
  "Wtxn_Cts_T0 s k \<longleftrightarrow> wtxn_cts s T0 = Some 0"

lemmas Wtxn_Cts_T0I = Wtxn_Cts_T0_def[THEN iffD2, rule_format]
lemmas Wtxn_Cts_T0E[elim] = Wtxn_Cts_T0_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_cts_t0 [simp, dest]: "reach tps_s s \<Longrightarrow> Wtxn_Cts_T0 s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Wtxn_Cts_T0_def tps_s_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Wtxn_Cts_T0_def tps_trans_defs)
qed


subsubsection \<open>Lemmas\<close>

\<comment> \<open>tps_s \<longrightarrow> good execs\<close> 
lemma tps_s_ev_sub_tps:
  "tps_s: s\<midarrow>e\<rightarrow> s' \<Longrightarrow> tps: s\<midarrow>e\<rightarrow> s'"
  by (induction e) (auto simp add: read_done_s_def read_done_def read_done_G_s_def
      write_commit_s_def write_commit_def write_commit_G_s_def)

lemma reach_good_state_f_None:
  "\<lbrakk> tps_s: s \<midarrow>e\<rightarrow> s'; reach tps_s s; ev_ects e = None; reach_good_state tps ev_ects s \<rbrakk> \<Longrightarrow> 
     reach_good_state tps ev_ects s'"
  apply (auto simp add: reach_good_state_def valid_exec_def tps_def)
  subgoal for efl
  apply (intro exI[where x="efl @ [(s, e, s')]"], auto simp add: efrag_snoc_good)
    using tps_s_ev_sub_tps vef_snoc by fastforce.

lemma reach_good_state_f_Some:
  "\<lbrakk> Exec_frag s0 efl s \<in> Good_wrt ev_ects; ev_ects e = Some (cts, Suc cl);
     \<forall>i < length (trace_of_efrag (Exec_frag s0 efl s)). \<forall>cts' cl'.
       ev_ects (trace_of_efrag (Exec_frag s0 efl s) ! i) = Some (cts', cl')
        \<longrightarrow> (cts, Suc cl) > (cts', cl')\<rbrakk>
    \<Longrightarrow> Exec_frag s0 (efl @ [(s, e, s')]) s' \<in> Good_wrt ev_ects"
  apply (auto simp add: Good_wrt_def inverted_pairs_def trace_of_efrag_append nth_append)
  by (metis less_antisym order.asym)

\<comment> \<open>good execs \<longrightarrow> tps_s\<close>
lemma tps_non_commit_ev_sub_tps_s:
  "tps: s\<midarrow>e\<rightarrow> s' \<Longrightarrow> \<not>commit_ev e  \<Longrightarrow> tps_s: s\<midarrow>e\<rightarrow> s'"
  by (induction e) (auto)

lemma tps_RDone_sub_tps_s:
  "tps: s\<midarrow>RDone cl kv_map sn u''\<rightarrow> s' \<Longrightarrow>
   tps_s: s\<midarrow>RDone cl kv_map sn (view_of (cts_order s) (get_view s cl))\<rightarrow> s'"
  by (simp add: read_done_def read_done_s_def read_done_G_s_def)

lemma min_ects: "(0, 0) < ects x y" by (auto simp add: less_prod_def ects_def)

lemma efrag_snoc_good_def:
  "Exec_frag state_init (efl @ [(s, e, s')]) s' \<in> Good_wrt ev_ects \<longleftrightarrow>
    (\<forall>j i. j < Suc (length (trace_of_efrag (Exec_frag state_init efl s))) \<longrightarrow> i < j \<longrightarrow>
     (\<forall>cts cl. ev_ects ((trace_of_efrag (Exec_frag state_init efl s) @ [e]) ! j) = Some (cts, cl) \<longrightarrow>
     (\<forall>cts' cl'. ev_ects (trace_of_efrag (Exec_frag state_init efl s) ! i) = Some (cts', cl') \<longrightarrow>
           \<not> (cts, cl) < (cts', cl'))))"
  by (auto simp add: Good_wrt_def inverted_pairs_def trace_of_efrag_append nth_append)

lemma new_wrc_no_conflict:
  "\<lbrakk> Exec_frag state_init (efl @ [(s, e, s')]) s' \<in> Good_wrt ev_ects;
     ev_ects e = Some (cts, cl);
     i < length efl;
     ev_ects (trace_of_efrag (Exec_frag state_init efl s) ! i) = Some (cts', cl') \<rbrakk>
     \<Longrightarrow> (cts, cl) \<ge> (cts', cl')"
  unfolding efrag_snoc_good_def
  by (metis lessI linorder_le_less_linear nth_append_length trace_of_efrag_length)


lemma init_tps_tps_s_eq:
  "init tps_s s \<longleftrightarrow> init tps s"
  by (simp add: tps_def tps_s_defs)

lemma trace_cts_order_tps_s:
  assumes
    \<open>tps_s: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>init tps_s s\<close>
  shows "Tn (Tn_cl sn cl) \<in> set (cts_order s' k) \<longleftrightarrow>
    (\<exists>kv_map cts u''. k \<in> dom kv_map \<and> WCommit cl kv_map cts sn u'' \<in> set \<tau>)"
  using assms(1)
proof (induction \<tau> s' rule: trace.induct)
  case trace_nil
  then show ?case using assms(2) by (simp add: tps_s_defs)
next
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: tps_trans_all_defs set_insort_key)
      by (metis domIff option.discI)
  qed (auto simp add: tps_trans_defs)
qed

lemma trace_cts_order_tps:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>init tps s\<close>
  shows "Tn (Tn_cl sn cl) \<in> set (cts_order s' k) \<longleftrightarrow>
    (\<exists>kv_map cts u''. k \<in> dom kv_map \<and> WCommit cl kv_map cts sn u'' \<in> set \<tau>)"
  using assms(1)
proof (induction \<tau> s' rule: trace.induct)
  case trace_nil
  then show ?case using assms(2) by (simp add: tps_defs)
next
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: "EP+.tps_trans_all_defs" set_insort_key)
      by (metis domIff option.discI)
  qed (auto simp add: "EP+.tps_trans_defs")
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
qed (auto simp add: "EP+.tps_trans_defs")

lemma WC_in_\<tau>_wtxn_cts:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>init tps s\<close>
  shows " WCommit cl kv_map cts sn u'' \<in> set \<tau> \<Longrightarrow> wtxn_cts s' (Tn (Tn_cl sn cl)) = Some cts"
  using assms
proof (induction \<tau> s' arbitrary: cl kv_map cts sn u'' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: set_insort_key)
      subgoal by (simp add: "EP+.tps_trans_all_defs") 
      subgoal using wtxn_cts_immutable[of s' "Tn (Tn_cl sn cl)" cts "WCommit x1 x2 x3 x4 x5" s'']
        apply (simp add: trace_is_trace_of_exec_frag reach_last_exec valid_exec_def)
        apply (cases "get_txn s' x1 = Tn_cl sn cl")
        by (auto simp add: "EP+.tps_trans_all_defs")
      done
  qed (auto simp add: "EP+.tps_trans_defs")
qed simp

lemma tps_WCommit_sub_tps_s:
  "\<lbrakk> tps: s\<midarrow>WCommit cl kv_map cts sn u''\<rightarrow> s';
     reach tps_s s; init tps s0;
     valid_exec_frag tps (Exec_frag s0 efl s);
     Exec_frag s0 (efl @ [(s, WCommit cl kv_map cts sn u'', s')]) s' \<in> Good_wrt ev_ects\<rbrakk>
    \<Longrightarrow> tps_s: s\<midarrow>WCommit cl kv_map cts sn (view_of (cts_order s) (get_view s cl))\<rightarrow> s'"
    apply (auto simp add: write_commit_s_def write_commit_def write_commit_G_s_def unique_ts_def')
    subgoal using Wtxn_Cts_T0_def[of s] by (simp add: min_ects order_less_imp_le)
    subgoal for _ t
      apply (cases t, simp) subgoal for x2 apply (cases x2)
      using valid_exec_frag_is_trace[of tps s0 efl s] trace_cts_order_tps[of s0]
      apply (auto simp add: init_tps_tps_s_eq)
      using exec_frag_good_ects[of s0 efl s _ s' ev_ects]
      by (simp add: WC_in_\<tau>_wtxn_cts tps_def).
    done

lemma reach_tps_s_non_commit:
  "\<lbrakk> tps: s \<midarrow>e\<rightarrow> s';
    \<not>commit_ev e;
    \<lbrakk> init tps s0; Exec_frag s0 efl s \<in> Good_wrt ev_ects \<rbrakk> \<Longrightarrow> reach tps_s s;
    Exec_frag s0 (efl @ [(s, e, s')]) s' \<in> Good_wrt ev_ects;
    init tps s0\<rbrakk>
    \<Longrightarrow> reach tps_s s'"
  by (metis tps_non_commit_ev_sub_tps_s efrag_trim_good reach_trans)


lemma ev_ects_some:
  "ev_ects (trace_of_efrag (Exec_frag state_init efl s) ! i) = Some (cts, cl) \<Longrightarrow>
  \<exists>cl' kv_map sn u''. trace_of_efrag (Exec_frag state_init efl s) ! i = WCommit cl' kv_map cts sn u'' \<and> cl = Suc cl'"
  by (cases "trace_of_efrag (Exec_frag state_init efl s) ! i", simp_all add: ects_def)

lemma "i < length (trace_of_efrag ef) \<and> valid_exec E ef \<and> trace_of_efrag ef ! i = e \<Longrightarrow>
  (let s = (states_of_efrag ef ! i); s' = (states_of_efrag ef ! Suc i) in
   reach E s \<and> E: s\<midarrow>e\<rightarrow> s' \<and> reach E (ef_last ef))"
  using id_take_nth_drop [of i "ef_list ef"]
  apply (auto simp add: reach_last_exec valid_exec_def Let_def trace_of_efrag_length)
    apply (intro exI[where x="ef_first ef"], simp)
    apply (intro exI[where x="take i (ef_list ef)"], simp add: states_of_efrag_def) oops

definition WCommit_in_Trace where
  "WCommit_in_Trace s k \<longleftrightarrow> (\<forall>efl :: ('v global_conf \<times> 'v ev \<times> 'v global_conf) list.
   \<forall>i cl kv_map cts sn u''. valid_exec_frag tps_s (Exec_frag state_init efl s) \<and> i < length efl \<and>
   trace_of_efrag (Exec_frag state_init efl s) ! i = WCommit cl kv_map cts sn u'' \<and> k \<in> dom kv_map \<longrightarrow>
   Tn (Tn_cl sn cl) \<in> set (cts_order s k) \<and> wtxn_cts s (Tn (Tn_cl sn cl)) = Some cts)"

lemmas WCommit_in_TraceI = WCommit_in_Trace_def[THEN iffD2, rule_format]
lemmas WCommit_in_TraceE[elim] = WCommit_in_Trace_def[THEN iffD1, elim_format, rule_format]

lemma reach_pend_wt_ub [simp]: "reach tps_s s \<Longrightarrow> WCommit_in_Trace s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    apply (auto simp add: WCommit_in_Trace_def tps_s_def) apply (rotate_tac 1)
    subgoal for efl
      apply (induction "Exec_frag state_init efl state_init" arbitrary: efl rule: valid_exec_frag.induct, simp)
      sorry sorry
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e) oops


subsubsection \<open>Proof reach tps_s = reach E\<close>

lemma "reach tps_s s \<longleftrightarrow> reach_good_state tps ev_ects s"
  unfolding reach_good_state_def valid_exec_def
proof (intro iffI; clarsimp simp only: exec_frag.sel)
  assume \<open>reach tps_s s\<close>
  then show \<open>\<exists>s0 efl. (valid_exec_frag tps (Exec_frag s0 efl s) \<and> init tps s0) \<and> Exec_frag s0 efl s \<in> Good_wrt ev_ects\<close>
  proof (induction rule: reach.induct)
    case (reach_init s)
    then show ?case
      by (auto simp add: reach_good_state_def valid_exec_def tps_s_def tps_def Good_wrt_def
          trace_of_efrag_def inverted_pairs_def)
  next
    case (reach_trans s e s')
    then show ?case using reach_good_state_f_None[of s e s']
      unfolding reach_good_state_def valid_exec_def
    proof (induction e)
      case (WCommit x1 x2 x3 x4 x5)
      then show ?case apply (auto simp add: tps_def)
        subgoal for efl
        apply (intro exI[where x="efl @ [(s, WCommit x1 x2 x3 x4 x5, s')]"], auto)
           apply (metis WCommit.prems(1) tps_def tps_s_ev_sub_tps vef_snoc)
          apply (auto dest!: reach_good_state_f_Some[of _ efl])
          apply (thin_tac "Exec_frag _ _ _ \<notin> _ _")
          apply (auto simp add: Good_wrt_def inverted_pairs_def trace_of_efrag_append write_commit_s_def
              write_commit_G_s_def unique_ts_def' nth_append dest!: ev_ects_some)
          apply (auto simp add: ects_def) sorry.
    qed auto
  qed
next
  fix s0 efl
  assume a: \<open>valid_exec_frag tps (Exec_frag s0 efl s)\<close> \<open>init tps s0\<close> \<open>Exec_frag s0 efl s \<in> Good_wrt ev_ects\<close>
  then show \<open>reach tps_s s\<close>
  proof (induction "(Exec_frag s0 efl s)" arbitrary: efl s rule: valid_exec_frag.induct)
    case (vef_snoc efl s e s')
    then show ?case using reach_tps_s_non_commit[of s e s']
    proof (induction e)
      case (RDone x1 x2 x3 x4)
      then show ?case by (metis tps_RDone_sub_tps_s efrag_trim_good reach_trans)
    next
      case (WCommit x1 x2 x3 x4 x5)
      then show ?case by (metis tps_WCommit_sub_tps_s efrag_trim_good reach_trans)
    qed auto
  qed (auto simp add: tps_s_def tps_def)
qed

end