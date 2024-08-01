section \<open>Proof of reachable states equivalence for EP+_Sorted and Good Executions (reach epp_s = reach E)\<close>

theory "EP+_Sorted_eq_E"
  imports "EP+_Sorted" "EP+_Trace" Reductions
begin

subsubsection \<open>Lemmas\<close>

\<comment> \<open>epp_s \<longrightarrow> good execs\<close> 

lemma reach_good_state_f_None:
  "\<lbrakk> epp_s: s \<midarrow>e\<rightarrow> s'; reach epp_s s; ev_ects e = None; reach_good_state epp ev_ects s \<rbrakk> \<Longrightarrow> 
     reach_good_state epp ev_ects s'"
  apply (auto simp add: reach_good_state_def valid_exec_def epp_def)
  subgoal for efl
  apply (intro exI[where x="efl @ [(s, e, s')]"], auto simp add: efrag_snoc_good)
    using epp_s_ev_sub_epp vef_snoc by fastforce.

\<comment> \<open>good execs \<longrightarrow> epp_s\<close>

lemma epp_non_commit_ev_sub_epp_s:           
  "epp: s\<midarrow>e\<rightarrow> s' \<Longrightarrow> \<not>commit_ev e \<Longrightarrow> \<forall>cl. \<not>v_ext_ev e cl \<Longrightarrow> epp_s: s\<midarrow>e\<rightarrow> s'"
  by (induction e) (auto)

lemma epp_RInvoke_sub_epp_s:
  "epp: s\<midarrow>RInvoke cl keys sn u' clk\<rightarrow> s' \<Longrightarrow>
   epp_s: s\<midarrow>RInvoke cl keys sn (updated_view s cl) clk\<rightarrow> s'"
  by (simp add: cl_read_invoke_def cl_read_invoke_s_def cl_read_invoke_G_s_def)

lemma epp_RDone_sub_epp_s:
  "epp: s\<midarrow>RDone cl kv_map sn u'' clk\<rightarrow> s' \<Longrightarrow>
   epp_s: s\<midarrow>RDone cl kv_map sn (view_of (cts_order s) (get_view s cl)) clk\<rightarrow> s'"
  by (simp add: cl_read_done_def cl_read_done_s_def cl_read_done_G_s_def)

lemma epp_WCommit_sub_epp_s:
  assumes "epp: s\<midarrow>WCommit cl kv_map cts sn u'' clk mmap\<rightarrow> s'"
    "reach epp_s s" "init epp s0"
    "valid_exec_frag epp (Exec_frag s0 efl s)"
    "Exec_frag s0 (efl @ [(s, WCommit cl kv_map cts sn u'' clk mmap, s')]) s' \<in> Good_wrt ev_ects"
  shows "epp_s: s\<midarrow>WCommit cl kv_map cts sn (view_of (cts_order s) (get_view s cl)) clk mmap\<rightarrow> s'"
  using assms
    apply (auto simp add: cl_write_commit_s_def cl_write_commit_def cl_write_commit_G_s_def unique_ts_def')
    subgoal using Wtxn_Cts_T0_def[of s] reach_epp[of s] by (simp add: min_ects order_less_imp_le)
    subgoal for _ t
      apply (cases t, simp) subgoal for x2 apply (cases x2)
      using valid_exec_frag_is_trace[of epp s0 efl s] trace_cts_order_epp[of s0]
      apply (auto simp add: init_epp_epp_s_eq)
      using exec_frag_good_ects[of s0 efl s _ s' ev_ects]
      by (simp add: WC_in_\<tau>_wtxn_cts epp_def).
    done

lemma reach_epp_s_non_commit:
  "\<lbrakk> epp: s \<midarrow>e\<rightarrow> s';
    \<not>commit_ev e; \<forall>cl. \<not>v_ext_ev e cl;
    \<lbrakk> init epp s0; Exec_frag s0 efl s \<in> Good_wrt ev_ects \<rbrakk> \<Longrightarrow> reach epp_s s;
    Exec_frag s0 (efl @ [(s, e, s')]) s' \<in> Good_wrt ev_ects;
    init epp s0\<rbrakk>
    \<Longrightarrow> reach epp_s s'"
  by (metis epp_non_commit_ev_sub_epp_s efrag_trim_good reach_trans)

subsubsection \<open>Proof reach epp_s = reach E\<close>

lemma reach_epp_s_reach_good_eq: "reach epp_s s \<longleftrightarrow> reach_good_state epp ev_ects s"
  unfolding reach_good_state_def valid_exec_def
proof (intro iffI; clarsimp simp only: exec_frag.sel)
  assume \<open>reach epp_s s\<close>
  then show \<open>\<exists>s0 efl. (valid_exec_frag epp (Exec_frag s0 efl s) \<and> init epp s0) \<and> Exec_frag s0 efl s \<in> Good_wrt ev_ects\<close>
  proof (induction rule: reach.induct)
    case (reach_init s)
    then show ?case
      by (auto simp add: reach_good_state_def valid_exec_def epp_s_def epp_def Good_wrt_def
          trace_of_efrag_def inverted_pairs_def)
  next
    case (reach_trans s e s')
    then show ?case using reach_good_state_f_None[of s e s']
    proof (induction e)
      case (WCommit x1 x2 x3 x4 x5 x6 x7)
      then show ?case apply auto
        subgoal for s0 efl
        apply (intro exI[where x=s0])
        apply (intro exI[where x="efl @ [(s, WCommit x1 x2 x3 x4 x5 x6 x7, s')]"], auto)
          subgoal by (metis WCommit.prems(1) epp_s_ev_sub_epp vef_snoc)
          apply (auto intro!: reach_good_state_f_Some)
          subgoal for i using ev_ects_Some[of "trace_of_efrag (Exec_frag s0 efl s) ! i"]
          apply (auto simp add: Good_wrt_def inverted_pairs_def trace_of_efrag_snoc cl_write_commit_s_def
              cl_write_commit_G_s_def unique_ts_def' nth_append simp del: trace_of_efrag_length)
              subgoal for _ _ cts cl kv_map sn u''
              using valid_exec_frag_is_trace[of epp s0 efl s]
                nth_mem[of i "trace_of_efrag (Exec_frag s0 efl s)"]
                WC_in_\<tau>_kv_map_non_emp[of s0 "trace_of_efrag (Exec_frag s0 efl s)" s cl kv_map cts sn u'']
              apply auto
              using trace_cts_order_epp[of s0 "trace_of_efrag (Exec_frag s0 efl s)" s sn cl]
              by (smt (verit) WC_in_\<tau>_wtxn_cts domI get_cl_w.simps(2) leD option.sel reach_init
                  txid.distinct(1))
            done
          done.
    qed (auto simp add: reach_good_state_def valid_exec_def)
  qed
next
  fix s0 efl
  assume a: \<open>valid_exec_frag epp (Exec_frag s0 efl s)\<close> \<open>init epp s0\<close> \<open>Exec_frag s0 efl s \<in> Good_wrt ev_ects\<close>
  then show \<open>reach epp_s s\<close>
  proof (induction "(Exec_frag s0 efl s)" arbitrary: efl s rule: valid_exec_frag.induct)
    case (vef_snoc efl s e s')
    then show ?case using reach_epp_s_non_commit[of s e s']
    proof (induction e)
      case (RInvoke x1 x2 x3 x4 x5)
      then show ?case by (metis (lifting) epp_RInvoke_sub_epp_s efrag_trim_good reach_trans)
    next
      case (RDone x1 x2 x3 x4 x5)
      then show ?case by (metis epp_RDone_sub_epp_s efrag_trim_good reach_trans)
    next
      case (WCommit x1 x2 x3 x4 x5 x6 x7)
      then show ?case by (metis epp_WCommit_sub_epp_s efrag_trim_good reach_trans)
    qed auto
  qed (auto simp add: epp_s_def epp_def)
qed

lemma reacheable_set_epp_s_good_eq:
  "{s. reach epp_s s} = ef_last ` Good_execs epp ev_ects"
  apply (auto intro: Collect_eqI simp add: reach_epp_s_reach_good_eq reach_good_state_def image_iff)
  apply force
  by (metis exec_frag.collapse)

end