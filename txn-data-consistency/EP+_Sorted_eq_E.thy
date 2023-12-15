section \<open>Proof of reachable states equivalence for EP+_Sorted and Good Executions (reach tps_s = reach E)\<close>

theory "EP+_Sorted_eq_E"
  imports "EP+_Sorted" "EP+_Trace" Reductions
begin

subsubsection \<open>Lemmas\<close>

lemma init_tps_tps_s_eq:
  "init tps_s s \<longleftrightarrow> init tps s"
  by (simp add: tps_def tps_s_defs)

lemma tps_s_ev_sub_tps:
  "tps_s: s\<midarrow>e\<rightarrow> s' \<Longrightarrow> tps: s\<midarrow>e\<rightarrow> s'"
  by (induction e) (auto simp add: read_done_s_def read_done_def read_done_G_s_def
      write_commit_s_def write_commit_def write_commit_G_s_def)

lemma tps_s_tr_sub_tps:
  "(tps_s: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s') \<Longrightarrow> (tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s')"
  apply (induction \<tau> s' rule: trace.induct, auto)
  by (metis tps_trans tps_s_ev_sub_tps trace_snoc)

lemma reach_tps: "reach tps_s s \<Longrightarrow> reach tps s" \<comment> \<open>All tps invs can also be used for tps_s\<close>
proof (induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (simp add: init_tps_tps_s_eq)
next
  case (reach_trans s e s')
  then show ?case using tps_s_ev_sub_tps[of s e s'] by auto
qed

\<comment> \<open>tps_s \<longrightarrow> good execs\<close> 

lemma reach_good_state_f_None:
  "\<lbrakk> tps_s: s \<midarrow>e\<rightarrow> s'; reach tps_s s; ev_ects e = None; reach_good_state tps ev_ects s \<rbrakk> \<Longrightarrow> 
     reach_good_state tps ev_ects s'"
  apply (auto simp add: reach_good_state_def valid_exec_def tps_def)
  subgoal for efl
  apply (intro exI[where x="efl @ [(s, e, s')]"], auto simp add: efrag_snoc_good)
    using tps_s_ev_sub_tps vef_snoc by fastforce.

\<comment> \<open>good execs \<longrightarrow> tps_s\<close>

lemma tps_non_commit_ev_sub_tps_s:
  "tps: s\<midarrow>e\<rightarrow> s' \<Longrightarrow> \<not>commit_ev e  \<Longrightarrow> tps_s: s\<midarrow>e\<rightarrow> s'"
  by (induction e) (auto)

lemma tps_RDone_sub_tps_s:
  "tps: s\<midarrow>RDone cl kv_map sn u''\<rightarrow> s' \<Longrightarrow>
   tps_s: s\<midarrow>RDone cl kv_map sn (view_of (cts_order s) (get_view s cl))\<rightarrow> s'"
  by (simp add: read_done_def read_done_s_def read_done_G_s_def)

lemma tps_WCommit_sub_tps_s:
  assumes "tps: s\<midarrow>WCommit cl kv_map cts sn u''\<rightarrow> s'"
    "reach tps_s s" "init tps s0"
    "valid_exec_frag tps (Exec_frag s0 efl s)"
    "Exec_frag s0 (efl @ [(s, WCommit cl kv_map cts sn u'', s')]) s' \<in> Good_wrt ev_ects"
  shows "tps_s: s\<midarrow>WCommit cl kv_map cts sn (view_of (cts_order s) (get_view s cl))\<rightarrow> s'"
  using assms
    apply (auto simp add: write_commit_s_def write_commit_def write_commit_G_s_def unique_ts_def')
    subgoal using Wtxn_Cts_T0_def[of s] reach_tps[of s] by (simp add: min_ects order_less_imp_le)
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

subsubsection \<open>Proof reach tps_s = reach E\<close>

lemma reach_tps_s_reach_good_eq: "reach tps_s s \<longleftrightarrow> reach_good_state tps ev_ects s"
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
    proof (induction e)
      case (WCommit x1 x2 x3 x4 x5)
      then show ?case apply auto
        subgoal for s0 efl
        apply (intro exI[where x=s0])
        apply (intro exI[where x="efl @ [(s, WCommit x1 x2 x3 x4 x5, s')]"], auto)
          subgoal by (metis WCommit.prems(1) tps_s_ev_sub_tps vef_snoc)
          apply (auto intro!: reach_good_state_f_Some)
          subgoal for i using ev_ects_Some[of "trace_of_efrag (Exec_frag s0 efl s) ! i"]
          apply (auto simp add: Good_wrt_def inverted_pairs_def trace_of_efrag_append write_commit_s_def
              write_commit_G_s_def unique_ts_def' nth_append)
              subgoal for _ _ cts cl kv_map sn u''
              using valid_exec_frag_is_trace[of tps s0 efl s]
                nth_mem[of i "trace_of_efrag (Exec_frag s0 efl s)"]
                WC_in_\<tau>_kv_map_non_emp[of s0 "trace_of_efrag (Exec_frag s0 efl s)" s cl kv_map cts sn u'']
              apply (auto simp add: trace_of_efrag_length)
              using trace_cts_order_tps[of s0 "trace_of_efrag (Exec_frag s0 efl s)" s sn cl]
              by (smt (verit) WC_in_\<tau>_wtxn_cts domI get_cl_w.simps(2) leD option.sel reach_init
                  txid.distinct(1))
            done
          done.
    qed (auto simp add: reach_good_state_def valid_exec_def)
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

lemma reacheable_set_tps_s_good_eq:
  "{s. reach tps_s s} = ef_last ` Good_execs tps ev_ects"
  apply (auto intro: Collect_eqI simp add: reach_tps_s_reach_good_eq reach_good_state_def image_iff)
  apply force
  by (metis exec_frag.collapse)

end