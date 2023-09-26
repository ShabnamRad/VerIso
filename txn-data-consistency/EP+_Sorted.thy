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
    (\<forall>k\<comment>\<open>\<in> dom kv_map\<close>. \<forall>t \<in> set (cts_order s k). (cts, Suc cl) > unique_ts (wtxn_cts s) t)"

definition write_commit_s :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> tstmp \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "write_commit_s cl kv_map cts sn u'' s s' \<equiv>
    write_commit_G_s cl kv_map cts sn u'' s \<and> 
    s' = write_commit_U cl kv_map cts s"


subsection \<open>The Event System\<close>

fun state_trans :: "('v, 'm) global_conf_scheme \<Rightarrow> 'v ev \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "state_trans s (RInvoke cl keys)          s' \<longleftrightarrow> read_invoke cl keys s s'" |
  "state_trans s (Read cl k v t rts rlst)   s' \<longleftrightarrow> read cl k v t rts rlst s s'" |
  "state_trans s (RDone cl kv_map sn u'')   s' \<longleftrightarrow> read_done_s cl kv_map sn u'' s s'" |
  "state_trans s (WInvoke cl kv_map)        s' \<longleftrightarrow> write_invoke cl kv_map s s'" |
  "state_trans s (WCommit cl kv_map cts sn u'') s' \<longleftrightarrow> write_commit_s cl kv_map cts sn u'' s s'" |
  "state_trans s (WDone cl kv_map)          s' \<longleftrightarrow> write_done cl kv_map s s'" |
  "state_trans s (RegR svr t t_wr rts)      s' \<longleftrightarrow> register_read svr t t_wr rts s s'" |
  "state_trans s (PrepW svr t v)            s' \<longleftrightarrow> prepare_write svr t v s s'" |
  "state_trans s (CommitW svr t v cts)      s' \<longleftrightarrow> commit_write svr t v cts s s'" |
  "state_trans s Skip2 s' \<longleftrightarrow> s' = s"

definition tps_s :: "('v ev, 'v global_conf) ES" where
  "tps_s \<equiv> \<lparr>
    init = (=) state_init,
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
  "\<lbrakk> tps_s: s \<midarrow>e\<rightarrow> s'; reach tps_s s; ev_cts e = None; reach_good_state tps ev_cts s \<rbrakk> \<Longrightarrow> 
     reach_good_state tps ev_cts s'"
  apply (auto simp add: reach_good_state_def valid_exec_def tps_def)
  subgoal for efl
  apply (intro exI[where x="efl @ [(s, e, s')]"], auto simp add: efrag_snoc_good)
    using tps_s_ev_sub_tps vef_snoc by fastforce.

lemma reach_good_state_f_Some:
  "\<lbrakk> Exec_frag s0 efl s \<in> Good_wrt ev_cts; ev_cts e = Some (cts, Suc cl);
     \<forall>i < length (trace_of_efrag (Exec_frag s0 efl s)). \<forall>cts' cl'.
       ev_cts (trace_of_efrag (Exec_frag s0 efl s) ! i) = Some (cts', cl')
        \<longrightarrow> (cts, Suc cl) > (cts', cl')\<rbrakk>
    \<Longrightarrow> Exec_frag s0 (efl @ [(s, e, s')]) s' \<in> Good_wrt ev_cts"
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

lemma lowest_ts_lt_all: "(0, 0) < (x :: nat, Suc y)" by (auto simp add: less_prod_def)

lemma efrag_snoc_good_def:
  "Exec_frag state_init (efl @ [(s, e, s')]) s' \<in> Good_wrt ev_cts \<longleftrightarrow>
    (\<forall>j i. j < Suc (length (trace_of_efrag (Exec_frag state_init efl s))) \<longrightarrow> i < j \<longrightarrow>
     (\<forall>cts cl. ev_cts ((trace_of_efrag (Exec_frag state_init efl s) @ [e]) ! j) = Some (cts, cl) \<longrightarrow>
     (\<forall>cts' cl'. ev_cts (trace_of_efrag (Exec_frag state_init efl s) ! i) = Some (cts', cl') \<longrightarrow>
           \<not> (cts, cl) < (cts', cl'))))"
  by (auto simp add: Good_wrt_def inverted_pairs_def trace_of_efrag_append nth_append)

lemma new_wrc_no_conflict:
  "\<lbrakk> Exec_frag state_init (efl @ [(s, e, s')]) s' \<in> Good_wrt ev_cts;
     ev_cts e = Some (cts, cl);
     i < length efl;
     ev_cts (trace_of_efrag (Exec_frag state_init efl s) ! i) = Some (cts', cl') \<rbrakk>
     \<Longrightarrow> (cts, cl) \<ge> (cts', cl')"
  unfolding efrag_snoc_good_def
  by (metis lessI linorder_le_less_linear nth_append_length trace_of_efrag_length)

lemma tps_WCommit_sub_tps_s:
  "\<lbrakk> tps: s\<midarrow>WCommit cl kv_map cts sn u''\<rightarrow> s';
     reach tps_s s;
     valid_exec_frag tps (Exec_frag s0 efl s);
     Exec_frag s0 (efl @ [(s, e, s')]) s' \<in> Good_wrt ev_cts\<rbrakk>
    \<Longrightarrow> tps_s: s\<midarrow>WCommit cl kv_map cts sn (view_of (cts_order s) (get_view s cl))\<rightarrow> s'"
    using Wtxn_Cts_T0_def[of s]
    apply (auto simp add: write_commit_s_def write_commit_def write_commit_G_s_def unique_ts_def
             lowest_ts_lt_all)
    sorry

lemma reach_tps_s_non_commit:
  "\<lbrakk> tps: s \<midarrow>e\<rightarrow> s';
    \<not>commit_ev e;
    \<lbrakk> init tps s0; Exec_frag s0 efl s \<in> Good_wrt ev_cts \<rbrakk> \<Longrightarrow> reach tps_s s;
    Exec_frag s0 (efl @ [(s, e, s')]) s' \<in> Good_wrt ev_cts;
    init tps s0\<rbrakk>
    \<Longrightarrow> reach tps_s s'"
  by (metis tps_non_commit_ev_sub_tps_s efrag_trim_good reach_trans)


subsubsection \<open>Proof reach tps_s = reach E\<close>

lemma "reach tps_s s \<longleftrightarrow> reach_good_state tps ev_cts s"
  unfolding reach_good_state_def valid_exec_def
proof (intro iffI; clarsimp simp only: exec_frag.sel)
  assume \<open>reach tps_s s\<close>
  then show \<open>\<exists>s0 efl. (valid_exec_frag tps (Exec_frag s0 efl s) \<and> init tps s0) \<and> Exec_frag s0 efl s \<in> Good_wrt ev_cts\<close>
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
          apply (simp add: Good_wrt_def inverted_pairs_def trace_of_efrag_append write_commit_s_def
              write_commit_G_s_def unique_ts_def) sorry.

      thm trace.induct

    qed auto
  qed
next
  fix s0 efl
  assume a: \<open>valid_exec_frag tps (Exec_frag s0 efl s)\<close> \<open>init tps s0\<close> \<open>Exec_frag s0 efl s \<in> Good_wrt ev_cts\<close>
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