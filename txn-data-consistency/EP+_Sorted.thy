section \<open>EP+ Event System for well-sorted executions\<close>

theory "EP+_Sorted"
  imports "EP+"
begin

subsubsection \<open>Helper Functions\<close>

type_synonym view_txid = "key \<Rightarrow> txid set"

\<comment> \<open>The reason for the second condition (wtxns_dom) is that not all k are wrtten to by t\<close>
definition get_view :: "('v, 'm) global_conf_scheme \<Rightarrow> cl_id \<Rightarrow> view_txid" where
  "get_view s cl \<equiv> (\<lambda>k. {t. t \<in> dom (wtxn_cts s) \<inter> set (commit_order s k) \<and>
    (the (wtxn_cts s t) \<le> gst (cls s cl) \<or> get_cl_w t = cl)})"

abbreviation index_of where
  "index_of xs x \<equiv> (THE i. i < length xs \<and> xs ! i = x)"

definition view_of :: "(key \<Rightarrow> txid list) \<Rightarrow> view_txid \<Rightarrow> view" where
  "view_of corder u \<equiv> (\<lambda>k. {index_of (corder k) t | t. t \<in> u k \<and> t \<in> set (corder k)})"

abbreviation is_done :: "('v, 'm) global_conf_scheme \<Rightarrow> txid0 \<Rightarrow> bool" where
  "is_done s t \<equiv> cl_sn (cls s (get_cl t)) > get_sn t"

abbreviation is_done_w :: "('v, 'm) global_conf_scheme \<Rightarrow> txid \<Rightarrow> bool" where
  "is_done_w s t \<equiv> t = T0 \<or> (cl_sn (cls s (get_cl_w t)) > get_sn_w t) \<or> 
    (is_curr_wt s t \<and> (\<exists>cts kv_map. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map))"


\<comment> \<open>Updated Events\<close>
abbreviation updated_view where
  "updated_view s cl\<equiv> view_of (commit_order s) (\<lambda>k. {t. t \<in> dom (wtxn_cts s) \<inter> set (commit_order s k) \<and>
    (the (wtxn_cts s t) \<le> Min (range (lst_map (cls s cl))) \<or> get_cl_w t = cl)})"

definition cl_read_invoke_G_s where
  "cl_read_invoke_G_s cl keys sn u' clk s s' \<equiv>
    cl_read_invoke_G cl keys sn clk s \<and>
    u' = updated_view s cl"

definition cl_read_invoke_s where
  "cl_read_invoke_s cl keys sn u' clk s s' \<equiv>
    cl_read_invoke_G_s cl keys sn u' clk s s' \<and>
    s' = cl_read_invoke_U cl keys clk s"

definition cl_read_done_G_s where
  "cl_read_done_G_s cl kv_map sn u'' clk s \<equiv>
    cl_read_done_G cl kv_map sn clk s \<and>
    u'' = view_of (commit_order s) (get_view s cl)"

definition cl_read_done_s :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> tstmp \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "cl_read_done_s cl kv_map sn u'' clk s s' \<equiv>
    cl_read_done_G_s cl kv_map sn u'' clk s \<and>
    s' = cl_read_done_U cl kv_map s"

definition cl_write_commit_G_s where
  "cl_write_commit_G_s cl kv_map cts sn u'' clk mmap s \<equiv>
    cl_write_commit_G cl kv_map cts sn clk mmap s \<and>
    u'' = view_of (commit_order s) (get_view s cl) \<and>
    (\<forall>k\<comment>\<open>\<in> dom kv_map\<close>. \<forall>t \<in> set (commit_order s k). ects cts cl \<ge> unique_ts (wtxn_cts s) t)"
  \<comment> \<open>It's actually > but we don't need to enforce it here since \<ge> already works and is what Good_wrt defines\<close>

definition cl_write_commit_s :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> tstmp \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> tstmp \<Rightarrow> (key \<rightharpoonup> tstmp)
  \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "cl_write_commit_s cl kv_map cts sn u'' clk mmap s s' \<equiv>
    cl_write_commit_G_s cl kv_map cts sn u'' clk mmap s \<and> 
    s' = cl_write_commit_U cl kv_map cts s"


subsection \<open>The Event System\<close>

fun state_trans :: "('v, 'm) global_conf_scheme \<Rightarrow> 'v ev \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "state_trans s (RInvoke cl keys sn u' clk)             s' \<longleftrightarrow> cl_read_invoke_s cl keys sn u' clk s s'" |
  "state_trans s (Read cl k v t sn clk m)                s' \<longleftrightarrow> cl_read cl k v t sn clk m s s'" |
  "state_trans s (RDone cl kv_map sn u'' clk)            s' \<longleftrightarrow> cl_read_done_s cl kv_map sn u'' clk s s'" |
  "state_trans s (WInvoke cl kv_map sn clk)              s' \<longleftrightarrow> cl_write_invoke cl kv_map sn clk s s'" |
  "state_trans s (WCommit cl kv_map cts sn u'' clk mmap) s' \<longleftrightarrow> cl_write_commit_s cl kv_map cts sn u'' clk mmap s s'" |
  "state_trans s (WDone cl kv_map sn clk mmap)           s' \<longleftrightarrow> cl_write_done cl kv_map sn clk mmap s s'" |
  "state_trans s (RegR svr t t_wr rts clk lst m)         s' \<longleftrightarrow> register_read svr t t_wr rts clk lst m s s'" |
  "state_trans s (PrepW svr t v clk m)                   s' \<longleftrightarrow> prepare_write svr t v clk m s s'" |
  "state_trans s (CommitW svr t v cts clk lst m)         s' \<longleftrightarrow> commit_write svr t v cts clk lst m s s'"

definition tps_s :: "('v ev, 'v global_conf) ES" where
  "tps_s \<equiv> \<lparr>
    init = \<lambda>s. s = state_init,
    trans = state_trans
  \<rparr>"

lemmas tps_trans_top_defs = 
  cl_read_invoke_s_def cl_read_def cl_read_done_s_def cl_write_invoke_def cl_write_commit_s_def
  cl_write_done_def register_read_def prepare_write_def commit_write_def

lemmas tps_trans_G_defs = 
  cl_read_invoke_G_def cl_read_invoke_G_s_def
  cl_read_G_def
  cl_read_done_G_def cl_read_done_G_s_def
  cl_write_invoke_G_def
  cl_write_commit_G_def cl_write_commit_G_s_def
  cl_write_done_G_def clk_WDone_def
  register_read_G_def
  prepare_write_G_def
  commit_write_G_def

lemmas tps_trans_U_defs = 
  cl_read_invoke_U_def
  cl_read_U_def
  cl_read_done_U_def
  cl_write_invoke_U_def
  cl_write_commit_U_def
  cl_write_done_U_def
  register_read_U_def
  prepare_write_U_def
  commit_write_U_def

lemmas tps_trans_GU_defs = tps_trans_G_defs tps_trans_U_defs

lemmas tps_trans_defs = tps_trans_top_defs tps_trans_GU_defs

lemmas tps_trans_all_defs = tps_trans_defs ext_corder_def

lemmas tps_s_defs = tps_s_def state_init_def

lemma tps_trans [simp]: "trans tps_s = state_trans" by (simp add: tps_s_def)


subsection \<open>Relation of tps and tps_s\<close>

lemma init_tps_tps_s_eq:
  "init tps_s s \<longleftrightarrow> init tps s"
  by (simp add: tps_def tps_s_defs)

lemma tps_s_ev_sub_tps:
  "tps_s: s\<midarrow>e\<rightarrow> s' \<Longrightarrow> tps: s\<midarrow>e\<rightarrow> s'"
  by (induction e) (auto simp add: cl_read_invoke_s_def cl_read_invoke_G_s_def cl_read_invoke_def
      cl_read_done_s_def cl_read_done_def cl_read_done_G_s_def
      cl_write_commit_s_def cl_write_commit_def cl_write_commit_G_s_def)

lemma tps_s_tr_sub_tps:
  "(tps_s: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s') \<Longrightarrow> (tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s')"
  apply (induction \<tau> s' rule: trace.induct, auto)
  by (metis tps_trans tps_s_ev_sub_tps trace_snoc)

lemma reach_tps [simp, dest]:
  "reach tps_s s \<Longrightarrow> reach tps s" \<comment> \<open>All tps invs can also be used for tps_s\<close>
proof (induction s rule: reach.induct)
  case (reach_init s)
  then show ?case by (simp add: init_tps_tps_s_eq)
next
  case (reach_trans s e s')
  then show ?case using tps_s_ev_sub_tps[of s e s'] by auto
qed


subsection \<open>Simulation function\<close>

term "Set.filter (is_done s) rs"
abbreviation rs_conc_to_abst where
  "rs_conc_to_abst s rs \<equiv> {t. \<exists>rts rlst. rs t = Some (rts, rlst) \<and> is_done s t}"

abbreviation get_abst_rs where
  "get_abst_rs s svr t \<equiv> rs_conc_to_abst s (get_rs (svr_state (svrs s svr) t))"

definition txn_to_vers :: "('v, 'm) global_conf_scheme \<Rightarrow> key \<Rightarrow> txid \<Rightarrow> 'v version" where
  "txn_to_vers s k = (\<lambda>t. case svr_state (svrs s k) t of
    Prep pd ts v \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = {}\<rparr> |
    Commit cts ts lst v rs \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = rs_conc_to_abst s rs\<rparr>)"

definition kvs_of_s :: "'v global_conf \<Rightarrow> 'v kv_store" where
  "kvs_of_s s \<equiv> (\<lambda>k. map (txn_to_vers s k) (commit_order s k))"

lemmas kvs_of_s_defs = kvs_of_s_def txn_to_vers_def

definition views_of_s :: "'v global_conf \<Rightarrow> (cl_id \<Rightarrow> view)" where
  "views_of_s s = (\<lambda>cl. view_of (commit_order s) (get_view s cl))"

definition sim :: "'v global_conf \<Rightarrow> 'v config" where         
  "sim s = (kvs_of_s s, views_of_s s)"

lemmas sim_defs = sim_def kvs_of_s_defs views_of_s_def

subsection \<open>Mediator function\<close>

fun med :: "'v ev \<Rightarrow> 'v label" where
  "med (RInvoke cl keys sn u' clk) = ETViewExt cl u'" |
  "med (RDone cl kv_map sn u'' clk) = ET cl sn u'' (read_only_fp kv_map)" |
  "med (WCommit cl kv_map _ sn u'' clk mmap) = ET cl sn u'' (write_only_fp kv_map)" |
  "med _ = ETSkip"

end