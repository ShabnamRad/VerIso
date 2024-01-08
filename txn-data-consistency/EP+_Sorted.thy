section \<open>EP+ Event System for well-sorted executions\<close>

theory "EP+_Sorted"
  imports "EP+"
begin

\<comment> \<open>Updated Events\<close>

definition read_done_G_s where
  "read_done_G_s cl kv_map sn u'' clk s \<equiv>
    read_done_G cl kv_map sn clk s \<and>
    u'' = view_of (cts_order s) (get_view s cl)"

definition read_done_s :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> tstmp \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "read_done_s cl kv_map sn u'' clk s s' \<equiv>
    read_done_G_s cl kv_map sn u'' clk s \<and>
    s' = read_done_U cl kv_map s"

definition write_commit_G_s where
  "write_commit_G_s cl kv_map cts sn u'' clk s \<equiv>
    write_commit_G cl kv_map cts sn clk s \<and>
    u'' = view_of (cts_order s) (get_view s cl) \<and>
    (\<forall>k\<comment>\<open>\<in> dom kv_map\<close>. \<forall>t \<in> set (cts_order s k). ects cts cl \<ge> unique_ts (wtxn_cts s) t)"
  \<comment> \<open>It's actually > but we don't need to enforce it here since \<ge> already works and is what Good_wrt defines\<close>

definition write_commit_s :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> tstmp \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> tstmp \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "write_commit_s cl kv_map cts sn u'' clk s s' \<equiv>
    write_commit_G_s cl kv_map cts sn u'' clk s \<and> 
    s' = write_commit_U cl kv_map cts s"


subsection \<open>The Event System\<close>

fun state_trans :: "('v, 'm) global_conf_scheme \<Rightarrow> 'v ev \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "state_trans s (RInvoke cl keys sn clk)           s' \<longleftrightarrow> read_invoke cl keys sn clk s s'" |
  "state_trans s (Read cl k v t rts rlst sn clk)    s' \<longleftrightarrow> read cl k v t rts rlst sn clk s s'" |
  "state_trans s (RDone cl kv_map sn u'' clk)       s' \<longleftrightarrow> read_done_s cl kv_map sn u'' clk s s'" |
  "state_trans s (WInvoke cl kv_map sn clk)         s' \<longleftrightarrow> write_invoke cl kv_map sn clk s s'" |
  "state_trans s (WCommit cl kv_map cts sn u'' clk) s' \<longleftrightarrow> write_commit_s cl kv_map cts sn u'' clk s s'" |
  "state_trans s (WDone cl kv_map sn clk)           s' \<longleftrightarrow> write_done cl kv_map sn clk s s'" |
  "state_trans s (RegR svr t t_wr rts clk)          s' \<longleftrightarrow> register_read svr t t_wr rts clk s s'" |
  "state_trans s (PrepW svr t v clk)                s' \<longleftrightarrow> prepare_write svr t v clk s s'" |
  "state_trans s (CommitW svr t v cts clk)          s' \<longleftrightarrow> commit_write svr t v cts clk s s'" |
  "state_trans s Skip2                              s' \<longleftrightarrow> s' = s"

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
  write_done_G_def clk_WDone_def write_done_U_def
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
    Commit cts ts lst v rs \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = {t. \<exists>rts rlst. rs t = Some (rts, rlst) \<and> is_done s t}\<rparr>)"

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
  "med (RDone cl kv_map sn u'' clk) = ET cl sn u'' (read_only_fp kv_map)" |
  "med (WCommit cl kv_map _ sn u'' clk) = ET cl sn u'' (write_only_fp kv_map)" |
  "med _ = ETSkip"

end