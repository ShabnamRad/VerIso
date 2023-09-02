section \<open>Eiger Port Plus Protocol Satisfying CCv (Causal+)\<close>

theory "EP+_TCCv_h"
  imports "EP+_TCCv"
begin

section \<open>Event system & Refinement from ET_ES to tps\<close>

\<comment> \<open>Extended Global State\<close>
record 'v global_conf_h = "'v global_conf" +
  rtxn_rts :: "txid0 \<rightharpoonup> tstmp"
  wtxn_cts :: "txid \<rightharpoonup> tstmp"
  commit_order :: "key \<Rightarrow> txid list"
  \<comment> \<open>history variable: order of client commit for write transactions\<close>

\<comment> \<open>Updated Events\<close>

abbreviation read_done_G_h where
  "read_done_G_h cl kv_map sn u'' s \<equiv>
    read_done_G cl kv_map sn s \<and>
    u'' = view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s cl (dom kv_map))"

abbreviation read_done_U_h where
  "read_done_U_h cl kv_map s \<equiv>
    (read_done_U cl kv_map s)
      \<lparr> rtxn_rts := (rtxn_rts s) (get_txn s cl \<mapsto> gst (cls s cl)) \<rparr>"

definition read_done_h :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> 'v global_conf_h \<Rightarrow> 'v global_conf_h \<Rightarrow> bool" where
  "read_done_h cl kv_map sn u'' s s' \<equiv>
    read_done_G_h cl kv_map sn u'' s \<and>
    s' = read_done_U_h cl kv_map s"

abbreviation write_commit_G_h where
  "write_commit_G_h cl kv_map cts sn u'' s \<equiv>
    write_commit_G cl kv_map cts sn s \<and>
    u'' = view_of (commit_order s) (cl_ctx (cls s cl))"

abbreviation write_commit_U_h where
  "write_commit_U_h cl kv_map cts s \<equiv>
    (write_commit_U cl kv_map cts s)
      \<lparr> wtxn_cts := (wtxn_cts s) (get_wtxn s cl \<mapsto> cts),
        commit_order := ext_corder (get_wtxn s cl) kv_map (commit_order s) \<rparr>"

definition write_commit_h :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> tstmp \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> 'v global_conf_h \<Rightarrow> 'v global_conf_h \<Rightarrow> bool" where
  "write_commit_h cl kv_map cts sn u'' s s' \<equiv>
    write_commit_G_h cl kv_map cts sn u'' s \<and> 
    s' = write_commit_U_h cl kv_map cts s"


subsection \<open>The Event System\<close>

definition state_init_h :: "'v global_conf_h" where
  "state_init_h \<equiv> \<lparr> 
    cls = (\<lambda>cl. \<lparr> cl_state = Idle,
                  cl_sn = 0,
                  cl_clock = 0,
                  cl_ctx = dep_set_init,
                  gst = 0,
                  lst_map = (\<lambda>svr. 0) \<rparr>),
    svrs = (\<lambda>svr. \<lparr> svr_state = (\<lambda>t. No_Ver) (T0 := Commit 0 0 0 undefined {}),
                    svr_clock = 0,
                    lst = 0 \<rparr>),
    wtxn_deps = (\<lambda>t. {}),
    rtxn_rts = Map.empty,
    wtxn_cts = Map.empty (T0 \<mapsto> 0),
    commit_order = (\<lambda>k. [T0])
  \<rparr>"

fun state_trans_h :: "'v global_conf_h \<Rightarrow> 'v ev \<Rightarrow> 'v global_conf_h \<Rightarrow> bool" where
  "state_trans_h s (RInvoke cl keys)          s' \<longleftrightarrow> read_invoke cl keys s s'" |
  "state_trans_h s (Read cl k v t rts rlst)   s' \<longleftrightarrow> read cl k v t rts rlst s s'" |
  "state_trans_h s (RDone cl kv_map sn u'')   s' \<longleftrightarrow> read_done_h cl kv_map sn u'' s s'" |
  "state_trans_h s (WInvoke cl kv_map)        s' \<longleftrightarrow> write_invoke cl kv_map s s'" |
  "state_trans_h s (WCommit cl kv_map cts sn u'') s' \<longleftrightarrow> write_commit_h cl kv_map cts sn u'' s s'" |
  "state_trans_h s (WDone cl kv_map)          s' \<longleftrightarrow> write_done cl kv_map s s'" |
  "state_trans_h s (RegR svr t t_wr rts)      s' \<longleftrightarrow> register_read svr t t_wr rts s s'" |
  "state_trans_h s (PrepW svr t v)            s' \<longleftrightarrow> prepare_write svr t v s s'" |
  "state_trans_h s (CommitW svr t v cts)      s' \<longleftrightarrow> commit_write svr t v cts s s'" |
  "state_trans_h s Skip2 s' \<longleftrightarrow> s' = s"

definition tps_h :: "('v ev, 'v global_conf_h) ES" where
  "tps_h \<equiv> \<lparr>
    init = (=) state_init_h,
    trans = state_trans_h
  \<rparr>"

lemmas tps_trans_defs = read_invoke_def read_def read_done_h_def write_invoke_def write_commit_h_def
  write_done_def register_read_def prepare_write_def commit_write_def
  (* chsp added, should be put into a separate list, I guess *)
  read_done_G_def read_done_U_def
  prepare_write_G_def prepare_write_U_def
  write_commit_G_def write_commit_U_def
  write_done_G_def write_done_U_def
  register_read_G_def register_read_U_def
  commit_write_G_def commit_write_U_def

lemmas tps_trans_all_defs = tps_trans_defs ext_corder_def

lemmas tps_defs = tps_h_def state_init_h_def

lemma tps_trans [simp]: "trans tps_h = state_trans_h" by (simp add: tps_h_def)

subsection \<open>Simulation function\<close>

abbreviation is_done :: "('v, 'm) global_conf_scheme \<Rightarrow> txid0 \<Rightarrow> bool" where
  "is_done s t \<equiv> cl_sn (cls s (get_cl t)) > get_sn t"

abbreviation is_done_w :: "('v, 'm) global_conf_scheme \<Rightarrow> txid \<Rightarrow> bool" where
  "is_done_w s t \<equiv> cl_sn (cls s (get_cl_w t)) > get_sn_w t"

term "Set.filter (is_done s) rs"

definition txn_to_vers :: "('v, 'm) global_conf_scheme \<Rightarrow> key \<Rightarrow> txid \<Rightarrow> 'v version" where
  "txn_to_vers s k = (\<lambda>t. case svr_state (svrs s k) t of
    Prep ts v \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = {}\<rparr> |
    Commit cts ts lst v rs \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = {t. \<exists>rts rlst. (t, rts, rlst) \<in> rs \<and> is_done s t}\<rparr>)"

definition kvs_of_s :: "'v global_conf_h \<Rightarrow> 'v kv_store" where
  "kvs_of_s s \<equiv> (\<lambda>k. map (txn_to_vers s k) (commit_order s k))"

lemmas kvs_of_s_defs = kvs_of_s_def txn_to_vers_def

definition views_of_s :: "'v global_conf_h \<Rightarrow> (cl_id \<Rightarrow> view)" where
  "views_of_s s = (\<lambda>cl. view_of (commit_order s) (cl_ctx (cls s cl)))"

definition sim :: "'v global_conf_h \<Rightarrow> 'v config" where         
  "sim s = (kvs_of_s s, views_of_s s)"

lemmas sim_defs = sim_def kvs_of_s_defs views_of_s_def

subsection \<open>Mediator function\<close>

fun med :: "'v ev \<Rightarrow> 'v label" where
  "med (RDone cl kv_map sn u'') = ET cl sn u'' (read_only_fp kv_map)" |
  "med (WCommit cl kv_map _ sn u'') = ET cl sn u'' (write_only_fp kv_map)" |
  "med _ = ETSkip"

end