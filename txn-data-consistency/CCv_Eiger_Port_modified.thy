section \<open>Modified Eiger Port Protocol Satisfying CCv (Causal+)\<close>

theory CCv_Eiger_Port_modified
  imports Execution_Tests
begin

subsection \<open>Event system & Refinement from ET_ES to tps\<close>

subsubsection \<open>State\<close>

type_synonym svr_id = key
type_synonym tstmp = nat

record 'v ep_version = "'v version" +
  v_ts :: tstmp
  v_glts :: tstmp
  v_gst :: tstmp
  v_is_pending :: bool

type_synonym 'v datastore = "key \<Rightarrow> 'v ep_version list"

definition ep_version_init :: "'v ep_version" where
  "ep_version_init \<equiv> \<lparr>v_value = undefined, v_writer = T0, v_readerset = {},
    v_ts = 0, v_glts = 0, v_gst = 0, v_is_pending = False\<rparr>"

\<comment> \<open>Server State\<close>
datatype state_wtxn = Ready | Prep tstmp | Commit
record 'v server =
  wtxn_state :: "txid0 \<Rightarrow> state_wtxn"
  clock :: tstmp
  lst :: tstmp
  DS :: "'v ep_version list"

definition DS_vl_init :: "'v ep_version list" where
  "DS_vl_init \<equiv> [ep_version_init]"

definition DS_init :: "'v datastore" where
  "DS_init \<equiv> (\<lambda>k. DS_vl_init)"

\<comment> \<open>Client State\<close>
datatype 'v state_txn = Idle | RtxnInProg "key set" "key \<rightharpoonup> 'v" | WtxnPrep "key \<rightharpoonup> 'v" |
  WtxnCommit tstmp tstmp "key \<rightharpoonup> 'v"
type_synonym view_txid = "key \<Rightarrow> txid set"

record 'v client =
  txn_state :: "'v state_txn"
  txn_sn :: sqn
  gst :: tstmp
  lst_map :: "svr_id \<Rightarrow> tstmp"
  cl_view :: view_txid
  cl_clock :: tstmp

definition view_txid_init :: view_txid where
  "view_txid_init \<equiv> (\<lambda>k. {T0})"

\<comment> \<open>Global State\<close>
record 'v state = 
  cls :: "cl_id \<Rightarrow> 'v client"
  svrs :: "svr_id \<Rightarrow> 'v server"
  global_time :: tstmp \<comment> \<open>history variable - not used for the algorithm itself\<close>


subsubsection \<open>Functions\<close>

\<comment> \<open>Helper functions\<close>

fun add_to_readerset :: "'v ep_version list \<Rightarrow> txid0 \<Rightarrow> txid \<Rightarrow> 'v ep_version list" where
  "add_to_readerset [] t t' = []" |
  "add_to_readerset (ver # vl) t t' =
    (if v_writer ver = t'
     then (ver \<lparr>v_readerset := insert t (v_readerset ver)\<rparr>) # vl
     else ver # (add_to_readerset vl t t'))"

abbreviation is_txn_writer where "is_txn_writer t \<equiv> (\<lambda>ver. v_writer ver = t)"

definition remove_ver :: "'v ep_version list \<Rightarrow> txid \<Rightarrow> 'v ep_version list" where
  "remove_ver vl t \<equiv> (case find (is_txn_writer t) vl of None \<Rightarrow> vl | Some ver \<Rightarrow> remove1 ver vl)"

definition committed_ver :: "'v ep_version list \<Rightarrow> tstmp \<Rightarrow> tstmp \<Rightarrow> txid \<rightharpoonup> 'v ep_version" where
  "committed_ver vl gts cts t \<equiv> (case find (is_txn_writer t) vl of None \<Rightarrow> None |
     Some ver \<Rightarrow> Some (ver \<lparr>v_ts := cts, v_glts := gts, v_is_pending := False\<rparr>))"

fun insert_in_vl :: "'v ep_version list \<Rightarrow> 'v ep_version option \<Rightarrow> 'v ep_version list" where
  "insert_in_vl vl None = vl" |
  "insert_in_vl [] (Some c_ver) = [c_ver]" |
  "insert_in_vl (ver # vl) (Some c_ver) = (if v_glts ver \<le> v_glts c_ver \<and> \<not> v_is_pending ver
    then ver # (insert_in_vl vl (Some c_ver)) else c_ver # ver # vl)"

definition commit_in_vl :: "'v ep_version list \<Rightarrow> tstmp \<Rightarrow> tstmp \<Rightarrow> txid \<Rightarrow> 'v ep_version list" where
  "commit_in_vl vl global_t commit_t t \<equiv> insert_in_vl (remove_ver vl t) (committed_ver vl global_t commit_t t)"

lemmas commit_in_vl_defs = commit_in_vl_def remove_ver_def committed_ver_def

fun at :: "'v ep_version list \<Rightarrow> tstmp \<Rightarrow> 'v ep_version option \<Rightarrow> 'v ep_version" where
  "at [] ts None = ep_version_init" |
  "at [] ts (Some ver) = ver" |
  "at (ver # vl) ts None = (if v_ts ver \<le> ts \<and> \<not>v_is_pending ver then at vl ts (Some ver) else at vl ts None)" |
  "at (ver # vl) ts (Some ver') = (if v_ts ver \<le> ts \<and> v_ts ver > v_ts ver' \<and> \<not>v_is_pending ver
      then at vl ts (Some ver) else at vl ts (Some ver'))"

fun newest_own_write :: "'v ep_version list \<Rightarrow> tstmp \<Rightarrow> cl_id \<Rightarrow> 'v ep_version option \<rightharpoonup> 'v ep_version" where
  "newest_own_write [] ts cl verop = verop" |
  "newest_own_write (ver # vl) ts cl None =
    (if v_ts ver \<ge> ts
     then (case v_writer ver of
        T0 \<Rightarrow> newest_own_write vl ts cl None |
        Tn (Tn_cl sn cl') \<Rightarrow> (if cl' = cl \<and> \<not>v_is_pending ver 
        then newest_own_write vl ts cl (Some ver) else newest_own_write vl ts cl None))
     else newest_own_write vl ts cl None)" |
  "newest_own_write (ver # vl) ts cl (Some ver') =
    (if v_ts ver \<ge> ts
     then (case v_writer ver of
        T0 \<Rightarrow> newest_own_write vl ts cl (Some ver') |
        Tn (Tn_cl sn cl') \<Rightarrow> (if cl' = cl \<and> v_ts ver > v_ts ver' \<and> \<not>v_is_pending ver 
        then newest_own_write vl ts cl (Some ver) else newest_own_write vl ts cl (Some ver')))
     else newest_own_write vl ts cl None)"

record 'v ver_ptr =
  ver_val :: 'v
  ver_writer :: txid
definition read_at :: "'v ep_version list \<Rightarrow> tstmp \<Rightarrow> cl_id \<Rightarrow> 'v ver_ptr" where
  "read_at vl ts cl \<equiv> let ver = at vl ts None in
    (case newest_own_write vl (v_ts ver) cl None of
      None \<Rightarrow> \<lparr> ver_val = v_value ver, ver_writer = v_writer ver \<rparr> |
      Some ver' \<Rightarrow> \<lparr> ver_val = v_value ver', ver_writer = v_writer ver' \<rparr>)"

\<comment> \<open>Translator function\<close>
abbreviation get_txn_cl :: "'v state \<Rightarrow> cl_id \<Rightarrow> txid0" where
  "get_txn_cl s cl \<equiv> Tn_cl (txn_sn (cls s cl)) cl"

\<comment> \<open>Lemmas about the functions\<close>

lemma add_to_readerset_length_inv: "length (add_to_readerset vl t t') = length vl"
  apply (induction vl, simp)
  subgoal for ver by (cases "v_writer ver = t'"; simp).

lemma add_to_readerset_v_value_inv:
  "v_value (add_to_readerset vl t t' ! i) = v_value (vl ! i)"
  apply (induction vl arbitrary: i, simp)
  subgoal for ver vl i by (cases "v_writer ver = t'"; cases "i = 0"; simp).

lemma add_to_readerset_v_writer_inv:
  "v_writer (add_to_readerset vl t t' ! i) = v_writer (vl ! i)"
  apply (induction vl arbitrary: i, simp)
  subgoal for ver vl i by (cases "v_writer ver = t'"; cases "i = 0"; simp).

lemma add_to_readerset_v_ts_inv:
  "v_ts (add_to_readerset vl t t' ! i) = v_ts (vl ! i)"
  apply (induction vl arbitrary: i, simp)
  subgoal for ver vl i by (cases "v_writer ver = t'"; cases "i = 0"; auto).

lemma add_to_readerset_v_glts_inv:
  "v_glts (add_to_readerset vl t t' ! i) = v_glts (vl ! i)"
  apply (induction vl arbitrary: i, simp)
  subgoal for ver vl i by (cases "v_writer ver = t'"; cases "i = 0"; auto).

lemma add_to_readerset_v_gst_inv:
  "v_gst (add_to_readerset vl t t' ! i) = v_gst (vl ! i)"
  apply (induction vl arbitrary: i, simp)
  subgoal for ver vl i by (cases "v_writer ver = t'"; cases "i = 0"; auto).

lemma add_to_readerset_v_is_pending_inv:
  "v_is_pending (add_to_readerset vl t t' ! i) = v_is_pending (vl ! i)"
  apply (induction vl arbitrary: i, simp)
  subgoal for ver vl i by (cases "v_writer ver = t'"; cases "i = 0"; simp).

lemma index_not_found: "committed_ver vl gts cts i = None \<Longrightarrow> remove_ver vl i = vl"
  by (auto simp add: committed_ver_def remove_ver_def split: option.split)

lemma insert_in_vl_Some_length:
  "length (insert_in_vl vl (Some ver)) = Suc (length vl)"
  by (induction vl; simp)

lemma find_Some_in_set:
  "find P vl = Some ver \<Longrightarrow> ver \<in> set vl"
  apply (simp add: find_Some_iff)
  by (meson nth_mem)

lemma commit_in_vl_length_inv:
  "length (commit_in_vl vl gts cts i) = length vl"
  apply (cases "find (is_txn_writer i) vl"; simp add: commit_in_vl_defs)
  subgoal for ver apply (cases "remove1 ver vl", simp add: find_Some_iff)
    apply (metis Suc_diff_1 length_pos_if_in_set length_remove1 list.size(3) nth_mem)
    using length_remove1
    by (metis One_nat_def Suc_pred find.simps(1) find_Some_in_set insert_in_vl_Some_length
        length_greater_0_conv option.discI).

lemma commit_in_vl_v0_inv:
  assumes "t \<noteq> T0" and "gts > 0" and "vl \<noteq> []"
    and "v_writer (vl ! 0) = T0" and "v_glts (vl ! 0) = 0" and "\<not>v_is_pending (vl ! 0)"
  shows "commit_in_vl vl gts cts t ! 0 = vl ! 0"
  using assms
  apply (cases "find (is_txn_writer t) vl"; cases vl; simp add: commit_in_vl_defs)
  by (metis (mono_tags, lifting) find_Some_iff)


subsubsection \<open>Simulation function\<close>

definition pending_rtxn :: "'v state \<Rightarrow> txid0 \<Rightarrow> bool" where
  "pending_rtxn s t \<equiv> \<exists>keys kv_map. txn_state (cls s (get_cl_txn t)) = RtxnInProg keys kv_map \<and>
    txn_sn (cls s (get_cl_txn t)) = get_sn_txn t"

definition pending_wtxn :: "'v state \<Rightarrow> txid \<Rightarrow> bool" where
  "pending_wtxn s t \<equiv> case t of T0 \<Rightarrow> False |
    Tn (Tn_cl sn cl) \<Rightarrow> \<exists>kv_map. txn_state (cls s cl) = WtxnPrep kv_map \<and> txn_sn (cls s cl) = sn"

definition get_ver_committed_rd :: "'v state \<Rightarrow> 'v ep_version \<Rightarrow> 'v version" where
  "get_ver_committed_rd s \<equiv> (\<lambda>v.
   \<lparr>v_value = v_value v, v_writer = v_writer v, v_readerset = v_readerset v - {t. pending_rtxn s t}\<rparr>)"

definition get_vl_committed_wr :: "'v state \<Rightarrow> 'v ep_version list \<Rightarrow> 'v ep_version list" where
  "get_vl_committed_wr s vl \<equiv> filter (\<lambda>v. \<not>v_is_pending v) vl"

definition get_vl_ready_to_commit_wr :: "'v state \<Rightarrow> 'v ep_version list \<Rightarrow> 'v ep_version list" where
  "get_vl_ready_to_commit_wr s vl \<equiv> filter (\<lambda>v. v_is_pending v \<and> \<not>pending_wtxn s (v_writer v)) vl"

fun commit_all_in_vl :: "'v state \<Rightarrow> 'v ep_version list \<Rightarrow> 'v ep_version list \<Rightarrow> 'v ep_version list" where
  "commit_all_in_vl s vl [] = vl" |
  "commit_all_in_vl s vl (ver # pvl) = commit_all_in_vl s (commit_in_vl vl
    (case v_writer ver of T0 \<Rightarrow> 0 | Tn (Tn_cl sn cl) \<Rightarrow>
     (SOME glts. \<exists>cts kv_map. txn_state (cls s cl) =  WtxnCommit glts cts kv_map)) \<comment> \<open>show as an invariant\<close>
    0 \<comment> \<open>commit_t doesn't matter\<close>
    (v_writer ver)) pvl"

definition get_vl_pre_committed :: "'v state \<Rightarrow> 'v ep_version list \<Rightarrow> 'v ep_version list" where
  "get_vl_pre_committed s vl \<equiv> commit_all_in_vl s (get_vl_committed_wr s vl) (get_vl_ready_to_commit_wr s vl)"

definition kvs_of_s :: "'v state \<Rightarrow> 'v kv_store" where
  "kvs_of_s s = (\<lambda>k. map (get_ver_committed_rd s) (get_vl_pre_committed s (DS (svrs s k))))"

fun indices_map where
  "indices_map [] mp i = mp" |
  "indices_map (ver # vl) mp i = indices_map vl (mp (v_writer ver \<mapsto> i)) (Suc i)"

abbreviation get_indices_map where "get_indices_map vl \<equiv> indices_map vl (Map.empty) 0"

abbreviation get_indices_fun :: "'v state \<Rightarrow> svr_id \<Rightarrow> txid \<Rightarrow> v_id" where
  "get_indices_fun s svr \<equiv>
    (\<lambda>tid. (case get_indices_map (kvs_of_s s svr) tid of
     Some vid \<Rightarrow> vid | None \<Rightarrow> undefined))"

abbreviation view_txid_vid :: "'v state \<Rightarrow> view_txid \<Rightarrow> view" where
  "view_txid_vid s u \<equiv> (\<lambda>k. (get_indices_fun s k) ` (u k))"

definition views_of_s :: "'v state \<Rightarrow> (cl_id \<Rightarrow> view)" where
  "views_of_s s = (\<lambda>cl. view_txid_vid s (cl_view (cls s cl)))"

definition sim :: "'v state \<Rightarrow> 'v config" where         
  "sim s = (kvs_of_s s, views_of_s s)"

lemmas sim_defs = sim_def kvs_of_s_def views_of_s_def
lemmas get_state_defs = get_ver_committed_rd_def get_vl_pre_committed_def 
  get_vl_committed_wr_def get_vl_ready_to_commit_wr_def


subsubsection \<open>Events\<close>

datatype 'v ev =
  RInvoke cl_id "key set" | Read cl_id key 'v | RDone cl_id "key \<rightharpoonup> 'v" sqn view |
  WInvoke cl_id "key \<rightharpoonup> 'v" | WCommit cl_id "key \<rightharpoonup> 'v" tstmp sqn view | WDone cl_id |
  RegR svr_id txid0 'v txid tstmp | PrepW svr_id txid0 'v tstmp | CommitW svr_id txid0 | Skip2

definition svr_t'_unchanged where
  "svr_t'_unchanged t k s s' \<equiv> \<forall>t'. t' \<noteq> t \<longrightarrow>
    wtxn_state (svrs s' k) t' = wtxn_state (svrs s k) t'"

definition other_insts_unchanged where
  "other_insts_unchanged e s s' \<equiv> \<forall>e'. e' \<noteq> e \<longrightarrow> s' e' = s e'"

definition cls_svr_k'_t'_unchanged where
  "cls_svr_k'_t'_unchanged t k s s' \<equiv> cls s' = cls s \<and>
    other_insts_unchanged k (svrs s) (svrs s') \<and> svr_t'_unchanged t k s s'"

definition svrs_cls_cl'_unchanged where
  "svrs_cls_cl'_unchanged cl s s' \<equiv> svrs s' = svrs s \<and> other_insts_unchanged cl (cls s) (cls s')"

lemmas svr_unchanged_defs = cls_svr_k'_t'_unchanged_def other_insts_unchanged_def svr_t'_unchanged_def
lemmas cl_unchanged_defs = svrs_cls_cl'_unchanged_def other_insts_unchanged_def
lemmas unchanged_defs = svr_unchanged_defs svrs_cls_cl'_unchanged_def

definition tid_match :: "'v state \<Rightarrow> txid0 \<Rightarrow> bool" where
  "tid_match s t \<equiv> txn_sn (cls s (get_cl_txn t)) = get_sn_txn t"

\<comment> \<open>Clint Events\<close>
definition read_invoke :: "cl_id \<Rightarrow> key set \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read_invoke cl keys s s' \<equiv>
    txn_state (cls s cl) = Idle \<and>
    txn_state (cls s' cl) = RtxnInProg keys (Map.empty) \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = max (gst (cls s cl)) (Min (range (lst_map (cls s cl)))) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    cl_clock (cls s' cl) = Suc (cl_clock (cls s cl)) \<and>
    svrs_cls_cl'_unchanged cl s s' \<and>
    global_time s' = Suc (global_time s)"

fun find_and_read_val :: "'v ep_version list \<Rightarrow> txid0 \<rightharpoonup> 'v" where
  "find_and_read_val [] t = None" |
  "find_and_read_val (ver # vl) t =
    (if t \<in> v_readerset ver then Some (v_value ver) else find_and_read_val vl t)"

definition read :: "cl_id \<Rightarrow> key \<Rightarrow> 'v \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read cl k v s s' \<equiv> \<exists>keys vals.
    txn_state (cls s cl) = RtxnInProg keys vals \<and> k \<in> keys \<and> vals k = None \<and>
    Some v = find_and_read_val (DS (svrs s k)) (get_txn_cl s cl) \<and>
    txn_state (cls s' cl) = RtxnInProg keys (vals (k \<mapsto> v)) \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) k = lst (svrs s k) \<and>
    (\<forall>k'. k' \<noteq> k \<longrightarrow> lst_map (cls s' cl) k' = lst_map (cls s cl) k') \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    cl_clock (cls s' cl) = Suc (max (cl_clock (cls s cl)) (clock (svrs s k))) \<and>
    svrs_cls_cl'_unchanged cl s s' \<and>
    global_time s' = Suc (global_time s)"

definition read_done :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read_done cl kv_map sn u'' s s' \<equiv>
    sn = txn_sn (cls s cl) \<and>
    u'' = views_of_s s' cl \<and>
    txn_state (cls s cl) = RtxnInProg (dom kv_map) kv_map \<and>
    txn_state (cls s' cl) = Idle \<and>
    txn_sn (cls s' cl) = Suc (txn_sn (cls s cl)) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    (\<forall>k \<in> dom kv_map. cl_view (cls s' cl) k =
      insert (ver_writer (read_at (DS (svrs s k)) (gst (cls s cl)) cl)) (cl_view (cls s cl) k)) \<and>
    (\<forall>k. k \<notin> dom kv_map \<longrightarrow> cl_view (cls s' cl) k = cl_view (cls s cl) k) \<and>
    cl_clock (cls s' cl) = Suc (cl_clock (cls s cl)) \<and>
    svrs_cls_cl'_unchanged cl s s' \<and>
    global_time s' = Suc (global_time s)"

definition write_invoke :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "write_invoke cl kv_map s s' \<equiv> 
    kv_map \<noteq> Map.empty \<and>
    txn_state (cls s cl) = Idle \<and>
    txn_state (cls s' cl) = WtxnPrep kv_map \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    cl_clock (cls s' cl) = Suc (cl_clock (cls s cl)) \<and>
    svrs_cls_cl'_unchanged cl s s' \<and>
    global_time s' = Suc (global_time s)"

definition write_commit :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> tstmp \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "write_commit cl kv_map commit_t sn u s s' \<equiv>
    sn = txn_sn (cls s cl) \<and>
    u = views_of_s s cl \<and>
    txn_state (cls s cl) = WtxnPrep kv_map \<and>
    (\<forall>k \<in> dom kv_map. \<exists>prep_t.
      wtxn_state (svrs s k) (get_txn_cl s cl) = Prep prep_t \<and>
      cl_view (cls s' cl) k = insert (Tn (get_txn_cl s cl)) (cl_view (cls s cl) k)) \<and>
    commit_t = Max {prep_t. (\<exists>k \<in> dom kv_map.
      wtxn_state (svrs s k) (get_txn_cl s cl) = Prep prep_t)} \<and>
    txn_state (cls s' cl) = WtxnCommit (global_time s) commit_t kv_map \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    (\<forall>k. k \<notin> dom kv_map \<longrightarrow> cl_view (cls s' cl) k = cl_view (cls s cl) k) \<and>
    cl_clock (cls s' cl) = Suc (max (cl_clock (cls s cl)) commit_t) \<and>
    svrs_cls_cl'_unchanged cl s s' \<and>
    global_time s' = Suc (global_time s)"

definition write_done :: "cl_id \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "write_done cl s s' \<equiv> \<exists>global_ts commit_t kv_map.
    txn_state (cls s cl) = WtxnCommit global_ts commit_t kv_map \<and>
    (\<forall>k\<in>dom kv_map. wtxn_state (svrs s k) (get_txn_cl s cl) = Commit) \<and>
    txn_state (cls s' cl) = Idle \<and>
    txn_sn (cls s' cl) = Suc (txn_sn (cls s cl)) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    (\<forall>k \<in> dom kv_map. lst_map (cls s' cl) k = lst (svrs s k)) \<and>
    (\<forall>k. k \<notin> dom kv_map \<longrightarrow> lst_map (cls s' cl) k = lst_map (cls s cl) k) \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    cl_clock (cls s' cl) = Suc (cl_clock (cls s cl)) \<and>
    svrs_cls_cl'_unchanged cl s s' \<and>
    global_time s' = Suc (global_time s)"

\<comment> \<open>Server Events\<close>
definition register_read :: "svr_id \<Rightarrow> txid0 \<Rightarrow> 'v \<Rightarrow> txid \<Rightarrow> tstmp \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "register_read svr t v t' gst_ts s s' \<equiv>
    tid_match s t \<and>
    (\<exists>keys vals.
      txn_state (cls s (get_cl_txn t)) = RtxnInProg keys vals \<and> svr \<in> keys \<and> vals svr = None) \<and>
    \<lparr>ver_val = v, ver_writer = t' \<rparr> = read_at (DS (svrs s svr)) gst_ts (get_cl_txn t) \<and>
    gst_ts = gst (cls s (get_cl_txn t)) \<and>
    wtxn_state (svrs s' svr) = wtxn_state (svrs s svr) \<and>
    clock (svrs s' svr) = Suc (clock (svrs s svr)) \<and>
    lst (svrs s' svr) = lst (svrs s svr) \<and>
    DS (svrs s' svr) = add_to_readerset (DS (svrs s svr)) t t' \<and>
    cls_svr_k'_t'_unchanged t svr s s' \<and>
    global_time s' = Suc (global_time s)"

definition prepare_write :: "svr_id \<Rightarrow> txid0 \<Rightarrow> 'v \<Rightarrow> tstmp \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "prepare_write svr t v gst_ts s s' \<equiv>
    tid_match s t \<and>
    (\<exists>kv_map.
      txn_state (cls s (get_cl_txn t)) = WtxnPrep kv_map \<and> svr \<in> dom kv_map \<and> kv_map svr = Some v) \<and>
    gst_ts = gst (cls s (get_cl_txn t)) \<and>
    wtxn_state (svrs s svr) t = Ready \<and>
    wtxn_state (svrs s' svr) t = Prep (clock (svrs s svr)) \<and>
    clock (svrs s' svr) = Suc (max (clock (svrs s svr)) (cl_clock (cls s (get_cl_txn t)))) \<and>
    lst (svrs s' svr) = lst (svrs s svr) \<and>
    DS (svrs s' svr) = DS (svrs s svr) @
      [\<lparr>v_value = v, v_writer = Tn t, v_readerset = {}, v_ts = clock (svrs s svr), v_glts = 10000,
       v_gst = gst_ts, v_is_pending = True \<rparr>] \<and>
    cls_svr_k'_t'_unchanged t svr s s' \<and>
    global_time s' = Suc (global_time s)"

abbreviation pending_wtxns where
  "pending_wtxns s k \<equiv> {prep_t. \<exists>t. wtxn_state (svrs s k) t = Prep prep_t}"

lemma pending_wtxns_empty [simp]:
  "pending_wtxns s k = {} \<longleftrightarrow> (\<forall>t. wtxn_state (svrs s k) t \<in> {Ready, Commit})"
  apply (auto) apply (meson state_wtxn.exhaust)
  by (metis state_wtxn.distinct(1) state_wtxn.distinct(5))

lemma pending_wtxns_non_empty [simp]:
  assumes "wtxn_state (svrs s k) t \<noteq> Ready"
    and "wtxn_state (svrs s k) t \<noteq> Commit"
  shows "pending_wtxns s k \<noteq> {}"
  using assms apply (auto)
  by (meson state_wtxn.exhaust)

definition commit_write :: "svr_id \<Rightarrow> txid0 \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "commit_write svr t s s' \<equiv>
    tid_match s t \<and>
    (\<exists>global_ts commit_t kv_map.
      txn_state (cls s (get_cl_txn t)) = WtxnCommit global_ts commit_t kv_map \<and> svr \<in> dom kv_map \<and>
      (\<exists>prep_t. wtxn_state (svrs s svr) t = Prep prep_t \<and>
       DS (svrs s' svr) = commit_in_vl (DS (svrs s svr)) global_ts commit_t (Tn t))) \<and>
    wtxn_state (svrs s' svr) t = Commit \<and>
    clock (svrs s' svr) = Suc (max (clock (svrs s svr)) (cl_clock (cls s (get_cl_txn t)))) \<and>
    lst (svrs s' svr) =
      (if pending_wtxns s' svr = {} then clock (svrs s svr) else Min (pending_wtxns s' svr)) \<and>
    cls_svr_k'_t'_unchanged t svr s s' \<and>
    global_time s' = Suc (global_time s)"

subsubsection \<open>The Event System\<close>

definition state_init :: "'v state" where
  "state_init \<equiv> \<lparr> 
    cls = (\<lambda>cl. \<lparr> txn_state = Idle,
                  txn_sn = 0,
                  gst = 0,
                  lst_map = (\<lambda>svr. 0),
                  cl_view = view_txid_init,
                  cl_clock = 0 \<rparr>),
    svrs = (\<lambda>svr. \<lparr> wtxn_state = (\<lambda>t. Ready),
                    clock = 0,
                    lst = 0,
                    DS = DS_vl_init \<rparr>),
    global_time = Suc 0
  \<rparr>"

fun state_trans :: "'v state \<Rightarrow> 'v ev \<Rightarrow> 'v state \<Rightarrow> bool" where
  "state_trans s (RInvoke cl keys)        s' \<longleftrightarrow> read_invoke cl keys s s'" |
  "state_trans s (Read cl k v)            s' \<longleftrightarrow> read cl k v s s'" |
  "state_trans s (RDone cl kv_map sn u)   s' \<longleftrightarrow> read_done cl kv_map sn u s s'" |
  "state_trans s (WInvoke cl kv_map)      s' \<longleftrightarrow> write_invoke cl kv_map s s'" |
  "state_trans s (WCommit cl kv_map cts sn u)  s' \<longleftrightarrow> write_commit cl kv_map cts sn u s s'" |
  "state_trans s (WDone cl)               s' \<longleftrightarrow> write_done cl s s'" |
  "state_trans s (RegR svr t v i gts)     s' \<longleftrightarrow> register_read svr t v i gts s s'" |
  "state_trans s (PrepW svr t v gts)      s' \<longleftrightarrow> prepare_write svr t v gts s s'" |
  "state_trans s (CommitW svr t)          s' \<longleftrightarrow> commit_write svr t s s'" |
  "state_trans s Skip2 s' \<longleftrightarrow> s' = s"

definition tps :: "('v ev, 'v state) ES" where
  "tps \<equiv> \<lparr>
    init = (=) state_init,
    trans = state_trans
  \<rparr>"

lemmas tps_trans_defs = read_invoke_def read_def read_done_def write_invoke_def write_commit_def
  write_done_def register_read_def prepare_write_def commit_write_def

lemmas tps_defs = tps_def state_init_def

lemma tps_trans [simp]: "trans tps = state_trans" by (simp add: tps_def)

\<comment> \<open>Mediator function\<close>
fun med :: "'v ev \<Rightarrow> 'v label" where
  "med (RDone cl kv_map sn u'') = ET cl sn u'' (\<lambda>k op. case op of R \<Rightarrow> kv_map k | W \<Rightarrow> None)" |
  "med (WCommit cl kv_map _ sn u'') = ET cl sn u'' (\<lambda>k op. case op of R \<Rightarrow> None | W \<Rightarrow> kv_map k)" |
  "med _ = ETSkip"


subsection \<open>Invariants and lemmas\<close>

\<comment> \<open>lemmas for unchanged elements in svrs\<close>

lemma DS_eq_all_k:
  assumes "DS (svrs s' k) = DS (svrs s k)"
    and "other_insts_unchanged k (svrs s) (svrs s')"
  shows "\<forall>k. DS (svrs s' k) = DS (svrs s k)"
  using assms by (auto simp add: other_insts_unchanged_def)

lemma eq_for_all_k: 
  assumes "f (svrs s' k) = f (svrs s k)"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> svrs s' k' = svrs s k'"
  shows "\<forall>k. f (svrs s' k) = f (svrs s k)"
  apply (auto simp add: fun_eq_iff) using assms
  subgoal for k' by (cases "k' = k"; simp).

lemma eq_for_all_k_t: 
  assumes "f (svrs s' k) t = f (svrs s k) t"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> svrs s' k' = svrs s k'"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> f (svrs s' k) t' = f (svrs s k) t'"
  shows "\<forall>k. f (svrs s' k) = f (svrs s k)"
  apply (auto simp add: fun_eq_iff) using assms
  subgoal for k' t' by (cases "k' = k"; cases "t' = t"; simp).

lemma eq_for_all_cl:
  assumes "f (cls s' cl) = f (cls s cl)"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "\<forall>cl. f (cls s' cl) = f (cls s cl)"
  apply (auto simp add: fun_eq_iff) using assms
  subgoal for cl' by (cases "cl' = cl"; simp).

subsection \<open>monotonic lemmas and inequality of timestamps invariants\<close>

lemma glts_monotonic:
  assumes "state_trans s e s'"
  shows "global_time s' \<ge> global_time s"
  using assms
  by (induction e) (auto simp add: tps_trans_defs)

lemma clock_monotonic:
  assumes "state_trans s e s'"
  shows "clock (svrs s' svr) \<ge> clock (svrs s svr)"
  using assms
proof (induction e)
  case (RegR k t)
  then show ?case apply (auto simp add: register_read_def svr_unchanged_defs)
    by (cases "k = svr"; simp)
next
  case (PrepW k t)
  then show ?case apply (auto simp add: prepare_write_def svr_unchanged_defs)
    by (cases "k = svr"; simp)
next
  case (CommitW k t)
  then show ?case apply (auto simp add: commit_write_def svr_unchanged_defs)
    by (metis le_SucI max.cobounded1 max_def)
qed (auto simp add: tps_trans_defs cl_unchanged_defs dest!:eq_for_all_k)


lemma cl_clock_monotonic:
  assumes "state_trans s e s'"
  shows "cl_clock (cls s' cl) \<ge> cl_clock (cls s cl)"
  using assms
proof (induction e)
  case (RInvoke x1 x2)
  then show ?case apply (auto simp add: read_invoke_def cl_unchanged_defs)
    by (metis Suc_n_not_le_n nat_le_linear)
next
  case (Read x1 x2 x3)
  then show ?case apply (auto simp add: read_def cl_unchanged_defs)
    by (metis Suc_n_not_le_n max.coboundedI1 nat_le_linear)
next
  case (RDone x1 x2 x3 x4)
  then show ?case apply (auto simp add: read_done_def cl_unchanged_defs)
    by (metis Suc_n_not_le_n nat_le_linear)
next
  case (WInvoke x1 x2)
  then show ?case apply (auto simp add: write_invoke_def cl_unchanged_defs)
    by (metis Suc_n_not_le_n nat_le_linear)
next
  case (WCommit x1 x2 x3 x4 x5)
  then show ?case apply (auto simp add: write_commit_def cl_unchanged_defs)
    by (metis (no_types, lifting) le_SucI max.absorb_iff2 max_def)
next
  case (WDone x)
  then show ?case apply (auto simp add: write_done_def cl_unchanged_defs)
    by (metis Suc_n_not_le_n nat_le_linear)
qed (auto simp add: tps_trans_defs svr_unchanged_defs dest!:eq_for_all_k)


definition PendingWtxnsUB where
  "PendingWtxnsUB s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns s svr. ts \<le> clock (svrs s svr))"

lemmas PendingWtxnsUBI = PendingWtxnsUB_def[THEN iffD2, rule_format]
lemmas PendingWtxnsUBE[elim] = PendingWtxnsUB_def[THEN iffD1, elim_format, rule_format]

lemma reach_PendingWtxnsUB [simp, dest]: "reach tps s \<Longrightarrow> PendingWtxnsUB s svr"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: PendingWtxnsUB_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (Read x1 x2 x3)
    then show ?case by (auto simp add: PendingWtxnsUB_def tps_trans_defs cl_unchanged_defs, blast)
  next
    case (WDone x)
    then show ?case by (auto simp add: PendingWtxnsUB_def tps_trans_defs cl_unchanged_defs, blast)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: PendingWtxnsUB_def tps_trans_defs svr_unchanged_defs)
      by (metis le_Suc_eq)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case  apply (auto simp add: PendingWtxnsUB_def tps_trans_defs svr_unchanged_defs ran_def)
      by (smt (z3) Suc_leD Suc_le_D max.bounded_iff not_less_eq_eq state_wtxn.inject)
  next
    case (CommitW x1 x2)
    then show ?case apply (auto simp add: PendingWtxnsUB_def tps_trans_defs svr_unchanged_defs ran_def)
      by (smt (z3) Suc_n_not_le_n max.bounded_iff max_def_raw state_wtxn.distinct(5))
  qed (auto simp add: PendingWtxnsUB_def tps_trans_defs cl_unchanged_defs)
qed


lemma finite_pending_wtxns_adding: 
  assumes "wtxn_state (svrs s' k) t = Prep prep_t"
    and "finite (pending_wtxns s svr)"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> wtxn_state (svrs s' k) t' = wtxn_state (svrs s k) t'"
  shows "finite (pending_wtxns s' svr)"
  using assms apply (auto simp add: finite_nat_set_iff_bounded_le)
  by (metis le_trans nat_le_linear state_wtxn.inject)

lemma finite_pending_wtxns_removing: 
  assumes "wtxn_state (svrs s' k) t = Commit"
    and "finite (pending_wtxns s svr)"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> wtxn_state (svrs s' k) t' = wtxn_state (svrs s k) t'"
  shows "finite (pending_wtxns s' svr)"
  using assms
  by (smt (verit, del_insts) finite_nat_set_iff_bounded_le mem_Collect_eq state_wtxn.distinct(5))

definition FinitePendingInv where
  "FinitePendingInv s svr \<longleftrightarrow> finite (pending_wtxns s svr)"

lemmas FinitePendingInvI = FinitePendingInv_def[THEN iffD2, rule_format]
lemmas FinitePendingInvE[elim] = FinitePendingInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_finitepending [simp, dest]: "reach tps s \<Longrightarrow> FinitePendingInv s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FinitePendingInv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (RegR x71 x72 x73 x74 x75)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs svr_unchanged_defs FinitePendingInv_def dest!: eq_for_all_k)
  next
    case (PrepW x81 x82 x83 x84)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs svr_unchanged_defs FinitePendingInv_def dest!: finite_pending_wtxns_adding)
  next
    case (CommitW x91 x92)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs svr_unchanged_defs FinitePendingInv_def dest!: finite_pending_wtxns_removing)
  qed (auto simp add: tps_trans_defs cl_unchanged_defs FinitePendingInv_def)
qed

lemma pending_wtxns_adding:
  assumes "wtxn_state (svrs s' k) t = Prep clk"
    and "\<forall>ts \<in> pending_wtxns s k. ts \<le> clk"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> wtxn_state (svrs s' k) t' = wtxn_state (svrs s k) t'"
  shows "\<forall>ts \<in> pending_wtxns s' k. ts \<le> clk"
  using assms apply (auto simp add: finite_nat_set_iff_bounded_le)
  by (metis order_refl state_wtxn.inject)

lemma pending_wtxns_removing:
  assumes "wtxn_state (svrs s' k) t = Commit"
    and "\<forall>ts \<in> pending_wtxns s k. ts \<le> clk"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> wtxn_state (svrs s' k) t' = wtxn_state (svrs s k) t'"
  shows "\<forall>ts \<in> pending_wtxns s' k. ts \<le> clk"
  using assms apply (auto simp add: finite_nat_set_iff_bounded_le)
  by (metis state_wtxn.distinct(5))

lemma all_smaller_min_smaller:
  assumes "finite a"
    and "a \<noteq> {}"
    and "\<forall>s \<in> a. s \<le> b"
  shows "Min a \<le> b"
  using assms by auto

definition ClockLstInv where
  "ClockLstInv s \<longleftrightarrow> (\<forall>svr. lst (svrs s svr) \<le> clock (svrs s svr))"

lemmas ClockLstInvI = ClockLstInv_def[THEN iffD2, rule_format]
lemmas ClockLstInvE[elim] = ClockLstInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_clocklstinv [simp, dest]: "reach tps s \<Longrightarrow> ClockLstInv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: ClockLstInv_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x71 x72 x73 x74 x75)
    then show ?case apply (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs)
      by (metis le_Suc_eq)
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case apply (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs)
      by (metis (no_types, lifting) clock_monotonic dual_order.trans reach_trans.hyps(1) tps_trans)
  next
    case (CommitW x91 x92)
    then show ?case apply (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs)
      apply (cases "pending_wtxns s' x91 = {}")
       apply (smt (z3) CommitW.prems(1) clock_monotonic equals0D mem_Collect_eq tps_trans)
    proof -
      fix svr
      assume a: "pending_wtxns s' x91 \<noteq> {}"
      hence fin: "finite (pending_wtxns s' x91)" using CommitW
        apply (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs)
        by (metis (mono_tags) FinitePendingInv_def reach.reach_trans reach_finitepending
            reach_trans.hyps(1) reach_trans.hyps(2))
      hence clk_ub: "\<forall>ts \<in> pending_wtxns s' x91. ts \<le> clock (svrs s x91)" using CommitW
        by (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs
            dest!: pending_wtxns_removing [of s' x91 x92 s "clock (svrs s x91)"])
      hence "Min (pending_wtxns s' x91) \<le> clock (svrs s x91)" using a fin CommitW
        apply (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs)
        by (metis (mono_tags, lifting) Min_in clk_ub a)
      then show "lst (svrs s' svr) \<le> clock (svrs s' svr)" using CommitW
        by (cases "svr = x91"; auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs)
    qed
  qed (auto simp add: ClockLstInv_def tps_trans_defs cl_unchanged_defs)
qed

definition PendingWtxnsLB where
  "PendingWtxnsLB s svr \<longleftrightarrow> (\<forall>ts \<in> pending_wtxns s svr. lst (svrs s svr) \<le> ts)"

lemmas PendingWtxnsLBI = PendingWtxnsLB_def[THEN iffD2, rule_format]
lemmas PendingWtxnsLBE[elim] = PendingWtxnsLB_def[THEN iffD1, elim_format, rule_format]

lemma reach_PendingWtxnsLB [simp, dest]: "reach tps s \<Longrightarrow> PendingWtxnsLB s svr"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: PendingWtxnsLB_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (Read x1 x2 x3)
    then show ?case by (auto simp add: PendingWtxnsLB_def tps_trans_defs cl_unchanged_defs, blast)
  next
    case (WDone x)
    then show ?case by (auto simp add: PendingWtxnsLB_def tps_trans_defs cl_unchanged_defs, blast)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case by (auto simp add: PendingWtxnsLB_def tps_trans_defs svr_unchanged_defs, metis)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case  apply (auto simp add: PendingWtxnsLB_def tps_trans_defs svr_unchanged_defs)
      by (metis ClockLstInv_def reach_clocklstinv state_wtxn.inject)
  next
    case (CommitW x1 x2)
    then show ?case apply (auto simp add: PendingWtxnsLB_def tps_trans_defs svr_unchanged_defs)
      apply (cases "pending_wtxns s' x1 = {}")
       apply (metis (mono_tags, lifting) ex_in_conv mem_Collect_eq)
      apply (cases "svr = x1"; auto)
      subgoal for x glts commit_t kv_map prep_t y t apply (cases "t = x2"; auto)
        proof -
          fix t x
          assume a: "wtxn_state (svrs s x1) t = Prep x" and b: "t \<noteq> x2"
          hence fin: "finite (pending_wtxns s' x1)" using CommitW
            apply (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs)
            by (metis (mono_tags) FinitePendingInv_def reach.reach_trans reach_finitepending
                reach_trans.hyps(1) reach_trans.hyps(2))
          then show "Min (pending_wtxns s' x1) \<le> x" using a b CommitW
            apply (auto simp add: PendingWtxnsLB_def tps_trans_defs svr_unchanged_defs)
            by (metis (mono_tags, lifting) Min.coboundedI mem_Collect_eq)
        qed.
  qed (auto simp add: PendingWtxnsLB_def tps_trans_defs cl_unchanged_defs)
qed

lemma min_pending_wtxns_monotonic:
  assumes "state_trans s e s'"
    and "pending_wtxns s' k \<noteq> {}"
  shows "Min (pending_wtxns s k) \<le> Min (pending_wtxns s' k)"
  using assms
  proof (induction e)
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (auto simp add: prepare_write_def svr_unchanged_defs)
      apply (cases "k = x1"; auto) sorry
  next
    case (CommitW x1 x2)
    then show ?case apply (auto simp add: commit_write_def svr_unchanged_defs)
      apply (cases "k = x1"; auto) subgoal for x t apply (cases "t = x2"; auto) sorry.
  qed (auto simp add: tps_trans_defs unchanged_defs dest!: eq_for_all_k)

lemma lst_monotonic:
  assumes "state_trans s e s'"
    and "ClockLstInv s"
  shows "lst (svrs s' svr) \<ge> lst (svrs s svr)"
  using assms
  proof (induction e)
    case (CommitW k t)
    then show ?case apply (auto simp add: commit_write_def svr_unchanged_defs)
      apply (cases "pending_wtxns s' k = {}"; cases "svr = k"; auto) sorry
  qed (auto simp add: tps_trans_defs unchanged_defs dest!:eq_for_all_k)

lemma gst_monotonic:
  assumes "state_trans s e s'"
  shows "gst (cls s' cl) \<ge> gst (cls s cl)"
  using assms
proof (induction e)
  case (RInvoke x1 x2)
  then show ?case apply (auto simp add: read_invoke_def cl_unchanged_defs)
    by (metis dual_order.refl max.cobounded1)
qed (auto simp add: tps_trans_defs unchanged_defs dest!:eq_for_all_cl)

\<comment> \<open>Invariants about kv store\<close>

definition KVSNonEmp where
  "KVSNonEmp s \<longleftrightarrow> (\<forall>k. DS (svrs s k) \<noteq> [])"

lemmas KVSNonEmpI = KVSNonEmp_def[THEN iffD2, rule_format]
lemmas KVSNonEmpE[elim] = KVSNonEmp_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_non_emp [simp, intro]: "reach tps s \<Longrightarrow> KVSNonEmp s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: KVSNonEmp_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: KVSNonEmp_def tps_trans_defs svr_unchanged_defs)
      by (metis add_to_readerset_length_inv length_0_conv)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: KVSNonEmp_def tps_trans_defs svr_unchanged_defs)
      by (metis Nil_is_append_conv)
  next
    case (CommitW x1 x2)
    then show ?case
      apply (auto simp add: KVSNonEmp_def tps_trans_defs svr_unchanged_defs)
      using commit_in_vl_length_inv by (metis length_0_conv)
  qed (auto simp add: KVSNonEmp_def tps_trans_defs cl_unchanged_defs)
qed

lemma non_empty_0_inv: "vl \<noteq> [] \<Longrightarrow> (vl @ [a]) ! 0 = vl ! 0"
  by (cases vl; auto)

lemma find_append: "find P (l1 @ l2) = (case find P l1 of None \<Rightarrow> find P l2 | Some a \<Rightarrow> Some a)"
  by (induction l1; simp)

definition GltsNotZero where
  "GltsNotZero s \<longleftrightarrow> global_time s > 0"

lemmas GltsNotZeroI = GltsNotZero_def[THEN iffD2, rule_format]
lemmas GltsNotZeroE[elim] = GltsNotZero_def[THEN iffD1, elim_format, rule_format]

lemma reach_glts_not_zero [simp, intro]: "reach tps s \<Longrightarrow> GltsNotZero s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: GltsNotZero_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (metis GltsNotZero_def bot_nat_0.extremum_uniqueI glts_monotonic gr0I tps_trans)
qed

definition CommitGltsNotZero where
  "CommitGltsNotZero s cl \<longleftrightarrow> (\<forall>gts cts kv_map. txn_state (cls s cl) = WtxnCommit gts cts kv_map \<longrightarrow> gts > 0)"

lemmas CommitGltsNotZeroI = CommitGltsNotZero_def[THEN iffD2, rule_format]
lemmas CommitGltsNotZeroE[elim] = CommitGltsNotZero_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_glts_not_zero [simp, intro]: "reach tps s \<Longrightarrow> CommitGltsNotZero s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: CommitGltsNotZero_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (auto simp add: CommitGltsNotZero_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(9))
  next
    case (Read x1 x2 x3)
    then show ?case apply (auto simp add: CommitGltsNotZero_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: CommitGltsNotZero_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(5))
  next
    case (WInvoke x1 x2)
    then show ?case apply (auto simp add: CommitGltsNotZero_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(11))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: CommitGltsNotZero_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) GltsNotZero_def reach_glts_not_zero state_txn.inject(3))
  next
    case (WDone x)
    then show ?case apply (auto simp add: CommitGltsNotZero_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(5))
  qed (auto simp add: CommitGltsNotZero_def tps_trans_defs svr_unchanged_defs)
qed
 

definition InitVerInv where
  "InitVerInv s k \<longleftrightarrow> v_writer (DS (svrs s k) ! 0) = T0 \<and> v_glts (DS (svrs s k) ! 0) = 0 \<and>
    \<not>v_is_pending (DS (svrs s k) ! 0)"

lemmas InitVerInvI = InitVerInv_def[THEN iffD2, rule_format]
lemmas InitVerInvE[elim] = InitVerInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_init_ver_inv [simp, intro]: "reach tps s \<Longrightarrow> InitVerInv s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: InitVerInv_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: InitVerInv_def tps_trans_defs svr_unchanged_defs)
      apply (metis add_to_readerset_v_writer_inv)
      apply (metis add_to_readerset_v_glts_inv)
      by (metis add_to_readerset_v_is_pending_inv)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: InitVerInv_def tps_trans_defs svr_unchanged_defs)
      by (metis KVSNonEmp_def non_empty_0_inv reach_kvs_non_emp)+
  next
    case (CommitW x1 x2)
    then show ?case
      apply (auto simp add: InitVerInv_def tps_trans_defs svr_unchanged_defs)
      apply (cases "k = x1"; auto) using commit_in_vl_v0_inv[where vl="(DS (svrs s x1))"]
      apply (metis CommitGltsNotZero_def KVSNonEmp_def reach_commit_glts_not_zero reach_kvs_non_emp
          txid.distinct(1))
      by (metis CommitGltsNotZero_def KVSNonEmp_def commit_in_vl_v0_inv reach_commit_glts_not_zero
          reach_kvs_non_emp txid.distinct(1))+
  qed (auto simp add: InitVerInv_def tps_trans_defs cl_unchanged_defs)
qed

definition KVSNotAllPending where
  "KVSNotAllPending s k \<longleftrightarrow>  \<not>v_is_pending (DS (svrs s k) ! 0)"

lemmas KVSNotAllPendingI = KVSNotAllPending_def[THEN iffD2, rule_format]
lemmas KVSNotAllPendingE[elim] = KVSNotAllPending_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_not_all_pending [simp, intro]: "reach tps s \<Longrightarrow> KVSNotAllPending s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: KVSNotAllPending_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case using reach_trans
      apply (auto simp add: KVSNotAllPending_def tps_trans_defs svr_unchanged_defs)
      apply (cases "k = x1"; auto)
      using add_to_readerset_v_is_pending_inv by blast
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case using reach_trans
      apply (auto simp add: KVSNotAllPending_def tps_trans_defs svr_unchanged_defs)
      apply (cases "k = x1"; auto)
      by (metis KVSNonEmp_def non_empty_0_inv reach_kvs_non_emp)
  next
    case (CommitW x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: KVSNotAllPending_def tps_trans_defs svr_unchanged_defs)
      by (metis InitVerInv_def reach.reach_trans reach_init_ver_inv reach_trans.hyps(1))
  qed (auto simp add: KVSNotAllPending_def tps_trans_defs cl_unchanged_defs)
qed

definition ReadyToCommitVer where
  "ReadyToCommitVer s k \<longleftrightarrow>
    (\<forall>cl v n. v \<in> set (get_vl_ready_to_commit_wr s (DS (svrs s k)))\<and> v_writer v = Tn (Tn_cl n cl) \<longrightarrow>
    (\<exists>glts cts kv_map. txn_state (cls s cl) =  WtxnCommit glts cts kv_map))"

lemmas ReadyToCommitVerI = ReadyToCommitVer_def[THEN iffD2, rule_format]
lemmas ReadyToCommitVerE[elim] = ReadyToCommitVer_def[THEN iffD1, elim_format, rule_format]

lemma reach_ready_to_commit_ver [simp, intro]: "reach tps s \<Longrightarrow> ReadyToCommitVer s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: ReadyToCommitVer_def tps_defs DS_vl_init_def ep_version_init_def get_state_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (auto simp add: ReadyToCommitVer_def tps_trans_defs cl_unchanged_defs
          get_state_defs pending_wtxn_def)
      subgoal for cl apply (cases "x1 = cl"; simp)
      apply (smt (verit) state_txn.distinct(3) state_txn.distinct(5) txid.simps(5) txid0.case)
        by (smt (verit, del_insts) txid.simps(5) txid0.case)
      subgoal for cl apply (cases "x1 = cl"; simp)
        apply (smt (verit) state_txn.distinct(5) txid.simps(5) txid0.case)
        by (smt (verit, ccfv_threshold) txid.simps(5) txid0.case).
  next
    case (Read x1 x2 x3)
    then show ?case apply (auto simp add: ReadyToCommitVer_def tps_trans_defs cl_unchanged_defs
          get_state_defs pending_wtxn_def)
      by (smt (z3) state_txn.distinct(7) state_txn.distinct(9) txid.simps(5) txid0.case)+
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: ReadyToCommitVer_def tps_trans_defs cl_unchanged_defs
          get_state_defs pending_wtxn_def)
      by (smt (z3) state_txn.distinct(7) state_txn.distinct(9) txid.simps(5) txid0.case)+
  next
    case (WInvoke x1 x2)
    then show ?case apply (auto simp add: ReadyToCommitVer_def tps_trans_defs cl_unchanged_defs
          get_state_defs pending_wtxn_def)
      by (smt (z3) state_txn.distinct(5) txid.simps(5) txid0.case)+
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: ReadyToCommitVer_def tps_trans_defs cl_unchanged_defs
          get_state_defs pending_wtxn_def)
      by (smt (z3) state_txn.distinct(5) txid.simps(5) txid0.case)+
  next
    case (WDone x)
    then show ?case apply (auto simp add: ReadyToCommitVer_def tps_trans_defs cl_unchanged_defs
          get_state_defs pending_wtxn_def split: txid.split)
      subgoal for glts cts kvm cl apply (cases "x = cl")
        subgoal sorry
        by (smt (verit, ccfv_threshold) txid.exhaust txid.simps(5) txid0.case).     
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: ReadyToCommitVer_def tps_trans_defs svr_unchanged_defs
          get_state_defs pending_wtxn_def; cases "k = x1"; simp)
      subgoal sorry
        apply (smt (z3) txid.simps(5) txid0.case)
      subgoal sorry
      by (smt (z3) txid.simps(5) txid0.case)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (auto simp add: ReadyToCommitVer_def tps_trans_defs svr_unchanged_defs
          get_state_defs pending_wtxn_def; cases "k = x1"; simp)
      apply (smt get_cl_txn.simps txid.inject txid.simps(5) txid0.case version.select_convs(2))
      apply (smt (z3) txid.simps(5) txid0.case)
      apply (smt get_cl_txn.simps get_sn_txn.cases get_sn_txn.simps tid_match_def txid.simps(5)
          txid0.case version.select_convs(2))
      by (smt (z3) txid.simps(5) txid0.case)
  next
    case (CommitW x1 x2)
    then show ?case apply (auto simp add: ReadyToCommitVer_def tps_trans_defs svr_unchanged_defs
          get_state_defs pending_wtxn_def; cases "k = x1"; simp)
      subgoal sorry
      apply (smt (z3) txid.simps(5) txid0.case)
      subgoal sorry
      by (smt (z3) txid.simps(5) txid0.case)
  qed simp
qed


definition KVSSNonEmp where
  "KVSSNonEmp s \<longleftrightarrow> (\<forall>k. kvs_of_s s k \<noteq> [])"

lemmas KVSSNonEmpI = KVSSNonEmp_def[THEN iffD2, rule_format]
lemmas KVSSNonEmpE[elim] = KVSSNonEmp_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_s_non_emp [simp, intro]:
  assumes "reach tps s"
    and "\<And>k. KVSNotAllPending s k"
  shows "KVSSNonEmp s"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: KVSSNonEmp_def kvs_of_s_def DS_vl_init_def ep_version_init_def get_state_defs
       tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: KVSSNonEmp_def KVSNotAllPending_def tps_trans_defs kvs_of_s_def
        get_state_defs unchanged_defs) sorry
  next
    case (Read x1 x2 x3)
    then show ?case sorry
  next
    case (RDone x1 x2 x3 x4)
    then show ?case sorry
  next
    case (WInvoke x1 x2)
    then show ?case sorry
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (WDone x)
    then show ?case sorry
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case sorry
  next
    case (CommitW x1 x2)
    then show ?case sorry
  qed (auto simp add: KVSSNonEmp_def KVSNotAllPending_def tps_trans_defs kvs_of_s_def
        get_state_defs unchanged_defs; metis (lifting) empty_filter_conv nth_mem)
qed

\<comment> \<open>Invariant about future and past transactions svrs\<close>

definition FutureTIDInv where
  "FutureTIDInv s cl \<longleftrightarrow> (\<forall>n k. n > txn_sn (cls s cl) \<longrightarrow> wtxn_state (svrs s k) (Tn_cl n cl) = Ready)"

lemmas FutureTIDInvI = FutureTIDInv_def[THEN iffD2, rule_format]
lemmas FutureTIDInvE[elim] = FutureTIDInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidfuturekm [simp, dest]: "reach tps s \<Longrightarrow> FutureTIDInv s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FutureTIDInv_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (RInvoke x11 x12)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def, metis)
  next
    case (Read x21 x22 x23)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def, metis)
  next
    case (RDone x31 x32 x33 x34)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def)
      by (metis Suc_lessD)
  next
    case (WInvoke x41 x42)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def, metis)
  next
    case (WCommit x51 x52 x53 x54 x55)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def)
      by (metis (lifting))
  next
    case (WDone x6)
    then show ?thesis  using reach_trans
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def)
      by (metis Suc_lessD)
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def FutureTIDInv_def, metis)
  next
    case (PrepW x81 x82 x83 x84)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def FutureTIDInv_def)
      by (metis get_cl_txn.simps get_sn_txn.simps nat_neq_iff)
  next
    case (CommitW x91 x92)
    then show ?thesis  using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def FutureTIDInv_def)
      by (metis state_wtxn.distinct(1))
  qed simp
qed

definition ReadOnlyTxn where
  "ReadOnlyTxn s cl \<longleftrightarrow> (\<forall>svr ks vs. txn_state (cls s cl) = RtxnInProg ks vs
    \<longrightarrow> wtxn_state (svrs s svr) (get_txn_cl s cl) = Ready)"

lemmas ReadOnlyTxnI = ReadOnlyTxn_def[THEN iffD2, rule_format]
lemmas ReadOnlyTxnE[elim] = ReadOnlyTxn_def[THEN iffD1, elim_format, rule_format]

lemma reach_readonlytxn [simp, dest]: "reach tps s \<Longrightarrow> ReadOnlyTxn s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: ReadOnlyTxn_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (RInvoke x11 x12)
    then show ?thesis using reach_trans
      apply (auto simp add: ReadOnlyTxn_def tps_trans_defs cl_unchanged_defs) sorry
  next
    case (Read x21 x22 x23)
    then show ?thesis sorry
  next
    case (RDone x31 x32 x33 x34)
    then show ?thesis sorry
  next
    case (WInvoke x41 x42)
    then show ?thesis sorry
  next
    case (WCommit x51 x52 x53 x54 x55)
    then show ?thesis sorry
  next
    case (WDone x6)
    then show ?thesis sorry
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?thesis sorry
  next
    case (PrepW x81 x82 x83 x84)
    then show ?thesis sorry
  next
    case (CommitW x91 x92)
    then show ?thesis sorry
  qed (auto simp add: ReadOnlyTxn_def tps_trans_defs unchanged_defs)
qed

definition PastTIDInv where
  "PastTIDInv s cl \<longleftrightarrow> (\<forall>n k. n < txn_sn (cls s cl) \<longrightarrow> wtxn_state (svrs s k) (Tn_cl n cl) \<in> {Ready, Commit})"

lemmas PastTIDInvI = PastTIDInv_def[THEN iffD2, rule_format]
lemmas PastTIDInvE[elim] = PastTIDInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidpastkm [simp, dest]: "reach tps s \<Longrightarrow> PastTIDInv s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: PastTIDInv_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (RInvoke x11 x12)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def, metis)
  next
    case (Read x21 x22 x23)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def, metis)
  next
    case (RDone x31 x32 x33 x34)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def)
      by (metis ReadOnlyTxn_def not_less_less_Suc_eq reach_readonlytxn reach_trans.hyps(2))
  next
    case (WInvoke x41 x42)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def, metis)
  next
    case (WCommit x51 x52 x53 x54 x55)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def)
      by (metis (lifting))
  next
    case (WDone x6)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def) sorry
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def PastTIDInv_def, metis)
  next
    case (PrepW x81 x82 x83 x84)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def PastTIDInv_def)
      by (metis get_cl_txn.simps get_sn_txn.simps nat_neq_iff)
  next
    case (CommitW x91 x92)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def PastTIDInv_def, fastforce)
  qed simp
qed

lemma other_sn_idle:  
  assumes "FutureTIDInv s cl" and "PastTIDInv s cl"
    and "get_cl_txn t = cl" and "get_sn_txn t \<noteq> txn_sn (cls s cl)"
  shows "\<And>k. wtxn_state (svrs s k) t \<in> {Ready, Commit}"
  using assms
  apply (auto simp add: FutureTIDInv_def PastTIDInv_def)
  apply (cases "get_sn_txn t > txn_sn (cls s cl)")
  apply (metis get_cl_txn.elims get_sn_txn.simps)
  by (metis get_cl_txn.elims get_sn_txn.simps linorder_cases)

abbreviation not_committing_ev where
  "not_committing_ev e \<equiv> \<forall>cl kv_map cts sn u. e \<noteq> RDone cl kv_map sn u \<and> e \<noteq> WCommit cl kv_map cts sn u"

abbreviation invariant_list_kvs where
  "invariant_list_kvs s \<equiv> \<forall>cl k. FutureTIDInv s cl \<and> PastTIDInv s cl \<and> KVSNonEmp s \<and> KVSNotAllPending s k"

abbreviation invariant_list where
  "invariant_list s \<equiv> invariant_list_kvs s"
                                                               
subsection \<open>Refinement Proof\<close>

(*need to add an invariant t is not in the v_readerset in the beginning of the transaction*)

lemma pending_rtxn_inv:
  assumes "\<forall>keys kv_map. txn_state (cls s cl) \<noteq> RtxnInProg keys kv_map"
    and "\<forall>keys kv_map. txn_state (cls s' cl) \<noteq> RtxnInProg keys kv_map"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "pending_rtxn s' t = pending_rtxn s t"
  using assms
  apply (auto simp add: pending_rtxn_def)oops

lemma pending_wtxn_inv:
  assumes "\<forall>kv_map. txn_state (cls s cl) \<noteq> WtxnPrep kv_map"
    and "\<forall>kv_map. txn_state (cls s' cl) \<noteq> WtxnPrep kv_map"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "pending_wtxn s' t = pending_wtxn s t"
  using assms
  by (auto simp add: pending_wtxn_def split: txid.split txid0.split)

lemma kvs_of_s_inv:
  assumes "state_trans s e s'"
    and "invariant_list_kvs s"
    and "not_committing_ev e"
  shows "kvs_of_s s' = kvs_of_s s"
  using assms
  proof (induction e)
    case (RInvoke x1 x2)
    then have "\<And>v. get_ver_committed_rd s' v = get_ver_committed_rd s v"
      apply (auto simp add: tps_trans_defs get_ver_committed_rd_def) sorry
    then show ?case using RInvoke reach_trans pending_wtxn_inv[of s x1 s']
      apply (auto simp add: tps_trans_defs kvs_of_s_def get_state_defs cl_unchanged_defs) sorry
  next
    case (Read x1 x2 x3)
    then show ?case sorry
  next
    case (WInvoke x1 x2)
    then show ?case sorry
  next
    case (WDone x)
    then show ?case sorry
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case sorry
  next
    case (CommitW x1 x2)
    then show ?case sorry
  qed auto

lemma indices_map_get_ver_committed_rd_inv:
  "indices_map (map (get_ver_committed_rd s) vl) mp i = indices_map vl mp i"
  apply (simp add: get_ver_committed_rd_def)
  by (induction vl arbitrary: s mp i; simp)

lemma indices_map_other_cl_inv:
  assumes "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
    and "cl' \<noteq> cl"
  shows "get_indices_map (kvs_of_s s' k) = get_indices_map (kvs_of_s s k)"
  using assms 
  apply (simp add: kvs_of_s_def get_vl_pre_committed_def indices_map_get_ver_committed_rd_inv) sorry

subsection\<open>View invariants\<close>

lemma cl_view_inv:
  assumes "state_trans s e s'"
    and "not_committing_ev e"
  shows "cl_view (cls s' cl) = cl_view (cls s cl)"
  using assms
  by (induction e) (auto simp add: tps_trans_defs unchanged_defs views_of_s_def dest!:eq_for_all_cl)

lemma views_of_s_inv:
  assumes "state_trans s e s'"
    and "invariant_list_kvs s"
    and "not_committing_ev e"
  shows "views_of_s s' cl = views_of_s s cl"
  using assms using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case by simp
  qed (auto simp add: tps_trans_defs unchanged_defs views_of_s_def dest!:eq_for_all_cl)

lemma views_of_s_other_cl_inv:
  assumes "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
    and "cl' \<noteq> cl"
  shows "views_of_s s' cl' = views_of_s s cl'"
  using assms
  apply (auto simp add: views_of_s_def cl_unchanged_defs image_def split: option.split)
  apply (rule ext) subgoal for k using indices_map_other_cl_inv[of cl s s' cl' k]
  by (simp add: assms(1)).

lemma tps_refines_et_es: "tps \<sqsubseteq>\<^sub>med ET_CC.ET_ES"
proof (intro simulate_ES_fun_with_invariant[where I="\<lambda>s. invariant_list s"])
  fix gs0 :: "'v state"
  assume p: "init tps gs0"
  then show "init ET_CC.ET_ES (sim gs0)"
    by (auto simp add: ET_CC.ET_ES_defs tps_defs sim_defs DS_vl_init_def ep_version_init_def
        get_state_defs kvs_init_def v_list_init_def version_init_def view_txid_init_def)
next
  fix gs a and gs' :: "'v state"
  assume p: "tps: gs\<midarrow>a\<rightarrow> gs'" and inv: "invariant_list gs"
  then show "ET_CC.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  using kvs_of_s_inv[of gs a gs'] views_of_s_inv[of gs a gs']
  proof (induction a)
    case (RDone cl kv_map sn u)
    then show ?case using p apply simp
      apply (auto simp add: read_done_def cl_unchanged_defs sim_def)
      apply (rule exI [where x="views_of_s gs' cl"]) apply auto
        subgoal apply (auto simp add: ET_CC.ET_cl_txn_def) sorry
        subgoal apply (rule ext)
          subgoal for cl' apply (cases "cl' = cl"; simp)
          using views_of_s_other_cl_inv[of cl gs gs' cl'] by (simp add: other_insts_unchanged_def).
      subgoal apply (auto simp add: fp_property_def view_snapshot_def)
        subgoal for k y apply (simp add: last_version_def kvs_of_s_def get_state_defs)
          apply (cases "k \<in> dom kv_map"; auto) sorry
        done
      done
  next
    case (WCommit cl kv_map cts sn u)
    then show ?case using p apply simp
      apply (auto simp add: write_commit_def cl_unchanged_defs sim_def fp_property_def)
      apply (rule exI [where x="views_of_s gs' cl"]) apply auto
        subgoal apply (auto simp add: ET_CC.ET_cl_txn_def) sorry
        subgoal apply (rule ext)
          subgoal for cl' apply (cases "cl' = cl"; simp)
          using views_of_s_other_cl_inv[of cl gs gs' cl'] by (simp add: other_insts_unchanged_def).
      done
  qed (auto simp add: sim_defs get_state_defs image_iff)
qed simp

end