section \<open>Modified Eiger Port Protocol Satisfying CCv (Causal+)\<close>

theory CCv_Eiger_Port_modified
  imports Execution_Tests "HOL-Library.Multiset"
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

type_synonym 'v epv_list = "'v ep_version list"
type_synonym 'v datastore = "key \<Rightarrow> 'v epv_list"

definition ep_version_init :: "'v ep_version" where
  "ep_version_init \<equiv> \<lparr>v_value = undefined, v_writer = T0, v_readerset = {},
    v_ts = 0, v_glts = 0, v_gst = 0, v_is_pending = False\<rparr>"

\<comment> \<open>Server State\<close>
datatype state_wtxn = Ready | Prep tstmp | Commit
record 'v server =
  wtxn_state :: "txid0 \<Rightarrow> state_wtxn"
  clock :: tstmp
  lst :: tstmp
  DS :: "'v epv_list"

definition DS_vl_init :: "'v epv_list" where
  "DS_vl_init \<equiv> [ep_version_init]"

definition DS_init :: "'v datastore" where
  "DS_init \<equiv> (\<lambda>k. DS_vl_init)"

\<comment> \<open>Client State\<close>
datatype 'v state_txn = Idle | RtxnInProg "key set" "key \<rightharpoonup> ('v \<times> txid)" | WtxnPrep "key \<rightharpoonup> 'v" |
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

fun add_to_readerset :: "'v epv_list \<Rightarrow> txid0 \<Rightarrow> txid \<Rightarrow> 'v epv_list" where
  "add_to_readerset [] t t' = []" |
  "add_to_readerset (ver # vl) t t' =
    (if v_writer ver = t'
     then (ver \<lparr>v_readerset := insert t (v_readerset ver)\<rparr>) # vl
     else ver # (add_to_readerset vl t t'))"

definition is_txn_writer where "is_txn_writer t \<equiv> (\<lambda>ver. v_writer ver = t)"

definition remove_ver :: "'v epv_list \<Rightarrow> txid \<Rightarrow> 'v epv_list" where
  "remove_ver vl t \<equiv> (case find (is_txn_writer t) vl of None \<Rightarrow> vl | Some ver \<Rightarrow> remove1 ver vl)"

definition committed_ver :: "'v ep_version \<Rightarrow> tstmp \<Rightarrow> tstmp \<Rightarrow> 'v ep_version" where
  "committed_ver ver gts cts \<equiv> ver \<lparr>v_glts := gts, v_ts := cts, v_is_pending := False\<rparr>"

definition find_and_commit_ver :: "'v epv_list \<Rightarrow> tstmp \<Rightarrow> tstmp \<Rightarrow> txid \<rightharpoonup> 'v ep_version" where
  "find_and_commit_ver vl gts cts t \<equiv> (case find (is_txn_writer t) vl of
     None \<Rightarrow> None |
     Some ver \<Rightarrow> Some (committed_ver ver gts cts))"

fun insert_in_vl :: "'v epv_list \<Rightarrow> 'v ep_version option \<Rightarrow> 'v epv_list" where
  "insert_in_vl vl None = vl" |
  "insert_in_vl [] (Some c_ver) = [c_ver]" |
  "insert_in_vl (ver # vl) (Some c_ver) = (if v_glts ver \<le> v_glts c_ver \<and> \<not> v_is_pending ver
    then ver # (insert_in_vl vl (Some c_ver)) else c_ver # ver # vl)"

definition commit_in_vl :: "'v epv_list \<Rightarrow> tstmp \<Rightarrow> tstmp \<Rightarrow> txid \<Rightarrow> 'v epv_list" where
  "commit_in_vl vl global_t commit_t t \<equiv> insert_in_vl (remove_ver vl t) (find_and_commit_ver vl global_t commit_t t)"

lemmas commit_in_vl_defs = commit_in_vl_def remove_ver_def find_and_commit_ver_def committed_ver_def

fun at :: "'v epv_list \<Rightarrow> tstmp \<Rightarrow> 'v ep_version option \<Rightarrow> 'v ep_version" where
  "at [] ts None = ep_version_init" |
  "at [] ts (Some ver) = ver" |
  "at (ver # vl) ts None = (if v_ts ver \<le> ts \<and> \<not>v_is_pending ver then at vl ts (Some ver) else at vl ts None)" |
  "at (ver # vl) ts (Some ver') = (if v_ts ver \<le> ts \<and> v_ts ver > v_ts ver' \<and> \<not>v_is_pending ver
      then at vl ts (Some ver) else at vl ts (Some ver'))"

fun newest_own_write :: "'v epv_list \<Rightarrow> tstmp \<Rightarrow> cl_id \<Rightarrow> 'v ep_version option \<rightharpoonup> 'v ep_version" where
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
definition read_at :: "'v epv_list \<Rightarrow> tstmp \<Rightarrow> cl_id \<Rightarrow> 'v ver_ptr" where
  "read_at vl ts cl \<equiv> let ver = at vl ts None in
    (case newest_own_write vl (v_ts ver) cl None of
      None \<Rightarrow> \<lparr> ver_val = v_value ver, ver_writer = v_writer ver \<rparr> |
      Some ver' \<Rightarrow> \<lparr> ver_val = v_value ver', ver_writer = v_writer ver' \<rparr>)"

\<comment> \<open>Translator function\<close>
abbreviation get_txn_cl :: "'v state \<Rightarrow> cl_id \<Rightarrow> txid0" where
  "get_txn_cl s cl \<equiv> Tn_cl (txn_sn (cls s cl)) cl"

\<comment> \<open>Lemmas about the functions\<close>

lemma add_to_readerset_length: "length (add_to_readerset vl t t') = length vl"
  apply (induction vl, simp)
  subgoal for ver by (cases "v_writer ver = t'"; simp).

lemma add_to_readerset_v_value:
  "v_value (add_to_readerset vl t t' ! i) = v_value (vl ! i)"
  apply (induction vl arbitrary: i, simp)
  subgoal for ver vl i by (cases "v_writer ver = t'"; cases "i = 0"; simp).

lemma add_to_readerset_v_writer:
  "v_writer (add_to_readerset vl t t' ! i) = v_writer (vl ! i)"
  apply (induction vl arbitrary: i, simp)
  subgoal for ver vl i by (cases "v_writer ver = t'"; cases "i = 0"; simp).

lemma add_to_readerset_v_ts:
  "v_ts (add_to_readerset vl t t' ! i) = v_ts (vl ! i)"
  apply (induction vl arbitrary: i, simp)
  subgoal for ver vl i by (cases "v_writer ver = t'"; cases "i = 0"; auto).

lemma add_to_readerset_v_glts:
  "v_glts (add_to_readerset vl t t' ! i) = v_glts (vl ! i)"
  apply (induction vl arbitrary: i, simp)
  subgoal for ver vl i by (cases "v_writer ver = t'"; cases "i = 0"; auto).

lemma add_to_readerset_v_gst:
  "v_gst (add_to_readerset vl t t' ! i) = v_gst (vl ! i)"
  apply (induction vl arbitrary: i, simp)
  subgoal for ver vl i by (cases "v_writer ver = t'"; cases "i = 0"; auto).

lemma add_to_readerset_v_is_pending:
  "v_is_pending (add_to_readerset vl t t' ! i) = v_is_pending (vl ! i)"
  apply (induction vl arbitrary: i, simp)
  subgoal for ver vl i by (cases "v_writer ver = t'"; cases "i = 0"; simp).

lemma add_to_readerset_v_writer_img:
  "v_writer ` set (add_to_readerset vl t t') = v_writer ` set vl"
  apply (induction vl, simp)
  subgoal for ver vl by (cases "v_writer ver = t'"; simp).

lemma add_to_readerset_v_writer_map:
  "map v_writer (add_to_readerset vl t t') = map v_writer vl"
  apply (induction vl, simp)
  subgoal for ver vl by (cases "v_writer ver = t'"; simp).

lemma add_to_readerset_find_None:
  assumes "find (is_txn_writer t) vl = None"
  shows "find (is_txn_writer t) (add_to_readerset vl t' t'') = None"
  using assms apply (induction vl; simp)
  subgoal for a by (cases "is_txn_writer t a"; cases "t'' = t"; simp add: is_txn_writer_def).

lemma add_to_readerset_find_Some:
  assumes "find (is_txn_writer t) vl = Some ver"
  shows "\<exists>ver'. find (is_txn_writer t) (add_to_readerset vl t' t'') = Some ver'"
  using assms apply (induction vl; simp)
  subgoal for a by (cases "is_txn_writer t a"; cases "t'' = t"; simp add: is_txn_writer_def).

lemma add_to_readerset_find_is_pending:
  assumes "find (is_txn_writer t) vl = Some ver"
    and "find (is_txn_writer t) (add_to_readerset vl t' t'') = Some ver'"
  shows "v_is_pending ver' = v_is_pending ver"
  using assms apply (induction vl; simp)
  subgoal for a by (cases "is_txn_writer t a"; cases "is_txn_writer t'' a"; auto simp add: is_txn_writer_def).

lemma find_Some_in_set:
  "find P vl = Some ver \<Longrightarrow> ver \<in> set vl \<and> P ver"
  apply (simp add: find_Some_iff)
  by (meson nth_mem)

lemma find_append:
  "find P (vl1 @ vl2) = (case find P vl1 of None \<Rightarrow> find P vl2 | Some ver \<Rightarrow> Some ver)"
  by (induction vl1; simp)

lemma append_image: "f ` set (vl @ [a]) = insert (f a) (f ` set vl)"
  by simp

lemma index_not_found: "find (is_txn_writer t) vl = None \<Longrightarrow> remove_ver vl t = vl"
  by (simp add: remove_ver_def)

lemma remove_ver_Some_readerset:
  assumes "find (is_txn_writer t) vl = Some ver"
  shows "insert (v_readerset ver) (v_readerset ` set (remove_ver vl t)) = v_readerset ` set vl"
  using assms apply (simp add: remove_ver_def)
  by (smt (verit) Collect_cong image_insert in_set_remove1 insert_compr find_Some_in_set
      mem_Collect_eq mk_disjoint_insert)

lemma remove_ver_Some_reader_multiset:
  assumes "find (is_txn_writer t) vl = Some ver"
  shows "add_mset (v_readerset ver) (image_mset v_readerset(mset (remove_ver vl t))) =
         image_mset v_readerset (mset vl)"
  using assms apply (simp add: remove_ver_def)
  by (metis find_Some_in_set image_mset_add_mset insert_DiffM set_mset_mset)

lemma remove_ver_Some_writer:
  assumes "find (is_txn_writer t) vl = Some ver"
  shows "insert (v_writer ver) (v_writer ` set (remove_ver vl t)) = v_writer ` set vl"
  using assms apply (simp add: remove_ver_def)
  by (smt (verit) Collect_cong image_insert in_set_remove1 insert_compr find_Some_in_set
      mem_Collect_eq mk_disjoint_insert)

lemma remove_ver_Some_writer_multiset:
  assumes "find (is_txn_writer t) vl = Some ver"
  shows "add_mset (v_writer ver) (image_mset v_writer (mset (remove_ver vl t))) =
         image_mset v_writer (mset vl)"
  using assms apply (simp add: remove_ver_def)
  by (metis find_Some_in_set image_mset_add_mset insert_DiffM set_mset_mset)

lemma insert_in_vl_Some_length:
  "length (insert_in_vl vl (Some ver)) = Suc (length vl)"
  by (induction vl; simp)

lemma insert_in_vl_Some_readerset:
  "v_readerset ` set (insert_in_vl vl (Some ver)) = insert (v_readerset ver) (v_readerset ` set vl)"
  apply (induction vl; simp) by blast

lemma insert_in_vl_Some_reader_multiset:
  "image_mset v_readerset (mset (insert_in_vl vl (Some ver))) =
    add_mset (v_readerset ver) (image_mset v_readerset (mset vl))"
  by (induction vl; simp)

lemma insert_in_vl_Some_writer:
  "v_writer ` set (insert_in_vl vl (Some ver)) = insert (v_writer ver) (v_writer ` set vl)"
  apply (induction vl; simp) by blast

lemma insert_in_vl_Some_writer_multiset:
  "image_mset v_writer (mset (insert_in_vl vl (Some ver))) =
    add_mset (v_writer ver) (image_mset v_writer (mset vl))"
  by (induction vl; simp)

lemma insert_in_vl_Some_find_another:
  assumes "\<not>is_txn_writer t ver"
  shows "find (is_txn_writer t) (insert_in_vl vl (Some ver)) = find (is_txn_writer t) vl"
  using assms by (induction vl; simp)

lemma commit_in_vl_length:
  "length (commit_in_vl vl gts cts t) = length vl"
  apply (cases "find (is_txn_writer t) vl"; simp add: commit_in_vl_defs)
  subgoal for ver apply (cases "remove1 ver vl", simp add: find_Some_iff)
    apply (metis Suc_diff_1 length_pos_if_in_set length_remove1 list.size(3) nth_mem)
    by (metis One_nat_def Suc_pred find.simps(1) find_Some_in_set insert_in_vl_Some_length
        length_greater_0_conv option.discI length_remove1).

lemma commit_in_vl_v0:
  assumes "t \<noteq> T0" and "gts > 0" and "vl \<noteq> []"
    and "v_writer (vl ! 0) = T0" and "v_glts (vl ! 0) = 0" and "\<not>v_is_pending (vl ! 0)"
  shows "commit_in_vl vl gts cts t ! 0 = vl ! 0"
  using assms
  apply (cases "find (is_txn_writer t) vl"; cases vl; simp add: commit_in_vl_defs is_txn_writer_def)
  by (metis (mono_tags, lifting) find_Some_iff)

lemma commit_in_vl_v_writer_img:
  "v_writer ` set (commit_in_vl vl gts cts t) = v_writer ` set vl"
    using insert_in_vl_Some_writer[of "remove1 _ vl"] remove_ver_Some_writer[of t vl]
    by (cases "find (is_txn_writer t) vl"; simp add: commit_in_vl_defs)

lemma commit_in_vl_v_writer_multiset:
  "image_mset v_writer (mset (commit_in_vl vl gts cts t)) = image_mset v_writer (mset vl)"
  using insert_in_vl_Some_writer_multiset[of "remove1 _ vl"] remove_ver_Some_writer_multiset[of t vl]
    by (cases "find (is_txn_writer t) vl"; simp add: commit_in_vl_defs)

lemma commit_in_vl_v_readerset_img:
  "v_readerset ` set (commit_in_vl vl gts cts t) = v_readerset ` set vl"
    using insert_in_vl_Some_readerset[of "remove1 _ vl"] remove_ver_Some_readerset[of t vl]
    by (cases "find (is_txn_writer t) vl"; simp add: commit_in_vl_defs)

lemma commit_in_vl_v_reader_multiset:
  "image_mset v_readerset (mset (commit_in_vl vl gts cts t)) = image_mset v_readerset (mset vl)"
    using insert_in_vl_Some_reader_multiset[of "remove1 _ vl"] remove_ver_Some_reader_multiset[of t vl]
    by (cases "find (is_txn_writer t) vl"; simp add: commit_in_vl_defs)

lemma split_remove_list:
  assumes "ver \<in> set vl"
  shows "\<exists>ls rs. vl = ls @ ver # rs \<and> ver \<notin> set ls \<and> remove1 ver vl = ls @ rs"
  using assms
  apply (simp add: remove1_split)
  by (metis split_list_first)

lemma remove_find_other:
  assumes "\<not>P ver"
  shows "find P (remove1 ver vl) = find P vl"
  using assms
  apply (cases "find P vl", simp)
  apply (metis find_None_iff in_set_remove1)
  apply(auto simp add: find_Some_iff)
  apply (cases "ver \<in> set vl")
  using split_remove_list[of ver vl] apply (auto simp add: find_append split: option.split)
  by (simp add: remove1_idem)

lemma commit_in_vl_find_another:
  assumes "t \<noteq> t'"
  shows  "find (is_txn_writer t) (commit_in_vl vl gts cts t') = find (is_txn_writer t) vl"
  using assms
  apply (auto simp add: commit_in_vl_defs split: option.split)
  subgoal for ver using insert_in_vl_Some_find_another[of t "committed_ver ver gts cts"]
    by (auto simp add: committed_ver_def find_Some_iff is_txn_writer_def remove_find_other).

lemma commit_in_vl_ver_in_set:
  assumes "ver \<in> set (commit_in_vl vl gts cts t)"
  shows "ver \<in> set vl \<or> (\<exists>v \<in> set vl. is_txn_writer t v \<and> ver = committed_ver v gts cts)"
  using assms
  apply (cases "is_txn_writer t ver"; simp add: commit_in_vl_def) sorry

subsubsection \<open>Simulation function\<close>

definition pending_rtxn :: "'v state \<Rightarrow> txid0 \<Rightarrow> bool" where
  "pending_rtxn s t \<equiv> \<exists>keys kvt_map. txn_state (cls s (get_cl_txn t)) = RtxnInProg keys kvt_map \<and>
    txn_sn (cls s (get_cl_txn t)) = get_sn_txn t"

definition pending_wtxn :: "'v state \<Rightarrow> txid \<Rightarrow> bool" where
  "pending_wtxn s t \<equiv> case t of T0 \<Rightarrow> False |
    Tn (Tn_cl sn cl) \<Rightarrow> \<exists>kv_map. txn_state (cls s cl) = WtxnPrep kv_map \<and> txn_sn (cls s cl) = sn"

definition epv_to_ver :: "'v ep_version \<Rightarrow> 'v version" where
  "epv_to_ver v \<equiv> \<lparr>v_value = v_value v, v_writer = v_writer v, v_readerset = v_readerset v\<rparr>"

definition get_ver_committed_rd :: "'v state \<Rightarrow> 'v ep_version \<Rightarrow> 'v ep_version" where
  "get_ver_committed_rd s \<equiv> (\<lambda>v. v \<lparr>v_readerset := v_readerset v - Collect (pending_rtxn s)\<rparr>)"

definition get_vl_committed_wr :: "'v epv_list \<Rightarrow> 'v epv_list" where
  "get_vl_committed_wr vl \<equiv> filter (\<lambda>v. \<not>v_is_pending v) vl"

definition get_vl_ready_to_commit_wr :: "'v state \<Rightarrow> 'v epv_list \<Rightarrow> 'v epv_list" where
  "get_vl_ready_to_commit_wr s vl \<equiv> filter (\<lambda>v. v_is_pending v \<and> \<not>pending_wtxn s (v_writer v)) vl"
(* an invariant to show this is definitely a write transaction*)

definition get_glts :: "'v state \<Rightarrow> 'v ep_version \<Rightarrow> tstmp" where
  "get_glts s ver \<equiv> (case v_writer ver of T0 \<Rightarrow> 0 | Tn (Tn_cl sn cl) \<Rightarrow>
     (SOME glts. \<exists>cts kv_map. txn_state (cls s cl) =  WtxnCommit glts cts kv_map))" \<comment> \<open>show as an invariant: ReadyToCommitVer\<close>

fun commit_all_in_vl :: "'v state \<Rightarrow> 'v epv_list \<Rightarrow> 'v epv_list \<Rightarrow> 'v epv_list" where
  "commit_all_in_vl s vl [] = vl" |
  "commit_all_in_vl s vl (ver # pvl) =
    commit_all_in_vl s (insert_in_vl vl (Some (committed_ver ver (get_glts s ver) 0))) pvl"

definition get_vl_pre_committed :: "'v state \<Rightarrow> 'v epv_list \<Rightarrow> 'v epv_list" where
  "get_vl_pre_committed s vl \<equiv> commit_all_in_vl s (get_vl_committed_wr vl) (get_vl_ready_to_commit_wr s vl)"

definition kvs_of_s :: "'v state \<Rightarrow> 'v kv_store" where
  "kvs_of_s s = (\<lambda>k. map (epv_to_ver o get_ver_committed_rd s) (get_vl_pre_committed s (DS (svrs s k))))"

fun indices_map :: "('v, 'm) vs_list \<Rightarrow> v_id \<Rightarrow> (txid \<rightharpoonup> v_id)" where
  "indices_map [] i = Map.empty" |
  "indices_map (ver # vl) i = (indices_map vl (Suc i))(v_writer ver \<mapsto> i)"

definition get_indices_map where "get_indices_map vl \<equiv> indices_map vl 0"

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
lemmas get_state_defs = epv_to_ver_def get_ver_committed_rd_def get_vl_pre_committed_def 
  get_vl_committed_wr_def get_vl_ready_to_commit_wr_def

\<comment> \<open>Lemmas about simulation functions\<close>

lemma pending_rtxn_inv:
  assumes "\<forall>keys kvt_map. txn_state (cls s cl) \<noteq> RtxnInProg keys kvt_map"
    and "\<forall>keys kvt_map. txn_state (cls s' cl) \<noteq> RtxnInProg keys kvt_map"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "pending_rtxn s' t = pending_rtxn s t"
  using assms
  by (auto simp add: pending_rtxn_def, metis+)

lemma pending_rtxn_added:
  assumes "txn_state (cls s cl) = Idle"
    and "txn_state (cls s' cl) = RtxnInProg keys kvt_map"
    and "txn_sn (cls s' cl) = txn_sn (cls s cl)"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "Collect (pending_rtxn s') = insert (get_txn_cl s cl) (Collect (pending_rtxn s))"
  using assms
  apply (auto simp add: pending_rtxn_def)
     apply (metis get_cl_txn.elims get_sn_txn.simps) by metis+

lemma pending_rtxn_removed:
  assumes "txn_state (cls s cl) = RtxnInProg keys kvt_map"
    and "txn_state (cls s' cl) = Idle"
    and "txn_sn (cls s' cl) = txn_sn (cls s cl)"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "Collect (pending_rtxn s') = Set.remove (get_txn_cl s cl) (Collect (pending_rtxn s))"
  using assms
  apply (auto simp add: pending_rtxn_def)
  apply metis
  apply metis
  apply (metis get_cl_txn.elims get_sn_txn.simps)
  by metis

lemma pending_wtxn_cl_ev_inv:
  assumes "\<forall>kv_map. txn_state (cls s cl) \<noteq> WtxnPrep kv_map"
    and "\<forall>kv_map. txn_state (cls s' cl) \<noteq> WtxnPrep kv_map"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "pending_wtxn s' t = pending_wtxn s t"
  using assms
  by (auto simp add: pending_wtxn_def split: txid.split txid0.split)

lemma pending_wtxn_svr_ev_inv:
  assumes "cls s' = cls s"
  shows "pending_wtxn s' t = pending_wtxn s t"
  using assms
  by (auto simp add: pending_wtxn_def split: txid.split txid0.split)

lemma pending_wtxn_added:
  assumes "txn_state (cls s cl) = Idle"
    and "txn_state (cls s' cl) = WtxnPrep kv_map"
    and "txn_sn (cls s' cl) = txn_sn (cls s cl)"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "Collect (pending_wtxn s') = insert (Tn (get_txn_cl s cl)) (Collect (pending_wtxn s))"
  using assms
  apply (auto simp add: pending_wtxn_def split: txid.split txid0.split) by metis+

lemma pending_wtxn_removed:
  assumes "txn_state (cls s cl) = WtxnPrep kv_map"
    and "txn_state (cls s' cl) = WtxnCommit gts cts kv_map"
    and "txn_sn (cls s' cl) = txn_sn (cls s cl)"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "Collect (pending_wtxn s') = Set.remove (Tn (get_txn_cl s cl)) (Collect (pending_wtxn s))"
  using assms
  apply (auto simp add: pending_wtxn_def split: txid.split txid0.split) by metis+

lemma indices_map_get_ver_committed_rd [simp]:
  "indices_map (map (epv_to_ver o get_ver_committed_rd s) vl) i = indices_map vl i"
  by (induction vl arbitrary: s i; simp add: get_ver_committed_rd_def epv_to_ver_def)

lemma dom_indices_map:
  "dom (indices_map vl i) = v_writer ` set (vl)"
  by (induction vl arbitrary: i; simp)

lemma insert_in_vl_ver_features:
  "f ` set (insert_in_vl vl (Some ver)) = insert (f ver) (f ` set vl)"
  by (induction vl; auto)

lemma commit_all_in_vl_length:
  "length (commit_all_in_vl s vl1 vl2) = length vl1 + length vl2"
  by (induction vl2 arbitrary: vl1; simp add: insert_in_vl_Some_length)

lemma commit_all_in_vl_writers:
  "v_writer ` set (commit_all_in_vl s vl1 vl2) = v_writer ` set vl1 \<union> v_writer ` set vl2"
  by (induction vl2 arbitrary: vl1; simp add: committed_ver_def insert_in_vl_ver_features)

lemma commit_all_in_vl_readersets:
  "v_readerset ` (set (commit_all_in_vl s vl1 vl2)) = v_readerset ` set vl1 \<union> v_readerset ` set vl2"
  by (induction vl2 arbitrary: vl1; simp add: committed_ver_def insert_in_vl_ver_features)

lemma commit_all_in_vl_append:
  "commit_all_in_vl s vl_c (vl @ [ver]) =
  insert_in_vl (commit_all_in_vl s vl_c vl) (Some (committed_ver ver (get_glts s ver) 0))"
  by (induction s vl_c vl rule: commit_all_in_vl.induct; simp)

lemma get_vl_pre_committed_writers:
  "v_writer ` set (get_vl_pre_committed s vl) = v_writer ` {x \<in> set vl. \<not>v_is_pending x \<or> \<not> pending_wtxn s (v_writer x)}"
  apply (simp add: get_state_defs commit_all_in_vl_writers)
  by blast

lemma get_vl_pre_committed_readersets:
  "v_readerset ` (set (get_vl_pre_committed s vl)) \<subseteq> v_readerset ` (set vl)"
  apply (simp add: get_state_defs commit_all_in_vl_readersets) by blast


subsubsection \<open>Events\<close>

datatype 'v ev =
  RInvoke cl_id "key set" | Read cl_id key 'v txid | RDone cl_id "key \<rightharpoonup> ('v \<times> txid)" sqn view |
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

fun find_and_read_val :: "'v epv_list \<Rightarrow> txid0 \<rightharpoonup> ('v \<times> txid)" where
  "find_and_read_val [] t = None" |
  "find_and_read_val (ver # vl) t =
    (if t \<in> v_readerset ver then Some (v_value ver, v_writer ver) else find_and_read_val vl t)"

definition read :: "cl_id \<Rightarrow> key \<Rightarrow> 'v \<Rightarrow> txid \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read cl k v t s s' \<equiv> (\<exists>keys vals.
    txn_state (cls s cl) = RtxnInProg keys vals \<and> k \<in> keys \<and> vals k = None \<and>
    txn_state (cls s' cl) = RtxnInProg keys (vals (k \<mapsto> (v, t)))) \<and>
    Some (v, t) = find_and_read_val (DS (svrs s k)) (get_txn_cl s cl) \<and>
    txn_sn (cls s' cl) = txn_sn (cls s cl) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) k = lst (svrs s k) \<and>
    (\<forall>k'. k' \<noteq> k \<longrightarrow> lst_map (cls s' cl) k' = lst_map (cls s cl) k') \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    cl_clock (cls s' cl) = Suc (max (cl_clock (cls s cl)) (clock (svrs s k))) \<and>
    svrs_cls_cl'_unchanged cl s s' \<and>
    global_time s' = Suc (global_time s)"

definition read_done :: "cl_id \<Rightarrow> (key \<rightharpoonup> ('v \<times> txid)) \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read_done cl kvt_map sn u'' s s' \<equiv>
    sn = txn_sn (cls s cl) \<and>
    u'' = view_txid_vid s (\<lambda>k. case kvt_map k of
      Some (v, t) \<Rightarrow> insert t (cl_view (cls s cl) k) |
      None \<Rightarrow> cl_view (cls s cl) k) \<and>
    txn_state (cls s cl) = RtxnInProg (dom kvt_map) kvt_map \<and>
    txn_state (cls s' cl) = Idle \<and>
    txn_sn (cls s' cl) = Suc (txn_sn (cls s cl)) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    lst_map (cls s' cl) = lst_map (cls s cl) \<and>
    cl_view (cls s' cl) = (\<lambda>k. case kvt_map k of
      Some (v, t) \<Rightarrow> insert t (cl_view (cls s cl) k) |
      None \<Rightarrow> cl_view (cls s cl) k) \<and>
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
  "write_commit cl kv_map commit_t sn u'' s s' \<equiv>
    sn = txn_sn (cls s cl) \<and>
    u'' = views_of_s s cl \<and>
    txn_state (cls s cl) = WtxnPrep kv_map \<and>
    (\<forall>k \<in> dom kv_map.
      (\<exists>prep_t. wtxn_state (svrs s k) (get_txn_cl s cl) = Prep prep_t) \<and>
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
  "write_done cl s s' \<equiv> 
    (\<exists>kv_map.
    (\<exists>global_ts commit_t. txn_state (cls s cl) = WtxnCommit global_ts commit_t kv_map) \<and>
    (\<forall>k\<in>dom kv_map. wtxn_state (svrs s k) (get_txn_cl s cl) = Commit) \<and>
    (\<forall>k \<in> dom kv_map. lst_map (cls s' cl) k = lst (svrs s k)) \<and>
    (\<forall>k. k \<notin> dom kv_map \<longrightarrow> lst_map (cls s' cl) k = lst_map (cls s cl) k)) \<and>
    txn_state (cls s' cl) = Idle \<and>
    txn_sn (cls s' cl) = Suc (txn_sn (cls s cl)) \<and>
    gst (cls s' cl) = gst (cls s cl) \<and>
    cl_view (cls s' cl) = cl_view (cls s cl) \<and>
    cl_clock (cls s' cl) = Suc (cl_clock (cls s cl)) \<and>
    svrs_cls_cl'_unchanged cl s s' \<and>
    global_time s' = Suc (global_time s)"

\<comment> \<open>Server Events\<close>
definition register_read :: "svr_id \<Rightarrow> txid0 \<Rightarrow> 'v \<Rightarrow> txid \<Rightarrow> tstmp \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "register_read svr t v t' gst_ts s s' \<equiv>
    tid_match s t \<and>
    (\<exists>keys kvt_map.
      txn_state (cls s (get_cl_txn t)) = RtxnInProg keys kvt_map \<and> svr \<in> keys \<and> kvt_map svr = None) \<and>
    \<lparr>ver_val = v, ver_writer = t'\<rparr> = read_at (DS (svrs s svr)) gst_ts (get_cl_txn t) \<and>
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

definition pending_wtxns where
  "pending_wtxns s k \<equiv> {prep_t. \<exists>t. wtxn_state (svrs s k) t = Prep prep_t}"

lemma pending_wtxns_empty:
  "pending_wtxns s k = {} \<longleftrightarrow> (\<forall>t. wtxn_state (svrs s k) t \<in> {Ready, Commit})"
  apply (auto simp add: pending_wtxns_def) apply (meson state_wtxn.exhaust)
  by (metis state_wtxn.distinct(1) state_wtxn.distinct(5))

lemma pending_wtxns_non_empty:
  assumes "wtxn_state (svrs s k) t \<noteq> Ready"
    and "wtxn_state (svrs s k) t \<noteq> Commit"
  shows "pending_wtxns s k \<noteq> {}"
  using assms apply (auto simp add: pending_wtxns_def)
  by (meson state_wtxn.exhaust)

definition commit_write :: "svr_id \<Rightarrow> txid0 \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "commit_write svr t s s' \<equiv>
    tid_match s t \<and>
    (\<exists>kv_map.  svr \<in> dom kv_map \<and> (\<exists>global_ts commit_t.
      txn_state (cls s (get_cl_txn t)) = WtxnCommit global_ts commit_t kv_map \<and>
       DS (svrs s' svr) = commit_in_vl (DS (svrs s svr)) global_ts commit_t (Tn t)) \<and>
      (\<exists>prep_t. wtxn_state (svrs s svr) t = Prep prep_t)) \<and>
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
  "state_trans s (RInvoke cl keys)          s' \<longleftrightarrow> read_invoke cl keys s s'" |
  "state_trans s (Read cl k v t)            s' \<longleftrightarrow> read cl k v t s s'" |
  "state_trans s (RDone cl kvt_map sn u'')  s' \<longleftrightarrow> read_done cl kvt_map sn u'' s s'" |
  "state_trans s (WInvoke cl kv_map)        s' \<longleftrightarrow> write_invoke cl kv_map s s'" |
  "state_trans s (WCommit cl kv_map cts sn u'')  s' \<longleftrightarrow> write_commit cl kv_map cts sn u'' s s'" |
  "state_trans s (WDone cl)                 s' \<longleftrightarrow> write_done cl s s'" |
  "state_trans s (RegR svr t v i gts)       s' \<longleftrightarrow> register_read svr t v i gts s s'" |
  "state_trans s (PrepW svr t v gts)        s' \<longleftrightarrow> prepare_write svr t v gts s s'" |
  "state_trans s (CommitW svr t)            s' \<longleftrightarrow> commit_write svr t s s'" |
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

term image
definition o_fst :: "('a \<Rightarrow> ('b \<times> 'c) option) \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "o_fst m \<equiv> (\<lambda>a. case m a of None \<Rightarrow> None | Some (b, c) \<Rightarrow> Some b)"

\<comment> \<open>Mediator function\<close>
fun med :: "'v ev \<Rightarrow> 'v label" where
  "med (RDone cl kvt_map sn u'') = ET cl sn u'' (\<lambda>k op. case op of R \<Rightarrow> o_fst kvt_map k | W \<Rightarrow> None)" |
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
  case (Read x1 x2 x3 x4)
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
  by (auto simp add: PendingWtxnsUB_def tps_defs tid_match_def pending_wtxns_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case
      apply (auto simp add: PendingWtxnsUB_def tps_trans_defs svr_unchanged_defs pending_wtxns_def)
      by (metis le_Suc_eq)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: PendingWtxnsUB_def tps_trans_defs svr_unchanged_defs pending_wtxns_def ran_def)
      by (smt (z3) Suc_leD Suc_le_D max.bounded_iff not_less_eq_eq state_wtxn.inject)
  next
    case (CommitW x1 x2)
    then show ?case
      apply (auto simp add: PendingWtxnsUB_def tps_trans_defs svr_unchanged_defs pending_wtxns_def ran_def)
      by (smt (z3) Suc_n_not_le_n max.bounded_iff max_def_raw state_wtxn.distinct(5))
  qed (auto simp add: PendingWtxnsUB_def tps_trans_defs cl_unchanged_defs pending_wtxns_def)
qed


lemma finite_pending_wtxns_adding: 
  assumes "wtxn_state (svrs s' k) t = Prep prep_t"
    and "finite (pending_wtxns s svr)"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> wtxn_state (svrs s' k) t' = wtxn_state (svrs s k) t'"
  shows "finite (pending_wtxns s' svr)"
  using assms apply (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_def)
  by (metis le_trans nat_le_linear state_wtxn.inject)

lemma finite_pending_wtxns_removing: 
  assumes "wtxn_state (svrs s' k) t = Commit"
    and "finite (pending_wtxns s svr)"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> wtxn_state (svrs s' k) t' = wtxn_state (svrs s k) t'"
  shows "finite (pending_wtxns s' svr)"
  using assms apply (simp add: pending_wtxns_def)
  by (smt (verit, del_insts) finite_nat_set_iff_bounded_le mem_Collect_eq state_wtxn.distinct(5))

definition FinitePendingInv where
  "FinitePendingInv s svr \<longleftrightarrow> finite (pending_wtxns s svr)"

lemmas FinitePendingInvI = FinitePendingInv_def[THEN iffD2, rule_format]
lemmas FinitePendingInvE[elim] = FinitePendingInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_finitepending [simp, dest]: "reach tps s \<Longrightarrow> FinitePendingInv s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FinitePendingInv_def tps_defs pending_wtxns_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x71 x72 x73 x74 x75)
    then show ?case
      by (auto simp add: tps_trans_defs svr_unchanged_defs FinitePendingInv_def pending_wtxns_def
          dest!: eq_for_all_k)
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case
      by (auto simp add: tps_trans_defs svr_unchanged_defs FinitePendingInv_def
          dest!: finite_pending_wtxns_adding)
  next
    case (CommitW x91 x92)
    then show ?case
      by (auto simp add: tps_trans_defs svr_unchanged_defs FinitePendingInv_def
          dest!: finite_pending_wtxns_removing)
  qed (auto simp add: tps_trans_defs cl_unchanged_defs FinitePendingInv_def pending_wtxns_def)
qed

lemma pending_wtxns_adding_ub:
  assumes "wtxn_state (svrs s' k) t = Prep clk"
    and "\<forall>ts \<in> pending_wtxns s k. ts \<le> clk"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> wtxn_state (svrs s' k) t' = wtxn_state (svrs s k) t'"
  shows "\<forall>ts \<in> pending_wtxns s' k. ts \<le> clk"
  using assms apply (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_def)
  by (metis order_refl state_wtxn.inject)

lemma pending_wtxns_removing_ub:
  assumes "wtxn_state (svrs s' k) t = Commit"
    and "\<forall>ts \<in> pending_wtxns s k. ts \<le> clk"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> wtxn_state (svrs s' k) t' = wtxn_state (svrs s k) t'"
  shows "\<forall>ts \<in> pending_wtxns s' k. ts \<le> clk"
  using assms apply (auto simp add: finite_nat_set_iff_bounded_le pending_wtxns_def)
  by (metis state_wtxn.distinct(5))

lemma pending_wtxns_adding:
  assumes "wtxn_state (svrs s' k) t = Prep clk"
    and "\<forall>clk. wtxn_state (svrs s k) t \<noteq> Prep clk"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> wtxn_state (svrs s' k) t' = wtxn_state (svrs s k) t'"
  shows "pending_wtxns s' k = insert clk (pending_wtxns s k)"
  using assms apply (auto simp add: pending_wtxns_def)
  apply (metis state_wtxn.inject)
  by metis

lemma pending_wtxns_removing:
  assumes "wtxn_state (svrs s k) t = Prep clk"
    and "\<forall>clk. wtxn_state (svrs s' k) t \<noteq> Prep clk"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> wtxn_state (svrs s' k') = wtxn_state (svrs s k')"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> wtxn_state (svrs s' k) t' = wtxn_state (svrs s k) t'"
  shows "pending_wtxns s' k = pending_wtxns s k \<or> pending_wtxns s' k = Set.remove clk (pending_wtxns s k)"
  using assms apply (auto simp add: pending_wtxns_def)
  apply (metis (mono_tags))+
  by (metis state_wtxn.inject)

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
      apply (metis clock_monotonic reach_trans.hyps(1) tps_trans)
    proof -
      fix svr
      assume a: "pending_wtxns s' x91 \<noteq> {}"
      hence fin: "finite (pending_wtxns s' x91)" using CommitW
        apply (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs)
        by (metis (mono_tags) FinitePendingInv_def reach.reach_trans reach_finitepending
            reach_trans.hyps(1) reach_trans.hyps(2))
      hence clk_ub: "\<forall>ts \<in> pending_wtxns s' x91. ts \<le> clock (svrs s x91)" using CommitW
        by (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs
            dest!: pending_wtxns_removing_ub [of s' x91 x92 s "clock (svrs s x91)"])
      hence "Min (pending_wtxns s' x91) \<le> clock (svrs s x91)" using a fin CommitW
        by (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs)
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
    case (RegR x1 x2 x3 x4 x5)
    then show ?case
    by (auto simp add: PendingWtxnsLB_def tps_trans_defs svr_unchanged_defs pending_wtxns_def, metis)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case
    apply (auto simp add: PendingWtxnsLB_def tps_trans_defs svr_unchanged_defs pending_wtxns_def)
      by (metis ClockLstInv_def reach_clocklstinv state_wtxn.inject)
  next
    case (CommitW x1 x2)
    then show ?case
    apply (auto simp add: PendingWtxnsLB_def commit_write_def svr_unchanged_defs pending_wtxns_def)
    apply (cases "pending_wtxns s' x1 = {}")
      apply (metis pending_wtxns_non_empty state_wtxn.distinct(1) state_wtxn.distinct(5))
      apply (cases "svr = x1"; auto)
      subgoal for x kv_map y glts prep_t commit_t t apply (cases "t = x2"; auto)
      proof -
        fix t x
        assume a: "wtxn_state (svrs s x1) t = Prep x" and b: "t \<noteq> x2"
        hence fin: "finite (pending_wtxns s' x1)" using CommitW
          apply (auto simp add: ClockLstInv_def tps_trans_defs svr_unchanged_defs)
          by (metis (mono_tags) FinitePendingInv_def reach.reach_trans reach_finitepending
              reach_trans.hyps(1) reach_trans.hyps(2))
        then show "Min (pending_wtxns s' x1) \<le> x" using a b CommitW
          apply (auto simp add: PendingWtxnsLB_def tps_trans_defs svr_unchanged_defs pending_wtxns_def)
          by (metis (mono_tags, lifting) Min.coboundedI mem_Collect_eq)
      qed.
  qed (auto simp add: PendingWtxnsLB_def tps_trans_defs cl_unchanged_defs pending_wtxns_def)
qed

lemma Min_insert_larger:
  assumes "a \<noteq> {}" and "b \<noteq> {}"
    and "finite a"
    and "b = insert x a"
    and "\<forall>y \<in> a. y \<le> x"
  shows "Min a \<le> Min b"
  using assms
  by simp

lemma min_pending_wtxns_monotonic:
  assumes "state_trans s e s'"
    and "pending_wtxns s k \<noteq> {}"
    and "pending_wtxns s' k \<noteq> {}"
    and "PendingWtxnsUB s k" and "FinitePendingInv s k"
  shows "Min (pending_wtxns s k) \<le> Min (pending_wtxns s' k)"
  using assms
  proof (induction e)
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (auto simp add: prepare_write_def svr_unchanged_defs PendingWtxnsUB_def
          FinitePendingInv_def)
      using pending_wtxns_adding[of s' x1 x2 "clock (svrs s x1)" s]
        Min_insert_larger[of "pending_wtxns s x1" "pending_wtxns s' x1" "clock (svrs s x1)"]
      by (cases "k = x1"; auto simp add: pending_wtxns_def)
  next
    case (CommitW x1 x2)
    then show ?case apply (auto simp add: commit_write_def svr_unchanged_defs pending_wtxns_empty 
          FinitePendingInv_def)
      apply (cases "k = x1") subgoal for t ta kv_map y global_ts prep_t
      using pending_wtxns_removing[of s x1 x2 prep_t s'] apply auto
      by (metis (no_types, lifting) Min_in Min_le assms(3) finite_pending_wtxns_removing member_remove)
      by (simp add: pending_wtxns_def)
  qed (auto simp add: tps_trans_defs unchanged_defs pending_wtxns_def dest!: eq_for_all_k)

lemma lst_monotonic:
  assumes "state_trans s e s'"
    and "ClockLstInv s" and "FinitePendingInv s svr"
    and "PendingWtxnsLB s svr" and "PendingWtxnsUB s svr"
  shows "lst (svrs s' svr) \<ge> lst (svrs s svr)"
  using assms
  proof (induction e)
    case (CommitW k t)
    then show ?case
      apply (auto simp add: commit_write_def svr_unchanged_defs ClockLstInv_def PendingWtxnsLB_def
          FinitePendingInv_def)
    apply (cases "svr = k"; simp)
    apply (cases "pending_wtxns s k = {}"; cases "pending_wtxns s' k = {}"; simp)
      apply (metis pending_wtxns_non_empty state_wtxn.distinct(1) state_wtxn.distinct(5))
      by (meson FinitePendingInvI Min.boundedI assms(1) le_trans min_pending_wtxns_monotonic)
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

\<comment> \<open>Invariants about kvs, global ts and init version v0\<close>

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
      by (metis add_to_readerset_length length_0_conv)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: KVSNonEmp_def tps_trans_defs svr_unchanged_defs)
      by (metis Nil_is_append_conv)
  next
    case (CommitW x1 x2)
    then show ?case
      apply (auto simp add: KVSNonEmp_def tps_trans_defs svr_unchanged_defs)
      using commit_in_vl_length by (metis length_0_conv)
  qed (auto simp add: KVSNonEmp_def tps_trans_defs cl_unchanged_defs)
qed

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
    case (Read x1 x2 x3 x4)
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

lemma non_empty_list_0: "vl \<noteq> [] \<Longrightarrow> (vl @ [a]) ! 0 = vl ! 0"
  by (cases vl; auto)

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
      apply (metis add_to_readerset_v_writer)
      apply (metis add_to_readerset_v_glts)
      by (metis add_to_readerset_v_is_pending)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: InitVerInv_def tps_trans_defs svr_unchanged_defs)
      by (metis KVSNonEmp_def non_empty_list_0 reach_kvs_non_emp)+
  next
    case (CommitW x1 x2)
    then show ?case
      apply (auto simp add: InitVerInv_def tps_trans_defs svr_unchanged_defs)
      apply (cases "k = x1"; auto) using commit_in_vl_v0[where vl="(DS (svrs s x1))"]
      apply (metis CommitGltsNotZero_def KVSNonEmp_def reach_commit_glts_not_zero reach_kvs_non_emp
          txid.distinct(1))
      by (metis CommitGltsNotZero_def KVSNonEmp_def commit_in_vl_v0 reach_commit_glts_not_zero
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
      using add_to_readerset_v_is_pending by blast
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case using reach_trans
      apply (auto simp add: KVSNotAllPending_def tps_trans_defs svr_unchanged_defs)
      apply (cases "k = x1"; auto)
      by (metis KVSNonEmp_def non_empty_list_0 reach_kvs_non_emp)
  next
    case (CommitW x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: KVSNotAllPending_def tps_trans_defs svr_unchanged_defs)
      by (metis InitVerInv_def reach.reach_trans reach_init_ver_inv reach_trans.hyps(1))
  qed (auto simp add: KVSNotAllPending_def tps_trans_defs cl_unchanged_defs)
qed

lemma get_vl_committed_length_inv:
  assumes "KVSNonEmp s"
    and "KVSNotAllPending s k"
  shows "length (get_vl_committed_wr (DS (svrs s k))) > 0"
  using assms
  apply (simp add: KVSNonEmp_def KVSNotAllPending_def get_vl_committed_wr_def)
  by (metis empty_filter_conv hd_conv_nth hd_in_set)

definition KVSSNonEmp where
  "KVSSNonEmp s \<longleftrightarrow> (\<forall>k. kvs_of_s s k \<noteq> [])"

lemmas KVSSNonEmpI = KVSSNonEmp_def[THEN iffD2, rule_format]
lemmas KVSSNonEmpE[elim] = KVSSNonEmp_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_s_non_emp [simp, intro]:
  assumes "reach tps s"
    and "KVSNonEmp s"
    and "\<And>k. KVSNotAllPending s k"
  shows "KVSSNonEmp s"
  using assms
  by (auto simp add: KVSSNonEmp_def KVSNotAllPending_def kvs_of_s_def get_vl_pre_committed_def,
    metis commit_all_in_vl_length get_vl_committed_length_inv length_0_conv not_add_less1)

(*
\<comment> \<open>To make sure get_glts works\<close>
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
    case (Read x1 x2 x3 x4)
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
      subgoal for cl apply (cases "x = cl")
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
*)


\<comment> \<open>Invariant about server and client state relations and (future and past) transactions ids\<close>

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
  proof (induction e)
    case (RInvoke x11 x12)
    then show ?case
      by (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def, metis)
  next
    case (Read x21 x22 x23 x24)
    then show ?case
      by (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def, metis)
  next
    case (RDone x31 x32 x33 x34)
    then show ?case
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def)
      by (metis Suc_lessD)
  next
    case (WInvoke x41 x42)
    then show ?case
      by (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def, metis)
  next
    case (WCommit x51 x52 x53 x54 x55)
    then show ?case
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def)
      by (metis (lifting))
  next
    case (WDone x6)
    then show ?case  using reach_trans
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def FutureTIDInv_def)
      by (metis Suc_lessD)
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?case
      by (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def FutureTIDInv_def, metis)
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case
      apply (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def FutureTIDInv_def)
      by (metis get_cl_txn.simps get_sn_txn.simps nat_neq_iff)
  next
    case (CommitW x91 x92)
    then show ?case  using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def FutureTIDInv_def)
      by (metis state_wtxn.distinct(1))
  qed simp
qed

definition IdleReadInv where
  "IdleReadInv s \<longleftrightarrow> (\<forall>cl k keys kvm. txn_state (cls s cl) \<in> {Idle, RtxnInProg keys kvm}
    \<longrightarrow> wtxn_state (svrs s k) (get_txn_cl s cl) = Ready)"

lemmas IdleReadInvI = IdleReadInv_def[THEN iffD2, rule_format]
lemmas IdleReadInvE[elim] = IdleReadInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_idle_read_inv [simp, dest]: "reach tps s \<Longrightarrow> IdleReadInv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: IdleReadInv_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs cl_unchanged_defs)
      by metis
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs cl_unchanged_defs)
      by metis
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs cl_unchanged_defs)
      by (metis (opaque_lifting) FutureTIDInv_def lessI reach_tidfuturekm)
  next
    case (WInvoke x1 x2)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs cl_unchanged_defs)
      by metis
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs cl_unchanged_defs)
      by (metis (opaque_lifting) state_txn.distinct(5) state_txn.distinct(9))
  next
    case (WDone x)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs cl_unchanged_defs)
      by (metis FutureTIDInv_def lessI reach_tidfuturekm)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs svr_unchanged_defs)
      by metis
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs svr_unchanged_defs)
      by (metis get_cl_txn.simps state_txn.distinct(3) state_txn.distinct(7))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: IdleReadInv_def tps_trans_defs svr_unchanged_defs)
      by (metis state_wtxn.distinct(1))
  qed simp
qed

definition WriteTxnIdleSvr where
  "WriteTxnIdleSvr s \<longleftrightarrow>
    (\<forall>cl k gts cts kv_map. txn_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit gts cts kv_map}
        \<and> kv_map k = None \<longrightarrow> wtxn_state (svrs s k) (get_txn_cl s cl) = Ready)"

lemmas WriteTxnIdleSvrI = WriteTxnIdleSvr_def[THEN iffD2, rule_format]
lemmas WriteTxnIdleSvrE[elim] = WriteTxnIdleSvr_def[THEN iffD1, elim_format, rule_format]

lemma reach_write_txn_idle_svr [simp, dest]: "reach tps s \<Longrightarrow> WriteTxnIdleSvr s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: WriteTxnIdleSvr_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: WriteTxnIdleSvr_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(7) state_txn.distinct(9))
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: WriteTxnIdleSvr_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(7) state_txn.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: WriteTxnIdleSvr_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) state_txn.distinct(3) state_txn.distinct(5))
  next
    case (WInvoke x1 x2)
    then show ?case apply (auto simp add: WriteTxnIdleSvr_def tps_trans_defs cl_unchanged_defs)
      apply (metis IdleReadInv_def insertI1 reach_idle_read_inv reach_trans.hyps(2))
      by (metis state_txn.distinct(11))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: WriteTxnIdleSvr_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) state_txn.distinct(11) state_txn.inject(3))
  next
    case (WDone x)
    then show ?case apply (simp add: WriteTxnIdleSvr_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(3) state_txn.distinct(5))
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case by (simp add: WriteTxnIdleSvr_def tps_trans_defs svr_unchanged_defs, metis)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: WriteTxnIdleSvr_def tps_trans_defs svr_unchanged_defs)
      by (metis domIff get_cl_txn.simps state_txn.distinct(11) state_txn.inject(2))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: WriteTxnIdleSvr_def tps_trans_defs svr_unchanged_defs)
      by (metis (lifting) state_wtxn.distinct(1))
  qed simp
qed

definition PastTIDInv where
  "PastTIDInv s cl \<longleftrightarrow> (\<forall>n k. n < txn_sn (cls s cl) \<longrightarrow> wtxn_state (svrs s k) (Tn_cl n cl) \<in> {Ready, Commit})"

lemmas PastTIDInvI = PastTIDInv_def[THEN iffD2, rule_format]
lemmas PastTIDInvE[elim] = PastTIDInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidpastkm [simp, dest]: "reach tps s \<Longrightarrow> PastTIDInv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: PastTIDInv_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x11 x12)
    then show ?case
      by (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def, metis)
  next
    case (Read x21 x22 x23)
    then show ?case
      by (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def, metis)
  next
    case (RDone x31 x32 x33 x34)
    then show ?case
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def)
      by (smt IdleReadInv_def insertI1 insert_commute not_less_less_Suc_eq reach_idle_read_inv reach_trans.hyps(2))
  next
    case (WInvoke x41 x42)
    then show ?case
      by (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def, metis)
  next
    case (WCommit x51 x52 x53 x54 x55)
    then show ?case
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def)
      by (metis (lifting))
  next
    case (WDone x6)
    then show ?case
      apply (auto simp add: tps_trans_defs cl_unchanged_defs tid_match_def PastTIDInv_def)
      subgoal for n kv_map gts cts k apply (cases "k \<in> dom kv_map")
        apply (metis less_antisym)
        by (metis WriteTxnIdleSvr_def domIff insertCI less_antisym reach_write_txn_idle_svr).
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?case
      by (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def PastTIDInv_def, metis)
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case
      apply (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def PastTIDInv_def)
      by (metis get_cl_txn.simps get_sn_txn.simps nat_neq_iff)
  next
    case (CommitW x91 x92)
    then show ?case
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

definition PrepInv where
  "PrepInv s \<longleftrightarrow> (\<forall>cl k kvm. \<exists>prep_t. txn_state (cls s cl) = WtxnPrep kvm
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> wtxn_state (svrs s k) (get_txn_cl s cl) \<in> {Ready, Prep prep_t}) \<and>
    (k \<notin> dom kvm \<longrightarrow> wtxn_state (svrs s k) (get_txn_cl s cl) = Ready))"

lemmas PrepInvI = PrepInv_def[THEN iffD2, rule_format]
lemmas PrepInvE[elim] = PrepInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_prep_inv [simp, dest]: "reach tps s \<Longrightarrow> PrepInv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: PrepInv_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(7))
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(7))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) state_txn.distinct(3))
  next
    case (WInvoke x1 x2)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs cl_unchanged_defs)
      by (metis IdleReadInv_def insertI1 reach_idle_read_inv)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) state_txn.distinct(11))
  next
    case (WDone x)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(3))
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case by (simp add: PrepInv_def tps_trans_defs svr_unchanged_defs, metis)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs svr_unchanged_defs)
      by (metis get_cl_txn.simps state_txn.inject(2))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: PrepInv_def tps_trans_defs svr_unchanged_defs)
      by (metis get_cl_txn.simps state_txn.distinct(11))
  qed simp
qed

definition CommitInv where
  "CommitInv s \<longleftrightarrow> (\<forall>cl k gts cts kvm. \<exists>prep_t. txn_state (cls s cl) = WtxnCommit gts cts kvm
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> wtxn_state (svrs s k) (get_txn_cl s cl) \<in> {Prep prep_t, Commit}) \<and>
    (k \<notin> dom kvm \<longrightarrow> wtxn_state (svrs s k) (get_txn_cl s cl) = Ready))"

lemmas CommitInvI = CommitInv_def[THEN iffD2, rule_format]
lemmas CommitInvE[elim] = CommitInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_commit_inv [simp, dest]: "reach tps s \<Longrightarrow> CommitInv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: CommitInv_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(9))
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) state_txn.distinct(5))
  next
    case (WInvoke x1 x2)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(11))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs cl_unchanged_defs)
      by (smt (verit) PrepInv_def reach_prep_inv state_txn.inject(3))
  next
    case (WDone x)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(5))
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case by (simp add: CommitInv_def tps_trans_defs svr_unchanged_defs, metis)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs svr_unchanged_defs)
      by (metis get_cl_txn.simps state_txn.distinct(11))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: CommitInv_def tps_trans_defs svr_unchanged_defs)
      by (metis (no_types, lifting) state_wtxn.distinct(1))
  qed simp
qed


definition FutureTidRdDS where
  "FutureTidRdDS s cl \<longleftrightarrow> (\<forall>n k. \<forall>ver \<in> set (DS (svrs s k)). n > txn_sn (cls s cl) \<longrightarrow> Tn_cl n cl \<notin> v_readerset ver)"

lemmas FutureTidRdDSI = FutureTidRdDS_def[THEN iffD2, rule_format]
lemmas FutureTidRdDSE[elim] = FutureTidRdDS_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidfuture_rd_ds [simp, dest]: "reach tps s \<Longrightarrow> FutureTidRdDS s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FutureTidRdDS_def tps_defs tid_match_def DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case by (simp add: FutureTidRdDS_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x1 x2 x3 x4)
    then show ?case by (simp add: FutureTidRdDS_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: FutureTidRdDS_def tps_trans_defs cl_unchanged_defs)
      by (metis Suc_lessD)
  next
    case (WInvoke x1 x2)
    then show ?case by (simp add: FutureTidRdDS_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case by (simp add: FutureTidRdDS_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WDone x)
    then show ?case apply (simp add: FutureTidRdDS_def tps_trans_defs cl_unchanged_defs)
      by (metis Suc_lessD)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: FutureTidRdDS_def tps_trans_defs svr_unchanged_defs tid_match_def) sorry
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: FutureTidRdDS_def tps_trans_defs svr_unchanged_defs)
      using append_image[of v_readerset "DS (svrs s x1)" "\<lparr>v_value = x3, v_writer = Tn x2, v_readerset = {}, v_ts = clock (svrs s x1), v_glts = 10000, v_gst = x4, v_is_pending = True\<rparr>"] sorry
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: FutureTidRdDS_def tps_trans_defs svr_unchanged_defs) sorry
  qed simp
qed

definition FutureTidWrDS where
  "FutureTidWrDS s cl \<longleftrightarrow> (\<forall>n k. n > txn_sn (cls s cl) \<longrightarrow> Tn (Tn_cl n cl) \<notin> v_writer ` set (DS (svrs s k)))"

lemmas FutureTidWrDSI = FutureTidWrDS_def[THEN iffD2, rule_format]
lemmas FutureTidWrDSE[elim] = FutureTidWrDS_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidfuture_wr_ds [simp, dest]: "reach tps s \<Longrightarrow> FutureTidWrDS s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FutureTidWrDS_def tps_defs tid_match_def DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x11 x12)
    then show ?case by (simp add: FutureTidWrDS_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x21 x22 x23)
    then show ?case by (simp add: FutureTidWrDS_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (RDone x31 x32 x33 x34)
    then show ?case apply (simp add: FutureTidWrDS_def tps_trans_defs cl_unchanged_defs)
      by (metis Suc_lessD)
  next
    case (WInvoke x41 x42)
    then show ?case by (simp add: FutureTidWrDS_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x51 x52 x53 x54 x55)
    then show ?case by (simp add: FutureTidWrDS_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WDone x6)
    then show ?case apply (simp add: FutureTidWrDS_def tps_trans_defs cl_unchanged_defs)
      by (metis Suc_lessD)
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?case apply (simp add: FutureTidWrDS_def tps_trans_defs svr_unchanged_defs)
      by (metis add_to_readerset_v_writer_img)
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case apply (simp add: FutureTidWrDS_def tps_trans_defs svr_unchanged_defs tid_match_def)
      by (metis append_image get_cl_txn.simps get_sn_txn.simps insertE linorder_neq_iff txid.inject
          version.select_convs(2))
  next
    case (CommitW x91 x92)
    then show ?case apply (simp add: FutureTidWrDS_def tps_trans_defs svr_unchanged_defs)
      by (metis commit_in_vl_v_writer_img)
  qed simp
qed

definition VerWrLCurrT where
  "VerWrLCurrT s cl \<longleftrightarrow> (\<forall>n k. \<forall>ver \<in> set (DS (svrs s k)).
   v_writer ver = Tn (Tn_cl n cl) \<longrightarrow> n \<le> txn_sn (cls s cl))"

lemmas VerWrLCurrTI = VerWrLCurrT_def[THEN iffD2, rule_format]
lemmas VerWrLCurrTE[elim] = VerWrLCurrT_def[THEN iffD1, elim_format, rule_format]

lemma reach_ver_wr_L_currT [simp, dest]: "reach tps s \<Longrightarrow> VerWrLCurrT s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: VerWrLCurrT_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case by (simp add: VerWrLCurrT_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x1 x2 x3 x4)
    then show ?case by (simp add: VerWrLCurrT_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: VerWrLCurrT_def tps_trans_defs cl_unchanged_defs)
      by (metis le_Suc_eq)
  next
    case (WInvoke x1 x2)
    then show ?case by (simp add: VerWrLCurrT_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case by (simp add: VerWrLCurrT_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WDone x)
    then show ?case apply (simp add: VerWrLCurrT_def tps_trans_defs cl_unchanged_defs)
      by (metis (mono_tags, lifting) nat_le_linear not_less_eq_eq)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: VerWrLCurrT_def tps_trans_defs svr_unchanged_defs)
    by (metis add_to_readerset_v_writer_img FutureTidWrDS_def linorder_le_less_linear not_in_image
        reach_tidfuture_wr_ds)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (auto simp add: VerWrLCurrT_def tps_trans_defs svr_unchanged_defs)
    subgoal for n kvm k apply (cases "k = x1"; simp)
    apply (metis get_cl_txn.simps get_sn_txn.simps order_class.order_eq_iff tid_match_def
            txid.inject version.select_convs(2)) by blast.
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: VerWrLCurrT_def tps_trans_defs svr_unchanged_defs)
      by (metis commit_in_vl_v_writer_img FutureTidWrDS_def linorder_le_less_linear not_in_image
        reach_tidfuture_wr_ds)
  qed simp
qed

lemma not_in_append: "ver \<in> set(vl @ [v]) \<and> ver \<noteq> v \<Longrightarrow> ver \<in> set vl"
  by auto

definition VerWrLCurrT2 where
  "VerWrLCurrT2 s cl \<longleftrightarrow> (\<forall>n k. \<forall>ver \<in> set (DS (svrs s k)). v_writer ver = Tn (Tn_cl n cl) \<and>
    (\<exists>keys kvm. txn_state (cls s cl) \<in> {Idle, RtxnInProg keys kvm}) \<longrightarrow> n < txn_sn (cls s cl))"

lemmas VerWrLCurrT2I = VerWrLCurrT2_def[THEN iffD2, rule_format]
lemmas VerWrLCurrT2E[elim] = VerWrLCurrT2_def[THEN iffD1, elim_format, rule_format]

lemma reach_ver_wr_L_currT2 [simp, dest]: "reach tps s \<Longrightarrow> VerWrLCurrT2 s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: VerWrLCurrT2_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case by (simp add: VerWrLCurrT2_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x1 x2 x3 x4)
    then show ?case by (simp add: VerWrLCurrT2_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: VerWrLCurrT2_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) less_SucI)
  next
    case (WInvoke x1 x2)
    then show ?case by (simp add: VerWrLCurrT2_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: VerWrLCurrT2_def tps_trans_defs cl_unchanged_defs)
    by (metis (lifting) state_txn.distinct(5) state_txn.distinct(9))
  next
    case (WDone x)
    then show ?case apply (simp add: VerWrLCurrT2_def tps_trans_defs cl_unchanged_defs)
    by (metis VerWrLCurrT_def less_Suc_eq nat_less_le reach_ver_wr_L_currT)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: VerWrLCurrT2_def tps_trans_defs svr_unchanged_defs)
      by (metis add_to_readerset_length add_to_readerset_v_writer in_set_conv_nth)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: VerWrLCurrT2_def tps_trans_defs svr_unchanged_defs)
      by (metis get_cl_txn.simps not_in_append state_txn.distinct(3) state_txn.distinct(7)
          txid.inject version.select_convs(2))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: VerWrLCurrT2_def tps_trans_defs svr_unchanged_defs)
        by (smt commit_in_vl_v_writer_img image_iff)
  qed simp
qed

definition VerWrLCurrT3 where
  "VerWrLCurrT3 s k \<longleftrightarrow> (\<forall>n cl. \<forall>ver \<in> set (DS (svrs s k)). v_writer ver = Tn (Tn_cl n cl) \<and>
    wtxn_state (svrs s k) (get_txn_cl s cl) = Ready \<longrightarrow> n < txn_sn (cls s cl))"

lemmas VerWrLCurrT3I = VerWrLCurrT3_def[THEN iffD2, rule_format]
lemmas VerWrLCurrT3E[elim] = VerWrLCurrT3_def[THEN iffD1, elim_format, rule_format]

lemma reach_ver_wr_L_currT3 [simp, dest]: "reach tps s \<Longrightarrow> VerWrLCurrT3 s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: VerWrLCurrT3_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case by (simp add: VerWrLCurrT3_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x1 x2 x3 x4)
    then show ?case by (simp add: VerWrLCurrT3_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: VerWrLCurrT3_def tps_trans_defs cl_unchanged_defs)
      by (metis (no_types, lifting) VerWrLCurrT2_def insertCI less_Suc_eq reach_ver_wr_L_currT2)
  next
    case (WInvoke x1 x2)
    then show ?case by (simp add: VerWrLCurrT3_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: VerWrLCurrT3_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting))
  next
    case (WDone x)
    then show ?case apply (simp add: VerWrLCurrT3_def tps_trans_defs cl_unchanged_defs)
      by (metis VerWrLCurrT_def nat_less_le not_less_eq_eq reach.reach_trans reach_trans.hyps(1)
          reach_ver_wr_L_currT)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: VerWrLCurrT3_def tps_trans_defs svr_unchanged_defs)
      by (metis add_to_readerset_length add_to_readerset_v_writer in_set_conv_nth)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: VerWrLCurrT3_def tps_trans_defs svr_unchanged_defs)
      by (smt (verit, best) get_cl_txn.simps get_sn_txn.simps not_in_append state_wtxn.distinct(1)
          tid_match_def txid.inject version.select_convs(2))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: VerWrLCurrT3_def tps_trans_defs svr_unchanged_defs)
      by (smt (verit) state_wtxn.distinct(3) commit_in_vl_v_writer_img image_iff)
  qed simp
qed

definition SvrVerWrTIDDistinct where
  "SvrVerWrTIDDistinct s k \<longleftrightarrow> distinct (map v_writer (DS (svrs s k)))"

lemmas SvrVerWrTIDDistinctI = SvrVerWrTIDDistinct_def[THEN iffD2, rule_format]
lemmas SvrVerWrTIDDistinctE[elim] = SvrVerWrTIDDistinct_def[THEN iffD1, elim_format, rule_format]

lemma reach_svr_ver_wr_tid_unique[simp, dest]: "reach tps s \<Longrightarrow> SvrVerWrTIDDistinct s k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: SvrVerWrTIDDistinct_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: SvrVerWrTIDDistinct_def tps_trans_defs svr_unchanged_defs)
      by (metis add_to_readerset_v_writer_map)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: SvrVerWrTIDDistinct_def tps_trans_defs svr_unchanged_defs tid_match_def)
      apply (cases "k = x1"; auto)
      using VerWrLCurrT3_def[of s x1] apply simp
      by (metis get_cl_txn.elims get_sn_txn.simps less_irrefl_nat)
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: SvrVerWrTIDDistinct_def tps_trans_defs svr_unchanged_defs)
      by (metis commit_in_vl_v_writer_multiset mset_eq_imp_distinct_iff mset_map)
  qed (auto simp add: SvrVerWrTIDDistinct_def tps_trans_defs cl_unchanged_defs)
qed

definition PastTIDNotPending where
  "PastTIDNotPending s cl \<longleftrightarrow> (\<forall>n k. \<forall>ver \<in> set (DS (svrs s k)).
   v_writer ver = Tn (Tn_cl n cl) \<and> n < txn_sn (cls s cl) \<longrightarrow> \<not>v_is_pending ver)"

lemmas PastTIDNotPendingI = PastTIDNotPending_def[THEN iffD2, rule_format]
lemmas PastTIDNotPendingE[elim] = PastTIDNotPending_def[THEN iffD1, elim_format, rule_format]

lemma reach_past_tid_notp [simp, dest]: "reach tps s \<Longrightarrow> PastTIDNotPending s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: PastTIDNotPending_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case by (simp add: PastTIDNotPending_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x1 x2 x3 x4)
    then show ?case by (simp add: PastTIDNotPending_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: PastTIDNotPending_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) VerWrLCurrT2_def insertCI reach_ver_wr_L_currT2)
  next
    case (WInvoke x1 x2)
    then show ?case by (simp add: PastTIDNotPending_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case by (simp add: PastTIDNotPending_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WDone x)
    then show ?case apply (simp add: PastTIDNotPending_def tps_trans_defs cl_unchanged_defs)
      apply (cases "cl = x", simp add: less_Suc_eq_le)
      subgoal sorry
      by metis
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: PastTIDNotPending_def tps_trans_defs svr_unchanged_defs)
      by (metis add_to_readerset_length add_to_readerset_v_is_pending add_to_readerset_v_writer
          in_set_conv_nth)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: PastTIDNotPending_def tps_trans_defs svr_unchanged_defs)
      by (smt get_cl_txn.simps get_sn_txn.simps nat_neq_iff not_in_append tid_match_def txid.inject
          version.select_convs(2))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: PastTIDNotPending_def tps_trans_defs svr_unchanged_defs) sorry
  qed simp
qed


abbreviation not_committing_ev where
  "not_committing_ev e \<equiv> \<forall>cl kvt_map kv_map cts sn u. e \<noteq> RDone cl kvt_map sn u \<and> e \<noteq> WCommit cl kv_map cts sn u"


definition FreshReadTxnInv where
  "FreshReadTxnInv s cl k \<longleftrightarrow> (txn_state (cls s cl) = Idle \<longrightarrow>
  (\<forall>i < length (DS (svrs s k)). get_txn_cl s cl \<notin> v_readerset (DS (svrs s k) ! i)))"

lemmas FreshReadTxnInvI = FreshReadTxnInv_def[THEN iffD2, rule_format]
lemmas FreshReadTxnInvE[elim] = FreshReadTxnInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_freshrdtxn [simp, dest]: "reach tps s \<Longrightarrow> FreshReadTxnInv s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FreshReadTxnInv_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x11 x12)
    then show ?case by (simp add: FreshReadTxnInv_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x21 x22 x23)
    then show ?case apply (simp add: FreshReadTxnInv_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(1))
  next
    case (RDone x31 x32 x33 x34)
    then show ?case apply (simp add: FreshReadTxnInv_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) FutureTidRdDS_def lessI nth_mem reach_tidfuture_rd_ds)
  next
    case (WInvoke x41 x42)
    then show ?case by (simp add: FreshReadTxnInv_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x51 x52 x53 x54 x55)
    then show ?case apply (simp add: FreshReadTxnInv_def tps_trans_defs cl_unchanged_defs)
      by (metis (lifting) state_txn.distinct(5))
  next
    case (WDone x6)
    then show ?case apply (simp add: FreshReadTxnInv_def tps_trans_defs cl_unchanged_defs)
      by (metis FutureTidRdDS_def lessI nth_mem reach_tidfuture_rd_ds)
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?case apply (simp add: FreshReadTxnInv_def tps_trans_defs svr_unchanged_defs tid_match_def)
      apply (cases "k = x71"; cases "cl = get_cl_txn x72"; auto) sorry
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case sorry
  next
    case (CommitW x91 x92)
    then show ?case sorry
  qed simp
qed

definition FreshWriteTxnInv where
  "FreshWriteTxnInv s cl \<longleftrightarrow> (\<forall>keys kvt_map k. txn_state (cls s cl) \<in> {Idle, RtxnInProg keys kvt_map} \<longrightarrow>
    Tn (get_txn_cl s cl) \<notin> v_writer ` set (DS (svrs s k)))"

lemmas FreshWriteTxnInvI = FreshWriteTxnInv_def[THEN iffD2, rule_format]
lemmas FreshWriteTxnInvE[elim] = FreshWriteTxnInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_freshwrtxn [simp, dest]: "reach tps s \<Longrightarrow> FreshWriteTxnInv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FreshWriteTxnInv_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case by (simp add: tps_trans_defs FreshWriteTxnInv_def cl_unchanged_defs, metis)
  next
    case (Read x1 x2 x3 x4)
    then show ?case by (simp add: tps_trans_defs FreshWriteTxnInv_def cl_unchanged_defs, metis)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: tps_trans_defs FreshWriteTxnInv_def cl_unchanged_defs)
      by (metis (lifting) FutureTidWrDS_def lessI reach_tidfuture_wr_ds)
  next
    case (WInvoke x1 x2)
    then show ?case by (simp add: tps_trans_defs FreshWriteTxnInv_def cl_unchanged_defs, metis)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: tps_trans_defs FreshWriteTxnInv_def cl_unchanged_defs)
      by (metis (no_types, lifting) state_txn.distinct(5) state_txn.distinct(9))
  next
    case (WDone x)
    then show ?case apply (simp add: tps_trans_defs FreshWriteTxnInv_def cl_unchanged_defs)
      by (metis FutureTidWrDS_def lessI reach_tidfuture_wr_ds)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (simp add: tps_trans_defs FreshWriteTxnInv_def svr_unchanged_defs)
      by (metis add_to_readerset_v_writer_img)
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: tps_trans_defs FreshWriteTxnInv_def svr_unchanged_defs)
      by (metis (no_types, lifting) append_image get_cl_txn.simps insert_iff state_txn.distinct(3)
          state_txn.distinct(7) txid.inject version.select_convs(2))
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: tps_trans_defs FreshWriteTxnInv_def svr_unchanged_defs)
      by (metis commit_in_vl_v_writer_img)
  qed simp
qed

lemma bla:
  assumes "x \<notin> a"
  shows "a - insert x b = a - b"
  using assms
  by simp

abbreviation invariant_list_kvs where
  "invariant_list_kvs s \<equiv> \<forall>cl k. FutureTIDInv s cl \<and> PastTIDInv s cl \<and> KVSNonEmp s \<and>
    KVSNotAllPending s k \<and> FreshReadTxnInv s cl k"

lemma kvs_of_s_inv:
  assumes "state_trans s e s'"
    and "invariant_list_kvs s"
    and "not_committing_ev e"
  shows "kvs_of_s s' = kvs_of_s s"
  using assms
  proof (induction e)
    case (RInvoke x1 x2)
    then have "get_ver_committed_rd s' = get_ver_committed_rd s"
      using pending_rtxn_added[of s x1 s'] bla[where x="get_txn_cl s x1" and b="Collect (pending_rtxn s)"]
      apply (auto simp add: tps_trans_defs get_ver_committed_rd_def cl_unchanged_defs FreshReadTxnInv_def get_vl_pre_committed_readersets) sorry
    then show ?case using RInvoke reach_trans pending_wtxn_cl_ev_inv[of s x1 s']
      apply (auto simp add: tps_trans_defs kvs_of_s_def cl_unchanged_defs get_vl_pre_committed_readersets)
      apply (rule ext) sorry
  next
    case (Read x1 x2 x3 x4)
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

lemma writers_inv_not_commit_write:
  assumes "state_trans s e s'"
    and "\<And>cl kv_map cts sn u. \<not>write_commit cl kv_map cts sn u s s'"
  shows "v_writer ` set (get_vl_pre_committed s' (DS (svrs s' svr))) =
  v_writer ` set (get_vl_pre_committed s (DS (svrs s svr)))"
  using assms
proof (induction e)
  case (RInvoke x1 x2)
  then show ?case using pending_wtxn_cl_ev_inv[of s x1 s']
    by (simp add: tps_trans_defs get_vl_pre_committed_writers cl_unchanged_defs)
next
  case (Read x1 x2 x3 x4)
  then show ?case using pending_wtxn_cl_ev_inv[of s x1 s']
    apply (simp add: tps_trans_defs get_vl_pre_committed_writers cl_unchanged_defs)
    by (metis state_txn.distinct(7))
next
  case (RDone x1 x2 x3 x4)
  then show ?case using pending_wtxn_cl_ev_inv[of s x1 s']
    by (simp add: tps_trans_defs get_vl_pre_committed_writers cl_unchanged_defs)
next
  case (WInvoke x1 x2)                    
  then show ?case using pending_wtxn_cl_ev_inv[of s x1 s']
    apply (simp add: tps_trans_defs get_vl_pre_committed_writers cl_unchanged_defs) sorry
next
  case (WDone x)
  then show ?case using pending_wtxn_cl_ev_inv[of s x s']
    apply (simp add: tps_trans_defs get_vl_pre_committed_writers cl_unchanged_defs)
    by (metis state_txn.distinct(11))
next
  case (RegR x1 x2 x3 x4 x5)
  then show ?case using pending_wtxn_svr_ev_inv[of s' s]
    apply (simp add: tps_trans_defs get_vl_pre_committed_writers svr_unchanged_defs) sorry
next
  case (PrepW x1 x2 x3 x4)
  then show ?case using pending_wtxn_svr_ev_inv[of s' s]
    apply (simp add: tps_trans_defs get_vl_pre_committed_writers svr_unchanged_defs) sorry
next
  case (CommitW x1 x2)
  then show ?case using pending_wtxn_svr_ev_inv[of s' s]
    apply (simp add: tps_trans_defs get_vl_pre_committed_writers cl_unchanged_defs) sorry
qed auto


definition NoPendingInView where
  "NoPendingInView s \<longleftrightarrow> (\<forall>cl k. cl_view (cls s cl) k \<subseteq> v_writer ` set (get_vl_pre_committed s (DS (svrs s k))))"

lemmas NoPendingInViewI = NoPendingInView_def[THEN iffD2, rule_format]
lemmas NoPendingInViewE[elim] = NoPendingInView_def[THEN iffD1, elim_format, rule_format]

lemma reach_no_pending_in_view [simp, dest]: "reach tps s \<Longrightarrow> NoPendingInView s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    apply (auto simp add: NoPendingInView_def tps_defs view_txid_init_def commit_all_in_vl_writers)
    by (simp add: get_state_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x11 x12)
    then show ?case
      apply (auto simp add: NoPendingInView_def tps_trans_defs get_vl_pre_committed_writers
          cl_unchanged_defs pending_wtxn_cl_ev_inv[of s x11 s'] dest!:eq_for_all_cl) by blast
  next
    case (Read x21 x22 x23)
    then show ?case
      apply (auto simp add: NoPendingInView_def tps_trans_defs get_vl_pre_committed_writers
          cl_unchanged_defs pending_wtxn_cl_ev_inv[of s x21 s'] dest!:eq_for_all_cl) by blast
  next
    case (RDone x31 x32 x33 x34)
    then show ?case 
      apply (auto simp add: NoPendingInView_def tps_trans_defs get_vl_pre_committed_writers
          cl_unchanged_defs pending_wtxn_cl_ev_inv[of s x31 s']) sorry
  next
    case (WInvoke x41 x42)
    then show ?case
      apply (auto simp add: NoPendingInView_def tps_trans_defs get_vl_pre_committed_writers
          cl_unchanged_defs dest!:eq_for_all_cl) sorry
  next
    case (WCommit x51 x52 x53 x54 x55)
    then show ?case 
      apply (auto simp add: NoPendingInView_def tps_trans_defs get_vl_pre_committed_writers
          cl_unchanged_defs) sorry
  next
    case (WDone x6)
    then show ?case
      apply (auto simp add: NoPendingInView_def tps_trans_defs get_vl_pre_committed_writers
          cl_unchanged_defs pending_wtxn_cl_ev_inv[of s x6 s'] dest!:eq_for_all_cl) by blast
  next
    case (RegR x71 x72 x73 x74 x75)
    then show ?case 
      apply (auto simp add: NoPendingInView_def tps_trans_defs get_vl_pre_committed_writers
          svr_unchanged_defs pending_wtxn_svr_ev_inv[of s' s]) sorry
  next
    case (PrepW x81 x82 x83 x84)
    then show ?case sorry
  next
    case (CommitW x91 x92)
    then show ?case sorry
  qed simp
qed

lemma in_view_index_not_none:
  assumes "x \<in> cl_view (cls s cl) k"
    and "NoPendingInView s"
  shows "x \<in> dom (get_indices_map (kvs_of_s s k))"
  using assms apply (auto simp add: kvs_of_s_def dom_indices_map get_indices_map_def)
  by blast

lemma map_extend_subset:
  assumes "k \<notin> dom m1"
    and "m2 = [k \<mapsto> v] ++ m1"
  shows "m1 \<subseteq>\<^sub>m m2"
  using assms
  by (simp add: map_le_def map_add_dom_app_simps(1))

lemma prefix_update_get_indices_map:
  shows "indices_map (vl1 @ [ver]) i = [v_writer ver \<mapsto> (i + length vl1)] ++ indices_map vl1 i"
  apply (induction vl1 i rule: indices_map.induct) subgoal by simp
  by (simp only: append_Cons indices_map.simps(2) map_add_upd length_Cons add_Suc_shift)

lemma prefix_subset_indices_map:
  assumes "v_writer ver \<notin> v_writer ` set vl1"
  shows "indices_map vl1 i \<subseteq>\<^sub>m indices_map (vl1 @ [ver]) i"
  using assms
  by (metis map_extend_subset dom_indices_map prefix_update_get_indices_map)

lemma read_commit_indices_map_grows:
  assumes "read_done cl kvt_map sn u s s'"
  shows "get_indices_map (kvs_of_s s k) \<subseteq>\<^sub>m get_indices_map (kvs_of_s s' k)"
  using assms
  apply (induction "kvs_of_s s k"; simp add: read_done_def dom_indices_map get_indices_map_def)
  apply (simp add: kvs_of_s_def) sorry

definition OnlyPendingVer where
  "OnlyPendingVer s cl k \<longleftrightarrow>
  (\<forall>t. \<forall>ver \<in> set (DS (svrs s k)). v_is_pending ver \<and> is_txn_writer t ver \<longrightarrow> t = Tn (get_txn_cl s cl))"

lemmas OnlyPendingVerI = OnlyPendingVer_def[THEN iffD2, rule_format]
lemmas OnlyPendingVerE[elim] = OnlyPendingVer_def[THEN iffD1, elim_format, rule_format]

lemma reach_only_pending_ver [simp, dest]: "reach tps s \<Longrightarrow> OnlyPendingVer s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: OnlyPendingVer_def tps_defs DS_vl_init_def ep_version_init_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case by (simp add: OnlyPendingVer_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x1 x2 x3 x4)
    then show ?case by (simp add: OnlyPendingVer_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: OnlyPendingVer_def tps_trans_defs cl_unchanged_defs)
      apply (cases "x1 = cl"; simp add: is_txn_writer_def)
      by (smt (z3) FreshWriteTxnInv_def insertI1 insert_commute insert_image reach_freshwrtxn reach_trans.hyps(2))
  next
    case (WInvoke x1 x2)
    then show ?case by (simp add: OnlyPendingVer_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case by (simp add: OnlyPendingVer_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WDone x)
    then show ?case apply (auto simp add: OnlyPendingVer_def tps_trans_defs cl_unchanged_defs)
      apply (cases "x = cl") subgoal sorry
      by metis 
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case sorry
  next
    case (CommitW x1 x2)
    then show ?case sorry
  qed simp
qed

definition CurrentVerPending where
  "CurrentVerPending s cl k \<longleftrightarrow>
    (\<forall>kvm keys ver kvtm. txn_state (cls s cl) \<in> {Idle, WtxnPrep kvm, RtxnInProg keys kvtm} \<and> 
    find (is_txn_writer (Tn (get_txn_cl s cl))) (DS (svrs s k)) = Some ver \<longrightarrow> v_is_pending ver)"

lemmas CurrentVerPendingI = CurrentVerPending_def[THEN iffD2, rule_format]
lemmas CurrentVerPendingE[elim] = CurrentVerPending_def[THEN iffD1, elim_format, rule_format]

lemma reach_curr_ver_pending [simp, dest]: "reach tps s \<Longrightarrow> CurrentVerPending s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: CurrentVerPending_def tps_defs DS_vl_init_def ep_version_init_def is_txn_writer_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case by (simp add: CurrentVerPending_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Read x1 x2 x3 x4)
    then show ?case by (simp add: CurrentVerPending_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: CurrentVerPending_def tps_trans_defs cl_unchanged_defs)
      by (metis (mono_tags, opaque_lifting) FutureTidWrDS_def find_Some_in_set image_iff
          is_txn_writer_def lessI reach_tidfuture_wr_ds)
  next
    case (WInvoke x1 x2)
    then show ?case by (simp add: CurrentVerPending_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: CurrentVerPending_def tps_trans_defs cl_unchanged_defs)
      by (metis (mono_tags))
  next
    case (WDone x)
    then show ?case apply (simp add: CurrentVerPending_def tps_trans_defs cl_unchanged_defs)
      by (metis (mono_tags) find_Some_in_set VerWrLCurrT_def Suc_n_not_le_n is_txn_writer_def
          reach_ver_wr_L_currT)
  next
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: CurrentVerPending_def tps_trans_defs svr_unchanged_defs)
      by (metis add_to_readerset_find_None add_to_readerset_find_is_pending option.exhaust)+
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case apply (simp add: CurrentVerPending_def tps_trans_defs svr_unchanged_defs)
      by (cases "x1 = k"; auto simp add: find_append split: option.split)
  next
    case (CommitW x1 x2)
    then show ?case apply (simp add: CurrentVerPending_def tps_trans_defs svr_unchanged_defs)
      apply (cases "get_txn_cl s cl = x2"; cases "x1 = k"; auto del: disjE)
      using commit_in_vl_find_another[of "Tn (get_txn_cl s cl)" "Tn x2" "DS (svrs s k)"] by auto
  qed simp
qed

lemma filter_non_existing:
  assumes "x \<notin> set vl"
    and "P x" and "\<not>Q x"
    and "\<And>y. y \<noteq> x \<longrightarrow> P y = Q y"
  shows "filter P vl = filter Q vl"
  using assms
  by (metis filter_cong)

lemma filter_existing:
  assumes "x \<in> set vl"
    and "P x" and "\<not>Q x"
    and "\<And>y. y \<noteq> x \<longrightarrow> P y = Q y"
  shows "filter P vl = filter Q vl @ [x]"
  using assms oops
  
lemma write_commit_not_add_to_ready:
  assumes "find (is_txn_writer (Tn (get_txn_cl s cl))) (DS (svrs s k)) = None"
    and "txn_sn (cls s' cl) = txn_sn (cls s cl)"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "get_vl_ready_to_commit_wr s' (DS (svrs s' k)) = get_vl_ready_to_commit_wr s (DS (svrs s k))"
  using assms eq_for_all_cl[of txn_sn s' cl s]
  apply (simp add: cl_unchanged_defs get_vl_ready_to_commit_wr_def pending_wtxn_def is_txn_writer_def
      split: txid.split txid0.split)
  by (smt (verit) filter_cong find_None_iff)
  

lemma write_commit_adds_one_to_ready:
  assumes "find (is_txn_writer (Tn (get_txn_cl s cl))) (DS (svrs s k)) = Some ver"
    and "txn_state (cls s cl) = WtxnPrep kv_map"
    and "txn_state (cls s' cl) = WtxnCommit (global_time s) cts kv_map"
    and "txn_sn (cls s' cl) = txn_sn (cls s cl)"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "\<exists>ver \<in> set (DS (svrs s' k)). get_vl_ready_to_commit_wr s' (DS (svrs s' k)) =
                                      get_vl_ready_to_commit_wr s (DS (svrs s k)) @ [ver]"
  using assms eq_for_all_cl[of txn_sn s' cl s]
  apply (simp add: cl_unchanged_defs get_vl_ready_to_commit_wr_def pending_wtxn_def
      split: txid.split txid0.split)
  apply (rule bexI [where x=ver])
    subgoal sorry
    by (meson find_Some_in_set)


lemma get_glts_ready_to_commit_inv:
  assumes "PastTIDNotPending s cl" and "VerWrLCurrT s cl"
    and "ver \<in> set (get_vl_ready_to_commit_wr s (DS (svrs s k)))"
    and "find (is_txn_writer (Tn (get_txn_cl s cl))) (DS (svrs s k)) = None"
    and "txn_state (cls s cl) = WtxnPrep kv_map"
    and "txn_state (cls s' cl) = WtxnCommit (global_time s) cts kv_map"
    and "txn_sn (cls s' cl) = txn_sn (cls s cl)"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "get_glts s' ver = get_glts s ver"
  using assms
  apply (auto simp add: get_glts_def get_state_defs cl_unchanged_defs split: txid.split txid0.split)
  subgoal for n cl' apply (cases "cl' = cl"; simp add: is_txn_writer_def)
    by (smt (verit) PastTIDNotPending_def VerWrLCurrT_def find_None_iff order_le_imp_less_or_eq).

lemma write_commit_indices_map_grows:
  assumes "write_commit cl kv_map cts sn u s s'"
  shows "get_indices_map (kvs_of_s s k) \<subseteq>\<^sub>m get_indices_map (kvs_of_s s' k)"
  using assms
  apply (simp add: write_commit_def dom_indices_map get_indices_map_def)
  apply (simp add: kvs_of_s_def get_vl_pre_committed_def svrs_cls_cl'_unchanged_def)
  apply (cases "find (is_txn_writer (Tn (get_txn_cl s cl))) (DS (svrs s k))")
  subgoal apply (auto dest!: write_commit_not_add_to_ready)
    apply (induction s "get_vl_committed_wr (DS (svrs s k))" "get_vl_ready_to_commit_wr s (DS (svrs s k))"
        arbitrary: k s' rule: commit_all_in_vl.induct; auto) sorry
  apply (auto dest!: write_commit_adds_one_to_ready simp add:commit_all_in_vl_append)
  using prefix_subset_indices_map sorry

lemma kvs_readers_sqns_other_cl_inv:
  assumes "FutureTIDInv s cl" and "PastTIDInv s cl" and "KVSNonEmp s"
    and "txn_state (cls s cl) = RtxnInProg keys kvm"
    and "txn_state (cls s' cl) = Idle"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
    and "cl' \<noteq> cl"
  shows "kvs_readers_sqns (kvs_of_s s') cl' = kvs_readers_sqns (kvs_of_s s) cl'"
  using assms sorry

lemma vl_writers_sqns_other_cl_inv:
  assumes "KVSNonEmp s"
  shows "\<And>cl. vl_writers_sqns (map (epv_to_ver o get_ver_committed_rd s') (get_vl_pre_committed s' vl)) cl =
              vl_writers_sqns vl cl'"
  using assms
  apply (auto simp add: vl_writers_sqns_def vl_writers_def) sorry

lemma read_done_kvs_writers_sqns_inv:
  assumes "FutureTIDInv s cl" and "PastTIDInv s cl" and "KVSNonEmp s"
    and "txn_state (cls s cl) = RtxnInProg keys kvm"
    and "txn_state (cls s' cl) = Idle"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "\<And>cl. kvs_writers_sqns (kvs_of_s s') cl = kvs_writers_sqns (kvs_of_s s) cl"
  using assms
  apply (simp add: kvs_writers_sqns_def kvs_of_s_def)
  by (metis vl_writers_sqns_other_cl_inv)

lemma read_done_get_sqns_other_cl_inv:
  assumes "FutureTIDInv s cl" and "PastTIDInv s cl" and "KVSNonEmp s"
    and "txn_state (cls s cl) = RtxnInProg keys kvm"
    and "txn_state (cls s' cl) = Idle"
    and "svrs_cls_cl'_unchanged cl s s'"
    and "cl' \<noteq> cl"
  shows "get_sqns (kvs_of_s s') cl' = get_sqns (kvs_of_s s) cl'"
  using assms by (auto simp add: get_sqns_def read_done_kvs_writers_sqns_inv
      kvs_readers_sqns_other_cl_inv cl_unchanged_defs)
                              

definition SqnInv_nc where
  "SqnInv_nc s cl \<longleftrightarrow> (\<forall>gts cts kvm.
    (txn_state (cls s cl) \<noteq> WtxnCommit gts cts kvm \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m < txn_sn (cls s cl))))"

lemmas SqnInv_ncI = SqnInv_nc_def[THEN iffD2, rule_format]
lemmas SqnInv_ncE[elim] = SqnInv_nc_def[THEN iffD1, elim_format, rule_format]

lemma reach_sql_inv_nc [simp, intro]:
  assumes "reach tps s"
  shows "SqnInv_nc s cl"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    apply (auto simp add: SqnInv_nc_def tps_defs kvs_of_s_def get_sqns_old_def kvs_txids_def
        get_state_defs full_view_def DS_vl_init_def ep_version_init_def)
    apply (auto simp add: kvs_writers_def vl_writers_def)
    by (auto simp add: kvs_readers_def vl_readers_def)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: SqnInv_nc_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(5))
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: SqnInv_nc_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: SqnInv_nc_def tps_trans_defs)
       apply (metis (lifting) state_txn.distinct(9) cl_unchanged_defs)
      apply (cases "cl = x1", simp)
      subgoal sorry
      by (smt (verit) other_insts_unchanged_def reach_kvs_non_emp reach_tidfuturekm reach_tidpastkm
          svrs_cls_cl'_unchanged_def read_done_get_sqns_other_cl_inv)
  next
    case (WInvoke x1 x2)
    then show ?case apply (simp add: SqnInv_nc_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(5))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: SqnInv_nc_def tps_trans_defs cl_unchanged_defs) sorry
  next
    case (WDone x)
    then show ?case apply (simp add: SqnInv_nc_def tps_trans_defs cl_unchanged_defs)
      by (metis less_SucI nat.discI state_txn.inject(3))
  qed (auto simp add: SqnInv_nc_def tps_trans_defs svr_unchanged_defs)
qed

definition SqnInv_c where
  "SqnInv_c s cl \<longleftrightarrow> (\<forall>gts cts kvm.
    (txn_state (cls s cl) = WtxnCommit gts cts kvm \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_s s) cl. m \<le> txn_sn (cls s cl))))"

lemmas SqnInv_cI = SqnInv_c_def[THEN iffD2, rule_format]
lemmas SqnInv_cE[elim] = SqnInv_c_def[THEN iffD1, elim_format, rule_format]

lemma reach_sql_inv_c [simp, intro]:
  assumes "reach tps s"
    and "KVSNonEmp s"
  shows "SqnInv_c s cl"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: SqnInv_c_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_s_inv[of s e s']
  proof (induction e)
    case (RInvoke x1 x2)
    then show ?case apply (simp add: SqnInv_c_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(9))
  next
    case (Read x1 x2 x3 x4)
    then show ?case apply (simp add: SqnInv_c_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(9))
  next
    case (RDone x1 x2 x3 x4)
    then show ?case apply (auto simp add: SqnInv_c_def tps_trans_defs cl_unchanged_defs)
      apply (metis state_txn.distinct(5))
      by (metis SqnInv_nc_def nat.distinct(1) nless_le reach.reach_trans reach_sql_inv_nc
          reach_trans.hyps(1) state_txn.inject(3))
  next
    case (WInvoke x1 x2)
    then show ?case apply (simp add: SqnInv_c_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(11))
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: SqnInv_c_def tps_trans_defs cl_unchanged_defs)
      by (metis SqnInv_nc_def leD nat_le_linear reach.reach_trans reach_sql_inv_nc
          reach_trans.hyps(1) state_txn.inject(3))
  next
    case (WDone x)
    then show ?case apply (simp add: SqnInv_c_def tps_trans_defs cl_unchanged_defs)
      by (metis state_txn.distinct(5))
  qed (auto simp add: SqnInv_c_def tps_trans_defs svr_unchanged_defs)
qed

lemma t_is_fresh:
  assumes "SqnInv_c s cl" and "SqnInv_nc s cl"
    and "txn_state (cls s cl) \<in> {WtxnPrep kv_map, RtxnInProg keys kvt_map}"
  shows "get_txn_cl s cl \<in> next_txids (kvs_of_s s) cl"
  using assms by (auto simp add: kvs_of_s_def next_txids_def)

\<comment> \<open>CanCommit\<close>

definition RO_WO_Inv where
  "RO_WO_Inv s \<equiv> (kvs_writers (\<lambda>k. DS (svrs s k)) \<inter> Tn ` kvs_readers (\<lambda>k. DS (svrs s k)) = {})"

(*lemmas RO_WO_InvI = RO_WO_Inv_def[THEN iffD2, rule_format]
lemmas RO_WO_InvE[elim] = RO_WO_Inv_def[THEN iffD1, elim_format, rule_format]*)

lemma reach_ro_wo_inv [simp, dest]: "reach tps s \<Longrightarrow> RO_WO_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: RO_WO_Inv_def tps_defs DS_vl_init_def ep_version_init_def txid_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5)
    then show ?case apply (auto simp add: RO_WO_Inv_def tps_trans_defs svr_unchanged_defs)
     using add_to_readerset_v_writer_img[of ] apply (simp add: txid_defs) sorry \<comment> \<open>Continue here!\<close>
  next
    case (PrepW x1 x2 x3 x4)
    then show ?case sorry
  next
    case (CommitW x1 x2)
    then show ?case sorry
  qed (auto simp add: RO_WO_Inv_def tps_trans_defs cl_unchanged_defs)
qed

lemma "kvs_txids (kvs_of_s gs) - kvs_writers (kvs_of_s gs) = Tn ` kvs_readers (kvs_of_s gs)"
  apply (simp add: kvs_of_s_def) sorry

lemma views_of_s_satisfies_ET_CC_canCommit:
  assumes "txn_state (cls gs cl) = RtxnInProg (dom kvt_map) kvt_map"
    and "u'' = (\<lambda>k. get_indices_fun gs k ` (case kvt_map k of
      None \<Rightarrow> cl_view (cls gs cl) k | Some (v, t) \<Rightarrow> insert t (cl_view (cls gs cl) k)))"
  shows "ET_CC.canCommit (kvs_of_s gs) u'' (\<lambda>k. case_op_type (o_fst kv_map k) None)"
  using assms
  apply (simp add: ET_CC.canCommit_def closed_def read_only_Txs_def R_CC_def R_onK_def views_of_s_def)
  sorry

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

lemma read_commit_views_of_s_other_cl_inv:
  assumes "read_done cl kv_map sn u s s'"
    and "NoPendingInView s"
    and "cl' \<noteq> cl"
  shows "views_of_s s' cl' = views_of_s s cl'"
  using assms
  apply (auto simp add: read_done_def svrs_cls_cl'_unchanged_def views_of_s_def image_def split: option.split)
  apply (rule ext) subgoal for k using read_commit_indices_map_grows [where s=s and s'=s' and k=k]
    unfolding map_le_def
    by (smt (z3) Collect_cong assms(1) domIff in_view_index_not_none other_insts_unchanged_def).

lemma write_commit_views_of_s_other_cl_inv:
  assumes "write_commit cl kv_map cts sn u s s'"
    and "NoPendingInView s"
    and "cl' \<noteq> cl"
  shows "views_of_s s' cl' = views_of_s s cl'"
  using assms
  apply (auto simp add: write_commit_def svrs_cls_cl'_unchanged_def views_of_s_def image_def split: option.split)
  apply (rule ext) subgoal for k using write_commit_indices_map_grows [where s=s and s'=s' and k=k]
    unfolding map_le_def
    by (smt (z3) Collect_cong assms(1) domIff in_view_index_not_none other_insts_unchanged_def).

abbreviation invariant_list where
  "invariant_list s \<equiv> (\<forall>cl. invariant_list_kvs s \<and> NoPendingInView s \<and> SqnInv_c s cl \<and> SqnInv_nc s cl)"

subsection \<open>Refinement Proof\<close>

lemma tps_refines_et_es: "tps \<sqsubseteq>\<^sub>med ET_CC.ET_ES"
proof (intro simulate_ES_fun_with_invariant[where I="\<lambda>s. invariant_list s"])
  fix gs0 :: "'v state"
  assume p: "init tps gs0"
  then show "init ET_CC.ET_ES (sim gs0)"
  by (auto simp add: ET_CC.ET_ES_defs tps_defs sim_defs DS_vl_init_def ep_version_init_def get_state_defs
    get_indices_map_def kvs_init_def v_list_init_def version_init_def view_txid_init_def)
next
  fix gs a and gs' :: "'v state"
  assume p: "tps: gs\<midarrow>a\<rightarrow> gs'" and inv: "invariant_list gs"
  then show "ET_CC.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  using kvs_of_s_inv[of gs a gs'] views_of_s_inv[of gs a gs']
  proof (induction a)
    case (RDone cl kvt_map sn u'')
    then show ?case using p apply simp
      apply (auto simp add: read_done_def cl_unchanged_defs sim_def)
      apply (rule exI [where x="views_of_s gs' cl"]) apply auto
      subgoal apply (auto simp add: ET_CC.ET_cl_txn_def t_is_fresh KVSSNonEmp_def)
        subgoal apply (simp add: view_wellformed_def views_of_s_def) sorry
        subgoal sorry
        subgoal by (simp add: views_of_s_satisfies_ET_CC_canCommit)
        sorry
        subgoal apply (rule ext)
          subgoal for cl' apply (cases "cl' = cl"; simp)
          using read_commit_views_of_s_other_cl_inv [where s=gs and s'=gs' and cl=cl and cl'=cl']
          by (metis RDone.prems(1) state_trans.simps(3) tps_trans).
      subgoal apply (auto simp add: fp_property_def view_snapshot_def)
        subgoal for k y apply (simp add: last_version_def kvs_of_s_def get_state_defs)
          apply (cases "k \<in> dom kvt_map") sorry
        done
      done
  next
    case (WCommit cl kv_map cts sn u'')
    then show ?case using p apply simp
      apply (auto simp add: write_commit_def cl_unchanged_defs sim_def fp_property_def)
      apply (rule exI [where x="views_of_s gs' cl"]) apply auto
        subgoal apply (auto simp add: ET_CC.ET_cl_txn_def t_is_fresh) sorry
        subgoal apply (rule ext)
          subgoal for cl' apply (cases "cl' = cl"; simp)
          using write_commit_views_of_s_other_cl_inv [where s=gs and s'=gs' and cl=cl and cl'=cl']
          by (metis WCommit.prems(1) state_trans.simps(5) tps_trans).
      done
  qed (auto simp add: sim_defs get_state_defs image_iff)
qed simp

end