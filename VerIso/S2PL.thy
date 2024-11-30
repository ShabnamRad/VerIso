section \<open>Strict Two Phase Locking (S2PL) protocol\<close>

theory S2PL
  imports Execution_Tests
begin

subsection \<open>2PC Event system & Refinement from ET_ES to tpl\<close>

subsubsection \<open>State\<close>

datatype state_svr = working | prepared | read_lock | write_lock | no_lock | notokay | committed | aborted
datatype state_cl = cl_init | cl_prepared | cl_committed | cl_aborted

\<comment>\<open>Client State\<close>
record cl_conf =
  cl_state :: state_cl
  cl_sn :: nat

\<comment>\<open>Server State\<close>
record 'v svr_conf =
  svr_state :: "txid0 \<Rightarrow> state_svr"
  svr_vl :: "'v v_list"
  svr_fp :: "txid0 \<Rightarrow> 'v key_fp"

\<comment>\<open>System Global State: Clients and key Servers\<close>
record 'v global_conf =
  cls :: "cl_id \<Rightarrow> cl_conf"
  svrs :: "key \<Rightarrow> 'v svr_conf"

\<comment> \<open>Translator functions\<close>

abbreviation get_txn :: "cl_id \<Rightarrow> 'v global_conf \<Rightarrow> txid0" where
  "get_txn cl s \<equiv> Tn_cl (cl_sn (cls s cl)) cl"

subsubsection \<open>Simulation function\<close>

definition eligible_reads :: "(txid0 \<Rightarrow> state_cl) \<Rightarrow> (txid0 \<Rightarrow> state_svr) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> txid0 set" where
  "eligible_reads tCls tSvrs tFk \<equiv> {t.
     tCls t = cl_committed \<and> tSvrs t \<in> {read_lock, write_lock} \<and> tFk t R \<noteq> None}"

definition update_kv_key_reads_all_txn :: "(txid0 \<Rightarrow> state_cl) \<Rightarrow> (txid0 \<Rightarrow> state_svr) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_key_reads_all_txn tCls tSvrs tFk vl =
    (let uk = full_view vl; lv = last_version vl uk in
     vl [Max uk := lv \<lparr>v_readerset := (v_readerset lv) \<union> eligible_reads tCls tSvrs tFk\<rparr>])"

abbreviation the_wr_t :: "(txid0 \<Rightarrow> state_svr) \<Rightarrow> txid0" where
  "the_wr_t tSvrs \<equiv> (THE t. tSvrs t = write_lock)"

definition update_kv_key_writes_all_txn :: "(txid0 \<Rightarrow> state_cl) \<Rightarrow> (txid0 \<Rightarrow> state_svr) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_key_writes_all_txn tCls tSvrs tFk vl =
    (if (\<exists>t. tCls t = cl_committed \<and> tSvrs t = write_lock) then
        update_kv_key_writes (the_wr_t tSvrs) (tFk (the_wr_t tSvrs) W) vl
     else vl)"

definition update_kv_all_txn :: "(txid0 \<Rightarrow> state_cl) \<Rightarrow> (txid0 \<Rightarrow> state_svr) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_all_txn tCls tSvrs tFk =
    (update_kv_key_writes_all_txn tCls tSvrs tFk) o (update_kv_key_reads_all_txn tCls tSvrs tFk)"


definition kvs_of_gs :: "'v global_conf \<Rightarrow> 'v kv_store" where
  "kvs_of_gs gs = (\<lambda>k.
   update_kv_all_txn (\<lambda>t. cl_state (cls gs (get_cl t)))
    (svr_state (svrs gs k)) (svr_fp (svrs gs k)) (svr_vl (svrs gs k)))"

definition views_of_gs :: "'v global_conf \<Rightarrow> (cl_id \<Rightarrow> view)" where
  "views_of_gs gs = (\<lambda>cl. view_init)"        \<comment> \<open>constant!\<close>

definition sim :: "'v global_conf \<Rightarrow> 'v config" where         
  "sim gs = (kvs_of_gs gs, views_of_gs gs)"

lemmas update_kv_key_reads_all_defs = update_kv_key_reads_all_txn_def Let_def 
lemmas update_kv_all_defs = update_kv_key_reads_all_defs update_kv_key_writes_all_txn_def update_kv_all_txn_def
lemmas sim_defs = sim_def kvs_of_gs_def views_of_gs_def


subsubsection \<open>Events\<close>

datatype 'v ev = Prepare key txid0 | RLock key 'v txid0 | WLock key 'v "'v option" txid0 |
  NoLock key txid0 | NOK key txid0 | Commit key txid0 | Abort key txid0 |
  Cl_Prep cl_id | Cl_Commit cl_id sqn view "'v fingerpr"| Cl_Abort cl_id | Cl_ReadyC cl_id |
  Cl_ReadyA cl_id | Skip2

text \<open>Auxiliary definitions\<close>

definition svr_t'_unchanged where
  "svr_t'_unchanged t k svrss svrss' \<equiv> (\<forall>t'. t' \<noteq> t \<longrightarrow>
     svr_fp (svrss' k) t' = svr_fp (svrss k) t' \<and>
     svr_state (svrss' k) t' = svr_state (svrss k) t')"

definition other_insts_unchanged where
  "other_insts_unchanged k svrss svrss' \<equiv> (\<forall>k'. k' \<noteq> k \<longrightarrow> svrss' k' = svrss k')"

definition cl_svr_k'_t'_unchanged where
  "cl_svr_k'_t'_unchanged k s s' t \<equiv> cls s' = cls s \<and>
    other_insts_unchanged k (svrs s) (svrs s') \<and> svr_t'_unchanged t k (svrs s) (svrs s')"

definition svr_cl_cl'_unchanged where
  "svr_cl_cl'_unchanged cl s s' \<equiv> svrs s' = svrs s \<and> other_insts_unchanged cl (cls s) (cls s')"

lemmas svr_unchanged_defs = cl_svr_k'_t'_unchanged_def other_insts_unchanged_def svr_t'_unchanged_def
lemmas cl_unchanged_defs = svr_cl_cl'_unchanged_def other_insts_unchanged_def
lemmas unchanged_defs = svr_unchanged_defs svr_cl_cl'_unchanged_def

definition tid_match :: "'v global_conf \<Rightarrow> txid0 \<Rightarrow> bool" where
  "tid_match s t \<equiv> cl_sn (cls s (get_cl t)) = get_sn t"

abbreviation svr_state_trans where
  "svr_state_trans s k s' t from_stat to_stat \<equiv>
      svr_state (svrs s k) t = from_stat
    \<and> svr_vl (svrs s' k) = svr_vl (svrs s k)
    \<and> svr_fp (svrs s' k) = svr_fp (svrs s k)
    \<and> svr_state (svrs s' k) t = to_stat
    \<and> cl_svr_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

abbreviation last_ver_v :: "'v v_list \<Rightarrow> 'v" where
  "last_ver_v vl \<equiv> v_value (last_version vl (full_view vl))"

abbreviation is_locked :: "state_svr \<Rightarrow> bool" where
  "is_locked svr_st \<equiv> svr_st \<in> {read_lock, write_lock, no_lock}"

abbreviation not_locked :: "state_svr \<Rightarrow> bool" where
  "not_locked svr_st \<equiv> svr_st \<notin> {write_lock, read_lock}"


text \<open>Events' transition relations\<close>

definition prepare where
  "prepare k t s s' \<equiv>
    cl_state (cls s (get_cl t)) = cl_prepared
    \<and> svr_state_trans s k s' t working prepared"

definition acq_rd_lock where \<comment>\<open>Read Lock acquired\<close>
  "acq_rd_lock k v t s s' \<equiv>
    (\<forall>t'. svr_state (svrs s k) t' \<noteq> write_lock)
    \<and> svr_state (svrs s k) t = prepared
    \<and> svr_vl (svrs s' k) = svr_vl (svrs s k)
    \<and> v = last_ver_v (svr_vl (svrs s k))
    \<and> svr_fp (svrs s' k) t W = None
    \<and> svr_fp (svrs s' k) t R = Some v
    \<and> svr_state (svrs s' k) t = read_lock
    \<and> cl_svr_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

definition acq_wr_lock where \<comment>\<open>Write Lock acquired\<close>
  "acq_wr_lock k v ov t s s' \<equiv>
    (\<forall>t'. not_locked (svr_state (svrs s k) t'))
    \<and> svr_state (svrs s k) t = prepared
    \<and> svr_vl (svrs s' k) = svr_vl (svrs s k)
    \<and> ov \<in> {None, Some (last_ver_v (svr_vl (svrs s k)))}
    \<and> svr_fp (svrs s' k) t W = Some v
    \<and> svr_fp (svrs s' k) t R = ov
    \<and> svr_state (svrs s' k) t = write_lock
    \<and> cl_svr_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

definition acq_no_lock where \<comment>\<open>No Lock needed\<close>
  "acq_no_lock k t s s' \<equiv>
    svr_fp (svrs s' k) t = Map.empty
    \<and> svr_state_trans s k s' t prepared no_lock"

definition nok where \<comment>\<open>Lock not available\<close>
  "nok k t s s' \<equiv>
    cl_state (cls s (get_cl t)) = cl_prepared
    \<and> svr_state_trans s k s' t prepared notokay"

definition commit where
  "commit k t s s' \<equiv>
    is_locked (svr_state (svrs s k) t)
    \<and> cl_state (cls s (get_cl t)) = cl_committed
    \<and> svr_vl (svrs s' k) =
        update_kv_key t (svr_fp (svrs s k) t) (full_view (svr_vl (svrs s k))) (svr_vl (svrs s k))
    \<and> svr_state (svrs s' k) t = committed
    \<and> svr_fp (svrs s' k) t = svr_fp (svrs s k) t
    \<and> cl_svr_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

definition abort where \<comment>\<open>Locks released (aborted)\<close>
  "abort k t s s' \<equiv>
    svr_state (svrs s k) t \<in> {read_lock, write_lock, no_lock, notokay}
    \<and> cl_state (cls s (get_cl t)) = cl_aborted
    \<and> svr_vl (svrs s' k) = svr_vl (svrs s k)
    \<and> svr_state (svrs s' k) t = aborted
    \<and> svr_fp (svrs s' k) t = svr_fp (svrs s k) t
    \<and> cl_svr_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

definition cl_prepare where
  "cl_prepare cl s s' \<equiv>
    cl_state (cls s cl) = cl_init
    \<and> cl_state (cls s' cl) = cl_prepared
    \<and> cl_sn (cls s' cl) = cl_sn (cls s cl)
    \<and> svr_cl_cl'_unchanged cl s s'"

definition cl_commit where
  "cl_commit cl sn u'' F s s' \<equiv>
    sn = cl_sn (cls s cl) \<and>
    u'' = full_view o kvs_of_gs s \<and>
    F = (\<lambda>k. svr_fp (svrs s k) (get_txn cl s)) \<and>
    cl_state (cls s cl) = cl_prepared \<and>
    (\<forall>k. is_locked (svr_state (svrs s k) (get_txn cl s))) \<and>
    cl_state (cls s' cl) = cl_committed \<and>
    cl_sn (cls s' cl) = cl_sn (cls s cl) \<and>
    svr_cl_cl'_unchanged cl s s'"

definition cl_abort where
  "cl_abort cl s s' \<equiv>
    cl_state (cls s cl) = cl_prepared
    \<and> (\<exists>k. svr_state (svrs s k) (get_txn cl s) = notokay)
    \<and> (\<forall>k. svr_state (svrs s k) (get_txn cl s) \<in> {read_lock, write_lock, no_lock, notokay})
    \<and> cl_state (cls s' cl) = cl_aborted
    \<and> cl_sn (cls s' cl) = cl_sn (cls s cl)
    \<and> svr_cl_cl'_unchanged cl s s'"

definition cl_ready_c where
  "cl_ready_c cl s s' \<equiv>
    cl_state (cls s cl) = cl_committed
    \<and> (\<forall>k. svr_state (svrs s k) (get_txn cl s) = committed)
    \<and> cl_state (cls s' cl) = cl_init
    \<and> cl_sn (cls s' cl) = Suc (cl_sn (cls s cl))
    \<and> svr_cl_cl'_unchanged cl s s'"

definition cl_ready_a where
  "cl_ready_a cl s s' \<equiv>
    cl_state (cls s cl) = cl_aborted
    \<and> (\<forall>k. svr_state (svrs s k) (get_txn cl s) = aborted)
    \<and> cl_state (cls s' cl) = cl_init
    \<and> cl_sn (cls s' cl) = Suc (cl_sn (cls s cl))
    \<and> svr_cl_cl'_unchanged cl s s'"


subsubsection \<open>The Event System\<close>

definition gs_init :: "'v global_conf" where
  "gs_init \<equiv> \<lparr> 
    cls = (\<lambda>cl. \<lparr> cl_state = cl_init,
                 cl_sn = 0 \<rparr>),
    svrs = (\<lambda>k. \<lparr> svr_state = (\<lambda>t. working),
                 svr_vl = [version_init],
                 svr_fp = (\<lambda>t. Map.empty)\<rparr>)
  \<rparr>"

fun gs_trans :: "'v global_conf \<Rightarrow> 'v ev \<Rightarrow> 'v global_conf \<Rightarrow> bool" where
  "gs_trans s (Prepare k t)         s' \<longleftrightarrow> prepare k t s s'" |
  "gs_trans s (RLock k v t)         s' \<longleftrightarrow> acq_rd_lock k v t s s'" |
  "gs_trans s (WLock k v ov t)      s' \<longleftrightarrow> acq_wr_lock k v ov t s s'" |
  "gs_trans s (NoLock k t)          s' \<longleftrightarrow> acq_no_lock k t s s'" |
  "gs_trans s (NOK k t)             s' \<longleftrightarrow> nok k t s s'" |
  "gs_trans s (Commit k t)          s' \<longleftrightarrow> commit k t s s'" |
  "gs_trans s (Abort k t)           s' \<longleftrightarrow> abort k t s s'" |
  "gs_trans s (Cl_Prep cl)          s' \<longleftrightarrow> cl_prepare cl s s'" |
  "gs_trans s (Cl_Commit cl sn u F) s' \<longleftrightarrow> cl_commit cl sn u F s s'" |
  "gs_trans s (Cl_Abort cl)         s' \<longleftrightarrow> cl_abort cl s s'" |
  "gs_trans s (Cl_ReadyC cl)        s' \<longleftrightarrow> cl_ready_c cl s s'" |
  "gs_trans s (Cl_ReadyA cl)        s' \<longleftrightarrow> cl_ready_a cl s s'" |
  "gs_trans s Skip2                 s' \<longleftrightarrow> s' = s"

definition tpl :: "('v ev, 'v global_conf) ES" where
  "tpl \<equiv> \<lparr>
    init = (=) gs_init,
    trans = gs_trans
  \<rparr>"

lemmas tpl_trans_defs = prepare_def acq_rd_lock_def acq_wr_lock_def
                        acq_no_lock_def nok_def commit_def abort_def
                        cl_prepare_def cl_commit_def cl_abort_def cl_ready_c_def cl_ready_a_def

lemmas tpl_defs = tpl_def gs_init_def

lemma tpl_trans [simp]: "trans tpl = gs_trans" by (simp add: tpl_def)

subsubsection \<open>Mediator function\<close>

fun med :: "'v ev \<Rightarrow> 'v label" where
  "med (Cl_Commit cl sn u'' F) = ET cl sn u'' F" |
  "med _ = ETSkip"

end
