section \<open>Two Phase Commit (2PC) with Two Phase Locking (2PL)\<close>

theory Serializable_2PC_2PL
  imports Execution_Tests
begin

subsection \<open>2PC Event system & Refinement from ET_ES to tps\<close>

subsubsection \<open>State\<close>

datatype state_km = working | prepared | read_lock | write_lock | no_lock | notokay | committed | aborted
datatype state_tm = tm_init | tm_prepared | tm_committed | tm_aborted

\<comment>\<open>Client State\<close>
record cl_state =
  tm_state :: state_tm
  cl_sn :: nat
  cl_view :: view

\<comment>\<open>Server State\<close>
record 'v svr_state =
  km_state :: "txid0 \<Rightarrow> state_km"
  svr_vl :: "'v v_list"
  svr_key_fp :: "txid0 \<Rightarrow> 'v key_fp"

\<comment>\<open>System Global State: Clients and key Servers\<close>
record 'v global_state =
  cls :: "cl_id \<Rightarrow> cl_state"
  svrs :: "key \<Rightarrow> 'v svr_state"

\<comment> \<open>Translator functions\<close>

abbreviation get_txn_cl :: "cl_id \<Rightarrow> 'v global_state \<Rightarrow> txid0" where
  "get_txn_cl cl s \<equiv> Tn_cl (cl_sn (cls s cl)) cl"

subsubsection \<open>Simulation function\<close>

abbreviation eligible_reads :: "(txid0 \<Rightarrow> state_tm) \<Rightarrow> (txid0 \<Rightarrow> state_km) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> txid0 \<Rightarrow> bool" where
  "eligible_reads tStm tSkm tFk t \<equiv>
    tStm t = tm_committed \<and> tSkm t \<in> {read_lock, write_lock} \<and> tFk t R \<noteq> None"

definition update_kv_reads_all_txn :: "(txid0 \<Rightarrow> state_tm) \<Rightarrow> (txid0 \<Rightarrow> state_km) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_reads_all_txn tStm tSkm tFk vl =
    (let uk = full_view vl; lv = last_version vl uk in
     vl [Max uk := lv \<lparr>v_readerset := (v_readerset lv) \<union> {t. eligible_reads tStm tSkm tFk t}\<rparr>])"

abbreviation the_wr_t :: "(txid0 \<Rightarrow> state_km) \<Rightarrow> txid0" where
  "the_wr_t tSkm \<equiv> (THE t. tSkm t = write_lock)"

definition update_kv_writes_all_txn :: "(txid0 \<Rightarrow> state_tm) \<Rightarrow> (txid0 \<Rightarrow> state_km) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_writes_all_txn tStm tSkm tFk vl =
    (if (\<exists>t. tStm t = tm_committed \<and> tSkm t = write_lock) then
        update_kv_writes (the_wr_t tSkm) (tFk (the_wr_t tSkm)) vl
     else vl)"

definition update_kv_all_txn :: "(txid0 \<Rightarrow> state_tm) \<Rightarrow> (txid0 \<Rightarrow> state_km) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_all_txn tStm tSkm tFk =
    (update_kv_writes_all_txn tStm tSkm tFk) o (update_kv_reads_all_txn tStm tSkm tFk)"

definition kvs_of_gs :: "'v global_state \<Rightarrow> 'v kv_store" where
  "kvs_of_gs gs = (\<lambda>k.
   update_kv_all_txn (\<lambda>t. tm_state (cls gs (get_cl_txn t)))
    (km_state (svrs gs k)) (svr_key_fp (svrs gs k)) (svr_vl (svrs gs k)))"

definition views_of_gs :: "'v global_state \<Rightarrow> (cl_id \<Rightarrow> view)" where
  "views_of_gs gs = (\<lambda>cl. cl_view (cls gs cl))"

definition sim :: "'v global_state \<Rightarrow> 'v config" where         
  "sim gs = (kvs_of_gs gs, views_of_gs gs)"

lemmas update_kv_reads_all_defs = update_kv_reads_all_txn_def Let_def last_version_def
lemmas update_kv_all_defs = update_kv_reads_all_defs update_kv_writes_all_txn_def update_kv_all_txn_def
lemmas sim_defs = sim_def kvs_of_gs_def views_of_gs_def


subsubsection \<open>Events\<close>

datatype 'v ev = Prepare key txid0 | RLock key 'v txid0 | WLock key 'v "'v option" txid0 |
  NoLock key txid0 | NOK key txid0 | Commit key txid0 | Abort key txid0 |
  User_Commit cl_id | TM_Commit cl_id sqn view "'v fingerpr"| TM_Abort cl_id | TM_ReadyC cl_id |
  TM_ReadyA cl_id | Skip2

definition km_t'_unchanged where
  "km_t'_unchanged t k svrss svrss' \<equiv> (\<forall>t'. t' \<noteq> t \<longrightarrow>
     svr_key_fp (svrss' k) t' = svr_key_fp (svrss k) t' \<and>
     km_state (svrss' k) t' = km_state (svrss k) t')"

definition other_insts_unchanged where
  "other_insts_unchanged k svrss svrss' \<equiv> (\<forall>k'. k' \<noteq> k \<longrightarrow> svrss' k' = svrss k')"

definition tm_km_k'_t'_unchanged where
  "tm_km_k'_t'_unchanged k s s' t \<equiv> cls s' = cls s \<and>
    other_insts_unchanged k (svrs s) (svrs s') \<and> km_t'_unchanged t k (svrs s) (svrs s')"

definition km_tm_cl'_unchanged where
  "km_tm_cl'_unchanged cl s s' \<equiv> svrs s' = svrs s \<and> other_insts_unchanged cl (cls s) (cls s')"

lemmas km_unchanged_defs = tm_km_k'_t'_unchanged_def other_insts_unchanged_def km_t'_unchanged_def
lemmas tm_unchanged_defs = km_tm_cl'_unchanged_def other_insts_unchanged_def
lemmas unchanged_defs = km_unchanged_defs km_tm_cl'_unchanged_def

definition tid_match :: "'v global_state \<Rightarrow> txid0 \<Rightarrow> bool" where
  "tid_match s t \<equiv> cl_sn (cls s (get_cl_txn t)) = get_sn_txn t"

abbreviation km_state_trans where
  "km_state_trans s k s' t from_stat to_stat \<equiv>
      km_state (svrs s k) t = from_stat
    \<and> svr_vl (svrs s' k) = svr_vl (svrs s k)
    \<and> svr_key_fp (svrs s' k) = svr_key_fp (svrs s k)
    \<and> km_state (svrs s' k) t = to_stat
    \<and> tm_km_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

definition prepare where
  "prepare s k s' t \<equiv>
    tm_state (cls s (get_cl_txn t)) = tm_prepared
    \<and> km_state_trans s k s' t working prepared"

definition acquire_rd_lock where \<comment>\<open>Read Lock acquired\<close>
  "acquire_rd_lock s k v s' t \<equiv>
    tm_state (cls s (get_cl_txn t)) = tm_prepared
    \<and> (\<forall>t'. km_state (svrs s k) t' \<noteq> write_lock)
    \<and> km_state (svrs s k) t = prepared
    \<and> svr_vl (svrs s' k) = svr_vl (svrs s k)
    \<and> v = v_value (last_version (svr_vl (svrs s k)) (full_view (svr_vl (svrs s k))))
    \<and> svr_key_fp (svrs s' k) t W = None
    \<and> svr_key_fp (svrs s' k) t R = Some v
    \<and> km_state (svrs s' k) t = read_lock
    \<and> tm_km_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

definition acquire_wr_lock where \<comment>\<open>Write Lock acquired\<close>
  "acquire_wr_lock s k v ov s' t \<equiv>
    tm_state (cls s (get_cl_txn t)) = tm_prepared
    \<and> (\<forall>t'. km_state (svrs s k) t' \<notin> {write_lock, read_lock})
    \<and> km_state (svrs s k) t = prepared
    \<and> svr_vl (svrs s' k) = svr_vl (svrs s k)
    \<and> (ov = None \<or>
       ov = Some (v_value (last_version (svr_vl (svrs s k)) (full_view (svr_vl (svrs s k))))))
    \<and> svr_key_fp (svrs s' k) t W = Some v
    \<and> svr_key_fp (svrs s' k) t R = ov
    \<and> km_state (svrs s' k) t = write_lock
    \<and> tm_km_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

definition acquire_no_lock where \<comment>\<open>No Lock needed\<close>
  "acquire_no_lock s k s' t \<equiv>
    tm_state (cls s (get_cl_txn t)) = tm_prepared
    \<and> svr_key_fp (svrs s' k) t W = None
    \<and> svr_key_fp (svrs s' k) t R = None
    \<and> km_state_trans s k s' t prepared no_lock"

definition nok where \<comment>\<open>Lock not available\<close>
  "nok s k s' t \<equiv>
    tm_state (cls s (get_cl_txn t)) = tm_prepared
    \<and> km_state_trans s k s' t prepared notokay"

definition commit where
  "commit s k s' t \<equiv>
    km_state (svrs s k) t \<in> {read_lock, write_lock, no_lock}
    \<and> tm_state (cls s (get_cl_txn t)) = tm_committed
    \<and> svr_vl (svrs s' k) =
        update_kv_key t (svr_key_fp (svrs s k) t) (full_view (svr_vl (svrs s k))) (svr_vl (svrs s k))
    \<and> km_state (svrs s' k) t = committed
    \<and> svr_key_fp (svrs s' k) t = svr_key_fp (svrs s k) t
    \<and> tm_km_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

definition abort where \<comment>\<open>Locks released (aborted)\<close>
  "abort s k s' t \<equiv>
    km_state (svrs s k) t \<in> {read_lock, write_lock, no_lock, notokay}
    \<and> tm_state (cls s (get_cl_txn t)) = tm_aborted
    \<and> svr_vl (svrs s' k) = svr_vl (svrs s k)
    \<and> km_state (svrs s' k) t = aborted
    \<and> svr_key_fp (svrs s' k) t = svr_key_fp (svrs s k) t
    \<and> tm_km_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

definition user_commit where
  "user_commit s s' cl \<equiv>
    tm_state (cls s cl) = tm_init
    \<and> tm_state (cls s' cl) = tm_prepared
    \<and> cl_sn (cls s' cl) = cl_sn (cls s cl)
    \<and> cl_view (cls s' cl) = cl_view (cls s cl)
    \<and> km_tm_cl'_unchanged cl s s'"

definition tm_commit where
  "tm_commit s s' cl sn u'' F \<equiv>
    tm_state (cls s cl) = tm_prepared
    \<and> (\<forall>k. km_state (svrs s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock})
    \<and> tm_state (cls s' cl) = tm_committed
    \<and> cl_sn (cls s' cl) = cl_sn (cls s cl)
    \<and> cl_view (cls s' cl) = (\<lambda>k. full_view (kvs_of_gs s' k))
    \<and> km_tm_cl'_unchanged cl s s'
    \<and> sn = cl_sn (cls s cl)
    \<and> u'' = (\<lambda>k. full_view (kvs_of_gs s k))
    \<and> F = (\<lambda>k. svr_key_fp (svrs s k) (get_txn_cl cl s))"

definition tm_abort where
  "tm_abort s s' cl \<equiv>
    tm_state (cls s cl) = tm_prepared
    \<and> (\<exists>k. km_state (svrs s k) (get_txn_cl cl s) = notokay)
    \<and> (\<forall>k. km_state (svrs s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock, notokay})
    \<and> tm_state (cls s' cl) = tm_aborted
    \<and> cl_sn (cls s' cl) = cl_sn (cls s cl)
    \<and> cl_view (cls s' cl) = cl_view (cls s cl)
    \<and> km_tm_cl'_unchanged cl s s'"

definition tm_ready_c where
  "tm_ready_c s s' cl \<equiv>
    tm_state (cls s cl) = tm_committed
    \<and> (\<forall>k. km_state (svrs s k) (get_txn_cl cl s) = committed)
    \<and> tm_state (cls s' cl) = tm_init
    \<and> cl_sn (cls s' cl) = Suc (cl_sn (cls s cl))
    \<and> cl_view (cls s' cl) = cl_view (cls s cl)
    \<and> km_tm_cl'_unchanged cl s s'"

definition tm_ready_a where
  "tm_ready_a s s' cl \<equiv>
    tm_state (cls s cl) = tm_aborted
    \<and> (\<forall>k. km_state (svrs s k) (get_txn_cl cl s) = aborted)
    \<and> tm_state (cls s' cl) = tm_init
    \<and> cl_sn (cls s' cl) = Suc (cl_sn (cls s cl))
    \<and> cl_view (cls s' cl) = cl_view (cls s cl)
    \<and> km_tm_cl'_unchanged cl s s'"


subsubsection \<open>The Event System\<close>

definition gs_init :: "'v global_state" where
  "gs_init \<equiv> \<lparr> 
    cls = (\<lambda>cl. \<lparr> tm_state = tm_init,
                 cl_sn = 0,
                 cl_view = view_init \<rparr>),
    svrs = (\<lambda>k. \<lparr> km_state = (\<lambda>t. working),
                 svr_vl = [version_init],
                 svr_key_fp = (\<lambda>t. Map.empty)\<rparr>)
  \<rparr>"

fun gs_trans :: "'v global_state \<Rightarrow> 'v ev \<Rightarrow> 'v global_state \<Rightarrow> bool" where
  "gs_trans s (Prepare k t)         s' \<longleftrightarrow> prepare s k s' t" |
  "gs_trans s (RLock k v t)         s' \<longleftrightarrow> acquire_rd_lock s k v s' t" |
  "gs_trans s (WLock k v ov t)      s' \<longleftrightarrow> acquire_wr_lock s k v ov s' t" |
  "gs_trans s (NoLock k t)          s' \<longleftrightarrow> acquire_no_lock s k s' t" |
  "gs_trans s (NOK k t)             s' \<longleftrightarrow> nok s k s' t" |
  "gs_trans s (Commit k t)          s' \<longleftrightarrow> commit s k s' t" |
  "gs_trans s (Abort k t)           s' \<longleftrightarrow> abort s k s' t" |
  "gs_trans s (User_Commit cl)      s' \<longleftrightarrow> user_commit s s' cl" |
  "gs_trans s (TM_Commit cl sn u F) s' \<longleftrightarrow> tm_commit s s' cl sn u F" |
  "gs_trans s (TM_Abort cl)         s' \<longleftrightarrow> tm_abort s s' cl" |
  "gs_trans s (TM_ReadyC cl)        s' \<longleftrightarrow> tm_ready_c s s' cl" |
  "gs_trans s (TM_ReadyA cl)        s' \<longleftrightarrow> tm_ready_a s s' cl" |
  "gs_trans s Skip2                 s' \<longleftrightarrow> s' = s"

definition tps :: "('v ev, 'v global_state) ES" where
  "tps \<equiv> \<lparr>
    init = (=) gs_init,
    trans = gs_trans
  \<rparr>"

lemmas tps_trans_defs = prepare_def acquire_rd_lock_def acquire_wr_lock_def
                        acquire_no_lock_def nok_def commit_def abort_def
                        user_commit_def tm_commit_def tm_abort_def tm_ready_c_def tm_ready_a_def

lemmas tps_defs = tps_def gs_init_def

lemma tps_trans [simp]: "trans tps = gs_trans" by (simp add: tps_def)

subsubsection \<open>Mediator function\<close>

fun med :: "'v ev \<Rightarrow> 'v label" where
  "med (TM_Commit cl sn u F) = ET cl sn u F" |
  "med _ = ETSkip"

end