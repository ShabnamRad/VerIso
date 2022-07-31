section \<open>Two Phase Commit (2PC) with Two Phase Locking (2PL)\<close>

theory Serializable_2PC_2PL
  imports Execution_Tests
begin

subsection \<open>2PC Event system\<close>

subsubsection \<open>State\<close>

datatype status_km = working | prepared | read_lock | write_lock | no_lock | notokay | committed | aborted
datatype status_tm = tm_init | tm_prepared | tm_committed | tm_aborted

\<comment>\<open>Transaction Manager (TM)\<close>
record tm_state =
  tm_status :: status_tm
  tm_sn :: nat
  tm_view :: view

\<comment>\<open>Key Manager (KM)\<close>
record 'v km_state =
  km_vl :: "'v v_list"
  km_key_fp :: "txid0 \<Rightarrow> 'v key_fp"
  km_status :: "txid0 \<Rightarrow> status_km"

\<comment>\<open>System Global State: TM and KMs\<close>
record 'v global_state =
  tm :: "cl_id \<Rightarrow> tm_state"
  kms :: "key \<Rightarrow> 'v km_state"

\<comment> \<open>Translator functions\<close>
fun get_cl_txn :: "txid0 \<Rightarrow> cl_id" where
  "get_cl_txn (Tn_cl sn cl) = cl"

fun get_sn_txn :: "txid0 \<Rightarrow> nat" where
  "get_sn_txn (Tn_cl sn cl) = sn"

fun get_txn_cl :: "cl_id \<Rightarrow> 'v global_state \<Rightarrow> txid0" where
  "get_txn_cl cl s = Tn_cl (tm_sn (tm s cl)) cl"

subsubsection \<open>Simulation function\<close>
abbreviation eligible_reads :: "(txid0 \<Rightarrow> status_tm) \<Rightarrow> (txid0 \<Rightarrow> status_km) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> txid0 \<Rightarrow> bool" where
  "eligible_reads tStm tSkm tFk t \<equiv>
    tStm t = tm_committed \<and> tSkm t \<in> {read_lock, write_lock} \<and> tFk t R \<noteq> None"

definition update_kv_reads_all_txn :: "(txid0 \<Rightarrow> status_tm) \<Rightarrow> (txid0 \<Rightarrow> status_km) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_reads_all_txn tStm tSkm tFk vl =
    (let uk = full_view vl; lv = last_version vl uk in
     vl [Max uk := lv \<lparr>v_readerset := (v_readerset lv) \<union> {t. eligible_reads tStm tSkm tFk t}\<rparr>])"

abbreviation the_wr_t :: "(txid0 \<Rightarrow> status_km) \<Rightarrow> txid0" where
  "the_wr_t tSkm \<equiv> (THE t. tSkm t = write_lock)"

definition update_kv_writes_all_txn :: "(txid0 \<Rightarrow> status_tm) \<Rightarrow> (txid0 \<Rightarrow> status_km) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_writes_all_txn tStm tSkm tFk vl =
    (if (\<exists>t. tStm t = tm_committed \<and> tSkm t = write_lock) then
        update_kv_writes (the_wr_t tSkm) (tFk (the_wr_t tSkm)) vl
     else vl)"

definition update_kv_all_txn :: "(txid0 \<Rightarrow> status_tm) \<Rightarrow> (txid0 \<Rightarrow> status_km) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_all_txn tStm tSkm tFk =
    (update_kv_writes_all_txn tStm tSkm tFk) o (update_kv_reads_all_txn tStm tSkm tFk)"

definition kvs_of_gs :: "'v global_state \<Rightarrow> 'v kv_store" where
  "kvs_of_gs gs = (\<lambda>k.
   update_kv_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
    (km_status (kms gs k)) (km_key_fp (kms gs k)) (km_vl (kms gs k)))"

definition views_of_gs :: "'v global_state \<Rightarrow> (cl_id \<Rightarrow> view)" where
  "views_of_gs gs = (\<lambda>cl. tm_view (tm gs cl))"
  (*"views_of_gs gs = (\<lambda>cl k. full_view (kvs_of_gs gs k))"*)

definition sim :: "'v global_state \<Rightarrow> 'v config" where
  "sim gs = (kvs_of_gs gs, views_of_gs gs)"

lemmas update_kv_all_defs = update_kv_reads_all_txn_def update_kv_writes_all_txn_def update_kv_all_txn_def
lemmas sim_defs = sim_def kvs_of_gs_def views_of_gs_def


subsubsection \<open>Events\<close>

datatype 'v ev = Write2 key txid0 'v | Read2 key txid0 'v | Prepare key txid0 | RLock key txid0 |
  WLock key txid0 | NoLock key txid0 | NOK key txid0 | Commit key txid0 | Abort key txid0 |
  User_Commit cl_id | TM_Commit cl_id sqn view "'v fingerpr"| TM_Abort cl_id | TM_ReadyC cl_id |
  TM_ReadyA cl_id | Skip2

definition km_t'_unchanged where
  "km_t'_unchanged t k kmss kmss' \<equiv> (\<forall>t'. t' \<noteq> t \<longrightarrow>
     km_key_fp (kmss' k) t' = km_key_fp (kmss k) t' \<and>
     km_status (kmss' k) t' = km_status (kmss k) t')"

definition other_insts_unchanged where
  "other_insts_unchanged k kmss kmss' \<equiv> (\<forall>k'. k' \<noteq> k \<longrightarrow> kmss' k' = kmss k')"

definition tm_km_k'_t'_unchanged where
  "tm_km_k'_t'_unchanged k s s' t \<equiv> tm s' = tm s \<and>
    other_insts_unchanged k (kms s) (kms s') \<and> km_t'_unchanged t k (kms s) (kms s')"

definition km_tm_cl'_unchanged where
  "km_tm_cl'_unchanged cl s s' \<equiv> kms s' = kms s \<and> other_insts_unchanged cl (tm s) (tm s')"

lemmas km_unchanged_defs = tm_km_k'_t'_unchanged_def other_insts_unchanged_def km_t'_unchanged_def
lemmas tm_unchanged_defs = km_tm_cl'_unchanged_def other_insts_unchanged_def
lemmas unchanged_defs = km_unchanged_defs km_tm_cl'_unchanged_def

definition tid_match :: "'v global_state \<Rightarrow> txid0 \<Rightarrow> bool" where
  "tid_match s t \<equiv> tm_sn (tm s (get_cl_txn t)) = get_sn_txn t"

abbreviation km_status_trans where
  "km_status_trans s k s' t from_stat to_stat \<equiv>
      km_status (kms s k) t = from_stat
    \<and> km_vl (kms s' k) = km_vl (kms s k)
    \<and> km_key_fp (kms s' k) = km_key_fp (kms s k)
    \<and> km_status (kms s' k) t = to_stat
    \<and> tm_km_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

definition write2 where
  "write2 s k v s' t \<equiv>
    km_status (kms s k) t = working
    \<and> tid_match s t
    \<and> km_key_fp (kms s' k) t = update_key_fp (km_key_fp (kms s k) t) W v
    \<and> km_status (kms s' k) t = working
    \<and> km_vl (kms s' k) = km_vl (kms s k)
    \<and> tm_km_k'_t'_unchanged k s s' t"

definition read2 where
  "read2 s k v s' t  \<equiv>
    km_status (kms s k) t = working
    \<and> tid_match s t
    \<and> km_key_fp (kms s' k) t = update_key_fp (km_key_fp (kms s k) t) R v
    \<and> km_status (kms s' k) t = working
    \<and> km_vl (kms s' k) = km_vl (kms s k)
    \<and> tm_km_k'_t'_unchanged k s s' t"

definition prepare where
  "prepare s k s' t \<equiv>
    tm_status (tm s (get_cl_txn t)) = tm_prepared
    \<and> km_status_trans s k s' t working prepared"

definition acquire_rd_lock where \<comment>\<open>Read Lock acquired\<close>
  "acquire_rd_lock s k s' t \<equiv>
    tm_status (tm s (get_cl_txn t)) = tm_prepared
    \<and> km_key_fp (kms s k) t W = None
    \<and> km_key_fp (kms s k) t R \<noteq> None
    \<and> (\<forall>t'. km_status (kms s k) t' \<noteq> write_lock)
    \<and> km_status_trans s k s' t prepared read_lock"

definition acquire_wr_lock where \<comment>\<open>Write Lock acquired\<close>
  "acquire_wr_lock s k s' t \<equiv>
    tm_status (tm s (get_cl_txn t)) = tm_prepared
    \<and> km_key_fp (kms s k) t W \<noteq> None
    \<and> (\<forall>t'. km_status (kms s k) t' \<notin> {write_lock, read_lock})
    \<and> km_status_trans s k s' t prepared write_lock"

definition acquire_no_lock where \<comment>\<open>No Lock needed\<close>
  "acquire_no_lock s k s' t \<equiv>
    tm_status (tm s (get_cl_txn t)) = tm_prepared
    \<and> km_key_fp (kms s k) t W = None
    \<and> km_key_fp (kms s k) t R = None
    \<and> km_status_trans s k s' t prepared no_lock"

definition nok where \<comment>\<open>Lock not available\<close>
  "nok s k s' t \<equiv>
    tm_status (tm s (get_cl_txn t)) = tm_prepared
    \<and> ((km_key_fp (kms s k) t R \<noteq> None
        \<and> (\<exists>t'. km_status (kms s k) t' = write_lock))
       \<or> (km_key_fp (kms s k) t W \<noteq> None
        \<and> (\<exists>t'. km_status (kms s k) t' \<in> {write_lock, read_lock})))
    \<and> km_status_trans s k s' t prepared notokay"

definition commit where
  "commit s k s' t \<equiv>
    km_status (kms s k) t \<in> {read_lock, write_lock, no_lock}
    \<and> tm_status (tm s (get_cl_txn t)) = tm_committed
    \<and> km_vl (kms s' k) =
        update_kv_key t (km_key_fp (kms s k) t) (full_view (km_vl (kms s k))) (km_vl (kms s k))
    \<and> km_status (kms s' k) t = committed
    \<and> km_key_fp (kms s' k) t = km_key_fp (kms s k) t
    \<and> tm_km_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

definition abort where \<comment>\<open>Locks released (aborted)\<close>
  "abort s k s' t \<equiv>
    km_status (kms s k) t \<in> {read_lock, write_lock, no_lock, notokay}
    \<and> tm_status (tm s (get_cl_txn t)) = tm_aborted
    \<and> km_vl (kms s' k) = km_vl (kms s k)
    \<and> km_status (kms s' k) t = aborted
    \<and> km_key_fp (kms s' k) t = km_key_fp (kms s k) t
    \<and> tm_km_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

definition user_commit where
  "user_commit s s' cl \<equiv>
    tm_status (tm s cl) = tm_init
    \<and> tm_status (tm s' cl) = tm_prepared
    \<and> tm_sn (tm s' cl) = tm_sn (tm s cl)
    \<and> tm_view (tm s' cl) = tm_view (tm s cl)
    \<and> km_tm_cl'_unchanged cl s s'"

definition tm_commit where
  "tm_commit s s' cl sn u F \<equiv>
    tm_status (tm s cl) = tm_prepared
    \<and> (\<forall>k. km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock})
    \<and> tm_status (tm s' cl) = tm_committed
    \<and> tm_sn (tm s' cl) = tm_sn (tm s cl)
    \<and> tm_view (tm s' cl) = (\<lambda>k. full_view (kvs_of_gs s k))
    \<and> km_tm_cl'_unchanged cl s s'
    \<and> sn = tm_sn (tm s cl)
    \<and> u = (\<lambda>k. full_view (km_vl (kms s k)))
    \<and> F = (\<lambda>k. km_key_fp (kms s k) (get_txn_cl cl s))"

definition tm_abort where
  "tm_abort s s' cl \<equiv>
    (tm_status (tm s cl) = tm_prepared
     \<and> (\<exists>k. km_status (kms s k) (get_txn_cl cl s) = notokay)
     \<and> (\<forall>k. km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock, notokay}))
    \<and> tm_status (tm s' cl) = tm_aborted
    \<and> tm_sn (tm s' cl) = tm_sn (tm s cl)
    \<and> tm_view (tm s' cl) = tm_view (tm s cl)
    \<and> km_tm_cl'_unchanged cl s s'"

definition tm_ready_c where
  "tm_ready_c s s' cl \<equiv>
    tm_status (tm s cl) = tm_committed
    \<and> (\<forall>k. km_status (kms s k) (get_txn_cl cl s) = committed)
    \<and> tm_status (tm s' cl) = tm_init
    \<and> tm_sn (tm s' cl) = Suc (tm_sn (tm s cl))
    \<and> tm_view (tm s' cl) = tm_view (tm s cl)
    \<and> km_tm_cl'_unchanged cl s s'"

definition tm_ready_a where
  "tm_ready_a s s' cl \<equiv>
    tm_status (tm s cl) = tm_aborted
    \<and> (\<forall>k. km_status (kms s k) (get_txn_cl cl s) = aborted)
    \<and> tm_status (tm s' cl) = tm_init
    \<and> tm_sn (tm s' cl) = Suc (tm_sn (tm s cl))
    \<and> tm_view (tm s' cl) = tm_view (tm s cl)
    \<and> km_tm_cl'_unchanged cl s s'"

text\<open>The Event System\<close>
definition gs_init :: "'v global_state" where
  "gs_init \<equiv> \<lparr> 
    tm = (\<lambda>cl. \<lparr> tm_status = tm_init,
                 tm_sn = 0,
                 tm_view = view_init \<rparr>),
    kms = (\<lambda>k. \<lparr> km_vl = [version_init],
                 km_key_fp = (\<lambda>t. Map.empty), 
                 km_status = (\<lambda>t. working)\<rparr>)
  \<rparr>"

fun gs_trans :: "'v global_state \<Rightarrow> 'v ev \<Rightarrow> 'v global_state \<Rightarrow> bool" where
  "gs_trans s (Write2 k t v)        s' \<longleftrightarrow> write2 s k v s' t" |
  "gs_trans s (Read2 k t v)         s' \<longleftrightarrow> read2 s k v s' t" |
  "gs_trans s (Prepare k t)         s' \<longleftrightarrow> prepare s k s' t" |
  "gs_trans s (RLock k t)           s' \<longleftrightarrow> acquire_rd_lock s k s' t" |
  "gs_trans s (WLock k t)           s' \<longleftrightarrow> acquire_wr_lock s k s' t" |
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

lemmas tps_trans_defs = write2_def read2_def prepare_def acquire_rd_lock_def acquire_wr_lock_def
                        acquire_no_lock_def nok_def commit_def abort_def
                        user_commit_def tm_commit_def tm_abort_def tm_ready_c_def tm_ready_a_def

lemmas tps_defs = tps_def gs_init_def

lemma tps_trans [simp]: "trans tps = gs_trans" by (simp add: tps_def)

subsection \<open>Invariants\<close>

text\<open>Invariant about future and past transactions kms\<close>
definition TIDFutureKm where
  "TIDFutureKm s cl \<longleftrightarrow> (\<forall>n k. n > tm_sn (tm s cl) \<longrightarrow> km_status (kms s k) (Tn_cl n cl) = working)"

lemmas TIDFutureKmI = TIDFutureKm_def[THEN iffD2, rule_format]
lemmas TIDFutureKmE[elim] = TIDFutureKm_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidfuturekm [simp, dest]: "reach tps s \<Longrightarrow> TIDFutureKm s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: TIDFutureKm_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Write2 x11 x12 x13)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs TIDFutureKm_def, fastforce)
  next
    case (Read2 x21 x22 x23)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs TIDFutureKm_def, fastforce)
  next
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TIDFutureKm_def)
      subgoal for n k apply (cases "(Tn_cl n x) = x32"; cases "k = x31", auto) done.
  next
    case (RLock x41 x42)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDFutureKm_def)
      by (metis status_km.distinct(1))
  next
    case (WLock x51 x52)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDFutureKm_def)
      by (metis status_km.distinct(1))
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDFutureKm_def)
      by (metis status_km.distinct(1))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDFutureKm_def)
      by (metis status_km.distinct(1))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDFutureKm_def)
      apply (metis status_km.distinct(3))
      apply (metis status_km.distinct(5))
      by (metis status_km.distinct(7))
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDFutureKm_def)
      apply (metis status_km.distinct(3))
      apply (metis status_km.distinct(5))
      apply (metis status_km.distinct(7))
      by (metis status_km.distinct(9))
  next
    case (User_Commit x10)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs tm_unchanged_defs TIDFutureKm_def, metis)
  next
    case (TM_Commit x111 x112 x113 x114)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs tm_unchanged_defs TIDFutureKm_def, metis)
  next
    case (TM_Abort x12a)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs tm_unchanged_defs TIDFutureKm_def, metis)
  next
    case (TM_ReadyC x13a)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs TIDFutureKm_def)
      by (metis Suc_lessD)
  next
    case (TM_ReadyA x14)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs TIDFutureKm_def)
      by (metis Suc_lessD)
  qed simp
qed

definition TIDPastKm where
  "TIDPastKm s cl \<longleftrightarrow> (\<forall>n k. n < tm_sn (tm s cl) \<longrightarrow> km_status (kms s k) (Tn_cl n cl) \<in> {committed, aborted})"

lemmas TIDPastKmI = TIDPastKm_def[THEN iffD2, rule_format]
lemmas TIDPastKmE[elim] = TIDPastKm_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidpastkm [simp, dest]: "reach tps s \<Longrightarrow> TIDPastKm s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: TIDPastKm_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Write2 x11 x12 x13)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs TIDPastKm_def, metis)
  next
    case (Read2 x21 x22 x23)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs TIDPastKm_def, metis)
  next
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDPastKm_def)
      by (metis status_km.distinct(11) status_km.distinct(13))
  next
    case (RLock x41 x42)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDPastKm_def)
      by (metis status_km.distinct(23) status_km.distinct(25))
  next
    case (WLock x51 x52)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDPastKm_def)
      by (metis status_km.distinct(23) status_km.distinct(25))
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDPastKm_def)
      by (metis status_km.distinct(23) status_km.distinct(25))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDPastKm_def)
      by (metis status_km.distinct(23) status_km.distinct(25))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs TIDPastKm_def, fastforce+)
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs TIDPastKm_def, fastforce+)
  next
    case (User_Commit x10)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs tm_unchanged_defs TIDPastKm_def, metis)
  next
    case (TM_Commit x111 x112 x113 x114)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs tm_unchanged_defs TIDPastKm_def, metis)
  next
    case (TM_Abort x12a)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs tm_unchanged_defs TIDPastKm_def, metis)
  next
    case (TM_ReadyC x13a)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs tm_unchanged_defs TIDPastKm_def, metis less_antisym)
  next
    case (TM_ReadyA x14)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs tm_unchanged_defs TIDPastKm_def, metis less_antisym)
  qed auto
qed

text\<open>Lock Invariants\<close>
definition RLockInv where
  "RLockInv s k \<longleftrightarrow> (\<forall>t. km_status (kms s k) t = read_lock \<longrightarrow> (\<forall>t. km_status (kms s k) t \<noteq> write_lock))"

lemmas RLockInvI = RLockInv_def[THEN iffD2, rule_format]
lemmas RLockInvE[elim] = RLockInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_rlock [simp, intro]: "reach tps s \<Longrightarrow> RLockInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: RLockInv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Write2 x1 x2 x3)
    then show ?case using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs RLockInv_def, metis)
  next
    case (Read2 x1 x2 x3)
    then show ?case using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs RLockInv_def, metis)
  next
    case (Prepare x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockInv_def)
      by (metis status_km.distinct(15) status_km.distinct(17))
  next
    case (RLock x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockInv_def)
      by (metis status_km.distinct(27))
  next
    case (WLock x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockInv_def)
      by (metis status_km.distinct(27))
  next
    case (NoLock x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockInv_def)
      by (metis status_km.distinct(30) status_km.distinct(38))
  next
    case (NOK x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockInv_def)
      apply (metis status_km.distinct(31))
      apply (metis status_km.distinct(31))
      by (metis status_km.distinct(40))
  next
    case (Commit x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockInv_def)
      apply (metis status_km.distinct(42))
      apply (metis status_km.distinct(34))
      by (metis status_km.distinct(34) status_km.distinct(42))
  next
    case (Abort x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockInv_def)
      apply (metis status_km.distinct(44))
      apply (metis status_km.distinct(36))
      apply (metis status_km.distinct(36) status_km.distinct(44))
      by (metis status_km.distinct(35) status_km.distinct(44))
  qed (auto simp add: tps_trans_defs tm_unchanged_defs RLockInv_def)
qed

definition WLockInv where
  "WLockInv s k \<longleftrightarrow> (\<forall>t. km_status (kms s k) t \<noteq> write_lock) \<or> (\<exists>! t. km_status (kms s k) t = write_lock)"

lemmas WLockInvI = WLockInv_def[THEN iffD2, rule_format]
lemmas WLockInvE[elim] = WLockInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_wlock [simp, intro]: "reach tps s \<Longrightarrow> WLockInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: WLockInv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (cases e)
    case (Write2 x11 x12 x13)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs WLockInv_def, metis+)
  next
    case (Read2 x21 x22 x23)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs WLockInv_def, metis+)
  next
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockInv_def)
      by (metis status_km.distinct(17))
  next
    case (RLock x41 x42)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockInv_def)
      by (metis status_km.distinct(27))
  next
    case (WLock x51 x52)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockInv_def)
      by metis
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockInv_def)
      by (metis status_km.distinct(37))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockInv_def)
      by (metis status_km.distinct(39))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockInv_def)
      by (metis status_km.distinct(41))+
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockInv_def)
      by (metis status_km.distinct(43))+
  qed (auto simp add: tps_trans_defs tm_unchanged_defs WLockInv_def)
qed

subsection \<open>Refinement from ET_ES to tps\<close>

subsubsection \<open>Mediator function\<close>

fun med :: "'v ev \<Rightarrow> 'v label" where
  "med (TM_Commit cl sn u F) = ET cl sn u F" |
  "med _ = ETSkip"
  

text\<open>Invariants and lemmas for the refinement proof\<close>

\<comment> \<open>Invariants for fingerprint, knowing the lock (km status)\<close>

definition RLockFpInv where
  "RLockFpInv s k \<longleftrightarrow> (\<forall>t. km_status (kms s k) t = read_lock \<longrightarrow>
    km_key_fp (kms s k) t W = None \<and>
    km_key_fp (kms s k) t R \<noteq> None)"

lemmas RLockFpInvI = RLockFpInv_def[THEN iffD2, rule_format]
lemmas RLockFpInvE[elim] = RLockFpInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_rlockfp [simp, intro]: "reach tps s \<Longrightarrow> RLockFpInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: RLockFpInv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Write2 x11 x12 x13)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpInv_def)
      by (metis status_km.distinct(3))+
  next
    case (Read2 x21 x22 x23)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpInv_def)
      by (metis status_km.distinct(3))+
  next
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpInv_def)
      by (metis status_km.distinct(15))+
  next
    case (RLock x41 x42)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpInv_def)
      by metis+
  next
    case (WLock x51 x52)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpInv_def)
      by (metis status_km.distinct(27))+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpInv_def)
      by (metis status_km.distinct(29))+
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpInv_def)
      apply (metis status_km.distinct(31), metis)
      by (metis status_km.distinct(31))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpInv_def)
      by (metis status_km.distinct(33))+
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpInv_def)
      by (metis status_km.distinct(35))+
  qed (auto simp add: tps_trans_defs tm_unchanged_defs RLockFpInv_def)
qed

definition WLockFpInv where
  "WLockFpInv s k \<longleftrightarrow> (\<forall>t. km_status (kms s k) t = write_lock \<longrightarrow> km_key_fp (kms s k) t W \<noteq> None)"

lemmas WLockFpInvI = WLockFpInv_def[THEN iffD2, rule_format]
lemmas WLockFpInvE[elim] = WLockFpInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_wlockfp [simp, intro]: "reach tps s \<Longrightarrow> WLockFpInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: WLockFpInv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Write2 x11 x12 x13)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpInv_def)
      by (metis status_km.distinct(5))
  next
    case (Read2 x21 x22 x23)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpInv_def)
      by (metis status_km.distinct(5))
  next
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpInv_def)
      by (metis status_km.distinct(17))
  next
    case (RLock x41 x42)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpInv_def)
      by (metis status_km.distinct(27))
  next
    case (WLock x51 x52)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpInv_def)
      by metis
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpInv_def)
      by (metis status_km.distinct(37))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpInv_def)
      by (metis status_km.distinct(39), metis+)
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpInv_def)
      by (metis status_km.distinct(41))+
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpInv_def)
      by (metis status_km.distinct(43))+
  qed (auto simp add: tps_trans_defs tm_unchanged_defs WLockFpInv_def)
qed

definition NoLockFpInv where
  "NoLockFpInv s k \<longleftrightarrow> (\<forall>t. km_status (kms s k) t = no_lock \<longrightarrow>
    km_key_fp (kms s k) t W = None \<and>
    km_key_fp (kms s k) t R = None)"

lemmas NoLockFpInvI = NoLockFpInv_def[THEN iffD2, rule_format]
lemmas NoLockFpInvE[elim] = NoLockFpInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_nolockfp [simp, intro]: "reach tps s \<Longrightarrow> NoLockFpInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: NoLockFpInv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Write2 x11 x12 x13)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs NoLockFpInv_def)
      by (metis status_km.distinct(7))+
  next
    case (Read2 x21 x22 x23)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs NoLockFpInv_def)
      by (metis status_km.distinct(7))+
  next
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs NoLockFpInv_def)
      by (metis status_km.distinct(19))+
  next
    case (RLock x41 x42)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs NoLockFpInv_def)
      by (metis status_km.distinct(29))+
  next
    case (WLock x51 x52)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs NoLockFpInv_def)
      by (metis status_km.distinct(37))+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs NoLockFpInv_def)
      by metis+
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs NoLockFpInv_def)
      by (metis status_km.distinct(45))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs NoLockFpInv_def)
      by (metis status_km.distinct(47))+
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs NoLockFpInv_def)
      by (metis status_km.distinct(49))+
  qed (auto simp add: tps_trans_defs tm_unchanged_defs NoLockFpInv_def)
qed

subsubsection \<open>Simulation function lemmas\<close>
lemma the_wr_tI:
  assumes "km_status (kms s k) t = write_lock"
      and "WLockInv s k"
  shows "the_wr_t (km_status (kms s k)) = t"
  using assms
  by blast

lemma update_kv_reads_all_txn_length [simp]:
  "length (update_kv_reads_all_txn tStm tSkm tFk vl) = length vl"
  by (auto simp add: update_kv_reads_all_txn_def Let_def)

(*lemma update_kv_writes_all_txn_none_length:
  assumes "\<forall>t. tStm t \<noteq> tm_committed \<or> tSkm t \<noteq> write_lock"
  shows "length (update_kv_writes_all_txn tStm tSkm tFk vl) = length vl"
  using assms
  by (auto simp add: update_kv_writes_all_txn_def)

lemma update_kv_writes_all_txn_some_length:
  assumes "\<forall>k. WLockFpInv s k" and "\<exists>t. tStm t = tm_committed \<and> tSkm t = write_lock"
  shows "length (update_kv_writes_all_txn tStm tSkm tFk vl) = Suc (length vl)"
  using assms
  apply (auto simp add: update_kv_writes_all_txn_def WLockFpInv_def)*)

lemma update_kv_writes_all_txn_length:
  "length (update_kv_writes_all_txn tStm tSkm tFk vl) = Suc (length vl) \<or>
  length (update_kv_writes_all_txn tStm tSkm tFk vl) = length vl"
  by (auto simp add: update_kv_writes_all_txn_def update_kv_writes_length)

lemma update_kv_writes_all_txn_length_increasing [simp]:
  "length vl \<le> length (update_kv_writes_all_txn tStm tSkm tFk vl)"
  by (metis Suc_n_not_le_n nat_le_linear update_kv_writes_all_txn_length)

lemma update_kv_writes_all_txn_on_diff_len:
  assumes "length vl1 \<le> length vl2"
  shows "length (update_kv_writes_all_txn tStm tSkm tFk vl1) \<le>
         length (update_kv_writes_all_txn tStm tSkm tFk vl2)"
  using assms
  by (auto simp add: update_kv_writes_all_txn_def update_kv_writes_on_diff_len)

lemma update_kv_all_txn_length [simp]:
  "length vl \<le> length (update_kv_all_txn tStm tSkm tFk vl)"
  by (auto simp add: update_kv_all_defs update_kv_writes_def Let_def split: option.split)

\<comment> \<open>lemmas for unchanged elements in kms\<close>

lemma [simp]: "last_version [v] {..<Suc 0} = v"
  by (auto simp add: last_version_def lessThan_def)

lemma [simp]: "Max {..<Suc n} = n" apply (simp add: lessThan_Suc)
  by (meson Max_insert2 finite_lessThan lessThan_iff less_imp_le_nat)

lemma km_vl_eq_all_k [dest!]:
  assumes "km_vl (kms s' k) = km_vl (kms s k)"
    and "other_insts_unchanged k (kms s) (kms s')"
  shows "\<forall>k. km_vl (kms s' k) = km_vl (kms s k)"
  using assms by (auto simp add: other_insts_unchanged_def)

lemma km_key_fp_eq_all_k: 
  assumes "km_key_fp (kms s' k) t = km_key_fp (kms s k) t"
    and " \<forall>k'. k' \<noteq> k \<longrightarrow> kms s' k' = kms s k'"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> km_key_fp (kms s' k) t' = km_key_fp (kms s k) t'"
  shows "\<forall>k. km_key_fp (kms s' k) = km_key_fp (kms s k)"
  apply (auto simp add: fun_eq_iff) using assms
  subgoal for k' t' by (cases "k' = k"; cases "t' = t"; simp).

lemma km_status_eq_all_k: 
  assumes "km_status (kms s' k) t = km_status (kms s k) t"
    and " \<forall>k'. k' \<noteq> k \<longrightarrow> kms s' k' = kms s k'"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> km_status (kms s' k) t' = km_status (kms s k) t'"
  shows "\<forall>k. km_status (kms s' k) = km_status (kms s k)"
  apply (auto simp add: fun_eq_iff) using assms
  subgoal for k' t' by (cases "k' = k"; cases "t' = t"; simp).

lemma other_sn_idle:  
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "get_cl_txn t = cl" and "get_sn_txn t \<noteq> tm_sn (tm s cl)"
  shows "\<forall>k. km_status (kms s k) t \<in> {working, committed, aborted}"
  using assms
  apply (auto simp add: TIDFutureKm_def TIDPastKm_def)
  apply (cases "get_sn_txn t > tm_sn (tm s cl)")
  apply (metis get_cl_txn.simps get_sn_txn.elims)
  by (metis get_cl_txn.elims get_sn_txn.simps nat_neq_iff)

\<comment> \<open>Lemmas for the cases where kvs_of_gs doesn't change\<close>
lemma eligible_reads_km_inv:
  assumes "\<forall>k. RLockInv s k" and "gs_trans s e s'"
    and "(km_status (kms s k) t \<notin> {write_lock, read_lock} \<and>
          km_status (kms s' k) t = km_status (kms s k) t) \<or>
          tm_status (tm s (get_cl_txn t)) \<noteq> tm_committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "\<forall>k t.
  eligible_reads (\<lambda>t. tm_status (tm s' (get_cl_txn t))) (km_status (kms s' k)) (km_key_fp (kms s' k)) t =
  eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k)) (km_key_fp (kms s k)) t"
  apply(rule allI)+ subgoal for k t' using assms
    apply (cases "t' = t"; simp add: km_unchanged_defs)
    by metis+.

lemma none_eligible: "vl[Max (full_view vl) := last_version vl (full_view vl)
  \<lparr>v_readerset := v_readerset (last_version vl (full_view vl)) \<union> {}\<rparr>] = vl"
  by (simp add: last_version_def)

lemma eligible_reads_read_lock_inv:
  assumes "\<forall>k. RLockFpInv s k"
    and "gs_trans s e s'"
    and "km_status (kms s k) t = read_lock"
    and "km_status (kms s' k) t = committed"
    and "tm_status (tm s (get_cl_txn t)) = tm_committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "{t. eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
            (km_key_fp (kms s k)) t} =
          insert t {t. eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s' k))
            (km_key_fp (kms s k)) t}"
  using assms by (auto simp add: km_unchanged_defs)

lemma eligible_reads_write_lock_s_the_t:
  assumes "\<forall>k. RLockInv s k" and "\<forall>k. WLockInv s k"
    and "gs_trans s e s'"
    and "km_status (kms s k) t = write_lock"
    and "km_status (kms s' k) t = committed"
    and "tm_status (tm s (get_cl_txn t)) = tm_committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "{t. eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
            (km_key_fp (kms s k)) t} =
         (case (km_key_fp (kms s k) t R) of None \<Rightarrow> {} | Some y \<Rightarrow> {t})"
  using assms
  apply (auto intro: Collect_empty_eq split: option.split)
  subgoal for t' by (cases "t' = t"; auto simp add: RLockInv_def WLockInv_def km_unchanged_defs)
  by blast

lemma update_kv_reads_commit_w_s_inv:
  assumes "\<forall>k. RLockInv s k" and "\<forall>k. WLockInv s k"
    and "gs_trans s e s'"
    and "km_status (kms s k) t = write_lock"
    and "km_status (kms s' k) t = committed"
    and "tm_status (tm s (get_cl_txn t)) = tm_committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "\<forall>vl. update_kv_reads_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) 
                (km_status (kms s k)) (km_key_fp (kms s k)) vl =
        (case (km_key_fp (kms s k) t R) of None \<Rightarrow> vl | Some y \<Rightarrow> 
          vl[Max (full_view vl) := last_version vl (full_view vl)
                \<lparr>v_readerset := v_readerset (last_version vl (full_view vl)) \<union> {t}\<rparr>])"
  apply (rule allI) subgoal for vl
  using assms eligible_reads_write_lock_s_the_t[of s]
  unfolding update_kv_reads_all_txn_def Let_def last_version_def
  by (cases "km_key_fp (kms s k) t R"; auto).

lemma eligible_reads_write_lock_s'_empty:
  assumes "\<forall>k. RLockInv s k" and "\<forall>k. WLockInv s k"
    and "gs_trans s e s'"
    and "km_status (kms s k) t = write_lock"
    and "km_status (kms s' k) t = committed"
    and "tm_status (tm s (get_cl_txn t)) = tm_committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "{t. eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s' k))
            (km_key_fp (kms s k)) t} = {}"
  using assms
  apply (auto intro: Collect_empty_eq)
  subgoal for t' by (cases "t' = t"; auto simp add: RLockInv_def WLockInv_def km_unchanged_defs)
  subgoal for t' by (cases "t' = t"; auto simp add: RLockInv_def WLockInv_def km_unchanged_defs).

lemma update_kv_reads_commit_w_s'_inv:
  assumes "\<forall>k. RLockInv s k" and "\<forall>k. WLockInv s k"
    and "gs_trans s e s'"
    and "km_status (kms s k) t = write_lock"
    and "km_status (kms s' k) t = committed"
    and "tm_status (tm s (get_cl_txn t)) = tm_committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "\<forall>vl. update_kv_reads_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) 
                (km_status (kms s' k)) (km_key_fp (kms s k)) vl = vl"
  apply (rule allI) subgoal for vl
  using assms eligible_reads_write_lock_s'_empty[of s] none_eligible[of vl]
  unfolding update_kv_reads_all_txn_def
  by presburger.

lemma eligible_reads_no_lock_inv:
  assumes "gs_trans s e s'"
    and "km_status (kms s k) t = no_lock"
    and "km_status (kms s' k) t = committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "\<forall>t.
  eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s' k)) (km_key_fp (kms s k)) t =
  eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k)) (km_key_fp (kms s k)) t"
  using assms apply (auto simp add: km_unchanged_defs)
  apply (metis status_km.distinct(33))
  apply (metis status_km.distinct(41))
  apply (metis status_km.distinct(29))
  by (metis status_km.distinct(37))

lemma update_kv_writes_km_fp_inv:
  assumes "\<forall>k. WLockInv s k" and "gs_trans s e s'"
    and "(\<forall>t. km_status (kms s k) t \<noteq> write_lock) \<or> 
              km_status (kms s' k) t \<noteq> write_lock"
    and "tm_status (tm s (get_cl_txn t)) \<noteq> tm_committed"
    and "tm_km_k'_t'_unchanged k s s' t"
    and "km_key_fp (kms s' k) = km_key_fp (kms s k)"
  shows "\<forall>k vl. update_kv_writes_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t)))
                (km_status (kms s' k)) (km_key_fp (kms s' k)) vl =
               update_kv_writes_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t)))
                (km_status (kms s k)) (km_key_fp (kms s k)) vl"
  apply (rule allI)+ using assms apply (auto simp add: update_kv_writes_all_txn_def)
  subgoal for k' vl t' t''
    by (cases "k' = k"; cases "t' = t"; cases "t'' = t"; simp add: km_unchanged_defs)
  subgoal for k' vl t' by (cases "k' = k"; cases "t' = t"; simp add: km_unchanged_defs)
  subgoal for k' vl t' by (cases "k' = k"; cases "t' = t"; auto simp add: km_unchanged_defs)
  subgoal for k' vl t' t''
    apply (cases "k' = k"; cases "t' = t"; cases "t'' = t"; simp add: km_unchanged_defs the_wr_tI)
    by (smt (verit) WLockInv_def the_equality)
  subgoal for k' vl t' by (cases "k' = k"; cases "t' = t"; simp add: km_unchanged_defs the_wr_tI)
  subgoal for k' vl t' by (cases "k' = k"; cases "t' = t"; auto simp add: km_unchanged_defs the_wr_tI).

lemma update_kv_writes_km_status_inv:
  assumes "\<forall>k. WLockInv s k" and "gs_trans s e s'"
    and "km_status (kms s k) t \<notin> {write_lock, read_lock}"
    and "km_status (kms s' k) t = km_status (kms s k) t"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "\<forall>k vl. update_kv_writes_all_txn tStm (km_status (kms s' k)) (km_key_fp (kms s' k)) vl =
                update_kv_writes_all_txn tStm (km_status (kms s k)) (km_key_fp (kms s k)) vl"
  apply (rule allI)+ using assms apply (auto simp add: update_kv_writes_all_txn_def)
  subgoal for k' vl t' t''
    apply (cases "k' = k"; cases "t' = t"; cases "t'' = t"; simp add: km_unchanged_defs the_wr_tI)
    by (smt (verit) WLockInv_def theI_unique)
  subgoal for k' vl t' by (cases "k' = k"; cases "t' = t"; simp add: km_unchanged_defs the_wr_tI)
  subgoal for k' vl t' by (cases "k' = k"; cases "t' = t"; auto simp add: km_unchanged_defs the_wr_tI).

lemma update_kv_writes_commit_r_inv:
  assumes "\<forall>k. RLockInv s k" and "gs_trans s e s'"
    and "km_status (kms s k) t = read_lock"
    and "km_status (kms s' k) t = committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "\<forall>vl. update_kv_writes_all_txn tStm (km_status (kms s' k)) (km_key_fp (kms s k)) vl = 
              update_kv_writes_all_txn tStm (km_status (kms s k)) (km_key_fp (kms s k)) vl"
  using assms apply (auto simp add: update_kv_writes_all_txn_def km_unchanged_defs)
  by (metis status_km.distinct(41))

lemma update_kv_writes_commit_w_s_inv:
  assumes "\<forall>k. WLockInv s k" and "gs_trans s e s'"
    and "km_status (kms s k) t = write_lock"
    and "km_status (kms s' k) t = committed"
    and "tm_status (tm s (get_cl_txn t)) = tm_committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "\<forall>vl. update_kv_writes_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
                (km_key_fp (kms s k)) vl = update_kv_writes t (km_key_fp (kms s k) t) vl"
  using assms apply (auto simp add: update_kv_writes_all_txn_def)
  using the_wr_tI by blast

lemma update_kv_writes_commit_w_s'_inv:
  assumes "\<forall>k. WLockInv s k" and "gs_trans s e s'"
    and "km_status (kms s k) t = write_lock"
    and "km_status (kms s' k) t = committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "\<forall>vl. update_kv_writes_all_txn tStm (km_status (kms s' k)) (km_key_fp (kms s k)) vl = vl"
  using assms apply (auto simp add: update_kv_writes_all_txn_def km_unchanged_defs)
  by (metis status_km.distinct(41) the_wr_tI)

lemma update_kv_writes_commit_n_inv:
  assumes "\<forall>k. WLockInv s k" and "\<forall>k. NoLockFpInv s k" and "gs_trans s e s'"
    and "km_status (kms s k) t = no_lock"
    and "km_status (kms s' k) t = committed"
    and "tm_status (tm s (get_cl_txn t)) = tm_committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "\<forall>vl. update_kv_writes_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s' k))
                (km_key_fp (kms s k)) vl =
              update_kv_writes_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
                (km_key_fp (kms s k)) vl"
  apply (rule allI)+ using assms apply (auto simp add: update_kv_writes_all_txn_def)
  subgoal for vl t' t''
    apply (cases "t' = t"; cases "t'' = t"; simp add: km_unchanged_defs the_wr_tI)
    by (smt (verit) WLockInv_def status_km.distinct(41) theI_unique)
  subgoal for vl t' by (cases "t' = t"; simp add: km_unchanged_defs the_wr_tI)
  subgoal for vl t' by (cases "t' = t"; auto simp add: km_unchanged_defs the_wr_tI).

lemma kvs_of_gs_km_fp_inv:
  assumes "gs_trans s e s'" and "\<forall>k. WLockInv s k" and "\<forall>k. RLockInv s k"
    and "(\<forall>t. km_status (kms s k) t \<noteq> write_lock) \<or> 
              km_status (kms s' k) t \<noteq> write_lock"
    and "tm_status (tm s (get_cl_txn t)) \<noteq> tm_committed"
    and "km_key_fp (kms s' k) t = km_key_fp (kms s k) t"
    and "\<forall>k. km_vl (kms s' k) = km_vl (kms s k)"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "kvs_of_gs s' = kvs_of_gs s"
  using assms apply (auto simp add: kvs_of_gs_def) apply (rule ext)
  subgoal for k' by (cases "k' = k";
    auto simp add: update_kv_all_txn_def update_kv_reads_all_txn_def dest!:eligible_reads_km_inv;
    auto dest!: update_kv_writes_km_fp_inv; auto simp add: km_unchanged_defs)
  apply (rule ext)
  subgoal for k' by (cases "k' = k";
    auto simp add: update_kv_all_txn_def update_kv_reads_all_txn_def dest!:eligible_reads_km_inv;
    auto dest!: update_kv_writes_km_fp_inv; auto simp add: km_unchanged_defs).

lemma kvs_of_gs_km_status_inv:
  assumes "gs_trans s e s'" and "\<forall>k. WLockInv s k" and "\<forall>k. RLockInv s k"
    and "km_status (kms s k) t \<notin> {write_lock, read_lock}"
    and "km_status (kms s' k) t = km_status (kms s k) t"
    and "\<forall>k. km_vl (kms s' k) = km_vl (kms s k)"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "kvs_of_gs s' = kvs_of_gs s"
  using assms apply (auto simp add: kvs_of_gs_def) apply (rule ext)
  subgoal for k' by (cases "k' = k";
    auto simp add: update_kv_all_txn_def update_kv_reads_all_txn_def dest!:eligible_reads_km_inv;
    auto dest!: update_kv_writes_km_status_inv; auto simp add: km_unchanged_defs).

lemma reads_writes_tm_inv:
  assumes "\<forall>cl. TIDFutureKm s cl \<and> TIDPastKm s cl"
    and "gs_trans s e s'"
    and "tm_status (tm s cl) \<noteq> tm_committed \<or>
         (\<forall>k. km_status (kms s k) (Tn_cl (tm_sn (tm s cl)) cl) = committed \<and>
          tm_sn (tm s' cl) = Suc (tm_sn (tm s cl)))"
    and "tm_status (tm s' cl) \<noteq> tm_committed"
    and "km_tm_cl'_unchanged cl s s'"
  shows "\<forall>k t.
  eligible_reads (\<lambda>t. tm_status (tm s' (get_cl_txn t))) (km_status (kms s k)) (km_key_fp (kms s k)) t =
  eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k)) (km_key_fp (kms s k)) t \<and>
  (\<forall>k vl. update_kv_writes_all_txn (\<lambda>t. tm_status (tm s' (get_cl_txn t)))
                (km_status (kms s k)) (km_key_fp (kms s k)) vl =
               update_kv_writes_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t)))
                (km_status (kms s k)) (km_key_fp (kms s k)) vl)"
  using assms apply (auto simp add: update_kv_writes_all_txn_def tm_unchanged_defs)
  subgoal for k t
    apply (cases "get_cl_txn t = cl"; cases "get_sn_txn t = tm_sn (tm s cl)";
            simp add: tm_unchanged_defs)
    apply (metis get_cl_txn.elims get_sn_txn.simps status_km.distinct(33))
    by (metis empty_iff insert_iff other_sn_idle status_km.distinct(3)
        status_km.distinct(33) status_km.distinct(35))
  subgoal for k t
    apply (cases "get_cl_txn t = cl"; cases "get_sn_txn t = tm_sn (tm s cl)";
            simp add: tm_unchanged_defs)
    apply (metis get_cl_txn.elims get_sn_txn.simps status_km.distinct(41))
    by (metis empty_iff insert_iff other_sn_idle status_km.distinct(41)
        status_km.distinct(43) status_km.distinct(5))
  subgoal for k vl t
    apply (cases "get_cl_txn t = cl"; cases "get_sn_txn t = tm_sn (tm s cl)"; simp)
    apply (metis get_cl_txn.elims get_sn_txn.simps status_km.distinct(41))
    by (metis ex_in_conv insertE other_sn_idle status_km.distinct(41)
        status_km.distinct(43) status_km.distinct(5)).

lemma kvs_of_gs_tm_inv:
  assumes "\<forall>cl. TIDFutureKm s cl \<and> TIDPastKm s cl"
    and "gs_trans s e s'"
    and "tm_status (tm s cl) \<noteq> tm_committed \<or>
         (\<forall>k. km_status (kms s k) (Tn_cl (tm_sn (tm s cl)) cl) = committed \<and>
         tm_sn (tm s' cl) = Suc (tm_sn (tm s cl)))"
    and "tm_status (tm s' cl) \<noteq> tm_committed"
    and "km_tm_cl'_unchanged cl s s'"
  shows "kvs_of_gs s' = kvs_of_gs s"
  using assms
  apply (auto simp add: kvs_of_gs_def)
  by (rule ext; auto simp add: update_kv_all_txn_def update_kv_reads_all_txn_def;
          auto dest!: reads_writes_tm_inv; auto simp add: tm_unchanged_defs)+

lemma kvs_of_gs_length_increasing:
  assumes "gs_trans s e s'"
    and "tm_status (tm s cl) = tm_prepared"
    and "\<forall>k. km_status (kms s k) (Tn_cl (tm_sn (tm s cl)) cl) = read_lock \<or>
             km_status (kms s k) (Tn_cl (tm_sn (tm s cl)) cl) = write_lock \<or>
             km_status (kms s k) (Tn_cl (tm_sn (tm s cl)) cl) = no_lock"
    and "tm_status (tm s' cl) = tm_committed"
    and "km_tm_cl'_unchanged cl s s'"
  shows "\<forall>k. length (kvs_of_gs s k) \<le> length (kvs_of_gs s' k)"
  using assms
  apply (auto simp add: tps_trans_defs kvs_of_gs_def tm_unchanged_defs update_kv_all_txn_def
      update_kv_writes_all_txn_def update_kv_writes_on_diff_len)
  by (metis (no_types, lifting) update_kv_reads_all_txn_length update_kv_writes_length_increasing)

definition KVSNonEmp where
  "KVSNonEmp s \<longleftrightarrow> (\<forall>k. km_vl (kms s k) \<noteq> [])"

lemmas KVSNonEmpI = KVSNonEmp_def[THEN iffD2, rule_format]
lemmas KVSNonEmpE[elim] = KVSNonEmp_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_non_emp [simp, intro]: "reach tps s \<Longrightarrow> KVSNonEmp s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: KVSNonEmp_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Commit x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: KVSNonEmp_def tps_trans_defs km_unchanged_defs)
      apply (metis bot_nat_0.not_eq_extremum full_view_def full_view_update_kv_writes
            length_0_conv lessThan_iff update_kv_writes_key_decides_length)
      apply (metis length_greater_0_conv update_kv_writes_key_decides_length
            update_kv_writes_length zero_less_Suc)
      by (metis length_greater_0_conv update_kv_writes_key_decides_length
            update_kv_writes_length zero_less_Suc)
  qed (auto simp add: KVSNonEmp_def tps_trans_defs unchanged_defs)
qed

(*definition KVSExpands where
  "KVSExpands s \<longleftrightarrow> (\<forall>k. (km_vl (kms s k)) \<sqsubseteq>\<sqsubseteq> (kvs_of_gs s k))"

lemmas KVSExpandsI = KVSExpands_def[THEN iffD2, rule_format]
lemmas KVSExpandsE[elim] = KVSExpands_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_len [simp, intro]: "reach tps s \<Longrightarrow> KVSExpands s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: vlist_order_def KVSExpands_def tps_defs kvs_of_gs_def update_kv_all_defs
        Let_def full_view_def update_kv_al)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Write2 x1 x2 x3)
    hence "\<forall>k. km_vl (kms s' k) = km_vl (kms s k)" using km_vl_eq_all_k by blast
    then show ?case using Write2 reach_trans
      apply (auto simp add: vlist_order_def KVSExpands_def kvs_of_gs_def update_kv_all_txn_length full_view_def) sorry*)

definition KVSLen where
  "KVSLen s cl \<longleftrightarrow> (\<forall>k. length (km_vl (kms s k)) \<le> length (kvs_of_gs s k))"

lemmas KVSLenI = KVSLen_def[THEN iffD2, rule_format]
lemmas KVSLenE[elim] = KVSLen_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_len [simp, intro]: "reach tps s \<Longrightarrow> KVSLen s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: KVSLen_def tps_defs kvs_of_gs_def update_kv_all_defs Let_def)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: KVSLen_def kvs_of_gs_def)
qed



lemma kvs_of_gs_inv:
  assumes "gs_trans s e s'"
    and inv: "\<forall>cl k. TIDFutureKm s cl \<and> TIDPastKm s cl \<and> RLockInv s k \<and> WLockInv s k \<and>
                      RLockFpInv s k \<and> NoLockFpInv s k \<and> KVSNonEmp s"
    and "\<forall>cl sn u F. e \<noteq> TM_Commit cl sn u F"
  shows "kvs_of_gs s' = kvs_of_gs s"
  using assms
  proof (induction e)
    case (Write2 x1 x2 x3)
    then show ?case using assms kvs_of_gs_km_status_inv[of s e s' x1 x2]
      by (auto simp add: tps_trans_defs km_unchanged_defs)
  next
    case (Read2 x1 x2 x3)
    then show ?case using assms kvs_of_gs_km_status_inv[of s e s' x1 x2]
      by (auto simp add: tps_trans_defs km_unchanged_defs)
  next
    case (Prepare x1 x2)
    then show ?case using assms kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: tps_trans_defs km_unchanged_defs)
  next
    case (RLock x1 x2)
    then show ?case using assms kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: tps_trans_defs km_unchanged_defs)
  next
    case (WLock x1 x2)
    then show ?case using assms kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: tps_trans_defs km_unchanged_defs)
  next
    case (NoLock x1 x2)
    then show ?case using assms kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: tps_trans_defs km_unchanged_defs)
  next
    case (NOK x1 x2)
    then show ?case using assms kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: tps_trans_defs km_unchanged_defs)
  next
    case (Commit x1 x2)
    hence u: "kvs_of_gs s' x1 = kvs_of_gs s x1" using assms
      apply (auto simp add: kvs_of_gs_def commit_def)
      subgoal
        using eligible_reads_read_lock_inv[of s]
              update_kv_writes_commit_r_inv[of s]
        by (auto simp add: update_kv_all_txn_def update_kv_reads_all_txn_def Let_def
            RLockFpInv_def KVSNonEmp_def km_unchanged_defs update_kv_key_ro_set_v_readerset
            dest!: km_key_fp_eq_all_k)
      subgoal
        using update_kv_reads_commit_w_s_inv[of s]
              update_kv_reads_commit_w_s'_inv[of s]
              update_kv_writes_commit_w_s_inv[of s]
              update_kv_writes_commit_w_s'_inv[of s]
        by (auto simp add: update_kv_all_txn_def update_kv_key_def update_kv_reads_defs
            km_unchanged_defs dest!: km_key_fp_eq_all_k split: option.split)
      subgoal
        using eligible_reads_no_lock_inv[of s]
        using update_kv_writes_commit_n_inv[of s]
        by (auto simp add: update_kv_all_txn_def update_kv_reads_all_txn_def
            NoLockFpInv_def km_unchanged_defs dest!: km_key_fp_eq_all_k) done
    hence "\<forall>k. k \<noteq> x1 \<longrightarrow> kvs_of_gs s' k = kvs_of_gs s k" using Commit assms
      by (auto simp add: commit_def km_unchanged_defs kvs_of_gs_def)
    then show ?case using u by auto
  next
    case (Abort x1 x2)
    then show ?case using assms kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: tps_trans_defs km_unchanged_defs)
  next
    case (User_Commit x)
    then show ?case using assms kvs_of_gs_tm_inv[of s e s' x]
     by (auto simp add: tps_trans_defs tm_unchanged_defs)
  next
    case (TM_Abort x)
    then show ?case using assms kvs_of_gs_tm_inv[of s e s' x]
     by (auto simp add: tps_trans_defs tm_unchanged_defs)
  next
    case (TM_ReadyC x)
    then show ?case using assms kvs_of_gs_tm_inv[of s e s' x]
     by (auto simp add: tps_trans_defs tm_unchanged_defs)
  next
    case (TM_ReadyA x)
    then show ?case using assms kvs_of_gs_tm_inv[of s e s' x]
     by (auto simp add: tps_trans_defs tm_unchanged_defs)
 qed auto

lemma list_nth_in_set [simp]:
  assumes "i \<in> full_view vl"
  shows "vl ! i \<in> set vl"
  using assms
  by (auto simp add: full_view_def)

lemma in_set_before_update [simp]:
  assumes "a \<noteq> vl [i := x] ! i"
    and "a \<in> set (vl [i := x])"
  shows "a \<in> set vl"
  using assms
  apply (simp add: in_set_conv_nth)
  apply (rule bexE [where A="{..<length vl}" and P="\<lambda>i'. vl[i := x] ! i' = a"])
   apply auto subgoal for i' i'' by (cases "i' = i"; auto).

lemma in_set_after_update [simp]:
  assumes "a \<noteq> vl ! i"
    and "a \<in> set vl"
  shows "a \<in> set (vl [i := x])"
  using assms
  apply (simp add: in_set_conv_nth)
  apply (rule bexE [where A="{..<length vl}" and P="\<lambda>i'. vl ! i' = a"])
   apply auto subgoal for i' i'' by (cases "i' = i"; auto).

lemma in_set_update [simp]:
  assumes "i \<in> full_view vl"
  shows "x \<in> set (vl [i := x])"
  using assms
  by (metis (full_types) full_view_nth_list_update_eq list_nth_in_set
      list_update_beyond set_update_memI verit_comp_simplify1(3))

lemma update_kv_writes_all_txn_v_readerset_set [simp]:
  "\<Union> (v_readerset ` set (update_kv_writes_all_txn tStm tSkm tFk vl)) = \<Union> (v_readerset ` set vl)"
  by (auto simp add: update_kv_writes_all_txn_def update_kv_writes_def split: option.split)

lemma the_update:
  assumes "a \<in> set (vl [i := x])"
    and "a \<notin> set vl"
  shows "x = a"
  using assms
  apply (simp add: in_set_conv_nth)
  by (metis nth_list_update_eq nth_list_update_neq)

lemma bla:
  assumes "i \<in> full_view vl" 
    and "a \<in> set (vl [i := (vl ! i) \<lparr> v_readerset := v_readerset (vl ! i) \<union> el \<rparr>])"
    and "x \<in> v_readerset a"
    and "\<forall>ver \<in> set vl. x \<notin> v_readerset ver"
  shows "x \<in> el"
  using assms
  apply (simp add: in_set_conv_nth)
  apply (rule bexE [where A="{..<length vl}" 
        and P="\<lambda>i'. vl[i := (vl ! i)\<lparr>v_readerset := v_readerset (vl ! i) \<union> el\<rparr>] ! i' = a"])
   apply auto subgoal for i' i'' by (cases "i' = i"; simp).

lemma set_update_kv_all_v_readerset:
  assumes "vl \<noteq> []"
  shows "\<Union> (v_readerset ` set (update_kv_all_txn tStm tSkm tFk vl)) =
   \<Union> (v_readerset ` set vl) \<union> {t. eligible_reads tStm tSkm tFk t}"
  using assms
  apply (auto simp add: update_kv_all_txn_def update_kv_reads_all_txn_def Let_def last_version_def)
  subgoal for x ver apply (cases "ver \<in> set vl")
    apply blast using bla[of "Max (full_view vl)" vl ver "{t. eligible_reads tStm tSkm tFk t}" x] assms
    sorry.

lemma update_kv_reads_all_txn_v_writer_set [simp]:
  "vl \<noteq> [] \<Longrightarrow> v_writer ` set (update_kv_reads_all_txn tStm tSkm tFk vl) = v_writer ` set vl"
  apply (auto simp add: image_iff update_kv_reads_all_txn_def Let_def last_version_def)
   apply (metis (no_types, lifting) full_view_nth_list_update_eq in_set_before_update list_nth_in_set
      max_in_full_view version.select_convs(2) version.surjective version.update_convs(3))
  by (metis (no_types, lifting) in_set_after_update in_set_update max_in_full_view
      version.select_convs(2) version.surjective version.update_convs(3))

lemma set_update_kv_all_v_writer:
  "vl \<noteq> [] \<Longrightarrow> v_writer ` set (update_kv_all_txn tStm tSkm tFk vl) =
  (if (\<exists>t. tStm t = tm_committed \<and> tSkm t = write_lock \<and> tFk (the_wr_t tSkm) W \<noteq> None) then
     insert (Tn (the_wr_t tSkm)) (v_writer ` set vl) else v_writer ` set vl)"
  by (auto simp add: update_kv_all_txn_def update_kv_writes_all_txn_def update_kv_writes_def
      split: option.split)

lemma the_wr_t_fp:
  assumes "\<forall>k. WLockInv s k"
    and "\<forall>k. WLockFpInv s k"
    and "km_status (kms s k) t = write_lock"
  shows "km_key_fp (kms s k) (the_wr_t (km_status (kms s k))) W \<noteq> None"
  using assms by (auto simp add: WLockInv_def WLockFpInv_def the_wr_tI)

lemma set_update_kv_all_v_writer':
  assumes "gs_trans s e s'"
    and "KVSNonEmp s"
    and "\<forall>k. WLockInv s k"
    and "\<forall>k. WLockFpInv s k"
  shows "v_writer ` set (update_kv_all_txn tStm (km_status (kms s k)) (km_key_fp (kms s k))
                    (km_vl (kms s k))) =
  (if (\<exists>t. tStm t = tm_committed \<and> km_status (kms s k) t = write_lock) then
     insert (Tn (the_wr_t (km_status (kms s k)))) (v_writer ` set (km_vl (kms s k)))
   else v_writer ` set (km_vl (kms s k)))"
  using assms set_update_kv_all_v_writer[of "(km_vl (kms s k))"]
  by (auto simp add: update_kv_all_txn_def update_kv_writes_all_txn_def update_kv_writes_def
      the_wr_t_fp KVSNonEmp_def split: option.split)

lemma read_only_update [simp]:
  assumes "\<forall>t. km_status (kms s k) t \<noteq> write_lock"
  shows "update_kv_all_txn tStm (km_status (kms s k)) tFk vl =
         update_kv_reads_all_txn tStm (km_status (kms s k)) tFk vl"
  using assms
  by (auto simp add: update_kv_all_txn_def update_kv_writes_all_txn_def)

lemma get_sqns_other_cl_inv:
  assumes "gs_trans s e s'"
    and "KVSNonEmp s"
    and "\<forall>k. WLockInv s k"
    and "\<forall>k. WLockFpInv s k"
    and "tm s' cl = tm s cl"
    and "kms s' = kms s"
  shows "get_sqns (kvs_of_gs s') cl = get_sqns (kvs_of_gs s) cl"
  using assms apply (auto simp add: fresh_txid_defs kvs_of_gs_def)
  subgoal for x k ver apply (auto simp add: set_update_kv_all_v_writer')
    apply (rule exI[where x=k]) apply auto
    apply (smt (verit, del_insts) image_eqI insert_iff set_update_kv_all_v_writer' the_equality the_wr_tI)
    by (smt (verit) get_cl_txn.simps imageI insertE set_update_kv_all_v_writer' the_wr_tI txid.inject)
  subgoal for x k ver apply (auto simp add: set_update_kv_all_v_writer') sorry
  subgoal for x k ver apply (auto simp add: set_update_kv_all_v_writer')
    apply (rule exI[where x=k]) apply auto
    apply (smt (verit, del_insts) image_eqI insert_iff set_update_kv_all_v_writer' the_equality the_wr_tI)
    by (smt (verit) get_cl_txn.simps imageI insertE set_update_kv_all_v_writer' the_wr_tI txid.inject)
  subgoal for x k ver apply (auto simp add: set_update_kv_all_v_writer') sorry
  done

definition SqnInv where
  "SqnInv s cl \<longleftrightarrow>
    (tm_status (tm s cl) \<noteq> tm_committed \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_gs s) cl. m < tm_sn (tm s cl))) \<and>
    (tm_status (tm s cl) = tm_committed \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_gs s) cl. m \<le> tm_sn (tm s cl)))"

lemmas SqnInvI = SqnInv_def[THEN iffD2, rule_format]
lemmas SqnInvE[elim] = SqnInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_view_wellformed [simp, intro]:
  assumes "reach tps s"
    and inv: "\<forall>cl k. TIDFutureKm s cl \<and> TIDPastKm s cl \<and> RLockInv s k \<and> WLockInv s k \<and>
                      RLockFpInv s k \<and> NoLockFpInv s k \<and> KVSNonEmp s \<and> KVSLen s cl"
  shows "\<forall>cl. SqnInv s cl"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: SqnInv_def tps_defs kvs_of_gs_def fresh_txid_defs update_kv_all_defs
        full_view_def version_init_def)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Write2 x1 x2 x3)
    then show ?case using reach_trans kvs_of_gs_km_status_inv[of s e s' x1 x2]
      by (auto simp add: SqnInv_def tps_trans_defs km_unchanged_defs)
  next
    case (Read2 x1 x2 x3)
    then show ?case using reach_trans kvs_of_gs_km_status_inv[of s e s' x1 x2]
      by (auto simp add: SqnInv_def tps_trans_defs km_unchanged_defs)
  next
    case (Prepare x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: SqnInv_def tps_trans_defs km_unchanged_defs)
  next
    case (RLock x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: SqnInv_def tps_trans_defs km_unchanged_defs)
  next
    case (WLock x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: SqnInv_def tps_trans_defs km_unchanged_defs)
  next
    case (NoLock x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: SqnInv_def tps_trans_defs km_unchanged_defs)
  next
    case (NOK x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: SqnInv_def tps_trans_defs km_unchanged_defs)
  next
    case (Commit x1 x2)
    then show ?case using assms kvs_of_gs_inv[of s "Commit x1 x2" s']
      by (auto simp add: SqnInv_def tps_trans_defs km_unchanged_defs)
  next
    case (Abort x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: SqnInv_def tps_trans_defs km_unchanged_defs)
  next
    case (User_Commit x)
    then show ?case using reach_trans kvs_of_gs_tm_inv[of s e s' x]
      apply (auto simp add: SqnInv_def tps_trans_defs tm_unchanged_defs)
      apply (metis status_tm.distinct(3))
      by (metis status_tm.distinct(7))
  next
    case (TM_Commit x1 x2 x3 x4)
    then show ?case using reach_trans
      apply (auto simp add: SqnInv_def tps_trans_defs tm_unchanged_defs)
      subgoal for cl m apply (cases "cl = x1")
         apply blast
        by (metis get_sqns_other_cl_inv)
      subgoal for cl m apply (cases "cl = x1")
        subgoal sorry
        by (metis get_sqns_other_cl_inv)
      done
  next
    case (TM_Abort x)
    then show ?case using reach_trans kvs_of_gs_tm_inv[of s e s' x]
      apply (auto simp add: SqnInv_def tps_trans_defs tm_unchanged_defs)
      apply (metis status_tm.distinct(7))
      by (metis status_tm.distinct(11))
  next
    case (TM_ReadyC x)
    then show ?case using reach_trans kvs_of_gs_tm_inv[of s e s' x]
      apply (auto simp add: SqnInv_def tps_trans_defs tm_unchanged_defs)
      apply (metis less_Suc_eq_le)
      by (metis status_tm.distinct(3))
  next
    case (TM_ReadyA x)
    then show ?case using reach_trans kvs_of_gs_tm_inv[of s e s' x]
      apply (auto simp add: SqnInv_def tps_trans_defs tm_unchanged_defs)
      apply (metis less_Suc_eq status_tm.distinct(11))
      by (metis status_tm.distinct(3))
  qed simp
qed

definition TMFullView where
  "TMFullView s cl \<longleftrightarrow>
    (tm_status (tm s cl) = tm_committed \<longrightarrow> tm_view (tm s cl) = (\<lambda>k. full_view (kvs_of_gs s k))) \<and>
    (tm_status (tm s cl) \<noteq> tm_committed \<longrightarrow> tm_view (tm s cl) \<sqsubseteq> (\<lambda>k. full_view (km_vl (kms s k))))"

lemmas TMFullViewI = TMFullView_def[THEN iffD2, rule_format]
lemmas TMFullViewE[elim] = TMFullView_def[THEN iffD1, elim_format, rule_format]

lemma reach_tm_full_view [simp, intro]:
  assumes "reach tps s"
    and inv: "\<forall>cl k. TIDFutureKm s cl \<and> TIDPastKm s cl \<and> RLockInv s k \<and> WLockInv s k \<and>
                      RLockFpInv s k \<and> NoLockFpInv s k \<and> KVSNonEmp s \<and> KVSLen s cl"
  shows "\<forall>cl. TMFullView s cl"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: TMFullView_def tps_defs full_view_def view_order_def view_init_def)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Write2 x1 x2 x3)
    then show ?case using reach_trans kvs_of_gs_km_status_inv[of s e s' x1 x2]
      by (auto simp add: TMFullView_def tps_trans_defs km_unchanged_defs)
  next
    case (Read2 x1 x2 x3)
    then show ?case using reach_trans kvs_of_gs_km_status_inv[of s e s' x1 x2]
      by (auto simp add: TMFullView_def tps_trans_defs km_unchanged_defs)
  next
    case (Prepare x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: TMFullView_def tps_trans_defs km_unchanged_defs)
  next
    case (RLock x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: TMFullView_def tps_trans_defs km_unchanged_defs)
  next
    case (WLock x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: TMFullView_def tps_trans_defs km_unchanged_defs)
  next
    case (NoLock x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: TMFullView_def tps_trans_defs km_unchanged_defs)
  next
    case (NOK x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: TMFullView_def tps_trans_defs km_unchanged_defs)
  next
    case (Commit x1 x2)
    then show ?case
      apply (auto simp add: TMFullView_def tps_trans_defs km_unchanged_defs) sorry
  next
    case (Abort x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: TMFullView_def tps_trans_defs km_unchanged_defs)
  next
    case (User_Commit x)
    then show ?case
      apply (auto simp add: TMFullView_def tps_trans_defs tm_unchanged_defs)
       apply (metis (no_types, opaque_lifting) User_Commit.prems(1) ev.distinct(181)
          kvs_of_gs_inv reach_kvs_non_emp reach_nolockfp reach_rlock reach_rlockfp
          reach_tidfuturekm reach_tidpastkm reach_wlock status_tm.distinct(7) tps_trans)
      by (metis status_tm.distinct(3))
  next
    case (TM_Commit x1 x2 x3 x4)
    then show ?case sorry
  next
    case (TM_Abort x)
    then show ?case
      apply (auto simp add: TMFullView_def tps_trans_defs tm_unchanged_defs)
       apply (metis TM_Abort.prems(1) gs_trans.simps(12) kvs_of_gs_tm_inv
          reach_tidfuturekm reach_tidpastkm reach_trans.hyps(2) status_tm.distinct(11)
          status_tm.distinct(7) tm_abort_def tps_trans)
      by (metis status_tm.distinct(7))
  next
    case (TM_ReadyC x)
    then show ?case using reach_trans kvs_of_gs_tm_inv[of s e s' x]
      apply (auto simp add: TMFullView_def tps_trans_defs tm_unchanged_defs)
      apply metis sorry
  next
    case (TM_ReadyA x)
    then show ?case using reach_trans kvs_of_gs_tm_inv[of s e s' x]
      apply (auto simp add: TMFullView_def tps_trans_defs tm_unchanged_defs)
      apply (metis status_tm.distinct(3)) sorry
  qed simp
qed


definition KVSView where
  "KVSView s cl \<longleftrightarrow> view_wellformed (kvs_of_gs s) (tm_view (tm s cl))"

lemmas KVSViewI = KVSView_def[THEN iffD2, rule_format]
lemmas KVSViewE[elim] = KVSView_def[THEN iffD1, elim_format, rule_format]

lemma reach_view_wellformed [simp, intro]:
  assumes "reach tps s"
    and inv: "\<forall>cl k. TIDFutureKm s cl \<and> TIDPastKm s cl \<and> RLockInv s k \<and> WLockInv s k \<and>
                      RLockFpInv s k \<and> NoLockFpInv s k \<and> KVSNonEmp s \<and> KVSLen s cl"
  shows "\<forall>cl. KVSView s cl"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: KVSView_def tps_defs sim_defs update_kv_all_defs Let_def
        view_wellformed_defs full_view_def view_init_def)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Write2 x1 x2 x3)
    then show ?case using reach_trans kvs_of_gs_km_status_inv[of s e s' x1 x2]
      by (auto simp add: KVSView_def tps_trans_defs km_unchanged_defs)
  next
    case (Read2 x1 x2 x3)
    then show ?case using reach_trans kvs_of_gs_km_status_inv[of s e s' x1 x2]
      by (auto simp add: KVSView_def tps_trans_defs km_unchanged_defs)
  next
    case (Prepare x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: KVSView_def tps_trans_defs km_unchanged_defs)
  next
    case (RLock x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: KVSView_def tps_trans_defs km_unchanged_defs)
  next
    case (WLock x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: KVSView_def tps_trans_defs km_unchanged_defs)
  next
    case (NoLock x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: KVSView_def tps_trans_defs km_unchanged_defs)
  next
    case (NOK x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: KVSView_def tps_trans_defs km_unchanged_defs)
  next
    case (Commit x1 x2)
    then show ?case using assms kvs_of_gs_inv[of s "Commit x1 x2" s']
      by (auto simp add: KVSView_def tps_trans_defs km_unchanged_defs)
  next
    case (Abort x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
      by (auto simp add: KVSView_def tps_trans_defs km_unchanged_defs)
  next
    case (User_Commit x)
    then show ?case using reach_trans kvs_of_gs_tm_inv[of s e s' x]
      by (auto simp add: KVSView_def tps_trans_defs tm_unchanged_defs, metis)
  next
    case (TM_Commit x1 x2 x3 x4)
    then show ?case using reach_trans
      apply (auto simp add: KVSView_def tps_trans_defs tm_unchanged_defs)
      subgoal for cl apply (cases "cl = x1")
         apply (auto simp add: view_wellformed_def view_in_range_def view_atomic_def
            key_view_in_range_def KVSNonEmp_def KVSLen_def full_view_def)
           apply (simp add: km_tm_cl'_unchanged_def kvs_of_gs_length_increasing other_insts_unchanged_def)
        sorry done
  next
    case (TM_Abort x)
    then show ?case using reach_trans kvs_of_gs_tm_inv[of s e s' x]
      by (auto simp add: KVSView_def tps_trans_defs tm_unchanged_defs, metis)
  next
    case (TM_ReadyC x)
    then show ?case using reach_trans kvs_of_gs_tm_inv[of s e s' x]
      by (auto simp add: KVSView_def tps_trans_defs tm_unchanged_defs, metis)
  next
    case (TM_ReadyA x)
    then show ?case using reach_trans kvs_of_gs_tm_inv[of s e s' x]
      by (auto simp add: KVSView_def tps_trans_defs tm_unchanged_defs, metis)
  qed simp
qed


definition KVSExpands where
  "KVSExpands s \<longleftrightarrow> (\<lambda>k. km_vl (kms s k)) \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s kvs_of_gs s"

lemmas KVSExpandsI = KVSExpands_def[THEN iffD2, rule_format]
lemmas KVSExpandsE[elim] = KVSExpands_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_expands [simp, intro]:
  assumes "reach tps s"
    and inv: "\<forall>cl k. TIDFutureKm s cl \<and> TIDPastKm s cl \<and> RLockInv s k \<and> WLockInv s k \<and>
                      RLockFpInv s k \<and> NoLockFpInv s k \<and> KVSNonEmp s \<and> KVSLen s cl"
  shows "KVSExpands s"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: KVSExpands_def kvs_expands_def vlist_order_def version_order_def
        tps_defs kvs_of_gs_def update_kv_all_defs Let_def full_view_def)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Write2 x1 x2 x3)
    then show ?case using reach_trans kvs_of_gs_km_status_inv[of s e s' x1 x2]
    by (auto simp add: KVSExpands_def tps_trans_defs km_unchanged_defs)
  next
    case (Read2 x1 x2 x3)
    then show ?case using reach_trans kvs_of_gs_km_status_inv[of s e s' x1 x2]
    by (auto simp add: KVSExpands_def tps_trans_defs km_unchanged_defs)
  next
    case (Prepare x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
    by (auto simp add: KVSExpands_def tps_trans_defs km_unchanged_defs)
  next
    case (RLock x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
    by (auto simp add: KVSExpands_def tps_trans_defs km_unchanged_defs)
  next
    case (WLock x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
    by (auto simp add: KVSExpands_def tps_trans_defs km_unchanged_defs)
  next
    case (NoLock x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
    by (auto simp add: KVSExpands_def tps_trans_defs km_unchanged_defs)
  next
    case (NOK x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
    by (auto simp add: KVSExpands_def tps_trans_defs km_unchanged_defs)
  next
    case (Commit x1 x2)
    then show ?case using assms kvs_of_gs_inv[of s "Commit x1 x2" s']
      apply (auto simp add: KVSExpands_def tps_trans_defs km_unchanged_defs kvs_expands_def)
      subgoal for k apply (cases "k = x1"; simp)
        apply (auto simp add: kvs_of_gs_def vlist_order_def)
           apply (metis update_kv_all_txn_length)
        apply (auto simp add: version_order_def) sorry sorry
  next
    case (Abort x1 x2)
    then show ?case using reach_trans kvs_of_gs_km_fp_inv[of s e s' x1 x2]
    by (auto simp add: KVSExpands_def tps_trans_defs km_unchanged_defs)
  next
    case (User_Commit x)
    then show ?case using reach_trans kvs_of_gs_tm_inv[of s e s' x]
    by (auto simp add: KVSExpands_def tps_trans_defs tm_unchanged_defs)
  next
    case (TM_Commit x1 x2 x3 x4)
    then show ?case sorry
  next
    case (TM_Abort x)
    then show ?case using reach_trans kvs_of_gs_tm_inv[of s e s' x]
    by (auto simp add: KVSExpands_def tps_trans_defs tm_unchanged_defs)
  next
    case (TM_ReadyC x)
    then show ?case using reach_trans kvs_of_gs_tm_inv[of s e s' x]
    by (auto simp add: KVSExpands_def tps_trans_defs tm_unchanged_defs)
  next
    case (TM_ReadyA x)
    then show ?case using reach_trans kvs_of_gs_tm_inv[of s e s' x]
    by (auto simp add: KVSExpands_def tps_trans_defs tm_unchanged_defs)
  qed simp
qed


lemma tps_refines_et_es: "tps \<sqsubseteq>\<^sub>med ET_SER.ET_ES"
proof (intro simulate_ES_fun_with_invariant[where I="\<lambda>s. \<forall>cl k. TIDFutureKm s cl \<and> TIDPastKm s cl \<and>
   RLockInv s k \<and> WLockInv s k \<and> RLockFpInv s k \<and> WLockFpInv s k \<and> NoLockFpInv s k \<and> KVSNonEmp s \<and>
   KVSLen s k \<and> KVSView s cl"])
  fix gs0 :: "'v global_state"
  assume p: "init tps gs0"
  then show "init ET_SER.ET_ES (sim gs0)" using p
    by (auto simp add: ET_SER.ET_ES_defs tps_defs sim_defs update_kv_all_defs last_version_def
        full_view_def kvs_init_def v_list_init_def lessThan_Suc)
next
  fix gs a and gs' :: "'v global_state"
  assume p: "tps: gs\<midarrow>a\<rightarrow> gs'"
     and inv: "\<forall>cl k. TIDFutureKm gs cl \<and> TIDPastKm gs cl \<and> RLockInv gs k \<and> WLockInv gs k \<and>
                      RLockFpInv gs k \<and> WLockFpInv gs k \<and> NoLockFpInv gs k \<and> KVSNonEmp gs \<and>
                      KVSLen gs k \<and> KVSView gs cl"
  then show "ET_SER.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  proof (induction a)
    case (Write2 x11 x12 x13)
    then show ?case using p inv kvs_of_gs_km_status_inv[of gs a gs' x11 x12]
      by (auto simp add: write2_def km_unchanged_defs; simp add: sim_defs update_kv_all_defs)
  next
    case (Read2 x21 x22 x23)
    then show ?case using p inv kvs_of_gs_km_status_inv[of gs a gs' x21 x22]
      by (auto simp add: read2_def km_unchanged_defs; simp add: sim_defs update_kv_all_defs)
  next
    case (Prepare x31 x32)
    then show ?case using p inv kvs_of_gs_km_fp_inv[of gs a gs' x31 x32]
      by (auto simp add: prepare_def km_unchanged_defs; simp add: sim_defs)
  next
    case (RLock x41 x42)
    then show ?case using p inv kvs_of_gs_km_fp_inv[of gs a gs' x41 x42]
      by (auto simp add: acquire_rd_lock_def km_unchanged_defs; simp add: sim_defs)
  next
    case (WLock x51 x52)
    then show ?case using p inv kvs_of_gs_km_fp_inv[of gs a gs' x51 x52]
      by (auto simp add: acquire_wr_lock_def km_unchanged_defs; simp add: sim_defs)
  next
    case (NoLock x61 x62)
    then show ?case using p inv kvs_of_gs_km_fp_inv[of gs a gs' x61 x62]
      by (auto simp add: acquire_no_lock_def km_unchanged_defs; simp add: sim_defs)
  next
    case (NOK x71 x72)
    then show ?case using p inv kvs_of_gs_km_fp_inv[of gs a gs' x71 x72]
      by (auto simp add: nok_def km_unchanged_defs; simp add: sim_defs)
  next
    case (Commit x81 x82)
    hence u: "kvs_of_gs gs' x81 = kvs_of_gs gs x81" using p inv
      apply (auto simp add: kvs_of_gs_def commit_def)
      subgoal
        using eligible_reads_read_lock_inv[of gs]
              update_kv_writes_commit_r_inv[of gs]
        by (auto simp add: update_kv_all_txn_def update_kv_reads_all_txn_def Let_def
            RLockFpInv_def KVSNonEmp_def km_unchanged_defs update_kv_key_ro_set_v_readerset
            dest!: km_key_fp_eq_all_k)
      subgoal
        using update_kv_reads_commit_w_s_inv[of gs]
              update_kv_reads_commit_w_s'_inv[of gs]
              update_kv_writes_commit_w_s_inv[of gs]
              update_kv_writes_commit_w_s'_inv[of gs]
        by (auto simp add: update_kv_all_txn_def update_kv_key_def update_kv_reads_defs
            km_unchanged_defs dest!: km_key_fp_eq_all_k split: option.split)
      subgoal
        using eligible_reads_no_lock_inv[of gs]
        using update_kv_writes_commit_n_inv[of gs]
        by (auto simp add: update_kv_all_txn_def update_kv_reads_all_txn_def
            NoLockFpInv_def km_unchanged_defs dest!: km_key_fp_eq_all_k) done
    hence "\<forall>k. k \<noteq> x81 \<longrightarrow> kvs_of_gs gs' k = kvs_of_gs gs k" using Commit p
      by (auto simp add: commit_def km_unchanged_defs kvs_of_gs_def)
    hence "\<forall>k. kvs_of_gs gs' k = kvs_of_gs gs k" using u by auto
    then show ?case using Commit p
      by (auto simp add: commit_def sim_defs km_unchanged_defs)
  next
    case (Abort x91 x92)
    then show ?case using p inv kvs_of_gs_km_fp_inv[of gs a gs' x91 x92]
      by (auto simp add: abort_def km_unchanged_defs; simp add: sim_defs)
  next
    case (User_Commit x10)
    then show ?case using p kvs_of_gs_tm_inv[of gs a gs' x10]
      by (auto simp add: user_commit_def sim_defs tm_unchanged_defs, metis)
  next
    case (TM_Commit x111 x112 x113 x114)
    then show ?case using TM_Commit p inv
      apply (auto simp add: tm_commit_def unchanged_defs sim_def)
      subgoal apply (rule exI [where x="(\<lambda>k. full_view (kvs_of_gs gs k))"])
        apply (auto simp add: views_of_gs_def KVSLen_def)
        apply (auto simp add: ET_SER.ET_cl_txn_def)
        subgoal sorry
        subgoal sorry
        subgoal apply (auto simp add: ET_SER.canCommit_def closed_def visTx_def read_only_Txs_def
              kvs_txids_def kvs_readers_def kvs_writers_def full_view_def)
            apply (metis image_eqI nth_mem order_less_le_trans)
          subgoal for t i k apply (auto simp add: R_SER_def R_onK_def WW_def image_def dest!: rtrancl_converseD) sorry
          subgoal for i k k' v apply (auto simp add: R_SER_def R_onK_def WW_def image_def dest!: rtrancl_converseD) sorry.
        subgoal sorry
        subgoal apply (auto simp add: kvs_of_gs_def next_txids_def) sorry
        subgoal sorry
        done
      subgoal sorry
      sorry  \<comment>\<open>map_add_union_db\<close>
  next
    case (TM_Abort x12a)
    then show ?case using p kvs_of_gs_tm_inv[of gs a gs' x12a]
      by (auto simp add: tm_abort_def sim_defs tm_unchanged_defs, metis)
  next
    case (TM_ReadyC x13a)
    then show ?case using p kvs_of_gs_tm_inv[of gs a gs' x13a]
      by (auto simp add: tm_ready_c_def sim_defs tm_unchanged_defs, metis)
  next
    case (TM_ReadyA x14)
    then show ?case using p kvs_of_gs_tm_inv[of gs a gs' x14]
      by (auto simp add: tm_ready_a_def sim_defs tm_unchanged_defs, metis)
  qed auto
qed auto

end