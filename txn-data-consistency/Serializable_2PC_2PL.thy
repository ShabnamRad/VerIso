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

\<comment>\<open>Key Manager (KM)\<close>
record 'v km_state =
  km_vl :: "'v v_list"
  km_key_fp :: "txid0 \<Rightarrow> 'v key_fp"
  km_status :: "txid0 \<Rightarrow> status_km"

\<comment>\<open>System Global State: TM and KMs\<close>
record 'v global_state =
  tm :: "cl_id \<Rightarrow> tm_state"
  kms :: "key \<Rightarrow> 'v km_state"


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

fun get_cl_txn :: "txid0 \<Rightarrow> cl_id" where
  "get_cl_txn (Tn_cl sn cl) = cl"

fun get_sn_txn :: "txid0 \<Rightarrow> nat" where
  "get_sn_txn (Tn_cl sn cl) = sn"

fun get_txn_cl :: "cl_id \<Rightarrow> 'v global_state \<Rightarrow> txid0" where
  "get_txn_cl cl s = Tn_cl (tm_sn (tm s cl)) cl"

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
    \<and> tm_km_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

definition abort where \<comment>\<open>Locks released (aborted)\<close>
  "abort s k s' t \<equiv>
    km_status (kms s k) t \<in> {read_lock, write_lock, no_lock, notokay}
    \<and> tm_status (tm s (get_cl_txn t)) = tm_aborted
    \<and> km_vl (kms s' k) = km_vl (kms s k)
    \<and> km_status (kms s' k) t = aborted
    \<and> tm_km_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

definition user_commit where
  "user_commit s s' cl \<equiv>
    tm_status (tm s cl) = tm_init
    \<and> tm_status (tm s' cl) = tm_prepared
    \<and> tm_sn (tm s' cl) = tm_sn (tm s cl)
    \<and> km_tm_cl'_unchanged cl s s'"

definition tm_commit where
  "tm_commit s s' cl sn u F \<equiv>
    tm_status (tm s cl) = tm_prepared
    \<and> (\<forall>k. km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock})
    \<and> tm_status (tm s' cl) = tm_committed
    \<and> tm_sn (tm s' cl) = tm_sn (tm s cl)
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
    \<and> km_tm_cl'_unchanged cl s s'"

definition tm_ready_c where
  "tm_ready_c s s' cl \<equiv>
    tm_status (tm s cl) = tm_committed
    \<and> (\<forall>k. km_status (kms s k) (get_txn_cl cl s) = committed)
    \<and> tm_status (tm s' cl) = tm_init
    \<and> tm_sn (tm s' cl) = Suc (tm_sn (tm s cl))
    \<and> km_tm_cl'_unchanged cl s s'"

definition tm_ready_a where
  "tm_ready_a s s' cl \<equiv>
    tm_status (tm s cl) = tm_aborted
    \<and> (\<forall>k. km_status (kms s k) (get_txn_cl cl s) = aborted)
    \<and> tm_status (tm s' cl) = tm_init
    \<and> tm_sn (tm s' cl) = Suc (tm_sn (tm s cl))
    \<and> km_tm_cl'_unchanged cl s s'"

text\<open>The Event System\<close>
definition gs_init :: "'v global_state" where
  "gs_init \<equiv> \<lparr> 
    tm = (\<lambda>cl. \<lparr> tm_status = tm_init, tm_sn = 0 \<rparr>),
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
      by (auto simp add: tps_trans_defs km_unchanged_defs WLockInv_def, metis)
  next
    case (Read2 x21 x22 x23)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs WLockInv_def, metis)
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
      by (auto simp add: tps_trans_defs km_unchanged_defs WLockInv_def, metis)
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


subsubsection \<open>Simulation function\<close>
abbreviation eligible_reads :: "(txid0 \<Rightarrow> status_tm) \<Rightarrow> (txid0 \<Rightarrow> status_km) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> txid0 \<Rightarrow> bool" where
  "eligible_reads tStm tSkm tFk t \<equiv>
    tStm t = tm_committed \<and> tSkm t \<in> {read_lock, write_lock} \<and> tFk t R \<noteq> None"

definition update_kv_reads_all_txn :: "(txid0 \<Rightarrow> status_tm) \<Rightarrow> (txid0 \<Rightarrow> status_km) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> key_view \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_reads_all_txn tStm tSkm tFk uk vl =
    (let lv = last_version vl uk in
     vl [Max uk := lv \<lparr>v_readerset := (v_readerset lv) \<union> {t. eligible_reads tStm tSkm tFk t}\<rparr>])"

abbreviation the_wr_t :: "(txid0 \<Rightarrow> status_km) \<Rightarrow> txid0" where
  "the_wr_t tSkm \<equiv> (THE t. tSkm t = write_lock)"

lemma the_wr_tI:
  assumes "km_status (kms s k) t = write_lock"
      and "WLockInv s k"
  shows "the_wr_t (km_status (kms s k)) = t"
  using assms
  by blast

definition update_kv_writes_all_txn :: "(txid0 \<Rightarrow> status_tm) \<Rightarrow> (txid0 \<Rightarrow> status_km) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_writes_all_txn tStm tSkm tFk vl =
    (if (\<exists>t. tStm t = tm_committed \<and> tSkm t = write_lock) then
        update_kv_writes (the_wr_t tSkm) (tFk (the_wr_t tSkm)) vl
     else vl)"

definition update_kv_all_txn :: "(txid0 \<Rightarrow> status_tm) \<Rightarrow> (txid0 \<Rightarrow> status_km) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> key_view \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_all_txn tStm tSkm tFk uk =
    (update_kv_writes_all_txn tStm tSkm tFk) o (update_kv_reads_all_txn tStm tSkm tFk uk)"

definition kvs_of_gs :: "'v global_state \<Rightarrow> 'v kv_store" where
  "kvs_of_gs gs = (\<lambda>k.
   update_kv_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
    (km_status (kms gs k)) (km_key_fp (kms gs k)) (full_view (km_vl (kms gs k))) (km_vl (kms gs k)))"

fun last_touched_version :: "cl_id \<Rightarrow> 'v v_list \<Rightarrow> v_id" where
  "last_touched_version cl [] = 0" |
  "last_touched_version cl (x # rest) =
    (if \<exists>sn. Tn (Tn_cl sn cl) = v_writer x \<or> (Tn_cl sn cl) \<in> v_readerset x then
      length rest
     else
      last_touched_version cl rest)"

definition cl_last_view :: "cl_id \<Rightarrow> sqn \<Rightarrow> 'v kv_store \<Rightarrow> view" where
  "cl_last_view cl sn K \<equiv> (\<lambda>k. {..(last_touched_version cl (rev (K k)))})"

definition views_of_gs :: "'v global_state \<Rightarrow> (cl_id \<Rightarrow> view)" where
  "views_of_gs gs = (\<lambda>cl. (\<lambda>k. full_view (kvs_of_gs gs k)))"

definition sim :: "'v global_state \<Rightarrow> 'v config" where
  "sim gs = (kvs_of_gs gs, views_of_gs gs)"

lemmas update_kv_all_defs = update_kv_reads_all_txn_def update_kv_writes_all_txn_def update_kv_all_txn_def
lemmas sim_defs = sim_def kvs_of_gs_def views_of_gs_def cl_last_view_def update_kv_all_defs

text\<open>Invariants and lemmas for the refinement proof\<close>

lemma update_kv_all_txn_length:
  "length vl \<le> length (update_kv_all_txn tStm tSkm tFk uk vl)"
  by (auto simp add: update_kv_all_defs update_kv_writes_def Let_def split: option.split)

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
    by (induction e) (auto simp add: KVSLen_def kvs_of_gs_def update_kv_all_txn_length)
qed

lemma [simp]: "last_version [version_init] {..<Suc 0} = version_init"
  by (auto simp add: last_version_def lessThan_def)

lemma [simp]: "Max {..<Suc 0} = 0" by (simp add: lessThan_Suc)

lemma reach_view_wellformed [simp, intro]:
  "reach tps s \<Longrightarrow> view_wellformed (kvs_of_gs s) (\<lambda>k. full_view (km_vl (kms s k)))"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: tps_defs sim_defs Let_def view_wellformed_defs full_view_def)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Write2 x1 x2 x3)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs view_wellformed_def km_unchanged_defs view_in_range_def key_view_in_range_def)
          \<comment> \<open>adding view_atomic_def or view_wellformed_defs (lemmas containing view_atomic_def) makes it loop\<close> sorry
  next
    case (Read2 x1 x2 x3)
    then show ?case sorry
  next
    case (Prepare x1 x2)
    then show ?case sorry
  next
    case (RLock x1 x2)
    then show ?case sorry
  next
    case (WLock x1 x2)
    then show ?case sorry
  next
    case (NoLock x1 x2)
    then show ?case sorry
  next
    case (NOK x1 x2)
    then show ?case sorry
  next
    case (Commit x1 x2)
    then show ?case sorry
  next
    case (Abort x1 x2)
    then show ?case sorry
  next
    case (User_Commit x)
    then show ?case sorry
  next
    case (TM_Commit x1 x2 x3 x4)
    then show ?case sorry
  next
    case (TM_Abort x)
    then show ?case sorry
  next
    case (TM_ReadyC x)
    then show ?case sorry
  next
    case (TM_ReadyA x)
    then show ?case sorry
  next
    case Skip2
    then show ?case sorry
  qed
qed

lemma km_vl_inv:
  assumes "tps: s\<midarrow>e\<rightarrow> s'" and "\<forall>k t. e \<noteq> Commit k t"
  shows "\<forall>k. km_vl (kms s' k) = km_vl (kms s k)"
  using assms
  by (induction e) (auto simp add: tps_trans_defs unchanged_defs, metis+)

lemma other_sn_idle:  
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "get_cl_txn t = cl" and "get_sn_txn t \<noteq> tm_sn (tm s cl)"
  shows "\<forall>k. km_status (kms s k) t \<in> {working, committed, aborted}"
  using assms
  apply (auto simp add: TIDFutureKm_def TIDPastKm_def)
  apply (cases "get_sn_txn t > tm_sn (tm s cl)")
  apply (metis get_cl_txn.simps get_sn_txn.elims)
  by (metis get_cl_txn.elims get_sn_txn.simps nat_neq_iff)

lemma tps_refines_et_es: "tps \<sqsubseteq>\<^sub>med ET_SER.ET_ES"
proof (intro simulate_ES_fun_with_invariant[where I="\<lambda>s. \<forall>cl k. TIDFutureKm s cl \<and> TIDPastKm s cl \<and>
   RLockInv s k \<and> WLockInv s k"])
  fix gs0
  assume p: "init tps gs0"
  then show "init ET_SER.ET_ES (sim gs0)" using p
    by (auto simp add: ET_SER.ET_ES_defs tps_defs sim_defs last_version_def full_view_def
        kvs_init_def v_list_init_def lessThan_Suc)
next
  fix gs a gs'
  assume p: "tps: gs\<midarrow>a\<rightarrow> gs'"
     and inv: "\<forall>cl k. TIDFutureKm gs cl \<and> TIDPastKm gs cl \<and> RLockInv gs k \<and> WLockInv gs k"
  then show "ET_SER.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  proof (cases a)
    case (Write2 x11 x12 x13)
    hence v: "\<forall>k. km_vl (kms gs' k) = km_vl (kms gs k)" using km_vl_inv p by blast
    hence s: "\<forall>k. km_status (kms gs' k) = km_status (kms gs k)" using p Write2
      apply (auto simp add: write2_def unchanged_defs fun_eq_iff)
      subgoal for k t by(cases "k = x11"; cases "t = x12"; simp).
    have r: "\<And>k t. eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs' k)) t =
                   eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs k)) t"
      using Write2 p subgoal for k t
        apply (cases "t = x12"; simp add: write2_def unchanged_defs)
        apply (metis status_km.distinct(3) status_km.distinct(5)) by metis.
    have w:"\<And>k vl. update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs' k)) vl =
               update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs k)) vl"
      using Write2 p inv apply (auto simp add: update_kv_writes_all_txn_def)
      subgoal for k vl t
        by (cases "k = x11"; cases "t = x12"; simp add: write2_def unchanged_defs the_wr_tI).
    then show ?thesis using Write2 p s v r w
      by (auto simp add: write2_def unchanged_defs sim_defs)
  next
    case (Read2 x21 x22 x23)
    hence v: "\<forall>k. km_vl (kms gs' k) = km_vl (kms gs k)" using km_vl_inv p by blast
    hence s: "\<forall>k. km_status (kms gs' k) = km_status (kms gs k)" using p Read2
      apply (auto simp add: read2_def unchanged_defs fun_eq_iff)
      subgoal for k t by(cases "k = x21"; cases "t = x22"; simp).
    have r: "\<And>k t. eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs' k)) t =
                   eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs k)) t"
      using Read2 p subgoal for k t
        apply (cases "t = x22"; simp add: read2_def unchanged_defs)
        apply (metis status_km.distinct(3) status_km.distinct(5)) by metis.
    have w:"\<And>k vl. update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs' k)) vl =
               update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs k)) vl"
      using Read2 p inv apply (auto simp add: update_kv_writes_all_txn_def)
      subgoal for k vl t
        by (cases "k = x21"; cases "t = x22"; simp add: read2_def unchanged_defs the_wr_tI).
    then show ?thesis using Read2 p s v r w
      by (auto simp add: read2_def unchanged_defs sim_defs)
  next
    case (Prepare x31 x32)
    hence v: "\<forall>k. km_vl (kms gs' k) = km_vl (kms gs k)" using km_vl_inv p by blast
    have r: "\<And>k t. eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs' k)) (km_key_fp (kms gs' k)) t =
                   eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs k)) t"
      using Prepare p subgoal for k t
        apply (cases "t = x32"; simp add: prepare_def unchanged_defs) by metis.
    have w:"\<And>k vl. update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs' k)) (km_key_fp (kms gs' k)) vl =
               update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs k)) vl"
      using Prepare p inv apply (auto simp add: update_kv_writes_all_txn_def)
      subgoal for k vl t t'
        apply (cases "k = x31"; cases "t = x32"; cases "t' = x32";
                simp add: prepare_def unchanged_defs the_wr_tI)
        by (metis WLockInv_def status_km.distinct(17) the_wr_tI)
      subgoal for k vl t
        by (cases "k = x31"; cases "t = x32"; simp add: prepare_def unchanged_defs the_wr_tI)
      subgoal for k vl t
        by (cases "k = x31"; cases "t = x32"; auto simp add: prepare_def unchanged_defs the_wr_tI).
    then show ?thesis using Prepare p v r w
      by (auto simp add: prepare_def unchanged_defs sim_defs)
  next
    case (RLock x41 x42)
    hence v: "\<forall>k. km_vl (kms gs' k) = km_vl (kms gs k)" using km_vl_inv p by blast
    have r: "\<And>k t. eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs' k)) (km_key_fp (kms gs' k)) t =
                   eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs k)) t"
      using RLock p subgoal for k t
        apply (cases "t = x42"; simp add: acquire_rd_lock_def unchanged_defs) by metis.
    have w:"\<And>k vl. update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs' k)) (km_key_fp (kms gs' k)) vl =
               update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs k)) vl"
      using RLock p inv apply (auto simp add: update_kv_writes_all_txn_def)
      subgoal for k vl t t'
        by (cases "k = x41"; cases "t = x42"; cases "t' = x42";
                simp add: acquire_rd_lock_def unchanged_defs the_wr_tI)
      subgoal for k vl t
        by (cases "k = x41"; cases "t = x42"; simp add: acquire_rd_lock_def unchanged_defs the_wr_tI)
      subgoal for k vl t
        by (cases "k = x41"; cases "t = x42"; auto simp add: acquire_rd_lock_def unchanged_defs the_wr_tI).
    then show ?thesis using RLock p v r w
      by (auto simp add: acquire_rd_lock_def unchanged_defs sim_defs)
  next
    case (WLock x51 x52)
    hence v: "\<forall>k. km_vl (kms gs' k) = km_vl (kms gs k)" using km_vl_inv p by blast
    have r: "\<And>k t. eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs' k)) (km_key_fp (kms gs' k)) t =
                   eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs k)) t"
      using WLock p subgoal for k t
        apply (cases "t = x52"; simp add: acquire_wr_lock_def unchanged_defs) by metis.
    have w:"\<And>k vl. update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs' k)) (km_key_fp (kms gs' k)) vl =
               update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs k)) vl"
      using WLock p inv apply (auto simp add: update_kv_writes_all_txn_def)
      subgoal for k vl t t'
        by (cases "k = x51"; cases "t = x52"; cases "t' = x52";
                simp add: acquire_wr_lock_def unchanged_defs the_wr_tI)
      subgoal for k vl t
        by (cases "k = x51"; cases "t = x52"; simp add: acquire_wr_lock_def unchanged_defs the_wr_tI)
      subgoal for k vl t
        by (cases "k = x51"; cases "t = x52"; auto simp add: acquire_wr_lock_def unchanged_defs the_wr_tI).
    then show ?thesis using WLock p v r w
      by (auto simp add: acquire_wr_lock_def unchanged_defs sim_defs)
  next
    case (NoLock x61 x62)
    hence v: "\<forall>k. km_vl (kms gs' k) = km_vl (kms gs k)" using km_vl_inv p by blast
    have r: "\<And>k t. eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs' k)) (km_key_fp (kms gs' k)) t =
                   eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs k)) t"
      using NoLock p subgoal for k t
        apply (cases "t = x62"; simp add: acquire_no_lock_def unchanged_defs) by metis.
    have w:"\<And>k vl. update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs' k)) (km_key_fp (kms gs' k)) vl =
               update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs k)) vl"
      using NoLock p inv apply (auto simp add: update_kv_writes_all_txn_def)
      subgoal for k vl t t'
        apply (cases "k = x61"; cases "t = x62"; cases "t' = x62";
                simp add: acquire_no_lock_def unchanged_defs the_wr_tI)
        by (metis WLockInv_def status_km.distinct(37) the_wr_tI)
      subgoal for k vl t
        by (cases "k = x61"; cases "t = x62"; simp add: acquire_no_lock_def unchanged_defs the_wr_tI)
      subgoal for k vl t
        by (cases "k = x61"; cases "t = x62"; auto simp add: acquire_no_lock_def unchanged_defs the_wr_tI).
    then show ?thesis using NoLock p v r w
      by (auto simp add: acquire_no_lock_def unchanged_defs sim_defs)
  next
    case (NOK x71 x72)
    hence v: "\<forall>k. km_vl (kms gs' k) = km_vl (kms gs k)" using km_vl_inv p by blast
    have r: "\<And>k t. eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs' k)) (km_key_fp (kms gs' k)) t =
                   eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs k)) t"
      using NOK p subgoal for k t
        apply (cases "t = x72"; simp add: nok_def unchanged_defs) by metis.
    have w:"\<And>k vl. update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs' k)) (km_key_fp (kms gs' k)) vl =
               update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs k)) vl"
      using NOK p inv apply (auto simp add: update_kv_writes_all_txn_def)
      subgoal for k vl t t'
        apply (cases "k = x71"; cases "t = x72"; cases "t' = x72";
                simp add: nok_def unchanged_defs the_wr_tI)
        by (metis WLockInvI status_km.distinct(39) the_wr_tI)
      subgoal for k vl t
        by (cases "k = x71"; cases "t = x72"; simp add: nok_def unchanged_defs the_wr_tI)
      subgoal for k vl t
        by (cases "k = x71"; cases "t = x72"; auto simp add: nok_def unchanged_defs the_wr_tI).
    then show ?thesis using NOK p v r w
      by (auto simp add: nok_def unchanged_defs sim_defs)
  next
    case (Commit x81 x82)
    hence r:
    "\<And>k. v_readerset (last_version (km_vl (kms gs' k)) (full_view (km_vl (kms gs' k)))) \<union>
          {t. eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t))) (km_status (kms gs' k))
              (km_key_fp (kms gs' k)) t} =
         v_readerset (last_version (km_vl (kms gs k)) (full_view (km_vl (kms gs k)))) \<union> 
          {t. eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t))) (km_status (kms gs k))
              (km_key_fp (kms gs k)) t}"
      using p inv subgoal for k
        apply (cases "k = x81")
        subgoal apply (simp add: commit_def unchanged_defs) sorry
        subgoal by (simp add: commit_def unchanged_defs) done.
    have w:"\<And>k vl. update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs' k)) (km_key_fp (kms gs' k)) vl =
               update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs k)) vl"
      using Commit p inv apply (auto simp add: update_kv_writes_all_txn_def)
      subgoal for k vl t t'
        apply (cases "k = x81"; cases "t = x82"; cases "t' = x82";
                simp add: commit_def unchanged_defs the_wr_tI)
        apply blast
        by (metis WLockInv_def status_km.distinct(41) the_wr_tI)
      subgoal for k vl t
        by (cases "k = x81"; cases "t = x82"; simp add: commit_def unchanged_defs the_wr_tI)
      subgoal for k vl t
        apply (cases "k = x81"; cases "t = x82"; auto simp add: commit_def unchanged_defs the_wr_tI) sorry .
    have u: "kvs_of_gs gs' x81 = kvs_of_gs gs x81" using Commit p
      apply (auto simp add: commit_def unchanged_defs kvs_of_gs_def update_kv_all_txn_def) sorry
    hence "\<forall>k. k \<noteq> x81 \<longrightarrow> kvs_of_gs gs' k = kvs_of_gs gs k" using Commit p
      by (auto simp add: commit_def unchanged_defs kvs_of_gs_def)
    then show ?thesis using Commit p r w u
      apply (auto simp add: commit_def unchanged_defs sim_def views_of_gs_def)
      by (fastforce, metis)+
  next
    case (Abort x91 x92)
    hence v: "\<forall>k. km_vl (kms gs' k) = km_vl (kms gs k)" using km_vl_inv p by blast
    have r: "\<And>k t. eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs' k)) (km_key_fp (kms gs' k)) t =
                   eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs k)) t"
      using Abort p subgoal for k t
        apply (cases "t = x92"; simp add: abort_def unchanged_defs) by metis.
    have w:"\<And>k vl. update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs' k)) (km_key_fp (kms gs' k)) vl =
               update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs k)) vl"
      using Abort p inv apply (auto simp add: update_kv_writes_all_txn_def)
      subgoal for k vl t t'
        apply (cases "k = x91"; cases "t = x92"; cases "t' = x92";
                simp add: abort_def unchanged_defs the_wr_tI)
        by (metis WLockInv_def status_km.distinct(43) the_wr_tI)
      subgoal for k vl t
        by (cases "k = x91"; cases "t = x92"; simp add: abort_def unchanged_defs the_wr_tI)
      subgoal for k vl t
        by (cases "k = x91"; cases "t = x92"; auto simp add: abort_def unchanged_defs the_wr_tI).
    then show ?thesis using Abort p v r w
      by (auto simp add: abort_def unchanged_defs sim_defs)
  next
    case (User_Commit x10)
    hence v: "\<forall>k. km_vl (kms gs' k) = km_vl (kms gs k)" using km_vl_inv p by blast
    hence s: "\<forall>cl. tm_sn (tm gs' cl) = tm_sn (tm gs cl)" using p User_Commit
      by (auto simp add: user_commit_def unchanged_defs)
    have r: "\<And>k t. eligible_reads (\<lambda>t. tm_status (tm gs' (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs k)) t =
                   eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs k)) t"
      using User_Commit p subgoal for k t
        by (cases "get_cl_txn t = x10"; simp add: user_commit_def unchanged_defs).
    have w:"\<And>k vl. update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs' (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs k)) vl =
               update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs k)) vl"
      using User_Commit p inv apply (auto simp add: update_kv_writes_all_txn_def)
      subgoal for k vl t
        by (cases "get_cl_txn t = x10"; simp add: user_commit_def unchanged_defs the_wr_tI)
      subgoal for k vl t
        by (cases "get_cl_txn t = x10"; simp add: user_commit_def unchanged_defs the_wr_tI).
    hence "\<forall>k. kvs_of_gs gs' k = kvs_of_gs gs k" using User_Commit p r w
      by (auto simp add: user_commit_def unchanged_defs sim_defs)
    then show ?thesis using User_Commit p s v
      by (auto simp add: user_commit_def unchanged_defs sim_def views_of_gs_def)
  next
    case (TM_Commit x111 x112 x113 x114)
    then show ?thesis using p inv
      apply (auto simp add: tm_commit_def unchanged_defs sim_def)
      subgoal apply (rule exI [where x="(\<lambda>k. full_view (km_vl (kms gs k)))"])
        apply (auto simp add: ET_SER.ET_cl_txn_def)
        sorry sorry \<comment>\<open>map_add_union_db\<close>
  next
    case (TM_Abort x12a)
    hence v: "\<forall>k. km_vl (kms gs' k) = km_vl (kms gs k)" using km_vl_inv p by blast
    hence s: "\<forall>cl. tm_sn (tm gs' cl) = tm_sn (tm gs cl)" using p TM_Abort
      by (auto simp add: tm_abort_def unchanged_defs)
    have r: "\<And>k t. eligible_reads (\<lambda>t. tm_status (tm gs' (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs k)) t =
                   eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs k)) t"
      using TM_Abort p subgoal for k t
        by (cases "get_cl_txn t = x12a"; simp add: tm_abort_def unchanged_defs).
    have w:"\<And>k vl. update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs' (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs k)) vl =
               update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs k)) vl"
      using TM_Abort p inv apply (auto simp add: update_kv_writes_all_txn_def)
      subgoal for k vl t
        by (cases "get_cl_txn t = x12a"; simp add: tm_abort_def unchanged_defs the_wr_tI)
      subgoal for k vl t
        by (cases "get_cl_txn t = x12a"; simp add: tm_abort_def unchanged_defs the_wr_tI).
    hence "\<forall>k. kvs_of_gs gs' k = kvs_of_gs gs k" using TM_Abort p r w
      by (auto simp add: tm_abort_def unchanged_defs sim_defs)
    then show ?thesis using TM_Abort p s v
      by (auto simp add: tm_abort_def unchanged_defs sim_def views_of_gs_def)
  next
    case (TM_ReadyC x13a)
    hence v: "\<forall>k. km_vl (kms gs' k) = km_vl (kms gs k)" using km_vl_inv p by blast
    have r: "\<And>k t. eligible_reads (\<lambda>t. tm_status (tm gs' (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs k)) t =
                   eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs k)) t"
      using TM_ReadyC p inv subgoal for k t
        apply (cases "get_cl_txn t = x13a"; cases "get_sn_txn t = tm_sn (tm gs x13a)";
               simp add: tm_ready_c_def unchanged_defs)
        apply (metis get_cl_txn.elims get_sn_txn.simps status_km.distinct(33) status_km.distinct(41))
        by (metis insertE insert_absorb insert_not_empty other_sn_idle status_km.distinct(3)
            status_km.distinct(33) status_km.distinct(35) status_km.distinct(41)
            status_km.distinct(43) status_km.distinct(5)).
    have w:"\<And>k vl. update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs' (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs k)) vl =
               update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs k)) vl"
      using TM_ReadyC p inv apply (auto simp add: update_kv_writes_all_txn_def)
      subgoal for k vl t
        by (cases "get_cl_txn t = x13a"; simp add: tm_ready_c_def unchanged_defs the_wr_tI)
      subgoal for k vl t
        apply (cases "get_cl_txn t = x13a"; cases "get_sn_txn t = tm_sn (tm gs x13a)";
               simp add: tm_ready_c_def unchanged_defs the_wr_tI)
        apply (metis get_cl_txn.simps get_sn_txn.simps status_km.distinct(41) txid0.exhaust)
        by (metis insertE insert_absorb insert_not_empty other_sn_idle status_km.distinct(41)
            status_km.distinct(43) status_km.distinct(5)).
    hence "\<forall>k. kvs_of_gs gs' k = kvs_of_gs gs k" using TM_ReadyC p r w
      by (auto simp add: tm_ready_c_def unchanged_defs sim_defs)
    then show ?thesis using TM_ReadyC p v
      by (auto simp add: tm_ready_c_def unchanged_defs sim_def views_of_gs_def)
  next
    case (TM_ReadyA x14)
    hence v: "\<forall>k. km_vl (kms gs' k) = km_vl (kms gs k)" using km_vl_inv p by blast
    have r: "\<And>k t. eligible_reads (\<lambda>t. tm_status (tm gs' (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs k)) t =
                   eligible_reads (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                    (km_status (kms gs k)) (km_key_fp (kms gs k)) t"
      using TM_ReadyA p subgoal for k t
        by (cases "get_cl_txn t = x14"; simp add: tm_ready_a_def unchanged_defs).
    have w:"\<And>k vl. update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs' (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs k)) vl =
               update_kv_writes_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
                (km_status (kms gs k)) (km_key_fp (kms gs k)) vl"
      using TM_ReadyA p inv apply (auto simp add: update_kv_writes_all_txn_def)
      subgoal for k vl t
        by (cases "get_cl_txn t = x14"; simp add: tm_ready_a_def unchanged_defs the_wr_tI)
      subgoal for k vl t
        by (cases "get_cl_txn t = x14"; simp add: tm_ready_a_def unchanged_defs the_wr_tI).
    hence "\<forall>k. kvs_of_gs gs' k = kvs_of_gs gs k" using TM_ReadyA p r w
      by (auto simp add: tm_ready_a_def unchanged_defs sim_defs)
    then show ?thesis using TM_ReadyA p v
      by (auto simp add: tm_ready_a_def unchanged_defs sim_def views_of_gs_def)
  qed auto
qed auto

end