section \<open>Two Phase Commit (2PC) with Two Phase Locking (2PL)\<close>

theory Prot_2PC_2PL
  imports Key_Value_Stores
begin

subsection \<open>2PC Event system\<close>

subsubsection \<open>State\<close>

datatype status_km = working | prepared | read_lock | write_lock | no_lock | notokay | committed | aborted
datatype status_tm = tm_init | tm_prepared | tm_committed | tm_aborted

\<comment>\<open>Transaction Manager (TM)\<close>
record tm_state =
  tm_status :: status_tm
  tm_sn :: nat
  (*tm_view :: view -- We used the full_view (seeing everything)*)

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
    \<and> (\<forall>t'. km_status (kms s k) t' \<in> {working, prepared, read_lock, no_lock, notokay})
    \<and> km_status_trans s k s' t prepared read_lock"

definition acquire_wr_lock where \<comment>\<open>Write Lock acquired\<close>
  "acquire_wr_lock s k s' t \<equiv>
    tm_status (tm s (get_cl_txn t)) = tm_prepared
    \<and> km_key_fp (kms s k) t W \<noteq> None
    \<and> (\<forall>t'. km_status (kms s k) t' \<in> {working, prepared, no_lock, notokay})
    \<and> km_status_trans s k s' t prepared write_lock"

definition acquire_no_lock where \<comment>\<open>No Lock needed\<close>
  "acquire_no_lock s k s' t \<equiv>
    tm_status (tm s (get_cl_txn t)) = tm_prepared
    \<and> km_key_fp (kms s k) t W = None
    \<and> km_key_fp (kms s k) t R = None
    \<and> (\<forall>t'. km_status (kms s k) t' \<in> {working, prepared, read_lock, write_lock, no_lock, notokay})
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
    \<and> km_key_fp (kms s' k) t = Map.empty
    \<and> km_status (kms s' k) t = committed
    \<and> tm_km_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

definition abort where \<comment>\<open>Locks released (aborted)\<close>
  "abort s k s' t \<equiv>
    km_status (kms s k) t \<in> {read_lock, write_lock, no_lock, notokay}
    \<and> tm_status (tm s (get_cl_txn t)) = tm_aborted
    \<and> km_vl (kms s' k) = km_vl (kms s k)
    \<and> km_key_fp (kms s' k) t = Map.empty
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

text\<open>Auxiliary invariants about idle and active kms\<close>
definition TIDActive where
  "TIDActive s cl \<longleftrightarrow> (\<forall>n k. n > tm_sn (tm s cl) \<longrightarrow> km_status (kms s k) (Tn_cl n cl) = working)"

lemmas TIDActiveI = TIDActive_def[THEN iffD2, rule_format]
lemmas TIDActiveE[elim] = TIDActive_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidactive [simp, dest]: "reach tps s \<Longrightarrow> TIDActive s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: TIDActive_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Write2 x11 x12 x13)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs TIDActive_def, fastforce)
  next
    case (Read2 x21 x22 x23)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs TIDActive_def, fastforce)
  next
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TIDActive_def)
      subgoal for n k apply (cases "(Tn_cl n x) = x32"; cases "k = x31", auto) done.
  next
    case (RLock x41 x42)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDActive_def)
      by (metis status_km.distinct(1))
  next
    case (WLock x51 x52)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDActive_def)
      by (metis status_km.distinct(1))
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDActive_def)
      by (metis status_km.distinct(1))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDActive_def)
      by (metis status_km.distinct(1))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDActive_def)
      apply (metis status_km.distinct(3))
      apply (metis status_km.distinct(5))
      by (metis status_km.distinct(7))
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDActive_def)
      apply (metis status_km.distinct(3))
      apply (metis status_km.distinct(5))
      apply (metis status_km.distinct(7))
      by (metis status_km.distinct(9))
  next
    case (User_Commit x10)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs tm_unchanged_defs TIDActive_def, metis)
  next
    case (TM_Commit x111 x112 x113 x114)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs tm_unchanged_defs TIDActive_def, metis)
  next
    case (TM_Abort x12a)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs tm_unchanged_defs TIDActive_def, metis)
  next
    case (TM_ReadyC x13a)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs TIDActive_def)
      by (metis Suc_lessD)
  next
    case (TM_ReadyA x14)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs TIDActive_def)
      by (metis Suc_lessD)
  qed simp
qed

text\<open>Auxiliary invariants about TM states\<close>
definition TCInit where
  "TCInit s cl \<longleftrightarrow> (tm_status (tm s cl) = tm_init
    \<longrightarrow> (\<forall>k. tid_match s (get_txn_cl cl s) \<and> km_status (kms s k) (get_txn_cl cl s) = working))"

lemmas TCInitI = TCInit_def[THEN iffD2, rule_format]
lemmas TCInitE[elim] = TCInit_def[THEN iffD1, elim_format, rule_format]

lemma reach_tcinit [simp, dest]: "reach tps s \<Longrightarrow> TCInit s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: TCInit_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Write2 x11 x12 x13)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCInit_def) by fastforce
  next
    case (Read2 x21 x22 x23)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCInit_def) by fastforce
  next
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCInit_def)
      by (smt get_cl_txn.simps status_tm.distinct(1))
  next
    case (RLock x41 x42)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCInit_def)
      by (smt get_cl_txn.simps status_tm.distinct(1))
  next
    case (WLock x51 x52)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCInit_def)
      by (smt status_km.distinct(1))
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCInit_def)
      by (smt status_km.distinct(1))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCInit_def)
      by (smt status_km.distinct(1))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCInit_def)
      apply (metis status_km.distinct(3))
      apply (metis status_km.distinct(5))
      by (metis status_km.distinct(7))
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCInit_def)
      apply (metis status_km.distinct(3))
      apply (metis status_km.distinct(5))
      apply (metis status_km.distinct(7))
      by (metis status_km.distinct(9))
  next
    case (User_Commit x10)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCInit_def)
      by metis
  next
    case (TM_Commit x111 x112 x113 x114)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCInit_def)
      by (metis status_tm.distinct(3))
  next
    case (TM_Abort x12a)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCInit_def)
      by (metis status_tm.distinct(5))
  next
    case (TM_ReadyC x13a)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCInit_def)
      by (metis TIDActive_def lessI reach_tidactive)
  next
    case (TM_ReadyA x14)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCInit_def)
      by (metis TIDActive_def lessI reach_tidactive)
  qed simp
qed

definition TCPrepared where
  "TCPrepared s cl \<longleftrightarrow> (tm_status (tm s cl) = tm_prepared \<longrightarrow>
    (\<forall>k. tid_match s (get_txn_cl cl s) \<and>
      km_status (kms s k) (get_txn_cl cl s)
      \<in> {working, prepared, read_lock, write_lock, no_lock, notokay}))"

lemmas TCPreparedI = TCPrepared_def[THEN iffD2, rule_format]
lemmas TCPreparedE[elim] = TCPrepared_def[THEN iffD1, elim_format, rule_format]

lemma reach_tcprepared [simp, intro]: "reach tps s \<Longrightarrow> TCPrepared s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: TCPrepared_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Write2 x11 x12 x13)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCPrepared_def)
      by smt
  next
    case (Read2 x21 x22 x23)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCPrepared_def)
      by smt
  next      
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCPrepared_def)
      by smt
  next
    case (RLock x41 x42)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCPrepared_def)
      by smt
  next
    case (WLock x51 x52)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCPrepared_def)
      by smt
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCPrepared_def)
      by smt
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCPrepared_def)
      by smt+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCPrepared_def)
      by (smt get_cl_txn.simps status_tm.distinct(7))+
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCPrepared_def)
      by (smt get_cl_txn.simps status_tm.distinct(9))+
  next
    case (User_Commit x10)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCPrepared_def)
      by (smt TCInit_def get_txn_cl.elims reach_tcinit)
  next
    case (TM_Commit x111 x112 x113 x114)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCPrepared_def)
      by smt
  next
    case (TM_Abort x12a)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCPrepared_def)
      by smt
  next
    case (TM_ReadyC x13a)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCPrepared_def)
      by (smt status_tm.distinct(1))
  next
    case (TM_ReadyA x14)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCPrepared_def)
      by (smt status_tm.distinct(1))
  qed simp
qed

definition TCCommitted where
  "TCCommitted s cl \<longleftrightarrow> (tm_status (tm s cl) = tm_committed \<longrightarrow> 
    (\<forall>k. tid_match s (get_txn_cl cl s) \<and>
     km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock, committed}))"

lemmas TCCommittedI = TCCommitted_def[THEN iffD2, rule_format]
lemmas TCCommittedE[elim] = TCCommitted_def[THEN iffD1, elim_format, rule_format]

lemma reach_tccommitted [simp, intro]: "reach tps s \<Longrightarrow> TCCommitted s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: TCCommitted_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Write2 x11 x12 x13)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCCommitted_def, metis)
  next
    case (Read2 x21 x22 x23)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCCommitted_def, metis)
  next
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCCommitted_def)
      by (metis get_cl_txn.simps status_tm.distinct(7))
  next
    case (RLock x41 x42)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCCommitted_def, smt)
  next
    case (WLock x51 x52)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCCommitted_def, smt)
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCCommitted_def, smt)
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCCommitted_def)
      by (metis get_cl_txn.simps status_tm.distinct(7))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCCommitted_def, metis+)
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCCommitted_def)
      by (metis get_cl_txn.simps status_tm.distinct(11))+
  next
    case (User_Commit x10)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCCommitted_def)
      by (metis status_tm.distinct(7))
  next
    case (TM_Commit x111 x112 x113 x114)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCCommitted_def, metis)
  next
    case (TM_Abort x12a)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCCommitted_def)
      by (metis status_tm.distinct(11))
  next
    case (TM_ReadyC x13a)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCCommitted_def)
      by (metis status_tm.distinct(3))
  next
    case (TM_ReadyA x14)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCCommitted_def)
      by (metis status_tm.distinct(3))
  qed simp
qed

definition TCAborted where
  "TCAborted s cl \<longleftrightarrow> (tm_status (tm s cl) = tm_aborted \<longrightarrow> 
    (\<forall>k. tid_match s (get_txn_cl cl s) \<and>
     km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock, notokay, aborted}))"

lemmas TCAbortedI = TCAborted_def[THEN iffD2, rule_format]
lemmas TCAbortedE[elim] = TCAborted_def[THEN iffD1, elim_format, rule_format]

lemma reach_tcaborted [simp, intro]: "reach tps s \<Longrightarrow> TCAborted s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: TCAborted_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Write2 x11 x12 x13)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCAborted_def, smt)
  next
    case (Read2 x21 x22 x23)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCAborted_def, smt)
  next
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCAborted_def)
      by (smt get_cl_txn.simps status_tm.distinct(9))
  next
    case (RLock x41 x42)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCAborted_def, smt)
  next
    case (WLock x51 x52)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCAborted_def, smt)
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCAborted_def, smt)
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCAborted_def)
      by (smt get_cl_txn.simps status_tm.distinct(9))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCAborted_def)
      by (smt get_cl_txn.simps status_tm.distinct(11))+
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TCAborted_def, smt+)
  next
    case (User_Commit x10)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCAborted_def)
      by (smt status_tm.distinct(9))
  next
    case (TM_Commit x111 x112 x113 x114)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCAborted_def, metis)
  next
    case (TM_Abort x12a)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCAborted_def, metis)
  next
    case (TM_ReadyC x13a)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCAborted_def)
      by (smt status_tm.distinct(5))
  next
    case (TM_ReadyA x14)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs tid_match_def TCAborted_def)
      by (smt status_tm.distinct(5))
  qed simp
qed

text\<open>Invariants about Shadow DB being empty after a commit and an abort\<close>
definition TCCommitEmpF where
  "TCCommitEmpF s cl k \<longleftrightarrow> (tm_status (tm s cl) = tm_committed
      \<and> km_status (kms s k) (get_txn_cl cl s) = committed
    \<longrightarrow> km_key_fp (kms s k) (get_txn_cl cl s) = Map.empty)"

lemmas TCCommitEmpFI = TCCommitEmpF_def[THEN iffD2, rule_format]
lemmas TCCommitEmpFE[elim] = TCCommitEmpF_def[THEN iffD1, elim_format, rule_format]

lemma reach_tccommitempfp [simp, intro]: "reach tps s \<Longrightarrow> TCCommitEmpF s cl k"
proof(induction s arbitrary: cl k rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: TCCommitEmpF_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Write2 x11 x12 x13)
    then show ?thesis  using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TCCommitEmpF_def)
      by (metis status_km.distinct(11))
  next
    case (Read2 x21 x22 x23)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TCCommitEmpF_def)
      by (metis status_km.distinct(11))
  next
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TCCommitEmpF_def)
      by (metis status_km.distinct(23))
  next
    case (RLock x41 x42)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TCCommitEmpF_def)
      by (metis status_km.distinct(33))
  next
    case (WLock x51 x52)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TCCommitEmpF_def)
      by (metis status_km.distinct(41))
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TCCommitEmpF_def)
      by (metis status_km.distinct(47))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TCCommitEmpF_def)
      by (metis status_km.distinct(51))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs TCCommitEmpF_def, metis+)
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs TCCommitEmpF_def, metis+)
  next
    case (User_Commit x10)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs TCCommitEmpF_def)
      by (metis status_tm.distinct(7))
  next
    case (TM_Commit x111 x112 x113 x114)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs TCCommitEmpF_def)
      by (metis status_km.distinct(33) status_km.distinct(41) status_km.distinct(47))
  next
    case (TM_Abort x12a)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs TCCommitEmpF_def)
      by (metis status_tm.distinct(11))
  next
    case (TM_ReadyC x13a)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs TCCommitEmpF_def)
      by (metis status_tm.distinct(3))
  next
    case (TM_ReadyA x14)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs TCCommitEmpF_def)
      by (metis status_tm.distinct(3))
  qed simp
qed

definition TCAbortEmpF where
  "TCAbortEmpF s cl k \<longleftrightarrow> (tm_status (tm s cl) = tm_aborted
      \<and> km_status (kms s k) (get_txn_cl cl s) = aborted
    \<longrightarrow> km_key_fp (kms s k) (get_txn_cl cl s) = Map.empty)"

lemmas TCAbortEmpFI = TCAbortEmpF_def[THEN iffD2, rule_format]
lemmas TCAbortEmpFE[elim] = TCAbortEmpF_def[THEN iffD1, elim_format, rule_format]

lemma reach_tcabortempsfp [simp, intro]: "reach tps s \<Longrightarrow> TCAbortEmpF s cl k"
proof(induction s arbitrary: cl k rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: TCAbortEmpF_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Write2 x11 x12 x13)
    then show ?thesis  using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TCAbortEmpF_def)
      by (metis status_km.distinct(13))
  next
    case (Read2 x21 x22 x23)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TCAbortEmpF_def)
      by (metis status_km.distinct(13))
  next
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TCAbortEmpF_def)
      by (metis status_km.distinct(25))
  next
    case (RLock x41 x42)
    then show ?thesis  using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TCAbortEmpF_def)
      by (metis status_km.distinct(35))
  next
    case (WLock x51 x52)
    then show ?thesis  using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TCAbortEmpF_def)
      by (metis status_km.distinct(43))
  next
    case (NoLock x61 x62)
    then show ?thesis  using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TCAbortEmpF_def)
      by (metis status_km.distinct(49))
  next
    case (NOK x71 x72)
    then show ?thesis  using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TCAbortEmpF_def)
      by (metis status_km.distinct(53))+
  next
    case (Commit x81 x82)
    then show ?thesis  using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs TCAbortEmpF_def, metis+)
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs km_unchanged_defs TCAbortEmpF_def, metis+)
  next
    case (User_Commit x10)
    then show ?thesis  using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs TCAbortEmpF_def)
      by (metis status_tm.distinct(9))
  next
    case (TM_Commit x111 x112 x113 x114)
    then show ?thesis  using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs TCAbortEmpF_def)
      by (metis status_tm.distinct(11))
  next
    case (TM_Abort x12a)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs TCAbortEmpF_def)
      by (metis status_km.distinct(35) status_km.distinct(43) status_km.distinct(49)
                  status_km.distinct(53))
  next
    case (TM_ReadyC x13a)
    then show ?thesis  using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs TCAbortEmpF_def)
      by (metis status_tm.distinct(5))
  next
    case (TM_ReadyA x14)
    then show ?thesis  using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs TCAbortEmpF_def)
      by (metis status_tm.distinct(5))
  qed simp
qed


subsection \<open>Refinement from ET_ES to tps\<close>

subsubsection \<open>Mediator function\<close>

fun med :: "'v ev \<Rightarrow> 'v label" where
  "med (TM_Commit cl sn u F) = ET cl sn u F" |
  "med _ = Skip"


subsubsection \<open>Simulation function\<close>

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
    then show ?thesis sorry
  next
    case (Read2 x21 x22 x23)
    then show ?thesis sorry
  next
    case (Prepare x31 x32)
    then show ?thesis sorry
  next
    case (RLock x41 x42)
    then show ?thesis sorry
  next
    case (WLock x51 x52)
    then show ?thesis sorry
  next
    case (NoLock x61 x62)
    then show ?thesis sorry
  next
    case (NOK x71 x72)
    then show ?thesis sorry
  next
    case (Commit x81 x82)
    then show ?thesis sorry
  next
    case (Abort x91 x92)
    then show ?thesis sorry
  next
    case (User_Commit x10)
    then show ?thesis sorry
  next
    case (TM_Commit x111 x112 x113 x114)
    then show ?thesis sorry
  next
    case (TM_Abort x12a)
    then show ?thesis sorry
  next
    case (TM_ReadyC x13a)
    then show ?thesis sorry
  next
    case (TM_ReadyA x14)
    then show ?thesis sorry
  qed simp
qed

definition update_kv_reads_all_txn :: "(txid0 \<Rightarrow> status_tm) \<Rightarrow> (txid0 \<Rightarrow> status_km) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> key_view \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_reads_all_txn tStm tSkm tFk uk vl =
    (let lv = last_version vl uk in
     vl [Max uk :=
       lv \<lparr>v_readerset := (v_readerset lv)
          \<union> {t.\<exists>v. tFk t R = Some v \<and> tStm t = tm_committed \<and> tSkm t \<in> {read_lock, write_lock}}\<rparr>])"

abbreviation the_wr_t :: "(txid0 \<Rightarrow> status_km) \<Rightarrow> txid0" where
  "the_wr_t tSkm \<equiv> (THE t. tSkm t = write_lock)"

definition update_kv_writes_all_txn :: "(txid0 \<Rightarrow> status_tm) \<Rightarrow> (txid0 \<Rightarrow> status_km) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_writes_all_txn tStm tSkm tFk vl =
    (if (\<forall>t. tSkm t \<noteq> write_lock) then
        vl
     else if tStm (the_wr_t tSkm) = tm_committed then
        update_kv_writes (the_wr_t tSkm) (tFk (the_wr_t tSkm)) vl
     else vl)"

definition update_kv_all_txn :: "(txid0 \<Rightarrow> status_tm) \<Rightarrow> (txid0 \<Rightarrow> status_km) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> key_view \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_all_txn tStm tSkm tFk uk =
    (update_kv_writes_all_txn tStm tSkm tFk) o (update_kv_reads_all_txn tStm tSkm tFk uk)"

definition kvs_of_gs :: "'v global_state \<Rightarrow> 'v kv_store" where
  "kvs_of_gs gs k =
   update_kv_all_txn (\<lambda>t. tm_status (tm gs (get_cl_txn t)))
    (km_status (kms gs k)) (km_key_fp (kms gs k)) (full_view (km_vl (kms gs k))) (km_vl (kms gs k))"

fun last_touched_version :: "txid0 \<Rightarrow> 'v v_list \<Rightarrow> v_id" where
  "last_touched_version t [] = 0" |
  "last_touched_version t (x # rest) =
    (if Tn t = v_writer x \<or> t \<in> v_readerset x then length rest else last_touched_version t rest)"

definition cl_last_view :: "cl_id \<Rightarrow> sqn \<Rightarrow> 'v kv_store \<Rightarrow> view" where
  "cl_last_view cl sn K k \<equiv> {..<(last_touched_version (Tn_cl sn cl) (rev (K k)))}"

definition views_of_gs :: "'v global_state \<Rightarrow> (cl_id \<Rightarrow> view)" where
  "views_of_gs gs = (\<lambda>cl.
    (if tm_status (tm gs cl) = tm_committed then
       (\<lambda>k. full_view (kvs_of_gs gs k))
     else cl_last_view cl (tm_sn (tm gs cl)) (\<lambda>k. km_vl (kms gs k)))
    )"

definition sim :: "'v global_state \<Rightarrow> 'v config" where
  "sim gs = (kvs_of_gs gs, views_of_gs gs)"


lemma tps_refines_et_es: "tps \<sqsubseteq>\<^sub>sim ET_ES"
proof (intro simulate_ES_fun_with_invariant[where I="\<lambda>s. TCCommittedTID s \<and> TCCommitEmpF s \<and> TCAbortedTID s \<and> TCAbortEmpF s"])
  fix gs0
  assume p: "init tps gs0"
  then show "init tps1 (sim21 gs0)" using p
    by (auto simp add: tps1_defs tps_defs union_db_def)
next
  fix gs a gs'
  assume p: "tps: gs\<midarrow>a\<rightarrow> gs'"
     and inv: "TCCommittedTID gs \<and> TCCommitEmpF gs \<and> TCAbortedTID gs \<and> TCAbortEmpF gs"
  then show "tps1: sim21 gs\<midarrow>\<pi>21 a\<rightarrow> sim21 gs'"
  proof (cases a)
    case (Write2 k k v)
    then show ?thesis using p inv
      apply (auto simp add: tps_trans_defs tps1_trans_defs union_db_write)
      by (metis other_insts_unchanged_def)
  next
    case (Read2 k k ov)
    then show ?thesis using p inv
      apply (auto simp add: tps_trans_defs tps1_trans_defs)
      apply (metis other_insts_unchanged_def)
      apply (metis other_insts_unchanged_def)
      by (simp add: map_add_def union_db_def)
  next
    case (Prepare k)
    then show ?thesis using p
      apply (auto simp add: tps_trans_defs tps1_trans_defs)
      by (metis other_insts_unchanged_def)+
  next
    case (OK x4)
    then show ?thesis using p
      apply (auto simp add: tps_trans_defs tps1_trans_defs)
      by (metis other_insts_unchanged_def)+
  next
    case (NOK x5)
    then show ?thesis using p
      apply (auto simp add: tps_trans_defs tps1_trans_defs)
      by (metis other_insts_unchanged_def)+
  next
    case (PrepUAbort x6)
    then show ?thesis using p
      apply (auto simp add: tps_trans_defs tps1_trans_defs)
      by (metis other_insts_unchanged_def)+
  next
    case (UAbort2 k)
    then show ?thesis using p
      apply (auto simp add: tps_trans_defs tps1_trans_defs)
      apply (metis other_insts_unchanged_def)
      by (metis other_insts_unchanged_def)
  next
    case (Commit2 k)
    then show ?thesis using p inv
      apply (auto simp add: tps_trans_defs tps1_trans_defs)
      by (smt commit2_def gs_trans.simps(6) map_add_empty
          other_insts_unchanged_def p tps_trans union_db_eq_cases)
  next
    case (Abort2 k)
    then show ?thesis using p
      apply (auto simp add: tps_trans_defs tps1_trans_defs)
      by (metis other_insts_unchanged_def)+
  next
    case (Ready k)
    then show ?thesis using p inv
      apply (auto simp add: tps_trans_defs tps1_trans_defs)
      apply (smt other_insts_unchanged_def union_db_eq_cases)
      by (metis other_insts_unchanged_def)
  next
    case TM_Commit
    then show ?thesis using p
      by (auto simp add: tps_trans_defs tps1_trans_defs map_add_union_db)
  next
    case TM_ReadyC
    then show ?thesis using p inv
      by (auto simp add: tps_trans_defs tps1_trans_defs union_db_def)
  next
    case TM_ReadyA
    then show ?thesis using p inv
      by (auto simp add: tps_trans_defs tps1_trans_defs union_db_def)
  qed (auto simp add: tps_trans_defs tps1_trans_defs)
qed auto


end