section \<open>Two Phase Commit (2PC) with Two Phase Locking (2PL)\<close>

theory Serializable_2PC_2PL
  imports Execution_Tests
begin

subsection \<open>2PC Event system & Refinement from ET_ES to tps\<close>

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

abbreviation get_txn_cl :: "cl_id \<Rightarrow> 'v global_state \<Rightarrow> txid0" where
  "get_txn_cl cl s \<equiv> Tn_cl (tm_sn (tm s cl)) cl"

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

definition prepare where
  "prepare s k s' t \<equiv>
    tm_status (tm s (get_cl_txn t)) = tm_prepared
    \<and> km_status_trans s k s' t working prepared"

definition acquire_rd_lock where \<comment>\<open>Read Lock acquired\<close>
  "acquire_rd_lock s k v s' t \<equiv>
    tm_status (tm s (get_cl_txn t)) = tm_prepared
    \<and> (\<forall>t'. km_status (kms s k) t' \<noteq> write_lock)
    \<and> km_status (kms s k) t = prepared
    \<and> km_vl (kms s' k) = km_vl (kms s k)
    \<and> v = v_value (last_version (km_vl (kms s k)) (full_view (km_vl (kms s k))))
    \<and> km_key_fp (kms s' k) t W = None
    \<and> km_key_fp (kms s' k) t R = Some v
    \<and> km_status (kms s' k) t = read_lock
    \<and> tm_km_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

definition acquire_wr_lock where \<comment>\<open>Write Lock acquired\<close>
  "acquire_wr_lock s k v ov s' t \<equiv>
    tm_status (tm s (get_cl_txn t)) = tm_prepared
    \<and> (\<forall>t'. km_status (kms s k) t' \<notin> {write_lock, read_lock})
    \<and> km_status (kms s k) t = prepared
    \<and> km_vl (kms s' k) = km_vl (kms s k)
    \<and> (ov = None \<or>
       ov = Some (v_value (last_version (km_vl (kms s k)) (full_view (km_vl (kms s k))))))
    \<and> km_key_fp (kms s' k) t W = Some v
    \<and> km_key_fp (kms s' k) t R = ov
    \<and> km_status (kms s' k) t = write_lock
    \<and> tm_km_k'_t'_unchanged k s s' t
    \<and> tid_match s t"

definition acquire_no_lock where \<comment>\<open>No Lock needed\<close>
  "acquire_no_lock s k s' t \<equiv>
    tm_status (tm s (get_cl_txn t)) = tm_prepared
    \<and> km_key_fp (kms s' k) t W = None
    \<and> km_key_fp (kms s' k) t R = None
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
    \<and> tm_view (tm s' cl) = (\<lambda>k. full_view (kvs_of_gs s' k))
    \<and> km_tm_cl'_unchanged cl s s'
    \<and> sn = tm_sn (tm s cl)
    \<and> u = (\<lambda>k. full_view (kvs_of_gs s k))
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


subsubsection \<open>The Event System\<close>

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


subsection \<open>Invariants and lemmas\<close>

(*modified version of expanding_feature3 for all txns read update*)
lemma expanding_feature3':
  assumes "i \<in> full_view vl"
    and "x \<in> v_readerset (vl ! i)"
  shows "x \<in> v_readerset (update_kv_reads_all_txn tStm tSkm tFk vl ! i)"
  using assms
  by (auto simp add: update_kv_reads_all_defs expanding_feature3)

\<comment> \<open>Invariant about future and past transactions kms\<close>

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
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs tid_match_def TIDFutureKm_def)
      subgoal for n k apply (cases "(Tn_cl n x) = x32"; cases "k = x31", auto) done.
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDFutureKm_def)
      by (metis status_km.distinct(1))
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDFutureKm_def)
      by (metis status_km.distinct(1))+
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
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDPastKm_def)
      by (metis status_km.distinct(11) status_km.distinct(13))
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDPastKm_def)
      by (metis status_km.distinct(23) status_km.distinct(25))
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs TIDPastKm_def)
      by (metis status_km.distinct(23) status_km.distinct(25))+
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
      apply (auto simp add: tps_trans_defs tm_unchanged_defs TIDPastKm_def)
        by (metis less_antisym)
  next
    case (TM_ReadyA x14)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs tm_unchanged_defs TIDPastKm_def)
        by (metis less_antisym)
  qed auto
qed

\<comment> \<open>Lock Invariants\<close>

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
    case (Prepare x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockInv_def)
      by (metis status_km.distinct(15) status_km.distinct(17))
  next
    case (RLock x1 x2 x3)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockInv_def)
      by (metis status_km.distinct(27))
  next
    case (WLock x1 x2 x3 x4)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockInv_def)
      by (metis status_km.distinct(27))+
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
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockInv_def)
      by (metis status_km.distinct(17))
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockInv_def)
      by (metis status_km.distinct(27))
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockInv_def)
      by metis+
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

\<comment> \<open>Simulation function lemmas\<close>

lemma the_wr_tI:
  assumes "km_status (kms s k) t = write_lock"
      and "WLockInv s k"
  shows "the_wr_t (km_status (kms s k)) = t"
  using assms
  by blast

lemma update_kv_reads_all_txn_length [simp]:
  "length (update_kv_reads_all_txn tStm tSkm tFk vl) = length vl"
  by (auto simp add: update_kv_reads_all_defs)

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

lemma update_kv_all_txn_length:
  "length (update_kv_all_txn tStm tSkm tFk vl) = length vl \<or>
  length (update_kv_all_txn tStm tSkm tFk vl) = Suc (length vl)"
  apply (auto simp add: update_kv_all_txn_def)
  by (metis update_kv_reads_all_txn_length update_kv_writes_all_txn_length)
  

lemma update_kv_all_txn_length_increasing [simp]:
  "length vl \<le> length (update_kv_all_txn tStm tSkm tFk vl)"
  by (auto simp add: update_kv_all_defs update_kv_writes_def split: option.split)

lemma index_in_longer_kv':
  assumes  "i \<in> full_view (update_kv_all_txn tStm tSkm tFk vl)"
    and "i \<notin> full_view vl"
  shows "length (update_kv_all_txn tStm tSkm tFk vl) = Suc (length vl)"
  using assms
  using full_view_same_length update_kv_all_txn_length by blast

lemma index_in_longer_kv:
  assumes  "i \<in> full_view (update_kv_all_txn tStm tSkm tFk vl)"
    and "i \<notin> full_view vl"
  shows "i = length vl"
  by (metis assms index_in_longer_kv' full_view_def lessThan_iff less_SucE)

lemma update_kv_all_txn_non_empty [simp]:
  assumes "vl \<noteq> []"
  shows "update_kv_all_txn tStm tSkm tFk vl \<noteq> []"
  using assms
  by (metis update_kv_all_txn_length_increasing le_zero_eq length_0_conv)

lemma read_only_update [simp]:
  assumes "\<forall>t. km_status (kms s k) t \<noteq> write_lock"
  shows "update_kv_all_txn tStm (km_status (kms s k)) tFk vl =
         update_kv_reads_all_txn tStm (km_status (kms s k)) tFk vl"
  using assms
  by (auto simp add: update_kv_all_txn_def update_kv_writes_all_txn_def)

lemma read_only_update':
  assumes "RLockInv s k"
    and "km_status (kms s k) t = read_lock"
  shows "update_kv_all_txn tStm (km_status (kms s k)) tFk vl =
         update_kv_reads_all_txn tStm (km_status (kms s k)) tFk vl"
  using assms
  by (meson RLockInv_def read_only_update)

lemma writer_update_before:
  assumes "WLockInv s k"
    and "tm_status (tm s cl) = tm_prepared"
    and "km_status (kms s k) (get_txn_cl cl s) = write_lock"
  shows "update_kv_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k)) tFk vl =
         update_kv_reads_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k)) tFk vl"
  using assms
  apply (auto simp add: update_kv_all_txn_def update_kv_writes_all_txn_def update_kv_writes_def
      WLockInv_def split: option.split)
  by (metis get_cl_txn.simps status_tm.distinct(7))


\<comment> \<open>lemmas for unchanged elements in kms\<close>

lemma km_vl_eq_all_k:
  assumes "km_vl (kms s' k) = km_vl (kms s k)"
    and "other_insts_unchanged k (kms s) (kms s')"
  shows "\<forall>k. km_vl (kms s' k) = km_vl (kms s k)"
  using assms by (auto simp add: other_insts_unchanged_def)

lemma eq_for_all_k: 
  assumes "f (kms s' k) t = f (kms s k) t"
    and " \<forall>k'. k' \<noteq> k \<longrightarrow> kms s' k' = kms s k'"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> f (kms s' k) t' = f (kms s k) t'"
  shows "\<forall>k. f (kms s' k) = f (kms s k)"
  apply (auto simp add: fun_eq_iff) using assms
  subgoal for k' t' by (cases "k' = k"; cases "t' = t"; simp).

lemma eq_for_all_cl:
  assumes "f (tm s' cl) = f (tm s cl)"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> tm s' cl' = tm s cl'"
  shows "\<forall>cl. f (tm s' cl) = f (tm s cl)"
  apply (auto simp add: fun_eq_iff) using assms
  subgoal for cl' by (cases "cl' = cl"; simp).

lemma other_sn_idle:  
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "get_cl_txn t = cl" and "get_sn_txn t \<noteq> tm_sn (tm s cl)"
  shows "\<forall>k. km_status (kms s k) t \<in> {working, committed, aborted}"
  using assms
  apply (auto simp add: TIDFutureKm_def TIDPastKm_def)
  apply (cases "get_sn_txn t > tm_sn (tm s cl)")
  apply (metis get_cl_txn.simps get_sn_txn.elims)
  by (metis get_cl_txn.elims get_sn_txn.simps nat_neq_iff)

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
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpInv_def)
      by (metis status_km.distinct(15))+
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpInv_def)
      by metis+
  next
    case (WLock x51 x52 x53 x54)
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
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpInv_def)
      by (metis status_km.distinct(17))
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpInv_def)
      by (metis status_km.distinct(27))
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpInv_def)
      by metis+
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
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs NoLockFpInv_def)
      by (metis status_km.distinct(19))+
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs NoLockFpInv_def)
      by (metis status_km.distinct(29))+
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs NoLockFpInv_def)
      apply (metis status_km.distinct(37), metis)
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

lemma the_wr_t_fp:
  assumes "\<forall>k. WLockInv s k"
    and "\<forall>k. WLockFpInv s k"
    and "km_status (kms s k) t = write_lock"
  shows "km_key_fp (kms s k) (the_wr_t (km_status (kms s k))) W \<noteq> None"
  using assms by (auto simp add: WLockInv_def WLockFpInv_def the_wr_tI)

\<comment> \<open>Invariants about kv store\<close>
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
  qed (auto simp add: KVSNonEmp_def tps_trans_defs unchanged_defs dest!: km_vl_eq_all_k)
qed

definition KVSGSNonEmp where
  "KVSGSNonEmp s \<longleftrightarrow> (\<forall>k. kvs_of_gs s k \<noteq> [])"

lemmas KVSGSNonEmpI = KVSGSNonEmp_def[THEN iffD2, rule_format]
lemmas KVSGSNonEmpE[elim] = KVSGSNonEmp_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_gs_non_emp [simp, intro]:
  assumes "reach tps s"
    and "KVSNonEmp s"
  shows "KVSGSNonEmp s"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: KVSGSNonEmp_def kvs_of_gs_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: KVSGSNonEmp_def tps_trans_defs kvs_of_gs_def unchanged_defs)
qed

definition KVSLen where
  "KVSLen s cl \<longleftrightarrow> (\<forall>k. length (km_vl (kms s k)) \<le> length (kvs_of_gs s k))"

lemmas KVSLenI = KVSLen_def[THEN iffD2, rule_format]
lemmas KVSLenE[elim] = KVSLen_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_len [simp, intro]: "reach tps s \<Longrightarrow> KVSLen s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: KVSLen_def tps_defs kvs_of_gs_def update_kv_all_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: KVSLen_def kvs_of_gs_def)
qed

subsubsection \<open>Lemmas for kvs_of_gs changing by different events\<close>

(*KM events*)

\<comment> \<open>eligible reads and read updates\<close>
lemma eligible_reads_km_inv:
  assumes "RLockInv s k"
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
  assumes "RLockFpInv s k"
    and "km_status (kms s k) t = read_lock"
    and "tm_status (tm s (get_cl_txn t)) = tm_committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "{t. eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
            (km_key_fp (kms s k)) t} =
          insert t {t. eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s' k))
            (km_key_fp (kms s k)) t}"
  using assms by (auto simp add: km_unchanged_defs)

lemma eligible_reads_write_lock_s_the_t:
  assumes "RLockInv s k" and "WLockInv s k"
    and "km_status (kms s k) t = write_lock"
    and "tm_status (tm s (get_cl_txn t)) = tm_committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "{t. eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
            (km_key_fp (kms s k)) t} =
         (case (km_key_fp (kms s k) t R) of None \<Rightarrow> {} | Some y \<Rightarrow> {t})"
  using assms
  apply (auto intro: Collect_empty_eq split: option.split)
  subgoal for t' by (cases "t' = t"; auto simp add: RLockInv_def WLockInv_def km_unchanged_defs).

lemma update_kv_reads_commit_w_s_inv:
  assumes "RLockInv s k" and "WLockInv s k"
    and "km_status (kms s k) t = write_lock"
    and "tm_status (tm s (get_cl_txn t)) = tm_committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "update_kv_reads_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) 
                (km_status (kms s k)) (km_key_fp (kms s k)) vl =
        (case (km_key_fp (kms s k) t R) of None \<Rightarrow> vl | Some y \<Rightarrow> 
          vl[Max (full_view vl) := last_version vl (full_view vl)
                \<lparr>v_readerset := v_readerset (last_version vl (full_view vl)) \<union> {t}\<rparr>])"
  using assms eligible_reads_write_lock_s_the_t[of s k t s']
  by (auto simp add: update_kv_reads_all_defs split: option.split)

lemma eligible_reads_write_lock_s'_empty:
  assumes "RLockInv s k" and "WLockInv s k"
    and "km_status (kms s k) t = write_lock"
    and "km_status (kms s' k) t = committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "{t. eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s' k))
            (km_key_fp (kms s k)) t} = {}"
  using assms
  apply (auto intro: Collect_empty_eq)
  subgoal for t' by (cases "t' = t"; auto simp add: RLockInv_def WLockInv_def km_unchanged_defs)
  subgoal for t' by (cases "t' = t"; auto simp add: RLockInv_def WLockInv_def km_unchanged_defs).

lemma update_kv_reads_commit_w_s'_inv:
  assumes "RLockInv s k" and "WLockInv s k"
    and "km_status (kms s k) t = write_lock"
    and "km_status (kms s' k) t = committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "update_kv_reads_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s' k))
    (km_key_fp (kms s k)) vl = vl"
  using assms eligible_reads_write_lock_s'_empty[of s k t s']
  unfolding update_kv_reads_all_defs
  by (metis (lifting) last_version_def none_eligible version.unfold_congs(3))

lemma eligible_reads_no_lock_inv:
  assumes "km_status (kms s k) t = no_lock"
    and "km_status (kms s' k) t = committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "
  eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s' k)) (km_key_fp (kms s k)) t' =
  eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k)) (km_key_fp (kms s k)) t'"
  using assms apply (auto simp add: km_unchanged_defs)
  apply (metis status_km.distinct(33))
  apply (metis status_km.distinct(41))
  apply (metis status_km.distinct(29))
  by (metis status_km.distinct(37))

\<comment> \<open>write updates\<close>
lemma update_kv_writes_km_inv:
  assumes "WLockInv s k"
    and "(\<forall>t. km_status (kms s k) t \<noteq> write_lock) \<or> 
              km_status (kms s' k) t \<noteq> write_lock"
    and "tm_status (tm s (get_cl_txn t)) \<noteq> tm_committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "update_kv_writes_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t)))
                (km_status (kms s' k')) (km_key_fp (kms s' k')) vl =
               update_kv_writes_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t)))
                (km_status (kms s k')) (km_key_fp (kms s k')) vl"
  using assms apply (auto simp add: update_kv_writes_all_txn_def)
  apply (cases "k' = k"; simp add: km_unchanged_defs)
  subgoal for t' by (cases "k' = k"; cases "t' = t"; simp add: km_unchanged_defs)
  apply (cases "k' = k"; simp add: km_unchanged_defs)
  apply (cases "k' = k", simp_all add: km_unchanged_defs, smt (verit) WLockInv_def theI)
  subgoal for t' by (cases "k' = k"; cases "t' = t"; simp add: km_unchanged_defs the_wr_tI)
  by (cases "k' = k"; auto simp add: km_unchanged_defs the_wr_tI)

lemma update_kv_writes_commit_r_inv:
  assumes "RLockInv s k"
    and "km_status (kms s k) t = read_lock"
    and "km_status (kms s' k) t = committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "update_kv_writes_all_txn tStm (km_status (kms s' k)) (km_key_fp (kms s k)) vl = 
         update_kv_writes_all_txn tStm (km_status (kms s k)) (km_key_fp (kms s k)) vl"
  using assms apply (auto simp add: update_kv_writes_all_txn_def km_unchanged_defs)
  by (metis status_km.distinct(41))

lemma update_kv_writes_commit_w_s_inv:
  assumes "WLockInv s k"
    and "km_status (kms s k) t = write_lock"
    and "tm_status (tm s (get_cl_txn t)) = tm_committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "update_kv_writes_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
           (km_key_fp (kms s k)) vl = update_kv_writes t (km_key_fp (kms s k) t) vl"
  using assms apply (auto simp add: update_kv_writes_all_txn_def)
  using the_wr_tI by blast

lemma update_kv_writes_commit_w_s'_inv:
  assumes "WLockInv s k"
    and "km_status (kms s k) t = write_lock"
    and "km_status (kms s' k) t = committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "update_kv_writes_all_txn tStm (km_status (kms s' k)) (km_key_fp (kms s k)) vl = vl"
  using assms apply (auto simp add: update_kv_writes_all_txn_def km_unchanged_defs)
  by (metis status_km.distinct(41) the_wr_tI)

lemma update_kv_writes_commit_n_inv:
  assumes "WLockInv s k"
    and "km_status (kms s k) t = no_lock"
    and "km_status (kms s' k) t = committed"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "update_kv_writes_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s' k))
           (km_key_fp (kms s k)) vl =
         update_kv_writes_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
           (km_key_fp (kms s k)) vl"
  using assms apply (auto simp add: update_kv_writes_all_txn_def)
  subgoal for t' apply (cases "t' = t"; simp add: km_unchanged_defs)
    by (smt (verit) status_km.distinct(41) theI the_wr_tI)
  subgoal for t' by (cases "t' = t"; simp add: km_unchanged_defs the_wr_tI)
  subgoal for t' by (cases "t' = t"; auto simp add: km_unchanged_defs the_wr_tI).

\<comment> \<open>kvs_of_gs\<close>
lemma kvs_of_gs_km_inv:
  assumes "WLockInv s k" and "RLockInv s k"
    and "(\<forall>t. km_status (kms s k) t \<noteq> write_lock) \<or> 
              km_status (kms s' k) t \<noteq> write_lock"
    and "tm_status (tm s (get_cl_txn t)) \<noteq> tm_committed"
    and "\<forall>k. km_vl (kms s' k) = km_vl (kms s k)"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "kvs_of_gs s' = kvs_of_gs s"
  using assms apply (auto simp add: kvs_of_gs_def del: disjE) apply (rule ext)
  subgoal for k' using eligible_reads_km_inv[of s k t s'] update_kv_writes_km_inv
  by (cases "k' = k"; simp add: update_kv_all_txn_def update_kv_reads_all_txn_def km_unchanged_defs).

(*TM events*)
\<comment> \<open>eligible reads\<close>
lemma eligible_reads_tm_inv:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "tm_status (tm s cl) \<noteq> tm_committed \<or>
         (\<forall>k. km_status (kms s k) (get_txn_cl cl s) = committed)"
    and "tm_status (tm s' cl) \<noteq> tm_committed"
    and "km_tm_cl'_unchanged cl s s'"
  shows "
  eligible_reads (\<lambda>t. tm_status (tm s' (get_cl_txn t))) (km_status (kms s k)) (km_key_fp (kms s k)) t =
  eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k)) (km_key_fp (kms s k)) t"
  using assms apply (auto simp add: update_kv_writes_all_txn_def tm_unchanged_defs)
  subgoal
    apply (cases "get_cl_txn t = cl"; cases "get_sn_txn t = tm_sn (tm s cl)";
            simp add: tm_unchanged_defs)
    apply (metis get_cl_txn.elims get_sn_txn.simps status_km.distinct(33))
    by (metis empty_iff insert_iff other_sn_idle status_km.distinct(3)
        status_km.distinct(33) status_km.distinct(35))
  subgoal
    apply (cases "get_cl_txn t = cl"; cases "get_sn_txn t = tm_sn (tm s cl)";
            simp add: tm_unchanged_defs)
    apply (metis get_cl_txn.elims get_sn_txn.simps status_km.distinct(41))
    by (metis empty_iff insert_iff other_sn_idle status_km.distinct(41)
        status_km.distinct(43) status_km.distinct(5))
  done

lemma eligible_reads_tm_commit_no_lock_inv:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "other_insts_unchanged cl (tm s) (tm s')"
    and "km_status (kms s k) (get_txn_cl cl s) = no_lock"
  shows "
  eligible_reads (\<lambda>t. tm_status (tm s' (get_cl_txn t))) (km_status (kms s k)) (km_key_fp (kms s k)) t =
  eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k)) (km_key_fp (kms s k)) t"
  using assms apply (cases "get_cl_txn t = cl"; simp add: other_insts_unchanged_def)
  by (metis empty_iff get_cl_txn.simps get_sn_txn.elims insert_iff other_sn_idle
      status_km.distinct(29) status_km.distinct(3) status_km.distinct(33) status_km.distinct(35)
      status_km.distinct(37) status_km.distinct(41) status_km.distinct(43) status_km.distinct(5))

\<comment> \<open>write updates\<close>
lemma update_kv_writes_tm_inv:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "tm_status (tm s cl) \<noteq> tm_committed \<or>
         (\<forall>k. km_status (kms s k) (get_txn_cl cl s) = committed)"
    and "tm_status (tm s' cl) \<noteq> tm_committed"
    and "km_tm_cl'_unchanged cl s s'"
  shows "update_kv_writes_all_txn (\<lambda>t. tm_status (tm s' (get_cl_txn t)))
                (km_status (kms s k)) (km_key_fp (kms s k)) vl =
               update_kv_writes_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t)))
                (km_status (kms s k)) (km_key_fp (kms s k)) vl"
  using assms apply (auto simp add: update_kv_writes_all_txn_def tm_unchanged_defs)
  subgoal for t
    apply (cases "get_cl_txn t = cl"; cases "get_sn_txn t = tm_sn (tm s cl)"; simp)
    apply (metis get_cl_txn.elims get_sn_txn.simps status_km.distinct(41))
    by (metis ex_in_conv insertE other_sn_idle status_km.distinct(41)
        status_km.distinct(43) status_km.distinct(5)).

\<comment> \<open>kvs_of_gs\<close>
lemma kvs_of_gs_tm_inv:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "tm_status (tm s cl) \<noteq> tm_committed \<or>
         (\<forall>k. km_status (kms s k) (get_txn_cl cl s) = committed)"
    and "tm_status (tm s' cl) \<noteq> tm_committed"
    and "km_tm_cl'_unchanged cl s s'"
  shows "kvs_of_gs s' = kvs_of_gs s"
  using assms
  apply (simp add: kvs_of_gs_def) apply (rule ext)
  using update_kv_writes_tm_inv[of s] eligible_reads_tm_inv[of s cl s']
  by (auto simp add: update_kv_all_txn_def update_kv_reads_all_txn_def tm_unchanged_defs)

lemma update_kv_all_tm_commit_no_lock_inv:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "other_insts_unchanged cl (tm s) (tm s')"
    and "km_status (kms s k) (get_txn_cl cl s) = no_lock"
  shows "update_kv_all_txn (\<lambda>t. tm_status (tm s' (get_cl_txn t))) (km_status (kms s k))
          (km_key_fp (kms s k)) (km_vl (kms s k)) =
         update_kv_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
          (km_key_fp (kms s k)) (km_vl (kms s k))"
  using assms eligible_reads_tm_commit_no_lock_inv[of s cl s' k]
  apply (auto simp add: NoLockFpInv_def update_kv_all_defs other_insts_unchanged_def)
  apply (metis (mono_tags, lifting) get_cl_txn.simps get_sn_txn.cases get_sn_txn.simps
      insert_compr mem_Collect_eq other_sn_idle singleton_conv2 status_km.distinct(37)
      status_km.distinct(41) status_km.distinct(43) status_km.distinct(5))
  by metis

(*All events*)
abbreviation not_tm_commit where
  "not_tm_commit e \<equiv> \<forall>cl sn u F. e \<noteq> TM_Commit cl sn u F"

lemma kvs_of_gs_inv:
  assumes "gs_trans s e s'"
    and inv: "\<forall>cl k. TIDFutureKm s cl \<and> TIDPastKm s cl \<and> RLockInv s k \<and> WLockInv s k \<and>
                      RLockFpInv s k \<and> NoLockFpInv s k \<and> KVSNonEmp s"
    and "not_tm_commit e"
  shows "kvs_of_gs s' = kvs_of_gs s"
  using assms
  proof (induction e)
    case (Prepare x1 x2)
    then show ?case using kvs_of_gs_km_inv[of s x1 s' x2]
      by (auto simp add: tps_trans_defs km_unchanged_defs dest!: km_vl_eq_all_k)
  next
    case (RLock x1 x2 x3)
    then show ?case using kvs_of_gs_km_inv[of s x1 s' x3]
      by (auto simp add: tps_trans_defs km_unchanged_defs dest!: km_vl_eq_all_k)
  next
    case (WLock x1 x2 x3 x4)
    then show ?case using kvs_of_gs_km_inv[of s x1 s' x4]
      by (auto simp add: tps_trans_defs km_unchanged_defs dest!: km_vl_eq_all_k)
  next
    case (NoLock x1 x2)
    then show ?case using kvs_of_gs_km_inv[of s x1 s' x2]
      by (auto simp add: tps_trans_defs km_unchanged_defs dest!: km_vl_eq_all_k)
  next
    case (NOK x1 x2)
    then show ?case using kvs_of_gs_km_inv[of s x1 s' x2]
      by (auto simp add: tps_trans_defs km_unchanged_defs dest!: km_vl_eq_all_k)
  next
    case (Commit x1 x2)
    hence u: "kvs_of_gs s' x1 = kvs_of_gs s x1"
      apply (auto simp add: kvs_of_gs_def commit_def)
      subgoal
        using eligible_reads_read_lock_inv[of s x1 x2 s']
              update_kv_writes_commit_r_inv[of s x1 x2 s']
        by (auto simp add: update_kv_all_txn_def update_kv_reads_all_txn_def Let_def
            RLockFpInv_def KVSNonEmp_def km_unchanged_defs update_kv_key_ro_set_v_readerset
            dest!: eq_for_all_k)
      subgoal
        using update_kv_reads_commit_w_s_inv[of s x1 x2 s']
              update_kv_reads_commit_w_s'_inv[of s x1 x2 s']
              update_kv_writes_commit_w_s_inv[of s x1 x2 s']
              update_kv_writes_commit_w_s'_inv[of s x1 x2 s']
        by (auto simp add: update_kv_all_txn_def update_kv_key_def update_kv_reads_defs
            km_unchanged_defs dest!: eq_for_all_k split: option.split)
      subgoal
        using eligible_reads_no_lock_inv[of s x1 x2 s']
        using update_kv_writes_commit_n_inv[of s x1 x2 s']
        by (auto simp add: update_kv_all_txn_def update_kv_reads_all_txn_def
            NoLockFpInv_def km_unchanged_defs dest!: eq_for_all_k) done
    hence "\<forall>k. k \<noteq> x1 \<longrightarrow> kvs_of_gs s' k = kvs_of_gs s k" using Commit
      by (auto simp add: commit_def km_unchanged_defs kvs_of_gs_def)
    then show ?case using u by auto
  next
    case (Abort x1 x2)
    then show ?case using kvs_of_gs_km_inv[of s x1 s' x2]
      by (auto simp add: tps_trans_defs km_unchanged_defs dest!: km_vl_eq_all_k)
  next
    case (User_Commit x)
    then show ?case using kvs_of_gs_tm_inv[of s x s']
     by (auto simp add: tps_trans_defs tm_unchanged_defs)
  next
    case (TM_Abort x)
    then show ?case using kvs_of_gs_tm_inv[of s x s']
     by (auto simp add: tps_trans_defs tm_unchanged_defs)
  next
    case (TM_ReadyC x)
    then show ?case using kvs_of_gs_tm_inv[of s x s']
     by (auto simp add: tps_trans_defs tm_unchanged_defs)
  next
    case (TM_ReadyA x)
    then show ?case using kvs_of_gs_tm_inv[of s x s']
     by (auto simp add: tps_trans_defs tm_unchanged_defs)
 qed auto

\<comment> \<open>More specific lemmas about TM commit\<close>
lemma kvs_of_gs_commit_length_increasing:
  assumes "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "km_tm_cl'_unchanged cl s s'"
  shows "length (kvs_of_gs s k) \<le> length (kvs_of_gs s' k)"
  using assms
  apply (auto simp add: kvs_of_gs_def tm_unchanged_defs update_kv_all_txn_def
      update_kv_writes_all_txn_def update_kv_writes_on_diff_len)
  by (metis (no_types, lifting) update_kv_reads_all_txn_length update_kv_writes_length_increasing)

lemma kvs_of_gs_length_increasing:
  assumes "gs_trans s e s'"
    and "\<forall>cl. TIDFutureKm s cl" and "\<forall>cl. TIDPastKm s cl"
    and "\<forall>k. RLockInv s k" and "\<forall>k. WLockInv s k"
    and "\<forall>k. RLockFpInv s k" and "\<forall>k. NoLockFpInv s k"
    and "KVSNonEmp s"
  shows "\<forall>k. length (kvs_of_gs s k) \<le> length (kvs_of_gs s' k)"
  using assms
  apply (cases "not_tm_commit e"; simp add: kvs_of_gs_inv)
  apply auto apply (simp add: tm_commit_def) by (auto dest!: kvs_of_gs_commit_length_increasing)

lemma tm_commit_expands_eligible_reads:
  assumes "tm_status (tm s' cl) = tm_committed"
    and "other_insts_unchanged cl (tm s) (tm s')"
  shows
  "{t. eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k)) (km_key_fp (kms s k)) t} \<subseteq>
   {t. eligible_reads (\<lambda>t. tm_status (tm s' (get_cl_txn t))) (km_status (kms s k)) (km_key_fp (kms s k)) t}"
  using assms by (auto simp add: other_insts_unchanged_def)

lemma tm_commit_expands_eligible_reads':
  assumes "NoLockFpInv s k" and "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock}"
    and "other_insts_unchanged cl (tm s) (tm s')"
  shows "{x. eligible_reads (\<lambda>t. tm_status (tm s' (get_cl_txn t))) (km_status (kms s k))
    (km_key_fp (kms s k)) x} = (case km_key_fp (kms s k) (get_txn_cl cl s) R of
   None \<Rightarrow> {x. eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
     (km_key_fp (kms s k)) x}|
   Some _ \<Rightarrow> insert (get_txn_cl cl s) {x. eligible_reads (\<lambda>t. tm_status (tm s (get_cl_txn t)))
     (km_status (kms s k)) (km_key_fp (kms s k)) x})"
  using assms
  apply (auto simp add: other_insts_unchanged_def NoLockFpInv_def split: option.split del: disjE)
  subgoal for t apply (cases "get_cl_txn t = cl"; cases "get_sn_txn t = tm_sn (tm s cl)"; simp)
    apply (metis get_cl_txn.elims get_sn_txn.simps option.distinct(1))
    by (metis emptyE insert_iff other_sn_idle status_km.distinct(3) status_km.distinct(33)
        status_km.distinct(35) status_km.distinct(41) status_km.distinct(43) status_km.distinct(5))
  subgoal for v t apply (cases "get_cl_txn t = cl"; cases "get_sn_txn t = tm_sn (tm s cl)"; simp)
    apply (metis get_cl_txn.elims get_sn_txn.simps)
    by (metis empty_iff insertE other_sn_idle status_km.distinct(3) status_km.distinct(33)
        status_km.distinct(35) status_km.distinct(41) status_km.distinct(43) status_km.distinct(5))
  by auto
  
lemma tm_commit_updates_kv_reads:
  assumes "KVSNonEmp s"
    and "tm_status (tm s' cl) = tm_committed"
    and "other_insts_unchanged cl (tm s) (tm s')"
  shows
  "update_kv_reads_all_txn (\<lambda>t. tm_status (tm s' (get_cl_txn t))) (km_status (kms s k))
      (km_key_fp (kms s k)) (km_vl (kms s k)) = 
   update_kv_reads_all_txn (\<lambda>t. tm_status (tm s' (get_cl_txn t))) (km_status (kms s k))
      (km_key_fp (kms s k))
        (update_kv_reads_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
          (km_key_fp (kms s k)) (km_vl (kms s k)))"
  using assms tm_commit_expands_eligible_reads[of s' cl s k]
  by (auto simp add: update_kv_reads_all_defs Un_assoc subset_Un_eq)

lemma tm_commit_updates_kv_reads':
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "KVSNonEmp s" and "NoLockFpInv s k"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock}"
    and "other_insts_unchanged cl (tm s) (tm s')"
  shows
  "update_kv_reads_all_txn (\<lambda>t. tm_status (tm s' (get_cl_txn t))) (km_status (kms s k))
      (km_key_fp (kms s k)) (km_vl (kms s k)) = 
   update_kv_reads (get_txn_cl cl s) (km_key_fp (kms s k) (get_txn_cl cl s))
     (full_view (update_kv_reads_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
          (km_key_fp (kms s k)) (km_vl (kms s k))))
        (update_kv_reads_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
          (km_key_fp (kms s k)) (km_vl (kms s k)))"
  using assms tm_commit_expands_eligible_reads'[of s k cl s']
  by (auto simp add: update_kv_reads_all_txn_def update_kv_reads_defs
      del:disjE split: option.split)

lemma tm_commit_writer_update_kv_all:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "WLockInv s k" and "RLockInv s k"
    and "NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock}"
    and "other_insts_unchanged cl (tm s) (tm s')"
  shows
  "update_kv_all_txn (\<lambda>t. tm_status (tm s' (get_cl_txn t))) (km_status (kms s k))
      (km_key_fp (kms s k)) (km_vl (kms s k)) = 
   update_kv_all_txn (\<lambda>t. tm_status (tm s' (get_cl_txn t))) (km_status (kms s k))
      (km_key_fp (kms s k))
        (update_kv_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
          (km_key_fp (kms s k)) (km_vl (kms s k)))"
  using assms apply auto
  subgoal apply (simp add: read_only_update')
    using tm_commit_updates_kv_reads by blast
  subgoal apply (simp add: writer_update_before)
    by (auto simp add: update_kv_all_txn_def tm_commit_updates_kv_reads[of s s' cl k])
  done

\<comment> \<open>Fingerprint content invariant and Lemmas for proving the fp_property\<close>

lemma km_vl_read_lock_commit_eq_length:
  assumes "RLockFpInv s k"
    and "km_status (kms s k) t = read_lock"
    and "km_vl (kms s' k) =
          update_kv_key t (km_key_fp (kms s k) t) (full_view (km_vl (kms s k))) (km_vl (kms s k))"
  shows "length (km_vl (kms s' k)) = length (km_vl (kms s k))"
  using assms
  apply (auto simp add: RLockFpInv_def)
  by (metis update_kv_writes_key_decides_length update_kv_writes_none_length)

lemma km_vl_read_commit_eq_lv:
  assumes "RLockFpInv s k"
    and "km_status (kms s k) t = read_lock"
    and "km_status (kms s' k) t = committed"
    and "km_vl (kms s' k) =
          update_kv_key t (km_key_fp (kms s k) t) (full_view (km_vl (kms s k))) (km_vl (kms s k))"
  shows "v_value (last_version (km_vl (kms s' k)) (full_view (km_vl (kms s' k)))) =
         v_value (last_version (km_vl (kms s k)) (full_view (km_vl (kms s k))))"
  using assms km_vl_read_lock_commit_eq_length[of s k t s']
  apply (auto simp add: last_version_def)
  by (metis full_view_def max_in_full_view update_kv_key_v_value_inv)

definition RLockFpContentInv where
  "RLockFpContentInv s k \<longleftrightarrow> (\<forall>t. km_status (kms s k) t = read_lock \<longrightarrow>
    km_key_fp (kms s k) t R =
      Some (v_value (last_version (km_vl (kms s k)) (full_view (km_vl (kms s k))))))"

lemmas RLockFpContentInvI = RLockFpContentInv_def[THEN iffD2, rule_format]
lemmas RLockFpContentInvE[elim] = RLockFpContentInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_rlockfp_content [simp, intro]: "reach tps s \<Longrightarrow> RLockFpContentInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: RLockFpContentInv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpContentInv_def)
      by (metis status_km.distinct(15))+
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpContentInv_def)
      by metis+
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpContentInv_def)
      by (metis status_km.distinct(27))+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpContentInv_def)
      by (metis status_km.distinct(29))+
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpContentInv_def)
      by (metis status_km.distinct(31))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans km_vl_read_commit_eq_lv[of s x81 x82 s']
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpContentInv_def del: disjE)
      by (metis NoLockFpInv_def RLockInv_def reach_nolockfp reach_rlock status_km.distinct(33)
          update_kv_key_empty_fp)
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs RLockFpContentInv_def)
      by (metis status_km.distinct(35))+
  qed (auto simp add: tps_trans_defs tm_unchanged_defs RLockFpContentInv_def)
qed

definition WLockFpContentInv where
  "WLockFpContentInv s k \<longleftrightarrow> (\<forall>t. km_status (kms s k) t = write_lock \<longrightarrow>
    km_key_fp (kms s k) t R = None \<or>
    km_key_fp (kms s k) t R =
      Some (v_value (last_version (km_vl (kms s k)) (full_view (km_vl (kms s k))))))"

lemmas WLockFpContentInvI = WLockFpContentInv_def[THEN iffD2, rule_format]
lemmas WLockFpContentInvE[elim] = WLockFpContentInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_wlockfp_content [simp, intro]: "reach tps s \<Longrightarrow> WLockFpContentInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: WLockFpContentInv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpContentInv_def)
      by (metis status_km.distinct(17))
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpContentInv_def)
      by (metis status_km.distinct(27))
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpContentInv_def)
      by metis+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpContentInv_def)
      by (metis status_km.distinct(37))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpContentInv_def)
      by (metis status_km.distinct(39))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpContentInv_def)
      apply (metis RLockInv_def reach_rlock status_km.distinct(41))
      apply (smt reach_wlock status_km.distinct(41) the_wr_tI)
      by (metis NoLockFpInv_def reach_nolockfp update_kv_key_empty_fp)
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs km_unchanged_defs WLockFpContentInv_def)
      by (metis status_km.distinct(43))+
  qed (auto simp add: tps_trans_defs tm_unchanged_defs WLockFpContentInv_def)
qed

lemma update_kv_all_txn_v_value_inv:
  assumes "i \<in> full_view vl"
  shows "v_value (update_kv_all_txn tStm tSkm tFk vl ! i) = v_value (vl ! i)"
  using assms update_kv_writes_version_inv
  by (auto simp add: update_kv_all_defs update_kv_writes_def nth_append full_view_def
      split: option.split)

lemma km_vl_kvs_eq_length:
  assumes "WLockInv s k" and "RLockInv s k"
    and "tm_status (tm s cl) = tm_prepared"
    and "km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock}"
  shows "length (kvs_of_gs s k) = length (km_vl (kms s k))"
  using assms
  apply (auto simp add: WLockInv_def RLockInv_def kvs_of_gs_def)
  by (metis assms(1) update_kv_reads_all_txn_length writer_update_before)

lemma km_vl_kvs_eq_lv:
  assumes "WLockInv s k" and "RLockInv s k" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock}"
  shows "v_value (last_version (kvs_of_gs s k) (full_view (kvs_of_gs s k))) =
         v_value (last_version (km_vl (kms s k)) (full_view (km_vl (kms s k))))"
  using assms km_vl_kvs_eq_length[of s]
    update_kv_all_txn_v_value_inv[of "Max {..<length (km_vl (kms s k))}" "km_vl (kms s k)"]
  apply (auto simp add: full_view_def last_version_def kvs_of_gs_def KVSNonEmp_def)
  apply (metis full_view_def lessThan_iff max_in_full_view)
  by (metis full_view_def lessThan_iff max_in_full_view)

\<comment> \<open>Lemmas for view growth after commit\<close>

lemma committed_kvs_view_grows:
  assumes "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "km_tm_cl'_unchanged cl s s'"
  shows "(\<lambda>k. full_view (kvs_of_gs s k)) \<sqsubseteq> (\<lambda>k. full_view (kvs_of_gs s' k))"
  using assms
  by (metis view_order_full_view_increasing kvs_of_gs_commit_length_increasing)
  
lemma updated_vl_view_grows:
  assumes "km_vl (kms s' k) =
    update_kv_key t (km_key_fp (kms s k) t) (full_view (km_vl (kms s k))) (km_vl (kms s k))"
    and "other_insts_unchanged k (kms s) (kms s')"
  shows "(\<lambda>k. full_view (km_vl (kms s k))) \<sqsubseteq> (\<lambda>k. full_view (km_vl (kms s' k)))"
  using assms update_kv_key_length_increasing[of "km_vl (kms s k)" t "km_key_fp (kms s k) t"
      "full_view (km_vl (kms s k))"]
  apply (auto simp add: view_order_def other_insts_unchanged_def)
  subgoal for k' x by (cases "k' = k"; auto simp add: full_view_length_increasing).

lemma tm_view_inv:
  assumes "gs_trans s e s'"
    and "not_tm_commit e"
  shows "tm_view (tm s' cl) = tm_view (tm s cl)"
  using assms by (induction e) (auto simp add: tps_trans_defs unchanged_defs dest!:eq_for_all_cl)

definition TMFullView where
  "TMFullView s cl \<longleftrightarrow> tm_view (tm s cl) \<sqsubseteq> (\<lambda>k. full_view (kvs_of_gs s k))"

lemmas TMFullViewI = TMFullView_def[THEN iffD2, rule_format]
lemmas TMFullViewE[elim] = TMFullView_def[THEN iffD1, elim_format, rule_format]

lemma reach_tm_full_view [simp, intro]:
  assumes "reach tps s"
    and "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<forall>k. RLockInv s k" and "\<forall>k. WLockInv s k"
    and "\<forall>k. RLockFpInv s k" and "\<forall>k. NoLockFpInv s k"
    and "KVSNonEmp s" and " KVSLen s cl"
  shows "TMFullView s cl"
  using assms
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: TMFullView_def tps_defs full_view_def view_order_def
        view_init_def kvs_of_gs_def)
next
  case (reach_trans s e s')
  then show ?case apply (cases "not_tm_commit e") using kvs_of_gs_inv[of s e s']
     apply (auto simp add: TMFullView_def unchanged_defs tm_view_inv)
    subgoal for cl' using committed_kvs_view_grows[of s]
      apply (auto simp add: TMFullView_def tps_trans_defs tm_unchanged_defs)
      apply (cases "cl = cl'"; simp) by (meson view_order_transitive).
qed

\<comment> \<open>TM_commit updating kv\<close>

lemma or3_not_eq:
  assumes "\<forall>k. P k = a \<or> P k = b \<or> P k = c"
    and "P k \<noteq> c"
  shows "P k = a \<or> P k = b"
  using assms by auto

lemma kvs_of_gs_tm_commit:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "WLockInv s k" and "WLockFpInv s k"
    and "RLockInv s k" and "RLockFpInv s k"
    and "NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock}"
    and "tm_status (tm s' cl) = tm_committed"
    and "other_insts_unchanged cl (tm s) (tm s')"
  shows "update_kv_all_txn (\<lambda>t. tm_status (tm s' (get_cl_txn t))) (km_status (kms s k))
          (km_key_fp (kms s k)) (km_vl (kms s k)) =
    update_kv_key (get_txn_cl cl s) (km_key_fp (kms s k) (get_txn_cl cl s))
      (full_view (update_kv_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
        (km_key_fp (kms s k)) (km_vl (kms s k))))
      (update_kv_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
        (km_key_fp (kms s k)) (km_vl (kms s k)))"
  using assms
  apply (auto simp add: update_kv_key_def)
  subgoal using tm_commit_updates_kv_reads'[of s cl k s']
    by (auto simp add: read_only_update' update_kv_writes_def)
  subgoal using tm_commit_updates_kv_reads'[of s cl k s']
    apply (simp add: writer_update_before)
    by (auto simp add: update_kv_all_txn_def update_kv_writes_all_txn_def the_wr_tI)
  by (auto simp add: update_kv_writes_def update_kv_reads_def update_kv_all_tm_commit_no_lock_inv)

\<comment> \<open>Lemmas about reader and writer transaction sets\<close>
lemma update_kv_writes_all_txn_v_readerset_set [simp]:
  "\<Union> (v_readerset ` set (update_kv_writes_all_txn tStm tSkm tFk vl)) = \<Union> (v_readerset ` set vl)"
  by (auto simp add: update_kv_writes_all_txn_def update_kv_writes_def split: option.split)

lemma set_update_kv_all_v_readerset:
  assumes "vl \<noteq> []"
  shows "\<Union> (v_readerset ` set (update_kv_all_txn tStm tSkm tFk vl)) =
   \<Union> (v_readerset ` set vl) \<union> {t. eligible_reads tStm tSkm tFk t}"
  using assms
  apply (auto simp add: update_kv_all_txn_def del: conjI disjE)
  subgoal for x ver
    apply (cases "ver = (update_kv_reads_all_txn tStm tSkm tFk vl) ! Max (full_view vl)")
    subgoal apply (cases "x \<in> v_readerset (vl ! Max (full_view vl))")
      by (auto simp add: update_kv_reads_all_defs)
    subgoal apply (cases "ver \<in> set vl")
      apply blast
      apply (auto simp add: update_kv_reads_all_defs)
      using the_update by fastforce+
    done
  subgoal for x ver apply (cases "ver = vl ! Max (full_view vl)")
    subgoal
      apply (rule bexI [where x="(update_kv_reads_all_txn tStm tSkm tFk vl) ! Max (full_view vl)"])
      by (auto simp add: update_kv_reads_all_defs)
    subgoal apply (rule bexI [where x=ver]) by (auto simp add: update_kv_reads_all_defs)
    done
  subgoal
    apply (rule bexI [where x="(update_kv_reads_all_txn tStm tSkm tFk vl) ! Max (full_view vl)"])
    by (auto simp add: update_kv_reads_all_defs)
  done

lemma update_kv_reads_all_txn_v_writer_set [simp]:
  "vl \<noteq> [] \<Longrightarrow> v_writer ` set (update_kv_reads_all_txn tStm tSkm tFk vl) = v_writer ` set vl"
  apply (auto simp add: image_iff)
  subgoal for x apply (cases "x = (update_kv_reads_all_txn tStm tSkm tFk vl) ! Max (full_view vl)")
    subgoal apply (rule bexI [where x="vl ! Max (full_view vl)"])
      by (auto simp add: update_kv_reads_all_defs)
    subgoal apply (rule bexI [where x=x])
      apply (auto simp add: update_kv_reads_all_defs)
      by (metis (no_types, lifting) full_view_nth_list_update_eq max_in_full_view in_set_before_update)
    done
  subgoal for x apply (cases "x = vl ! Max (full_view vl)")
    subgoal
      apply (rule bexI [where x="(update_kv_reads_all_txn tStm tSkm tFk vl) ! Max (full_view vl)"])
      by (auto simp add: update_kv_reads_all_defs)
    subgoal apply (rule bexI [where x=x]) by (auto simp add: update_kv_reads_all_defs)
    done
  done

lemma set_update_kv_all_v_writer:
  "vl \<noteq> [] \<Longrightarrow> v_writer ` set (update_kv_all_txn tStm tSkm tFk vl) =
  (if (\<exists>t. tStm t = tm_committed \<and> tSkm t = write_lock \<and> tFk (the_wr_t tSkm) W \<noteq> None) then
     insert (Tn (the_wr_t tSkm)) (v_writer ` set vl) else v_writer ` set vl)"
  by (auto simp add: update_kv_all_txn_def update_kv_writes_all_txn_def update_kv_writes_def
      split: option.split)

lemma set_update_kv_all_v_writer':
  assumes "KVSNonEmp s"
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

lemma kvs_readers_grows:
  assumes "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "other_insts_unchanged cl (tm s) (tm s')"
    and "t \<in> vl_readers (update_kv_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) tSkm tFk vl)"
  shows "t \<in> vl_readers (update_kv_all_txn (\<lambda>t. tm_status (tm s' (get_cl_txn t))) tSkm tFk vl)"
  using assms
  apply (auto simp add: vl_readers_def in_set_conv_nth update_kv_all_txn_def)
  subgoal for i apply (cases "i = Max (full_view vl)"; 
   rule bexI [where x="(update_kv_reads_all_txn (\<lambda>t. tm_status (tm s' (get_cl_txn t))) tSkm tFk vl) ! i"])
    subgoal by (auto simp add: other_insts_unchanged_def update_kv_reads_all_defs)
    apply (metis nth_mem update_kv_reads_all_txn_length)
    apply (metis (mono_tags, lifting) nth_list_update_neq update_kv_reads_all_txn_def)
    by (metis (no_types, lifting) in_set_conv_nth length_list_update update_kv_reads_all_txn_def)
  done

\<comment> \<open>Lemmas for showing transaction id freshness\<close>

lemma vl_writers_sqns_reads_other_cl_inv:
  "vl_writers_sqns (update_kv_reads_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) tSkm tFk vl) = 
   vl_writers_sqns vl"
  unfolding vl_writers_sqns_def apply (rule ext)
  apply (auto simp add: vl_writers_def in_set_conv_nth image_iff)
  subgoal for cl x i apply (rule bexI[where x="vl ! i"])
     apply (auto simp add: update_kv_reads_all_defs)
    by (metis (lifting) nth_list_update_eq nth_list_update_neq version.select_convs(2)
        version.surjective version.update_convs(3))
  subgoal for cl x i apply (rule bexI[where x="update_kv_reads_all_txn
      (\<lambda>t. tm_status (tm s (get_cl_txn t))) tSkm tFk vl ! i"])
     apply (auto simp add: update_kv_reads_all_defs)
    by (metis (lifting) nth_list_update_eq nth_list_update_neq version.select_convs(2)
        version.surjective version.update_convs(3))
  done

lemma vl_readers_sqns_other_cl_inv:
  assumes "vl \<noteq> []"
    and "\<forall>k. WLockInv s k"
    and "\<forall>k. WLockFpInv s k"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> tm s' cl' = tm s cl'"
    and "kms s' = kms s"
    and "cl' \<noteq> cl"
  shows "vl_readers_sqns (update_kv_key (get_txn_cl cl s) (km_key_fp (kms s k) (get_txn_cl cl s))
      (full_view vl) vl) cl'
       = vl_readers_sqns vl cl'"
  using assms
  by (auto simp add: update_kv_key_def update_kv_writes_def vl_readers_sqns_def
      update_kv_reads_vl_readers_inv split: option.split)

lemma kvs_readers_sqns_other_cl_inv:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<forall>k. WLockInv s k" and "\<forall>k. WLockFpInv s k"
    and "\<forall>k. RLockInv s k" and "\<forall>k. RLockFpInv s k"
    and "\<forall>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "\<forall>k. km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock}"
    and "other_insts_unchanged cl (tm s) (tm s')"
    and "kms s' = kms s"
    and "cl' \<noteq> cl"
  shows "kvs_readers_sqns (kvs_of_gs s') cl' = kvs_readers_sqns (kvs_of_gs s) cl'"
  using assms
  apply (auto simp add: kvs_readers_sqns_def kvs_of_gs_def)
  subgoal for x k using kvs_of_gs_tm_commit[of s cl k s'] apply (simp add: KVSNonEmp_def)
  apply (rule exI[where x=k])
  by (smt (verit) other_insts_unchanged_def update_kv_all_txn_non_empty vl_readers_sqns_other_cl_inv)
  subgoal for x k using kvs_of_gs_tm_commit[of s cl k s'] apply (simp add: KVSNonEmp_def)
  apply (rule exI[where x=k])apply simp
  by (smt (verit) assms(10) assms(12) assms(14) other_insts_unchanged_def
    update_kv_all_txn_non_empty vl_readers_sqns_other_cl_inv)
  done

lemma vl_writers_sqns_other_cl_inv:
  assumes "KVSNonEmp s"
    and "\<forall>k. WLockInv s k"
    and "\<forall>k. WLockFpInv s k"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> tm s' cl' = tm s cl'"
    and "kms s' = kms s"
    and "cl' \<noteq> cl"
  shows "vl_writers_sqns (update_kv_key (get_txn_cl cl s) (km_key_fp (kms s k) (get_txn_cl cl s))
      (full_view vl) vl) cl'
       = vl_writers_sqns vl cl'"
  using assms
  by (auto simp add: update_kv_key_def update_kv_writes_def vl_writers_sqns_def
      split: option.split)

lemma kvs_writers_sqns_other_cl_inv:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<forall>k. WLockInv s k" and "\<forall>k. WLockFpInv s k"
    and "\<forall>k. RLockInv s k" and "\<forall>k. RLockFpInv s k"
    and "\<forall>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "\<forall>k. km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock}"
    and "other_insts_unchanged cl (tm s) (tm s')"
    and "kms s' = kms s"
    and "cl' \<noteq> cl"
  shows "kvs_writers_sqns (kvs_of_gs s') cl' = kvs_writers_sqns (kvs_of_gs s) cl'"
  using assms
  apply (auto simp add: kvs_writers_sqns_def kvs_of_gs_def)
  subgoal for x k using kvs_of_gs_tm_commit[of s cl k s'] apply simp apply (rule exI[where x=k])
    by (smt (verit) other_insts_unchanged_def vl_writers_sqns_other_cl_inv)
  subgoal for x k using kvs_of_gs_tm_commit[of s cl k s'] apply simp apply (rule exI[where x=k])
    apply simp by (smt (verit) other_insts_unchanged_def vl_writers_sqns_other_cl_inv)
  done

lemma get_sqns_other_cl_inv:
  assumes "KVSNonEmp s"
    and "\<forall>k. WLockInv s k"
    and "\<forall>k. WLockFpInv s k"
    and "\<forall>k. RLockInv s k"
    and "\<forall>k. RLockFpInv s k"
    and "\<forall>k. NoLockFpInv s k"
    and "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "\<forall>k. km_status (kms s k) (get_txn_cl cl s) = read_lock \<or>
             km_status (kms s k) (get_txn_cl cl s) = write_lock \<or> 
             km_status (kms s k) (get_txn_cl cl s) = no_lock"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> tm s' cl' = tm s cl'"
    and "kms s' = kms s"
    and "cl' \<noteq> cl"
  shows "get_sqns (kvs_of_gs s') cl' = get_sqns (kvs_of_gs s) cl'"
  using assms by (auto simp add: get_sqns_def kvs_writers_sqns_other_cl_inv
      kvs_readers_sqns_other_cl_inv other_insts_unchanged_def)

lemma new_t_is_in_writers:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<forall>k. WLockInv s k" and "\<forall>k. WLockFpInv s k"
    and "\<forall>k. RLockInv s k" and "\<forall>k. RLockFpInv s k"
    and "\<forall>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "km_status (kms s k) (get_txn_cl cl s) = write_lock"
    and "other_insts_unchanged cl (tm s) (tm s')"
    and "kms s' = kms s"
  shows "vl_writers_sqns (kvs_of_gs s' k) cl = vl_writers_sqns (kvs_of_gs s k) cl \<union> {tm_sn (tm s cl)}"
  using assms kvs_of_gs_tm_commit[of s cl k s']
  by (auto simp add: kvs_of_gs_def vl_writers_sqns_def update_kv_key_def
      update_kv_writes_def split: option.split)

lemma new_t_is_in_writers2:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<forall>k. WLockInv s k" and "\<forall>k. WLockFpInv s k"
    and "\<forall>k. RLockInv s k" and "\<forall>k. RLockFpInv s k"
    and "\<forall>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "km_status (kms s k) (get_txn_cl cl s) = read_lock"
    and "other_insts_unchanged cl (tm s) (tm s')"
    and "kms s' = kms s"
  shows "vl_writers_sqns (kvs_of_gs s' k) cl = vl_writers_sqns (kvs_of_gs s k) cl"
  using assms kvs_of_gs_tm_commit[of s cl k s']
  apply (auto simp add: kvs_of_gs_def vl_writers_sqns_def update_kv_key_def update_kv_writes_def
      split: option.split)
  by (metis RLockFpInv_def option.discI)

lemma new_t_is_in_readers:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<forall>k. WLockInv s k" and "\<forall>k. WLockFpInv s k"
    and "\<forall>k. RLockInv s k" and "\<forall>k. RLockFpInv s k"
    and "\<forall>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "km_status (kms s k) (get_txn_cl cl s) = read_lock"
    and "other_insts_unchanged cl (tm s) (tm s')"
    and "kms s' = kms s"
  shows "vl_readers_sqns (kvs_of_gs s' k) cl = vl_readers_sqns (kvs_of_gs s k) cl \<union> {tm_sn (tm s cl)}"
  using assms kvs_of_gs_tm_commit[of s cl k s']
  apply (auto simp add: kvs_of_gs_def update_kv_key_def update_kv_writes_def vl_readers_sqns_def
      RLockFpInv_def update_kv_reads_vl_readers_inv KVSNonEmp_def split: option.split)
  by (meson RLockFpInv_def assms(6))

lemma new_t_is_in_readers2:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<forall>k. WLockInv s k" and "\<forall>k. WLockFpInv s k"
    and "\<forall>k. RLockInv s k" and "\<forall>k. RLockFpInv s k"
    and "\<forall>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "km_status (kms s k) (get_txn_cl cl s) = write_lock"
    and "km_key_fp (kms s k) (get_txn_cl cl s) R \<noteq> None"
    and "other_insts_unchanged cl (tm s) (tm s')"
    and "kms s' = kms s"
  shows "vl_readers_sqns (kvs_of_gs s' k) cl = vl_readers_sqns (kvs_of_gs s k) cl \<union> {tm_sn (tm s cl)}"
  using assms kvs_of_gs_tm_commit[of s cl k s']
  by (auto simp add: kvs_of_gs_def update_kv_key_def update_kv_writes_def vl_readers_sqns_def
       update_kv_reads_vl_readers_inv split: option.split)

lemma new_t_is_in_readers3:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<forall>k. WLockInv s k" and "\<forall>k. WLockFpInv s k"
    and "\<forall>k. RLockInv s k" and "\<forall>k. RLockFpInv s k"
    and "\<forall>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "km_status (kms s k) (get_txn_cl cl s) = write_lock"
    and "km_key_fp (kms s k) (get_txn_cl cl s) R = None"
    and "other_insts_unchanged cl (tm s) (tm s')"
    and "kms s' = kms s"
  shows "vl_readers_sqns (kvs_of_gs s' k) cl = vl_readers_sqns (kvs_of_gs s k) cl"
  using assms kvs_of_gs_tm_commit[of s cl k s']
  by (auto simp add: kvs_of_gs_def update_kv_key_def update_kv_writes_def vl_readers_sqns_def
       update_kv_reads_vl_readers_inv split: option.split)

lemma kvs_writers_tm_commit_grows:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<forall>k. WLockInv s k" and "\<forall>k. WLockFpInv s k"
    and "\<forall>k. RLockInv s k" and "\<forall>k. RLockFpInv s k"
    and "\<forall>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "\<forall>k. km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock}"
    and "km_status (kms s k) (get_txn_cl cl s) = write_lock"
    and "other_insts_unchanged cl (tm s) (tm s')"
    and "kms s' = kms s"
  shows "kvs_writers_sqns (kvs_of_gs s') cl = kvs_writers_sqns (kvs_of_gs s) cl \<union> {tm_sn (tm s cl)}"
  using assms new_t_is_in_writers[of s cl s' k]
  apply (auto simp add: kvs_writers_sqns_def)
  subgoal for x k' apply (auto elim!: allE[where x=k']; cases "k' = k", simp_all)
    apply (metis kvs_of_gs_def read_only_update' vl_writers_sqns_reads_other_cl_inv)
    apply (metis Un_empty_right Un_insert_right assms(3-7) insert_iff new_t_is_in_writers)
    by (metis kvs_of_gs_def update_kv_all_tm_commit_no_lock_inv)
  subgoal for x k' apply (rule exI[where x=k'])
    by (smt (verit, ccfv_SIG) UnCI assms(13) kvs_of_gs_def new_t_is_in_writers new_t_is_in_writers2
        update_kv_all_tm_commit_no_lock_inv)
  done

lemma kvs_writers_tm_commit_doesnt_grow:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<forall>k. WLockInv s k" and "\<forall>k. WLockFpInv s k"
    and "\<forall>k. RLockInv s k" and "\<forall>k. RLockFpInv s k"
    and "\<forall>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "\<forall>k. km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, no_lock}"
    and "other_insts_unchanged cl (tm s) (tm s')"
    and "kms s' = kms s"
  shows "kvs_writers_sqns (kvs_of_gs s') cl = kvs_writers_sqns (kvs_of_gs s) cl"
  using assms apply (auto simp add: kvs_writers_sqns_def)
  subgoal for x k apply (auto elim!: allE[where x=k])
    apply (metis assms(3-7) new_t_is_in_writers2)
    by (metis kvs_of_gs_def update_kv_all_tm_commit_no_lock_inv)
  subgoal for x k  apply (auto elim!: allE[where x=k])
    apply (metis assms(3-7) new_t_is_in_writers2)
    by (metis kvs_of_gs_def update_kv_all_tm_commit_no_lock_inv)
  done

lemma kvs_readers_sqns_tm_commit_grows:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<forall>k. WLockInv s k" and "\<forall>k. WLockFpInv s k"
    and "\<forall>k. RLockInv s k" and "\<forall>k. RLockFpInv s k"
    and "\<forall>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "\<forall>k. km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock}"
    and "km_status (kms s k) (get_txn_cl cl s) = read_lock \<or>
         (km_status (kms s k) (get_txn_cl cl s) = write_lock \<and>
          km_key_fp (kms s k) (get_txn_cl cl s) R \<noteq> None)"
    and "other_insts_unchanged cl (tm s) (tm s')"
    and "kms s' = kms s"
  shows "kvs_readers_sqns (kvs_of_gs s') cl = kvs_readers_sqns (kvs_of_gs s) cl \<union> {tm_sn (tm s cl)}"
  using assms
  apply (auto simp add: kvs_readers_sqns_def del: disjE)
  subgoal for x k' apply (auto elim!: allE[where x=k'])
    apply (metis (no_types) Un_insert_right assms(3-7) insert_iff new_t_is_in_readers sup_bot_right)
    apply (metis (no_types) Un_insert_right assms(3-7) insert_iff new_t_is_in_readers2
      new_t_is_in_readers3 sup_bot_right)
    apply (metis kvs_of_gs_def update_kv_all_tm_commit_no_lock_inv)
    apply (metis (no_types) Un_insert_right assms(3-7) insert_iff new_t_is_in_readers sup_bot_right)
    apply (metis (no_types) Un_insert_right assms(3-7) insert_iff new_t_is_in_readers2
      new_t_is_in_readers3 sup_bot_right)
    by (metis kvs_of_gs_def update_kv_all_tm_commit_no_lock_inv)
   subgoal apply (rule exI[where x=k])
     by (metis UnI2 assms(12,13) new_t_is_in_readers new_t_is_in_readers2 singletonI)
   subgoal for x k' apply (auto elim!: allE[where x=k'])
     apply (metis Un_iff assms(3) assms(4) assms(5) assms(6) assms(7) new_t_is_in_readers)
     apply (smt (verit) Un_insert_left assms(3-7) insert_iff mk_disjoint_insert
       new_t_is_in_readers2 new_t_is_in_readers3)
     apply (metis kvs_of_gs_def update_kv_all_tm_commit_no_lock_inv)
     apply (metis Un_iff assms(3) assms(4) assms(5) assms(6) assms(7) new_t_is_in_readers)
     apply (smt (verit) Un_insert_left assms(3-7) insert_iff mk_disjoint_insert
       new_t_is_in_readers2 new_t_is_in_readers3)
     by (metis kvs_of_gs_def update_kv_all_tm_commit_no_lock_inv)
   done

lemma kvs_readers_sqns_tm_commit_doesnt_grow:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<forall>k. WLockInv s k" and "\<forall>k. WLockFpInv s k"
    and "\<forall>k. RLockInv s k" and "\<forall>k. RLockFpInv s k"
    and "\<forall>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "\<forall>k. km_status (kms s k) (get_txn_cl cl s) \<in> {write_lock, no_lock}"
    and "\<forall>k. km_status (kms s k) (get_txn_cl cl s) \<noteq> write_lock \<or>
             km_key_fp (kms s k) (get_txn_cl cl s) R = None"
    and "other_insts_unchanged cl (tm s) (tm s')"
    and "kms s' = kms s"
  shows "kvs_readers_sqns (kvs_of_gs s') cl = kvs_readers_sqns (kvs_of_gs s) cl"
  using assms apply (auto simp add: kvs_readers_sqns_def)
  subgoal for x k apply (auto elim!: allE[where x=k])
    apply (metis assms(1, 3-7) new_t_is_in_readers3)
    by (metis kvs_of_gs_def update_kv_all_tm_commit_no_lock_inv)+
  subgoal for x k  apply (auto elim!: allE[where x=k])
    apply (metis assms(1, 3-7) new_t_is_in_readers3)
    by (metis kvs_of_gs_def update_kv_all_tm_commit_no_lock_inv)+
  done

lemma get_sqns_tm_commit_grows:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<forall>k. WLockInv s k" and "\<forall>k. WLockFpInv s k"
    and "\<forall>k. RLockInv s k" and "\<forall>k. RLockFpInv s k"
    and "\<forall>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "\<forall>k. km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock}"
    and "other_insts_unchanged cl (tm s) (tm s')"
    and "kms s' = kms s"
  shows "get_sqns (kvs_of_gs s') cl =
         (if \<forall>k. km_status (kms s k) (get_txn_cl cl s) = no_lock then
          get_sqns (kvs_of_gs s) cl else
          get_sqns (kvs_of_gs s) cl \<union> {tm_sn (tm s cl)})"
  using assms
  apply (cases "\<forall>k. km_status (kms s k) (get_txn_cl cl s) = no_lock")
   apply (simp add: kvs_of_gs_def update_kv_all_tm_commit_no_lock_inv)
  apply simp apply (rule conjI) apply blast
  apply (simp add: get_sqns_def)
  using kvs_readers_sqns_tm_commit_doesnt_grow[of s cl s']
        kvs_readers_sqns_tm_commit_grows[of s cl s']
        kvs_writers_tm_commit_doesnt_grow[of s cl s']
        kvs_writers_tm_commit_grows[of s cl s']
  by (smt (z3) Un_insert_right insertCI sup.right_idem sup_bot_right sup_commute)

definition SqnInv where
  "SqnInv s cl \<longleftrightarrow>
    (tm_status (tm s cl) \<noteq> tm_committed \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_gs s) cl. m < tm_sn (tm s cl))) \<and>
    (tm_status (tm s cl) = tm_committed \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_gs s) cl. m \<le> tm_sn (tm s cl)))"

lemmas SqnInvI = SqnInv_def[THEN iffD2, rule_format]
lemmas SqnInvE[elim] = SqnInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_sql_inv [simp, intro]:
  assumes "reach tps s"
    and "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<forall>k. RLockInv s k" and "\<forall>k. WLockInv s k"
    and "\<forall>k. RLockFpInv s k" and "\<forall>k. WLockFpInv s k"
    and "\<forall>k. NoLockFpInv s k" and "KVSNonEmp s" and "KVSLen s cl"
  shows "SqnInv s cl"
  using assms
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
    apply (auto simp add: SqnInv_def tps_defs kvs_of_gs_def get_sqns_old_def kvs_txids_def
        update_kv_all_defs full_view_def version_init_def)
    apply (auto simp add: kvs_writers_def vl_writers_def)
    by (auto simp add: kvs_readers_def vl_readers_def)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_gs_inv[of s e s']
  proof (induction e)
    case (WLock x1 x2 x3 x4)
    then show ?case
      by (auto simp add: SqnInv_def tps_trans_defs km_unchanged_defs)
  next
    case (NoLock x1 x2)
    then show ?case
      by (auto simp add: SqnInv_def tps_trans_defs km_unchanged_defs)
  next
    case (User_Commit x)
    then show ?case
      apply (auto simp add: SqnInv_def tps_trans_defs tm_unchanged_defs)
      apply (metis status_tm.distinct(3))
      by (metis status_tm.distinct(7))
  next
    case (TM_Commit x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: SqnInv_def tps_trans_defs tm_unchanged_defs)
      apply (smt (verit) get_sqns_other_cl_inv reach_kvs_non_emp reach_nolockfp reach_rlock
          reach_rlockfp reach_tidfuturekm reach_tidpastkm reach_wlock reach_wlockfp)
      apply (cases "cl = x1")
      using get_sqns_tm_commit_grows[of s cl s']
      apply (smt (z3) UnE insert_absorb insert_iff insert_not_empty order.strict_implies_order
        order_class.order_eq_iff other_insts_unchanged_def reach_kvs_non_emp reach_nolockfp
        reach_rlock reach_rlockfp reach_tidfuturekm reach_tidpastkm reach_wlock reach_wlockfp)
      by (smt (verit) get_sqns_other_cl_inv reach_kvs_non_emp reach_nolockfp reach_rlock
        reach_rlockfp reach_tidfuturekm reach_tidpastkm reach_wlock reach_wlockfp)
  next
    case (TM_Abort x)
    then show ?case apply (auto simp add: SqnInv_def tps_trans_defs tm_unchanged_defs)
    apply (metis status_tm.distinct(7)) by (metis status_tm.distinct(11))
  next
    case (TM_ReadyC x)
    then show ?case apply (auto simp add: SqnInv_def tps_trans_defs tm_unchanged_defs)
    apply (metis less_Suc_eq_le) by (metis status_tm.distinct(3))
  next
    case (TM_ReadyA x)
    then show ?case apply (auto simp add: SqnInv_def tps_trans_defs tm_unchanged_defs)
    apply (metis less_Suc_eq status_tm.distinct(11)) by (metis status_tm.distinct(3))
  qed (auto simp add: SqnInv_def tps_trans_defs km_unchanged_defs)
qed

\<comment> \<open>Lemmas for proving view wellformedness of tm_view\<close>

lemma helper_lemma:
  assumes "i \<in> full_view (update_kv_reads_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t)))
    (km_status (kms s k)) (km_key_fp (kms s k)) (km_vl (kms s k)))"
  shows "
  update_kv_writes (the_wr_t (km_status (kms s k))) (km_key_fp (kms s k) (the_wr_t (km_status (kms s k))))
    (update_kv_reads_all_txn (\<lambda>t. tm_status (tm s' (get_cl_txn t))) (km_status (kms s k))
      (km_key_fp (kms s k)) (km_vl (kms s k))) ! i =
  update_kv_reads_all_txn (\<lambda>t. tm_status (tm s' (get_cl_txn t))) (km_status (kms s k))
    (km_key_fp (kms s k)) (km_vl (kms s k)) ! i"
  using assms
  update_kv_writes_version_inv[of i "update_kv_reads_all_txn (\<lambda>t. tm_status (tm s' (get_cl_txn t)))
   (km_status (kms s k)) (km_key_fp (kms s k)) (km_vl (kms s k))" "the_wr_t (km_status (kms s k))"
   "km_key_fp (kms s k) (the_wr_t (km_status (kms s k)))"]
  by (simp add: full_view_def)

lemma kvs_of_gs_version_order:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl" and "WLockInv s k" and "RLockInv s k" and "KVSNonEmp s"
    and "i \<in> full_view (kvs_of_gs s k)"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock}"
    and "km_tm_cl'_unchanged cl s s'"
  shows "kvs_of_gs s k ! i \<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r kvs_of_gs s' k ! i"
  using assms
  apply (auto simp add: kvs_of_gs_def km_tm_cl'_unchanged_def update_kv_all_tm_commit_no_lock_inv)
   apply (simp_all add: writer_update_before read_only_update')
   apply (auto simp add: update_kv_all_txn_def update_kv_writes_all_txn_def helper_lemma)
   apply (auto simp add: version_order_def)
   using tm_commit_updates_kv_reads[of s s' cl k] 
     expanding_feature3'[where vl="update_kv_reads_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t)))
      (km_status (kms s k)) (km_key_fp (kms s k)) (km_vl (kms s k))"]
   by (auto simp add: update_kv_reads_all_defs)

lemma new_writer:
  assumes "WLockInv s k" and "WLockFpInv s k" and "tm_status (tm s' cl) = tm_committed"
    and "km_status (kms s k) (get_txn_cl cl s) = write_lock"
  shows "v_writer (update_kv_all_txn (\<lambda>t. tm_status (tm s' (get_cl_txn t))) (km_status (kms s k))
    (km_key_fp (kms s k)) (km_vl (kms s k)) ! length (km_vl (kms s k))) =
   Tn (the_wr_t (km_status (kms s k)))"
  using assms
  apply (auto simp add: update_kv_all_txn_def update_kv_writes_all_txn_def update_kv_writes_def
      the_wr_tI split: option.split)
  by (metis nth_append_length update_kv_reads_all_txn_length version.select_convs(2))

lemma update_kv_all_txn_v_writer_inv: 
  assumes "i \<in> full_view vl"
  shows "v_writer (update_kv_all_txn tStm tSkm tFk vl ! i) = v_writer (vl ! i)"
  using assms
  by (auto simp add: update_kv_all_defs update_kv_writes_def split: option.split)

lemma new_version_index:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "WLockInv s k" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "km_status (kms s k) (get_txn_cl cl s) = write_lock"
    and "other_insts_unchanged cl (tm s) (tm s')"
    and "i \<in> full_view (update_kv_all_txn (\<lambda>t. tm_status (tm s' (get_cl_txn t)))
    (km_status (kms s k)) (km_key_fp (kms s k)) (km_vl (kms s k)))"
    and "i \<notin> full_view (update_kv_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t)))
    (km_status (kms s k)) (km_key_fp (kms s k)) (km_vl (kms s k)))"
  shows "i = length (km_vl (kms s k))"
  using assms
  by (meson full_view_length_increasing index_in_longer_kv update_kv_all_txn_length_increasing)

lemma t_is_fresh:
  assumes "SqnInv s cl"
    and "tm_status (tm s cl) = tm_prepared"
  shows "get_txn_cl cl s \<in> next_txids (kvs_of_gs s) cl"
  using assms by (auto simp add: kvs_of_gs_def next_txids_def SqnInv_def)

lemma kvs_of_gs_view_atomic:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "\<forall>k. WLockInv s k" and "\<forall>k. WLockFpInv s k"
    and "\<forall>k. RLockInv s k" and "\<forall>k. NoLockFpInv s k"
    and "SqnInv s cl" and "KVSNonEmp s"
    and "tm_status (tm s cl) = tm_prepared"
    and "tm_status (tm s' cl) = tm_committed"
    and "\<forall>k. km_status (kms s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock}"
    and "km_tm_cl'_unchanged cl s s'"
  shows "view_atomic (kvs_of_gs s') (\<lambda>k. full_view (kvs_of_gs s k))"
  using assms
  apply (auto simp add: kvs_of_gs_def km_tm_cl'_unchanged_def view_atomic_def)
  subgoal for k k' i i'
    apply (auto elim!: allE[where x=k'])
    apply (auto simp add: update_kv_all_tm_commit_no_lock_inv read_only_update')
     apply (metis full_view_same_length update_kv_reads_all_txn_length)
    apply (cases "i' \<in> full_view (update_kv_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t)))
      (km_status (kms s k')) (km_key_fp (kms s k')) (km_vl (kms s k')))"; simp)
    using new_version_index[of s cl k' s' i'] apply (auto simp add: writer_update_before)
     apply (simp add: new_writer the_wr_tI)
    using tm_commit_writer_update_kv_all[of s cl k s'] apply simp
    using update_kv_all_txn_v_writer_inv[of i
        "update_kv_all_txn (\<lambda>t. tm_status (tm s (get_cl_txn t))) (km_status (kms s k))
          (km_key_fp (kms s k)) (km_vl (kms s k))"] assms(3, 5, 6, 11)
    apply (auto elim!: allE[where x=k])
    apply (simp_all add: update_kv_all_tm_commit_no_lock_inv)
    by (metis t_is_fresh fresh_txid_v_writer kvs_of_gs_def)+
  done

lemma reach_kvs_expands [simp, intro]:
  assumes "reach tps s" and "gs_trans s e s'"
    and "\<forall>cl. TIDFutureKm s cl" and "\<forall>cl. TIDPastKm s cl"
    and "\<forall>k. RLockInv s k" and "\<forall>k. WLockInv s k"
    and "\<forall>k. RLockFpInv s k" and "\<forall>k. NoLockFpInv s k"
    and "KVSNonEmp s" and "KVSLen s cl"
  shows "kvs_of_gs s \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s kvs_of_gs s'"
  using assms kvs_of_gs_inv[of s e s'] apply (cases "not_tm_commit e"; auto)
  using kvs_of_gs_view_atomic[of s]
  apply (auto simp add: tps_trans_defs kvs_expands_def vlist_order_def)
  apply (meson kvs_of_gs_commit_length_increasing)
  by (simp add: kvs_of_gs_version_order)

definition KVSView where
  "KVSView s cl \<longleftrightarrow> view_wellformed (kvs_of_gs s) (tm_view (tm s cl))"

lemmas KVSViewI = KVSView_def[THEN iffD2, rule_format]
lemmas KVSViewE[elim] = KVSView_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_view [simp, intro]:
  assumes "reach tps s"
    and "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<forall>k. RLockInv s k" and "\<forall>k. WLockInv s k"
    and "\<forall>k. RLockFpInv s k" and "\<forall>k. NoLockFpInv s k"
    and "KVSNonEmp s" and "KVSLen s cl" and "KVSGSNonEmp s"
  shows "KVSView s cl"
  using assms
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: KVSView_def tps_defs sim_defs update_kv_all_defs
        view_wellformed_defs full_view_def view_init_def)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_gs_inv[of s e s']
  proof (induction e)
    case (WLock x1 x2 x3 x4)
    then show ?case
      by (auto simp add: KVSView_def tps_trans_defs km_unchanged_defs)
  next
    case (NoLock x1 x2)
    then show ?case
      by (auto simp add: KVSView_def tps_trans_defs km_unchanged_defs)
  next
    case (User_Commit x)
    then show ?case
      by (auto simp add: KVSView_def tps_trans_defs tm_unchanged_defs, metis)
  next
    case (TM_Commit x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: KVSView_def tps_trans_defs tm_unchanged_defs)
      apply (cases "cl = x1")
        apply (simp add: KVSGSNonEmp_def full_view_wellformed)
        by (smt (verit) kvs_expanded_view_wellformed reach_kvs_expands reach_kvs_len
            reach_kvs_non_emp reach_nolockfp reach_rlock reach_rlockfp reach_tidfuturekm
            reach_tidpastkm reach_trans.hyps(1) reach_wlock tps_trans)
  next
    case (TM_Abort x)
    then show ?case
      by (auto simp add: KVSView_def tps_trans_defs tm_unchanged_defs, metis)
  next
    case (TM_ReadyC x)
    then show ?case
      by (auto simp add: KVSView_def tps_trans_defs tm_unchanged_defs, metis)
  next
    case (TM_ReadyA x)
    then show ?case
      by (auto simp add: KVSView_def tps_trans_defs tm_unchanged_defs, metis)
  qed (auto simp add: KVSView_def tps_trans_defs km_unchanged_defs)
qed

\<comment> \<open>CanCommit\<close>

lemma writers_visible:
  assumes "u = (\<lambda>k. full_view (K k))"
  shows "visTx K u = kvs_writers K"
  using assms
  apply (auto simp add: visTx_def kvs_writers_def vl_writers_def in_set_conv_nth)
  using list_nth_in_set apply blast
  subgoal for k i apply (rule exI[where x=i]) apply (rule exI[where x= k])
    by (simp add: full_view_def).

lemma WW_writers_id_helper:
  assumes "(x, v_writer x') \<in> {(xa, x). \<exists>xb i.
            i \<in> full_view (K xb) \<and>
            (\<exists>i'. i' \<in> full_view (K xb) \<and>
              x = v_writer (K xb ! i) \<and> xa = v_writer (K xb ! i') \<and> i < i')}\<^sup>* "
    and "x' \<in> set (K k)"
  shows "\<exists>xa. x \<in> v_writer ` set (K xa)"
  using assms
  apply (induction x rule: converse_rtrancl_induct, auto)
  subgoal for xb apply (rule exI[where x=xb])
    using list_nth_in_set by blast.

lemma WW_writers_id:
  "(((\<Union> (range (WW K)))\<inverse>)\<^sup>*)\<inverse> `` kvs_writers K = kvs_writers K"
  apply (auto simp add: converse_def WW_def kvs_writers_def vl_writers_def)
  by (simp add: WW_writers_id_helper)

lemma full_view_satisfies_ET_SER_canCommit:
  "u = (\<lambda>k. full_view (K k)) \<Longrightarrow> ET_SER.canCommit K u F"
  by (simp add: ET_SER.canCommit_def closed_def read_only_Txs_def R_SER_def R_onK_def
      writers_visible WW_writers_id Diff_triv)

abbreviation invariant_list where
  "invariant_list s \<equiv> (\<forall>cl k. TIDFutureKm s cl \<and> TIDPastKm s cl \<and> RLockInv s k \<and> WLockInv s k \<and>
    RLockFpInv s k \<and> WLockFpInv s k \<and> NoLockFpInv s k \<and> KVSNonEmp s \<and> KVSGSNonEmp s \<and> KVSLen s k \<and>
    RLockFpContentInv s k \<and> WLockFpContentInv s k \<and> TMFullView s cl \<and> KVSView s cl \<and> SqnInv s cl)"

subsection \<open>Refinement Proof\<close>

lemma tps_refines_et_es: "tps \<sqsubseteq>\<^sub>med ET_SER.ET_ES"
proof (intro simulate_ES_fun_with_invariant[where I="\<lambda>s. invariant_list s"])
  fix gs0 :: "'v global_state"
  assume p: "init tps gs0"
  then show "init ET_SER.ET_ES (sim gs0)"
    by (auto simp add: ET_SER.ET_ES_defs tps_defs sim_defs update_kv_all_defs
        full_view_def kvs_init_def v_list_init_def lessThan_Suc)
next
  fix gs a and gs' :: "'v global_state"
  assume p: "tps: gs\<midarrow>a\<rightarrow> gs'" and inv: "invariant_list gs"
  then show "ET_SER.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  using kvs_of_gs_inv[of gs a gs'] tm_view_inv[of gs a gs']
  proof (induction a)
  case (TM_Commit cl sn u F)
  then show ?case using p apply simp
    apply (auto simp add: tm_commit_def tm_unchanged_defs sim_def)
    subgoal apply (rule exI [where x="(\<lambda>k. full_view (kvs_of_gs gs' k))"])
      apply (auto simp add: views_of_gs_def KVSLen_def)
      apply (auto simp add: ET_SER.ET_cl_txn_def t_is_fresh KVSGSNonEmp_def full_view_wellformed)
      subgoal by (metis kvs_of_gs_length_increasing full_view_wellformed longer_list_not_empty)
      subgoal by (simp add: full_view_satisfies_ET_SER_canCommit)
      subgoal apply (auto simp add: kvs_of_gs_def update_kv_def) apply (rule ext)
        using kvs_of_gs_tm_commit[of gs cl] by (simp add: other_insts_unchanged_def)
      done
    subgoal apply (auto simp add: fp_property_def view_snapshot_def)
      subgoal for k y
        apply (cases "km_status (kms gs k) (get_txn_cl cl gs) = no_lock")
        apply (auto simp add: km_vl_kvs_eq_lv NoLockFpInv_def del: disjE dest!:or3_not_eq)
          by (metis RLockFpContentInv_def WLockFpContentInv_def option.discI option.inject).
      done
  qed (auto simp add: tps_trans_defs unchanged_defs sim_defs)
qed auto

end