section \<open>Two Phase Commit (2PC) with Two Phase Locking (2PL)\<close>

theory Prot_2PC_2PL
  imports Key_Value_Stores
begin

subsection \<open>2PC Event system\<close>

subsubsection \<open>State\<close>

datatype status_rm = working | prepared | read_lock | write_lock | no_lock | notokay | committed | aborted
datatype status_tm = tm_init | tm_prepared | tm_committed | tm_aborted

record tm_state =
  tm_status :: status_tm
  tm_sn :: nat
  (*tm_view :: view*)

record 'v rm_state =
  rm_db :: "'v version list"
  rm_fingerpr :: "txid0 \<Rightarrow> 'v key_fp"
  rm_status :: "txid0 \<Rightarrow> status_rm"

record 'v global_state =
  tm :: "cl_id \<Rightarrow> tm_state"
  rms :: "key \<Rightarrow> 'v rm_state"


subsubsection \<open>Events\<close>

datatype 'v rm_ev = Write2 txid0 'v | Read2 txid0 'v | Prepare txid0 | RLock txid0 | WLock txid0 |
                    NoLock txid0 | NOK txid0 | Commit txid0 | Abort txid0
datatype tm_ev = User_Commit | TM_Commit | TM_Abort | TM_ReadyC | TM_ReadyA | TM_Skip
datatype 'v ev = RM_ev key "'v rm_ev" | TM_ev cl_id tm_ev

definition other_instances_unchanged where
  "other_instances_unchanged t k rmss rmss' \<equiv> (\<forall>t'. t' \<noteq> t \<longrightarrow>
     rm_fingerpr (rmss' k) t' = rm_fingerpr (rmss k) t' \<and>
     rm_status (rmss' k) t' = rm_status (rmss k) t')"

definition other_rms_unchanged where
  "other_rms_unchanged k rmss rmss' \<equiv> (\<forall>k'. k' \<noteq> k \<longrightarrow> rmss' k' = rmss k')"

abbreviation tm_other_rms_unchanged where
  "tm_other_rms_unchanged k s s' t \<equiv> tm s' = tm s \<and>
    other_rms_unchanged k (rms s) (rms s') \<and> other_instances_unchanged t k (rms s) (rms s')"

abbreviation rm_status_trans where
  "rm_status_trans s k s' t from_stat to_stat \<equiv>
      rm_status (rms s k) t = from_stat
    \<and> rm_db (rms s' k) = rm_db (rms s k)
    \<and> rm_fingerpr (rms s' k) = rm_fingerpr (rms s k)
    \<and> rm_status (rms s' k) t = to_stat
    \<and> tm_other_rms_unchanged k s s' t"

fun get_cl_txn :: "txid0 \<Rightarrow> cl_id" where
  "get_cl_txn (Tn_cl sn cl) = cl"

definition write2 where
  "write2 s k v s' t \<equiv> rm_status (rms s k) t = working
                        \<and> rm_fingerpr (rms s' k) t = update_key_fp (rm_fingerpr (rms s k) t) W v
                        \<and> rm_status (rms s' k) t = working
                        \<and> rm_db (rms s' k) = rm_db (rms s k)
                        \<and> tm_other_rms_unchanged k s s' t"

definition read2 where
  "read2 s k v s' t  \<equiv> rm_status (rms s k) t = working
                        \<and> rm_fingerpr (rms s' k) t = update_key_fp (rm_fingerpr (rms s k) t) R v
                        \<and> rm_status (rms s' k) t = working
                        \<and> rm_db (rms s' k) = rm_db (rms s k)
                        \<and> tm_other_rms_unchanged k s s' t"

definition prepare where
  "prepare s k s' t \<equiv> tm_status (tm s (get_cl_txn t)) = tm_prepared
                      \<and> rm_status_trans s k s' t working prepared"

definition acquire_rd_lock where \<comment>\<open>Read Lock acquired\<close>
  "acquire_rd_lock s k s' t \<equiv> tm_status (tm s (get_cl_txn t)) = tm_prepared
                  \<and> rm_fingerpr (rms s k) t W = None
                  \<and> rm_fingerpr (rms s k) t R \<noteq> None
                  \<and> (\<forall>t'. rm_status (rms s k) t' \<in> {working, prepared, read_lock, no_lock, notokay})
                  \<and> rm_status_trans s k s' t prepared read_lock"

definition acquire_wr_lock where \<comment>\<open>Write Lock acquired\<close>
  "acquire_wr_lock s k s' t \<equiv> tm_status (tm s (get_cl_txn t)) = tm_prepared
                  \<and> rm_fingerpr (rms s k) t W \<noteq> None
                  \<and> (\<forall>t'. rm_status (rms s k) t' \<in> {working, prepared, no_lock, notokay})
                  \<and> rm_status_trans s k s' t prepared write_lock"

definition acquire_no_lock where \<comment>\<open>No Lock needed\<close>
  "acquire_no_lock s k s' t \<equiv> tm_status (tm s (get_cl_txn t)) = tm_prepared
                            \<and> rm_fingerpr (rms s k) t W = None
                            \<and> rm_fingerpr (rms s k) t R = None
                            \<and> rm_status_trans s k s' t prepared no_lock"

definition nok where \<comment>\<open>Lock not available\<close>
  "nok s k s' t \<equiv> tm_status (tm s (get_cl_txn t)) = tm_prepared \<and>
                    ((rm_fingerpr (rms s k) t R \<noteq> None \<and>
                      (\<exists>t'. rm_status (rms s k) t' = write_lock)) \<or>
                     (rm_fingerpr (rms s k) t W \<noteq> None \<and>
                      (\<exists>t'. rm_status (rms s k) t' \<in> {write_lock, read_lock}))) \<and>
                    rm_status_trans s k s' t prepared notokay"

definition commit where
  "commit s k s' t \<equiv> rm_status (rms s k) t \<in> {read_lock, write_lock, no_lock}
                      \<and> tm_status (tm s (get_cl_txn t)) = tm_committed
                      \<and> rm_db (rms s' k) =  update_kv t (rm_fingerpr (rms s k) t)
                                                       (tm_view (tm s)) (rm_db (rms s k)) \<comment>\<open>?\<close>
                      \<and> rm_fingerpr (rms s' k) t = Map.empty
                      \<and> rm_status (rms s' k) t = committed
                      \<and> tm_other_rms_unchanged rm s s' t"

definition abort where \<comment>\<open>Locks released (aborted)\<close>
  "abort s k s' t \<equiv> rm_status (rms s k) t \<in> {read_lock, write_lock, no_lock, notokay}
                    \<and> tm_status (tm s (get_cl_txn t)) = tm_aborted
                    \<and> rm_db (rms s' k) = rm_db (rms s k)
                    \<and> rm_fingerpr (rms s' k) t = Map.empty
                    \<and> rm_status (rms s' k) t = aborted
                    \<and> tm_other_rms_unchanged k s s' t"

definition user_commit where
  "user_commit s s' cl \<equiv> tm_status (tm s cl) = tm_init
                      \<and> tm_status (tm s' cl) = tm_prepared
                      \<and> tm_sn (tm s' cl) = tm_sn (tm s cl)
                      \<and> rms s' = rms s"

definition tm_commit where
  "tm_commit s s' cl \<equiv> let t = (Tn_cl (tm_sn (tm s cl)) cl) in
                        tm_status (tm s cl) = tm_prepared
                    \<and> (\<forall>k. rm_status (rms s k) t \<in> {read_lock, write_lock, no_lock})
                    \<and> tm_status (tm s' cl) = tm_committed
                    \<and> tm_sn (tm s' cl) = tm_sn (tm s cl)
                    \<and> rms s' = rms s"

definition tm_abort where
  "tm_abort s s' cl \<equiv> let t = (Tn_cl (tm_sn (tm s cl)) cl) in
                     (tm_status (tm s cl) = tm_prepared
                     \<and> (\<exists>k. rm_status (rms s k) t = notokay)
                     \<and> (\<forall>k. rm_status (rms s k) t \<in> {read_lock, write_lock, no_lock, notokay}))
                    \<and> tm_status (tm s' cl) = tm_aborted
                    \<and> tm_sn (tm s' cl) = tm_sn (tm s cl)
                    \<and> rms s' = rms s"

definition tm_ready_c where
  "tm_ready_c s s' cl \<equiv> let t = (Tn_cl (tm_sn (tm s cl)) cl) in
                        tm_status (tm s cl) = tm_committed
                      \<and> (\<forall>k. rm_status (rms s k) t = committed)
                      \<and> tm_status (tm s' cl) = tm_init
                      \<and> tm_sn (tm s' cl) = Suc (tm_sn (tm s cl))
                      \<and> rms s' = rms s"

definition tm_ready_a where
  "tm_ready_a s s' cl \<equiv> let t = (Tn_cl (tm_sn (tm s cl)) cl) in
                        tm_status (tm s cl) = tm_aborted
                      \<and> (\<forall>k. rm_status (rms s k) t = aborted)
                      \<and> tm_status (tm s' cl) = tm_init
                      \<and> tm_sn (tm s' cl) = Suc (tm_sn (tm s cl))
                      \<and> rms s' = rms s"

consts cl0 :: cl_id
text\<open>The Event System\<close>
definition gs_init :: "'v global_state" where
  "gs_init \<equiv> \<lparr> 
    tm = (\<lambda>cl. \<lparr> tm_status = tm_init, tm_sn = 0 \<rparr>),
    rms = (\<lambda>k. \<lparr> rm_db = [version_init],
                 rm_fingerpr = (\<lambda>t. Map.empty), 
                 rm_status = (\<lambda>t. working)\<rparr>)
  \<rparr>"

fun gs_trans :: "'v global_state \<Rightarrow> 'v ev \<Rightarrow> 'v global_state \<Rightarrow> bool" where
  "gs_trans s (RM_ev k (Write2 t v)) s' \<longleftrightarrow> write2 s k v s' t" |
  "gs_trans s (RM_ev k (Read2 t v))  s' \<longleftrightarrow> read2 s k v s' t" |
  "gs_trans s (RM_ev k (Prepare t))  s' \<longleftrightarrow> prepare s k s' t" |
  "gs_trans s (RM_ev k (RLock t))    s' \<longleftrightarrow> acquire_rd_lock s k s' t" |
  "gs_trans s (RM_ev k (WLock t))    s' \<longleftrightarrow> acquire_wr_lock s k s' t" |
  "gs_trans s (RM_ev k (NoLock t))   s' \<longleftrightarrow> acquire_no_lock s k s' t" |
  "gs_trans s (RM_ev k (NOK t))      s' \<longleftrightarrow> nok s k s' t" |
  (*"gs_trans s (RM_ev k (Commit t))   s' \<longleftrightarrow> commit s k s'" |*)
  "gs_trans s (RM_ev k (Abort t))    s' \<longleftrightarrow> abort s k s' t" |
  "gs_trans s (TM_ev cl User_Commit) s' \<longleftrightarrow> user_commit s s' cl" |
  "gs_trans s (TM_ev cl TM_Commit)   s' \<longleftrightarrow> tm_commit s s' cl" |
  "gs_trans s (TM_ev cl TM_Abort)    s' \<longleftrightarrow> tm_abort s s' cl" |
  "gs_trans s (TM_ev cl TM_ReadyC)   s' \<longleftrightarrow> tm_ready_c s s' cl" |
  "gs_trans s (TM_ev cl TM_ReadyA)   s' \<longleftrightarrow> tm_ready_a s s' cl" |
  "gs_trans s (TM_ev cl TM_Skip)     s' \<longleftrightarrow> s' = s"

definition tps :: "('v ev, 'v global_state) ES" where
  "tps \<equiv> \<lparr>
    init = (=) gs_init,
    trans = gs_trans
  \<rparr>"

lemmas tps_trans_defs = write2_def read2_def prepare_def acquire_rd_lock_def acquire_wr_lock_def
                        acquire_no_lock_def nok_def (*commit_def*) abort_def
                        user_commit_def tm_commit_def tm_abort_def tm_ready_c_def tm_ready_a_def

lemmas tps_defs = tps_def gs_init_def

lemma tps_trans [simp]: "trans tps = gs_trans" by (simp add: tps_def)


end