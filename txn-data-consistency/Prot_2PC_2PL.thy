section \<open>Two Phase Commit (2PC) with Two Phase Locking (2PL)\<close>

theory Prot_2PC_2PL
  imports Key_Value_Stores
begin

subsection \<open>2PC Event system\<close>

subsubsection \<open>State\<close>

datatype status_rm = working | prepared | okay | notokay | committed | aborted
datatype status_tm = tm_init | tm_prepared | tm_committed | tm_aborted

record tm_state =
  tm_status :: status_tm
  tm_tid :: txid0
  tm_view :: view

typedecl rmid
consts loc :: "key \<Rightarrow> rmid"

record 'v rm_state =
  rm_db :: "'v kv_store"
  rm_fingerpr :: "'v fingerpr"
  rm_status :: status_rm
  rm_tid :: txid0

type_synonym 'v rms_state = "rmid \<Rightarrow> 'v rm_state"

record 'v global_state =
  tm :: tm_state
  rms :: "'v rms_state"


subsubsection \<open>Events\<close>

datatype 'v ev = Write2 rmid key 'v | Read2 rmid key 'v |
                 Prepare rmid | OK rmid | NOK rmid | Commit rmid | Abort rmid | Ready rmid |
                 User_Commit | TM_Commit | TM_Abort | TM_ReadyC | TM_ReadyA | TM_Skip

definition other_rms_unchanged where
  "other_rms_unchanged rm rmss rmss' \<equiv> (\<forall>rm'. rm' \<noteq> rm \<longrightarrow> rmss' rm' = rmss rm')"

abbreviation tm_other_rms_unchanged where
  "tm_other_rms_unchanged rm s s' \<equiv> tm s' = tm s \<and> other_rms_unchanged rm (rms s) (rms s')"

abbreviation tid_match where
  "tid_match s rm \<equiv> rm_tid (rms s rm) = tm_tid (tm s)"

abbreviation rm_status_trans where
  "rm_status_trans s rm s' from_stat to_stat \<equiv>
      rm_status (rms s rm) = from_stat
    \<and> rm_db (rms s' rm) = rm_db (rms s rm)
    \<and> rm_fingerpr (rms s' rm) = rm_fingerpr (rms s rm)
    \<and> rm_status (rms s' rm) = to_stat
    \<and> rm_tid (rms s' rm) = rm_tid (rms s rm)
    \<and> tm_other_rms_unchanged rm s s'"

fun tid_inc :: "txid0 \<Rightarrow> txid0" where
  "tid_inc (Tn_cl sn cl) = Tn_cl (Suc sn) cl"

definition write2 where
  "write2 s rm k v s' \<equiv> loc k = rm
                        \<and> rm_status (rms s rm) = working
                        \<and> tid_match s rm
                        \<and> rm_fingerpr (rms s' rm) = update_fp (rm_fingerpr (rms s rm)) (Write k v)
                        \<and> rm_status (rms s' rm) = working
                        \<and> rm_db (rms s' rm) = rm_db (rms s rm)
                        \<and> rm_tid (rms s' rm) = rm_tid (rms s rm)
                        \<and> tm_other_rms_unchanged rm s s'"

definition read2 where
  "read2 s rm k v s' \<equiv> loc k = rm 
                        \<and> rm_status (rms s rm) = working
                        \<and> tid_match s rm
                        \<and> rm_fingerpr (rms s' rm) = update_fp (rm_fingerpr (rms s rm)) (Read k v)
                        \<comment> \<open>\<and> ov = (rm_main_db (rms s rm) ++ rm_shadow_db (rms s rm)) k\<close>
                        \<and> rm_status (rms s' rm) = working
                        \<and> rm_db (rms s' rm) = rm_db (rms s rm)
                        \<and> rm_tid (rms s' rm) = rm_tid (rms s rm)
                        \<and> tm_other_rms_unchanged rm s s'"

definition prepare where
  "prepare s rm s' \<equiv> tm_status (tm s) = tm_prepared
                      \<and> rm_status_trans s rm s' working prepared"

definition ok where \<comment>\<open>Lock acquired\<close>
  "ok s rm s' \<equiv> tm_status (tm s) = tm_prepared
                \<and> rm_status_trans s rm s' prepared okay"

definition nok where \<comment>\<open>Lock not available\<close>
  "nok s rm s' \<equiv> tm_status (tm s) = tm_prepared
                \<and> rm_status_trans s rm s' prepared notokay"

definition commit where
  "commit s rm s' \<equiv> rm_status (rms s rm) = okay
                    \<and> tm_status (tm s) = tm_committed
                    \<and> rm_db (rms s' rm) =  update_kv (rm_tid (rms s rm)) (rm_fingerpr (rms s rm))
                                                     (tm_view (tm s)) (rm_db (rms s rm)) \<comment>\<open>?\<close>
                    \<and> rm_fingerpr (rms s' rm) = Map.empty
                    \<and> rm_status (rms s' rm) = committed
                    \<and> rm_tid (rms s' rm) = rm_tid (rms s rm)
                    \<and> tm_other_rms_unchanged rm s s'"

definition abort where \<comment>\<open>Lock released (if starting from okay)\<close>
  "abort s rm s' \<equiv> (rm_status (rms s rm) = okay \<or>
                    rm_status (rms s rm) = notokay)
                    \<and> tm_status (tm s) = tm_aborted
                    \<and> rm_db (rms s' rm) = rm_db (rms s rm)
                    \<and> rm_fingerpr (rms s' rm) = Map.empty
                    \<and> rm_status (rms s' rm) = aborted
                    \<and> rm_tid (rms s' rm) = rm_tid (rms s rm)
                    \<and> tm_other_rms_unchanged rm s s'"

definition ready where \<comment>\<open>Lock released (if starting from committed)\<close>
  "ready s rm s' \<equiv> ((rm_status (rms s rm) = committed \<and> tm_status (tm s) = tm_committed)
                      \<or> (rm_status (rms s rm) = aborted \<and> tm_status (tm s) = tm_aborted))
                   \<and> rm_status (rms s' rm) = working
                   \<and> rm_tid (rms s' rm) = tid_inc (rm_tid (rms s rm))
                   \<and> rm_db (rms s' rm) = rm_db (rms s rm)
                   \<and> rm_fingerpr (rms s' rm) = rm_fingerpr (rms s rm)
                   \<and> tm_other_rms_unchanged rm s s'"

definition user_commit where
  "user_commit s s' \<equiv> tm_status (tm s) = tm_init
                      \<and> tm_status (tm s') = tm_prepared
                      \<and> tm_tid (tm s') = tm_tid (tm s)
                      \<and> tm_view (tm s') = tm_view (tm s)
                      \<and> rms s' = rms s"

definition tm_commit where
  "tm_commit s s' \<equiv> tm_status (tm s) = tm_prepared
                    \<and> (\<forall>rm. rm_status (rms s rm) = okay)
                    \<and> tm_status (tm s') = tm_committed
                    \<and> tm_tid (tm s') = tm_tid (tm s)
                    \<and> tm_view (tm s') = tm_view (tm s)
                    \<and> rms s' = rms s"

definition tm_abort where
  "tm_abort s s' \<equiv> (tm_status (tm s) = tm_prepared
                     \<and> (\<exists>rm. rm_status (rms s rm) = notokay)
                     \<and> (\<forall>rm. rm_status (rms s rm) = okay \<or> rm_status (rms s rm) = notokay))
                    \<and> tm_status (tm s') = tm_aborted
                    \<and> tm_tid (tm s') = tm_tid (tm s)
                    \<and> tm_view (tm s') = tm_view (tm s)
                    \<and> rms s' = rms s"

definition tm_ready_c where
  "tm_ready_c s s' \<equiv> tm_status (tm s) = tm_committed
                    \<and> (\<forall>rm. rm_status (rms s rm) = working \<and> rm_tid (rms s rm) = tid_inc (tm_tid (tm s)))
                    \<and> tm_status (tm s') = tm_init
                    \<and> tm_tid (tm s') = tid_inc (tm_tid (tm s))
                    \<and> tm_view (tm s') = tm_view (tm s) \<comment>\<open>Should see its own transaction?\<close>
                    \<and> rms s' = rms s"

definition tm_ready_a where
  "tm_ready_a s s' \<equiv> tm_status (tm s) = tm_aborted
                    \<and> (\<forall>rm. rm_status (rms s rm) = working \<and> rm_tid (rms s rm) = tid_inc (tm_tid (tm s)))
                    \<and> tm_status (tm s') = tm_init
                    \<and> tm_tid (tm s') = tid_inc (tm_tid (tm s))
                    \<and> tm_view (tm s') = tm_view (tm s) \<comment>\<open>Should see its own transaction?\<close>
                    \<and> rms s' = rms s"

consts cl0 :: cl_id
text\<open>The Event System\<close>
definition gs_init :: "'v global_state" where
  "gs_init \<equiv> \<lparr> 
    tm = \<lparr> tm_status = tm_init, tm_tid = Tn_cl 0 cl0, tm_view = view_init \<rparr>,
    rms = (\<lambda>rm. \<lparr> rm_db = kvs_init, rm_fingerpr = Map.empty, 
                  rm_status = working, rm_tid = Tn_cl 0 cl0 \<rparr>)
  \<rparr>"

fun gs_trans :: "'v global_state \<Rightarrow> 'v ev \<Rightarrow> 'v global_state \<Rightarrow> bool" where
  "gs_trans s (Write2 rm k v) s' \<longleftrightarrow> write2 s rm k v s'" |
  "gs_trans s (Read2 rm k ov) s' \<longleftrightarrow> read2 s rm k ov s'" |
  "gs_trans s (Prepare rm)    s' \<longleftrightarrow> prepare s rm s'" |
  "gs_trans s (OK rm)         s' \<longleftrightarrow> ok s rm s'" |
  "gs_trans s (NOK rm)        s' \<longleftrightarrow> nok s rm s'" |
  "gs_trans s (Commit rm)     s' \<longleftrightarrow> commit s rm s'" |
  "gs_trans s (Abort rm)      s' \<longleftrightarrow> abort s rm s'" |
  "gs_trans s (Ready rm)      s' \<longleftrightarrow> ready s rm s'" |
  "gs_trans s User_Commit     s' \<longleftrightarrow> user_commit s s'" |
  "gs_trans s TM_Commit       s' \<longleftrightarrow> tm_commit s s'" |
  "gs_trans s TM_Abort        s' \<longleftrightarrow> tm_abort s s'" |
  "gs_trans s TM_ReadyC       s' \<longleftrightarrow> tm_ready_c s s'" |
  "gs_trans s TM_ReadyA       s' \<longleftrightarrow> tm_ready_a s s'" |
  "gs_trans s TM_Skip         s' \<longleftrightarrow> s' = s"

definition tps :: "('v ev, 'v global_state) ES" where
  "tps \<equiv> \<lparr>
    init = (=) gs_init,
    trans = gs_trans
  \<rparr>"

lemmas tps_trans_defs = prepare_def ok_def nok_def (*commit_def*) abort_def ready_def
                        user_commit_def tm_commit_def tm_abort_def tm_ready_c_def tm_ready_a_def

lemmas tps_defs = tps_def gs_init_def

lemma tps_trans [simp]: "trans tps = gs_trans" by (simp add: tps_def)


end