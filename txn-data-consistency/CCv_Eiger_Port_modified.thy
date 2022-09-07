section \<open>Modified Eiger Port Protocol Satisfying CCv (Causal+)\<close>

theory CCv_Eiger_Port_modified
  imports Execution_Tests
begin

subsection \<open>Event system & Refinement from ET_ES to tps\<close>

subsubsection \<open>State\<close>

typedecl svr_id
type_synonym timestamp = nat
consts loc :: "key \<Rightarrow> svr_id" 

record 'v eversion =
  ev_value :: 'v
  ev_commit_t :: timestamp
  ev_gst :: timestamp
  ev_cl :: cl_id
  ev_is_pending :: bool

type_synonym 'v datastore = "key \<Rightarrow> 'v eversion list"
consts cl0 :: cl_id

definition eversion_init :: "'v eversion" where
  "eversion_init \<equiv> \<lparr>ev_value = undefined, ev_commit_t = 0, ev_gst = 0, ev_cl = cl0, ev_is_pending = False\<rparr>"

\<comment> \<open>Server State\<close>
record 'v server =
  clock :: timestamp
  lst :: timestamp
  pending_wtxns :: "timestamp list"
  DS :: "'v datastore"

\<comment> \<open>Client State\<close>
record client =
  lst_map :: "svr_id \<Rightarrow> timestamp"
  gst :: timestamp

\<comment> \<open>Global State\<close>
record 'v state = 
  svrs :: "svr_id \<Rightarrow> 'v server"
  cls :: "cl_id \<Rightarrow> client"

\<comment> \<open>Events\<close>

fun at :: "'v eversion list \<Rightarrow> timestamp \<Rightarrow> 'v eversion" where
  "at [] ts = eversion_init" |
  "at (ver # vl) ts = (if ts \<ge> ev_commit_t ver then ver else at vl ts)"

fun newest_own_write_val :: "'v eversion list \<Rightarrow> timestamp \<Rightarrow> cl_id \<Rightarrow> 'v eversion option" where
  "newest_own_write_val [] ts cl = None" |
  "newest_own_write_val (v # vl) ts cl =
    (if ev_commit_t v \<ge> ts then
      (if ev_cl v = cl then Some v else newest_own_write_val vl ts cl)
     else None)"

definition read :: "'v eversion list \<Rightarrow> timestamp \<Rightarrow> cl_id \<Rightarrow> 'v" where
  "read vl rts cl \<equiv> (let ver = at vl rts in
   (case newest_own_write_val vl (ev_commit_t ver) cl of None \<Rightarrow> ev_value ver | Some v \<Rightarrow> ev_value v))"

definition read_only_txns :: "key set \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> cl_id \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
  "read_only_txns keys vals cl s s' \<equiv> 
    gst (cls s' cl) = max (gst (cls s cl)) (Min (range (lst_map (cls s cl)))) \<and>
    (\<forall>k\<in>keys. vals k = Some (read (DS (svrs s (loc k)) k) (gst (cls s' cl)) cl) \<and>
     lst_map (cls s' cl) (loc k) = lst (svrs s (loc k))) \<and>
    dom vals = keys \<and>
    (\<forall>l. l \<notin> loc ` keys \<longrightarrow> lst_map (cls s' cl) l = lst_map (cls s cl) l)"

(*definition prepare_write :: "key \<Rightarrow> 'v \<Rightarrow> cl_id \<Rightarrow> timestamp \<Rightarrow> 'v eversion \<times> timestamp" where
  "prepare_write k v cl ts \<equiv> (let pending_t = clock (svrs s cl))"

definition write_coord :: "key \<Rightarrow> 'v \<Rightarrow> cl_id \<Rightarrow> timestamp \<Rightarrow> timestamp" where
  "write_coord k v cl ts \<equiv> "*)