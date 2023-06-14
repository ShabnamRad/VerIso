section \<open>Eiger Port Plus Protocol Satisfying CCv (Causal+)\<close>

theory "EP+_TCCv"
  imports Execution_Tests
begin

section \<open>Event system & Refinement from ET_ES to tps\<close>

subsection \<open>State\<close>

type_synonym key = key
type_synonym tstmp = nat
type_synonym dep_set = "(key \<times> txid) set"

\<comment> \<open>Client State\<close>
datatype 'v txn_state =
  Idle | RtxnInProg "key set" "key \<rightharpoonup> ('v \<times> txid)" | WtxnPrep "key \<rightharpoonup> 'v" | WtxnCommit tstmp "key \<rightharpoonup> 'v" dep_set

record 'v cl_conf =
  cl_state :: "'v txn_state"
  cl_sn :: sqn
  cl_clock :: tstmp
  cl_ctx :: dep_set \<comment> \<open>history variable\<close>
  gst :: tstmp
  lst_map :: "key \<Rightarrow> tstmp"

definition dep_set_init :: dep_set where
  "dep_set_init \<equiv> \<Union>k. {(k, T0)}"

\<comment> \<open>Server State\<close>
datatype 'v ver_state = No_Ver | Prep (get_ts: tstmp) (get_val: 'v)
  | Commit (get_ts: tstmp) (get_val: 'v) "txid0 set" (get_dep_set: dep_set)

fun is_committed :: "'v ver_state \<Rightarrow> bool" where
  "is_committed (Commit _ _ _ _) = True" |
  "is_committed _ = False"

fun is_prepared :: "'v ver_state \<Rightarrow> bool" where
  "is_prepared (Prep _ _) = True" |
  "is_prepared _ = False"

type_synonym 'v wtxn_state = "txid \<Rightarrow> 'v ver_state"

record 'v svr_conf =
  svr_state :: "'v wtxn_state"
  svr_clock :: tstmp
  lst :: tstmp

abbreviation wtxns_emp :: "txid \<Rightarrow> 'v ver_state" where
  "wtxns_emp \<equiv> (\<lambda>t. No_Ver)"

\<comment> \<open>Global State\<close>
record 'v global_conf = 
  cls :: "cl_id \<Rightarrow> 'v cl_conf"
  svrs :: "key \<Rightarrow> 'v svr_conf"
  rtxn_rts :: "txid0 \<rightharpoonup> tstmp"
  wtxn_cts :: "txid \<rightharpoonup> tstmp"
  commit_order :: "key \<Rightarrow> txid list"
  \<comment> \<open>history variable: order of client commit for write transactions\<close>


subsection \<open>Functions\<close>

subsubsection \<open>Translator functions\<close>

abbreviation get_txn :: "'v global_conf \<Rightarrow> cl_id \<Rightarrow> txid0" where
  "get_txn s cl \<equiv> Tn_cl (cl_sn (cls s cl)) cl"

abbreviation get_wtxn :: "'v global_conf \<Rightarrow> cl_id \<Rightarrow> txid" where
  "get_wtxn s cl \<equiv> Tn (get_txn s cl)"

fun get_cl_w :: "txid \<Rightarrow> cl_id" where
  "get_cl_w T0 = undefined" |
  "get_cl_w (Tn (Tn_cl sn cl)) = cl"

fun get_sn_w :: "txid \<Rightarrow> sqn" where
  "get_sn_w T0 = undefined" |
  "get_sn_w (Tn (Tn_cl sn cl)) = sn"

fun get_rs :: "'v ver_state \<Rightarrow> txid0 set" where
  "get_rs No_Ver = undefined" |
  "get_rs (Prep _ _) = {}" |
  "get_rs (Commit _ _ rs _) = rs"


subsubsection \<open>Customised dom and ran functions for svr_state\<close>

definition wtxns_dom :: "'v wtxn_state \<Rightarrow> txid set" where
  "wtxns_dom wtxns \<equiv> {t. wtxns t \<noteq> No_Ver}"

definition wtxns_vran :: "'v wtxn_state \<Rightarrow> 'v set" where
  "wtxns_vran wtxns \<equiv> {get_val (wtxns t) | t. t \<in> wtxns_dom wtxns}"

definition wtxns_rsran :: "'v wtxn_state \<Rightarrow> txid0 set" where
  "wtxns_rsran wtxns \<equiv> \<Union>{get_rs (wtxns t) | t. t \<in> wtxns_dom wtxns}"


subsubsection \<open>Execution Test in terms of dep_set\<close>

definition visTx' :: "'v kv_store \<Rightarrow> dep_set \<Rightarrow> txid set" where
  "visTx' K u \<equiv> kvs_writers K \<inter> snd ` u"

definition closed' :: "'v kv_store \<Rightarrow> dep_set \<Rightarrow> txid rel \<Rightarrow> bool" where
  "closed' K u r \<longleftrightarrow> closed_general (visTx' K u) (r\<inverse>) (read_only_Txs K)"


subsubsection \<open>Reading functions\<close>

definition ver_committed_before :: "'v ver_state \<Rightarrow> tstmp \<Rightarrow> bool" where
  "ver_committed_before ver ts \<longleftrightarrow> is_committed ver \<and> get_ts ver \<le> ts" 

definition ver_committed_after :: "'v ver_state \<Rightarrow> tstmp \<Rightarrow> bool" where
  "ver_committed_after ver ts \<longleftrightarrow> is_committed ver \<and> get_ts ver \<ge> ts" 


\<comment> \<open>returns the writer transaction id of the version read at read timestamp (highest cts less than ts)\<close>
definition at :: "'v wtxn_state \<Rightarrow> tstmp \<Rightarrow> txid" where 
  "at wtxns rts = (ARG_MAX (get_ts o wtxns) t. ver_committed_before (wtxns t) rts)"

definition newest_own_write :: "'v wtxn_state \<Rightarrow> tstmp \<Rightarrow> cl_id \<rightharpoonup> txid" where
  "newest_own_write wtxns ts cl = 
     (if \<exists>t. ver_committed_after (wtxns t) ts \<and> get_cl_w t = cl
     then Some (ARG_MAX (get_ts o wtxns) t. ver_committed_after (wtxns t) ts \<and> get_cl_w t = cl)
     else None)"

definition read_at :: "'v wtxn_state \<Rightarrow> tstmp \<Rightarrow> cl_id \<Rightarrow> txid" where
  "read_at wtxns ts cl \<equiv> let t = at wtxns ts in
    (case newest_own_write wtxns (get_ts (wtxns t)) cl of
      None \<Rightarrow> t |
      Some t' \<Rightarrow> t')"


subsubsection \<open>Helper functions\<close>

definition add_to_readerset :: "'v wtxn_state \<Rightarrow> txid0 \<Rightarrow> txid \<Rightarrow> 'v wtxn_state" where
  "add_to_readerset wtxns t t_wr \<equiv> (case wtxns t_wr of
    Commit cts v rs deps \<Rightarrow> wtxns (t_wr := Commit cts v (insert t rs) deps) |
    _ \<Rightarrow> wtxns)"

definition pending_wtxns_ts :: "'v wtxn_state \<Rightarrow> tstmp set" where
  "pending_wtxns_ts wtxns \<equiv> {prep_t. \<exists>t v. wtxns t = Prep prep_t v}"

definition get_view :: "'v global_conf \<Rightarrow> cl_id \<Rightarrow> dep_set" where
  "get_view s cl \<equiv> {(k, t). 
    \<exists>cts v rs deps. svr_state (svrs s k) t = Commit cts v rs deps \<and>
    (cts \<le> gst (cls s cl) \<or> get_cl_w t = cl)}"

definition get_ctx :: "'v global_conf \<Rightarrow> (key \<rightharpoonup> ('v \<times> txid)) \<Rightarrow> dep_set" where
  "get_ctx s kvt_map \<equiv> \<Union>{insert (k, t) deps | k t deps.
    \<exists>cts v rs. svr_state (svrs s k) t = Commit cts v rs deps \<and>
    kvt_map k = Some (v, t)}"

definition view_of :: "(key \<Rightarrow> txid list) \<Rightarrow> dep_set \<Rightarrow> view" where
  "view_of corder u \<equiv> (\<lambda>k. {THE i. i < length (corder k) \<and> corder k ! i = t
    | t. (k, t) \<in> u \<and> t \<in> set (corder k)})"


subsection \<open>Events\<close>

datatype 'v ev =
  RInvoke cl_id "key set" | Read cl_id key 'v txid | RDone cl_id "key \<rightharpoonup> ('v \<times> txid)" sqn view |
  WInvoke cl_id "key \<rightharpoonup> 'v" | WCommit cl_id "key \<rightharpoonup> 'v" tstmp sqn view | WDone cl_id "key \<rightharpoonup> 'v" |
  RegR key txid0 txid tstmp | PrepW key txid 'v | CommitW key txid 'v tstmp dep_set | Skip2

abbreviation is_curr_t :: "'v global_conf \<Rightarrow> txid0 \<Rightarrow> bool" where
  "is_curr_t s t \<equiv> cl_sn (cls s (get_cl t)) = get_sn t"

abbreviation is_curr_wt :: "'v global_conf \<Rightarrow> txid \<Rightarrow> bool" where
  "is_curr_wt s t \<equiv> t \<noteq> T0 \<and> cl_sn (cls s (get_cl_w t)) = get_sn_w t"


subsubsection \<open>Client Events\<close>

definition read_invoke :: "cl_id \<Rightarrow> key set \<Rightarrow> 'v global_conf \<Rightarrow> 'v global_conf \<Rightarrow> bool" where
  "read_invoke cl keys s s' \<equiv>
    keys \<noteq> {} \<and>
    finite keys \<and>
    cl_state (cls s cl) = Idle \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := RtxnInProg keys Map.empty,
        cl_clock := Suc (cl_clock (cls s cl)),
        gst := Min (range (lst_map (cls s cl)))
      \<rparr>)
    \<rparr>"

definition read :: "cl_id \<Rightarrow> key \<Rightarrow> 'v \<Rightarrow> txid \<Rightarrow> 'v global_conf \<Rightarrow> 'v global_conf \<Rightarrow> bool" where
  "read cl k v t s s' \<equiv> 
    \<comment> \<open>reads server k's value v for client transaction, lst, and svr_clock\<close>
    (\<exists>cts rs deps. svr_state (svrs s k) t = Commit cts v rs deps \<and> get_txn s cl \<in> rs) \<and>
    (\<exists>keys kvt_map. cl_state (cls s cl) = RtxnInProg keys kvt_map \<and> k \<in> keys \<and> kvt_map k = None) \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state :=
          (case cl_state (cls s cl) of RtxnInProg keys kvt_map \<Rightarrow> RtxnInProg keys (kvt_map (k \<mapsto> (v, t)))),
        cl_clock := Suc (max (cl_clock (cls s cl)) (svr_clock (svrs s k))),
        lst_map := (lst_map (cls s cl)) (k := lst (svrs s k))
      \<rparr>)
    \<rparr>"

definition read_done :: "cl_id \<Rightarrow> (key \<rightharpoonup> ('v \<times> txid)) \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> 'v global_conf \<Rightarrow> 'v global_conf \<Rightarrow> bool" where
  "read_done cl kvt_map sn u'' s s' \<equiv>
    sn = cl_sn (cls s cl) \<and>
    u'' = view_of (commit_order s) (cl_ctx (cls s cl) \<union> get_ctx s kvt_map) \<and>
    cl_state (cls s cl) = RtxnInProg (dom kvt_map) kvt_map \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := Idle,
        cl_sn := Suc (cl_sn (cls s cl)),
        cl_clock := Suc (cl_clock (cls s cl)),
        cl_ctx := cl_ctx (cls s cl) \<union> get_ctx s kvt_map
      \<rparr>),
      rtxn_rts := (rtxn_rts s) (get_txn s cl \<mapsto> gst (cls s cl))
    \<rparr>"

definition write_invoke :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> 'v global_conf \<Rightarrow> 'v global_conf \<Rightarrow> bool" where
  "write_invoke cl kv_map s s' \<equiv> 
    kv_map \<noteq> Map.empty \<and>
    finite (dom kv_map) \<and>
    cl_state (cls s cl) = Idle \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := WtxnPrep kv_map,
        cl_clock := Suc (cl_clock (cls s cl))
      \<rparr>)
    \<rparr>"

definition write_commit :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> tstmp \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> 'v global_conf \<Rightarrow> 'v global_conf \<Rightarrow> bool" where
  "write_commit cl kv_map commit_t sn u'' s s' \<equiv>
    sn = cl_sn (cls s cl) \<and>            \<comment> \<open>@{term sn} needed in mediator function, not in event\<close>
    u'' = view_of (commit_order s) (cl_ctx (cls s cl)) \<and>
    cl_state (cls s cl) = WtxnPrep kv_map \<and>
    (\<forall>k \<in> dom kv_map. \<exists>ts v. svr_state (svrs s k) (get_wtxn s cl) = Prep ts v \<and> kv_map k = Some v) \<and>
    commit_t = Max {get_ts (svr_state (svrs s k) (get_wtxn s cl)) | k. k \<in> dom kv_map} \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := WtxnCommit commit_t kv_map (cl_ctx (cls s cl)),
        cl_clock := Suc (max (cl_clock (cls s cl)) commit_t), \<comment> \<open>Why not max of all involved server svr_clocks\<close>
        cl_ctx := cl_ctx (cls s cl) \<union> (\<Union>k \<in> dom kv_map. {(k, get_wtxn s cl)})
      \<rparr>), 
      wtxn_cts := (wtxn_cts s) (get_wtxn s cl \<mapsto> commit_t),
      commit_order :=
        (\<lambda>k. if kv_map k = None then commit_order s k else commit_order s k @ [get_wtxn s cl])
    \<rparr>"

definition write_done :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> 'v global_conf \<Rightarrow> 'v global_conf \<Rightarrow> bool" where
  "write_done cl kv_map s s' \<equiv>
    (\<exists>cts ctx. cl_state (cls s cl) = WtxnCommit cts kv_map ctx \<and>
      (\<forall>k\<in>dom kv_map. \<exists>v rs. svr_state (svrs s k) (get_wtxn s cl) = Commit cts v rs ctx \<and>
         kv_map k = Some v)) \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := Idle,
        cl_sn := Suc (cl_sn (cls s cl)),
        cl_clock := Suc (max (cl_clock (cls s cl)) (Max {svr_clock (svrs s k) | k. k \<in> dom kv_map})),
        lst_map := (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k else lst (svrs s k))
      \<rparr>)
    \<rparr>"


subsubsection \<open>Server Events\<close>

definition register_read :: "key \<Rightarrow> txid0 \<Rightarrow> txid \<Rightarrow> tstmp \<Rightarrow> 'v global_conf \<Rightarrow> 'v global_conf \<Rightarrow> bool" where
  "register_read svr t t_wr gst_ts s s' \<equiv>
    is_curr_t s t \<and>
    (\<exists>keys kvt_map. cl_state (cls s (get_cl t)) = RtxnInProg keys kvt_map \<and> svr \<in> keys \<and> kvt_map svr = None) \<and>
    gst_ts = gst (cls s (get_cl t)) \<and>
    t_wr = read_at (svr_state (svrs s svr)) gst_ts (get_cl t) \<and>
    s' = s \<lparr> svrs := (svrs s)
      (svr := svrs s svr \<lparr>
        svr_state := add_to_readerset (svr_state (svrs s svr)) t t_wr,
        svr_clock := Suc (max (svr_clock (svrs s svr)) (cl_clock (cls s (get_cl t))))
      \<rparr>)
    \<rparr>"

definition prepare_write :: "key \<Rightarrow> txid \<Rightarrow> 'v \<Rightarrow> 'v global_conf \<Rightarrow> 'v global_conf \<Rightarrow> bool" where
  "prepare_write svr t v s s' \<equiv>
    is_curr_wt s t \<and>
    \<comment> \<open>get client's value v for svr and cl_clock\<close>
    (\<exists>kv_map. cl_state (cls s (get_cl_w t)) = WtxnPrep kv_map \<and> kv_map svr = Some v) \<and>
    svr_state (svrs s svr) t = No_Ver \<and>
    s' = s \<lparr> svrs := (svrs s)
      (svr := svrs s svr \<lparr>
        svr_state := (svr_state (svrs s svr))(t := Prep (svr_clock (svrs s svr)) v),
        svr_clock := Suc (max (svr_clock (svrs s svr)) (cl_clock (cls s (get_cl_w t)))) 
      \<rparr>)
    \<rparr>"

definition commit_write :: "key \<Rightarrow> txid \<Rightarrow> 'v \<Rightarrow> tstmp \<Rightarrow> dep_set \<Rightarrow> 'v global_conf \<Rightarrow> 'v global_conf \<Rightarrow> bool" where
  "commit_write svr t v cts deps s s' \<equiv>
    is_curr_wt s t \<and>
    (\<exists>kv_map. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map deps \<and> svr \<in> dom kv_map) \<and>
    is_prepared (svr_state (svrs s svr) t) \<and> 
    v = get_val (svr_state (svrs s svr) t) \<and>
    s' = s \<lparr> svrs := (svrs s)
      (svr := svrs s svr \<lparr>
        svr_state := (svr_state (svrs s svr))(t := Commit cts v {} deps),
        svr_clock := Suc (max (svr_clock (svrs s svr)) (cl_clock (cls s (get_cl_w t)))),
        lst := if pending_wtxns_ts ((svr_state (svrs s svr)) (t := Commit cts v {} deps)) = {}
               then svr_clock (svrs s svr)
               else Min (pending_wtxns_ts ((svr_state (svrs s svr)) (t := Commit cts v {} deps)))
      \<rparr>)
    \<rparr>"


subsection \<open>The Event System\<close>

definition state_init :: "'v global_conf" where
  "state_init \<equiv> \<lparr> 
    cls = (\<lambda>cl. \<lparr> cl_state = Idle,
                  cl_sn = 0,
                  cl_clock = 0,
                  cl_ctx = dep_set_init,
                  gst = 0,
                  lst_map = (\<lambda>svr. 0) \<rparr>),
    svrs = (\<lambda>svr. \<lparr> svr_state = (\<lambda>t. No_Ver) (T0 := Commit 0 undefined {} {}),
                    svr_clock = 0,
                    lst = 0 \<rparr>),
    rtxn_rts = Map.empty,
    wtxn_cts = Map.empty (T0 \<mapsto> 0),
    commit_order = (\<lambda>k. [T0])
  \<rparr>"

fun state_trans :: "'v global_conf \<Rightarrow> 'v ev \<Rightarrow> 'v global_conf \<Rightarrow> bool" where
  "state_trans s (RInvoke cl keys)          s' \<longleftrightarrow> read_invoke cl keys s s'" |
  "state_trans s (Read cl k v t)            s' \<longleftrightarrow> read cl k v t s s'" |
  "state_trans s (RDone cl kvt_map sn u'')  s' \<longleftrightarrow> read_done cl kvt_map sn u'' s s'" |
  "state_trans s (WInvoke cl kv_map)        s' \<longleftrightarrow> write_invoke cl kv_map s s'" |
  "state_trans s (WCommit cl kv_map cts sn u'') s' \<longleftrightarrow> write_commit cl kv_map cts sn u'' s s'" |
  "state_trans s (WDone cl kv_map)          s' \<longleftrightarrow> write_done cl kv_map s s'" |
  "state_trans s (RegR svr t i rts)         s' \<longleftrightarrow> register_read svr t i rts s s'" |
  "state_trans s (PrepW svr t v)            s' \<longleftrightarrow> prepare_write svr t v s s'" |
  "state_trans s (CommitW svr t v cts deps) s' \<longleftrightarrow> commit_write svr t v cts deps s s'" |
  "state_trans s Skip2 s' \<longleftrightarrow> s' = s"

definition tps :: "('v ev, 'v global_conf) ES" where
  "tps \<equiv> \<lparr>
    init = (=) state_init,
    trans = state_trans
  \<rparr>"

lemmas tps_trans_defs = read_invoke_def read_def read_done_def write_invoke_def write_commit_def
  write_done_def register_read_def prepare_write_def commit_write_def

lemmas tps_defs = tps_def state_init_def

lemma tps_trans [simp]: "trans tps = state_trans" by (simp add: tps_def)


subsection \<open>Simulation function\<close>

abbreviation is_done :: "'v global_conf \<Rightarrow> txid0 \<Rightarrow> bool" where
  "is_done s t \<equiv> cl_sn (cls s (get_cl t)) > get_sn t"

term "Set.filter (is_done s) rs"

definition txn_to_vers :: "'a global_conf \<Rightarrow> key \<Rightarrow> txid \<Rightarrow> 'a version" where
  "txn_to_vers s k = (\<lambda>t. case svr_state (svrs s k) t of
        Prep ts v \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = {}\<rparr> |
        Commit cts v rs deps \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = {t \<in> rs. is_done s t}\<rparr>)"

definition kvs_of_s :: "'v global_conf \<Rightarrow> 'v kv_store" where
  "kvs_of_s s \<equiv> (\<lambda>k. map (txn_to_vers s k) (commit_order s k))"

lemmas kvs_of_s_defs = kvs_of_s_def txn_to_vers_def

definition views_of_s :: "'v global_conf \<Rightarrow> (cl_id \<Rightarrow> view)" where
  "views_of_s s = (\<lambda>cl. view_of (commit_order s) (cl_ctx (cls s cl)))"

definition sim :: "'v global_conf \<Rightarrow> 'v config" where         
  "sim s = (kvs_of_s s, views_of_s s)"

lemmas sim_defs = sim_def kvs_of_s_def views_of_s_def

subsection \<open>Mediator function\<close>

fun med :: "'v ev \<Rightarrow> 'v label" where
  "med (RDone cl kvt_map sn u'') = ET cl sn u'' (\<lambda>k. case_op_type (map_option fst (kvt_map k)) None)" |
  "med (WCommit cl kv_map _ sn u'') = ET cl sn u'' (\<lambda>k. case_op_type None (kv_map k))" |
  "med _ = ETSkip"

end