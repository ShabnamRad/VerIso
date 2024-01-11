section \<open>Eiger Port Plus Protocol Event System\<close>

theory "EP+"
  imports Execution_Tests
begin

section \<open>Event system\<close>

subsection \<open>State\<close>

type_synonym key = key
type_synonym tstmp = nat
type_synonym view_txid = "key \<Rightarrow> txid set"
type_synonym readerset = "txid0 \<rightharpoonup> (tstmp \<times> tstmp)" \<comment> \<open>t, svr_clock at read, svr_lst at read\<close>

\<comment> \<open>For unique transaction timestamps: (ts, cl_id)\<close>
instantiation prod :: (linorder, linorder) linorder
begin

definition
  less_prod_def : "p1 < p2 = (fst p1 < fst p2 \<or> (fst p1 = fst p2 \<and> snd p1 < snd p2))" 

definition
  less_eq_prod_def : "p1 \<le> p2 = (fst p1 < fst p2 \<or> (fst p1 = fst p2 \<and> snd p1 \<le> snd p2))" 

instance proof
  fix x y z :: "'a ::linorder \<times> 'b::linorder"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (auto simp add: less_prod_def less_eq_prod_def)
  show "x \<le> x"
    by (auto simp add: less_eq_prod_def)
  show "\<lbrakk>x \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> x \<le> z"
    by (auto simp add: less_eq_prod_def)
  show "\<lbrakk>x \<le> y; y \<le> x\<rbrakk> \<Longrightarrow> x = y"
    by (auto simp add: less_eq_prod_def prod_eq_iff)
  show "x \<le> y \<or> y \<le> x"
    by (auto simp add: less_eq_prod_def)
qed

end

\<comment> \<open>Client State\<close>
datatype 'v txn_state =
  Idle | RtxnInProg "key set" "key \<rightharpoonup> 'v" | WtxnPrep "key \<rightharpoonup> 'v" | WtxnCommit (cl_cts: tstmp) "key \<rightharpoonup> 'v"

record 'v cl_conf =
  cl_state :: "'v txn_state"
  cl_sn :: sqn
  cl_clock :: tstmp
  gst :: tstmp
  lst_map :: "key \<Rightarrow> tstmp"

\<comment> \<open>Server State\<close>
datatype 'v ver_state = No_Ver | Prep (get_ts: tstmp) (get_val: 'v)
  | Commit (get_ts: tstmp) (get_sclk: tstmp) (get_lst: tstmp) (get_val: 'v) readerset

abbreviation rs_emp :: readerset where "rs_emp \<equiv> Map.empty"

fun is_committed :: "'v ver_state \<Rightarrow> bool" where
  "is_committed (Commit _ _ _ _ _) = True" |
  "is_committed _ = False"

fun is_prepared :: "'v ver_state \<Rightarrow> bool" where
  "is_prepared (Prep _ _) = True" |
  "is_prepared _ = False"

type_synonym 'v wtxn_state = "txid \<Rightarrow> 'v ver_state"

record 'v svr_conf =
  svr_state :: "'v wtxn_state"
  svr_clock :: tstmp
  svr_lst :: tstmp

abbreviation wtxns_emp :: "txid \<Rightarrow> 'v ver_state" where
  "wtxns_emp \<equiv> (\<lambda>t. No_Ver)"

\<comment> \<open>Global State\<close>
record 'v global_conf =
  cls :: "cl_id \<Rightarrow> 'v cl_conf"
  svrs :: "key \<Rightarrow> 'v svr_conf"
  rtxn_rts :: "txid0 \<rightharpoonup> tstmp"
  wtxn_cts :: "txid \<rightharpoonup> tstmp"
  cts_order :: "key \<Rightarrow> txid list"


subsection \<open>Functions\<close>

subsubsection \<open>Translator functions\<close>

abbreviation get_txn :: "('v, 'm) global_conf_scheme \<Rightarrow> cl_id \<Rightarrow> txid0" where
  "get_txn s cl \<equiv> Tn_cl (cl_sn (cls s cl)) cl"

abbreviation get_wtxn :: "('v, 'm) global_conf_scheme \<Rightarrow> cl_id \<Rightarrow> txid" where
  "get_wtxn s cl \<equiv> Tn (get_txn s cl)"

fun get_cl_w :: "txid \<Rightarrow> cl_id" where
  "get_cl_w T0 = undefined" |
  "get_cl_w (Tn (Tn_cl sn cl)) = cl"

fun get_sn_w :: "txid \<Rightarrow> sqn" where
  "get_sn_w T0 = undefined" |
  "get_sn_w (Tn (Tn_cl sn cl)) = sn"

fun get_rs :: "'v ver_state \<Rightarrow> readerset" where
  "get_rs No_Ver = undefined" |
  "get_rs (Prep _ _) = rs_emp" |
  "get_rs (Commit _ _ _ _ rs) = rs"


subsubsection \<open>Customised dom and ran functions for svr_state\<close>

definition wtxns_dom :: "'v wtxn_state \<Rightarrow> txid set" where
  "wtxns_dom wtxns \<equiv> {t. wtxns t \<noteq> No_Ver}"

definition wtxns_vran :: "'v wtxn_state \<Rightarrow> 'v set" where
  "wtxns_vran wtxns \<equiv> {get_val (wtxns t) | t. t \<in> wtxns_dom wtxns}"

definition wtxns_rsran :: "'v wtxn_state \<Rightarrow> txid0 set" where
  "wtxns_rsran wtxns \<equiv> \<Union>{dom (get_rs (wtxns t)) | t. t \<in> wtxns_dom wtxns}"


subsubsection \<open>Execution Test in terms of dep_set\<close>

definition visTx' :: "'v kv_store \<Rightarrow> txid set \<Rightarrow> txid set" where
  "visTx' K u \<equiv> kvs_writers K \<inter> u"

definition closed' :: "'v kv_store \<Rightarrow> txid set \<Rightarrow> txid rel \<Rightarrow> bool" where
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

definition add_to_readerset :: "'v wtxn_state \<Rightarrow> txid0 \<Rightarrow> tstmp \<Rightarrow> tstmp \<Rightarrow> txid \<Rightarrow> 'v wtxn_state" where
  "add_to_readerset wtxns t rts rlst t_wr \<equiv> (case wtxns t_wr of
    Commit cts ts lst v rs \<Rightarrow> wtxns (t_wr := Commit cts ts lst v (rs (t \<mapsto> (rts, rlst)))) |
    _ \<Rightarrow> wtxns)"

definition pending_wtxns_ts :: "'v wtxn_state \<Rightarrow> tstmp set" where
  "pending_wtxns_ts wtxns \<equiv> {prep_t. \<exists>t v. wtxns t = Prep prep_t v}"

definition get_view :: "('v, 'm) global_conf_scheme \<Rightarrow> cl_id \<Rightarrow> view_txid" where
  "get_view s cl \<equiv> (\<lambda>k. {t. t \<in> (dom (wtxn_cts s) \<inter> wtxns_dom (svr_state (svrs s k))) \<and>
    (the (wtxn_cts s t) \<le> gst (cls s cl) \<or> get_cl_w t = cl)})"

abbreviation index_of where
  "index_of xs x \<equiv> (THE i. i < length xs \<and> xs ! i = x)"

definition view_of :: "(key \<Rightarrow> txid list) \<Rightarrow> view_txid \<Rightarrow> view" where
  "view_of corder u \<equiv> (\<lambda>k. {index_of (corder k) t | t. t \<in> u k \<and> t \<in> set (corder k)})"

definition ext_corder :: "txid \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> (txid \<Rightarrow> (tstmp \<times> cl_id)) \<Rightarrow> (key \<Rightarrow> txid list) \<Rightarrow> key \<Rightarrow> txid list" where
  "ext_corder t kv_map f corder \<equiv> 
     (\<lambda>k. if kv_map k = None then corder k else insort_key f t (corder k))"

abbreviation is_curr_t :: "('v, 'm) global_conf_scheme \<Rightarrow> txid0 \<Rightarrow> bool" where
  "is_curr_t s t \<equiv> cl_sn (cls s (get_cl t)) = get_sn t"

abbreviation is_curr_wt :: "('v, 'm) global_conf_scheme \<Rightarrow> txid \<Rightarrow> bool" where
  "is_curr_wt s t \<equiv> t \<noteq> T0 \<and> cl_sn (cls s (get_cl_w t)) = get_sn_w t"

abbreviation is_done :: "('v, 'm) global_conf_scheme \<Rightarrow> txid0 \<Rightarrow> bool" where
  "is_done s t \<equiv> cl_sn (cls s (get_cl t)) > get_sn t"

abbreviation is_done_w :: "('v, 'm) global_conf_scheme \<Rightarrow> txid \<Rightarrow> bool" where
  "is_done_w s t \<equiv> t = T0 \<or> (cl_sn (cls s (get_cl_w t)) > get_sn_w t) \<or> 
    (is_curr_wt s t \<and> (\<exists>cts kv_map. cl_state (cls s (get_cl_w t)) = WtxnCommit cts kv_map))"


subsection \<open>Events\<close>

datatype 'v ev =
  RInvoke cl_id "key set" sqn tstmp | Read cl_id key 'v txid tstmp tstmp sqn tstmp
  | RDone cl_id "key \<rightharpoonup> 'v" sqn view tstmp | WInvoke cl_id "key \<rightharpoonup> 'v" sqn tstmp
  | WCommit cl_id "key \<rightharpoonup> 'v" tstmp sqn view tstmp | WDone cl_id "key \<rightharpoonup> 'v" sqn tstmp
  | RegR key txid0 txid tstmp tstmp | PrepW key txid0 'v tstmp | CommitW key txid0 'v tstmp tstmp
  | Skip2

fun commit_ev :: "'v ev \<Rightarrow> bool" where
  "commit_ev (RDone cl kv_map sn u'' clk) = True" |
  "commit_ev (WCommit cl kv_map cts sn u'' clk) = True" |
  "commit_ev _ = False"

fun ev_cl :: "'v ev \<Rightarrow> cl_id option" where
  "ev_cl (RInvoke cl keys sn clk)           = Some cl" |
  "ev_cl (Read cl k v t rts rlst sn clk)    = Some cl" |
  "ev_cl (RDone cl kv_map sn u'' clk)       = Some cl" |
  "ev_cl (WInvoke cl kv_map sn clk)         = Some cl" |
  "ev_cl (WCommit cl kv_map cts sn u'' clk) = Some cl" |
  "ev_cl (WDone cl kv_map sn clk)           = Some cl" |
  "ev_cl _ = None"

fun ev_key :: "'v ev \<Rightarrow> key option" where
  "ev_key (RegR svr t t_wr rts clk)         = Some svr" |
  "ev_key (PrepW svr t v clk)               = Some svr" |
  "ev_key (CommitW svr t v cts clk)         = Some svr" |
  "ev_key _ = None"

fun ev_txn :: "'v ev \<Rightarrow> txid" where
  "ev_txn (RInvoke cl keys sn clk)           = Tn (Tn_cl sn cl)" |
  "ev_txn (Read cl k v t rts rlst sn clk)    = Tn (Tn_cl sn cl)" |
  "ev_txn (RDone cl kv_map sn u'' clk)       = Tn (Tn_cl sn cl)" |
  "ev_txn (WInvoke cl kv_map sn clk)         = Tn (Tn_cl sn cl)" |
  "ev_txn (WCommit cl kv_map cts sn u'' clk) = Tn (Tn_cl sn cl)" |
  "ev_txn (WDone cl kv_map sn clk)           = Tn (Tn_cl sn cl)" |
  "ev_txn (RegR svr t t_wr rts clk)          = Tn t" |
  "ev_txn (PrepW svr t v clk)                = Tn t" |
  "ev_txn (CommitW svr t v cts clk)          = Tn t" |
  "ev_txn Skip2                              = T0" \<comment> \<open>dummy value\<close>

fun ev_clk :: "'v ev \<Rightarrow> tstmp option" where
  "ev_clk (RInvoke cl keys sn clk)           = Some clk" |
  "ev_clk (Read cl k v t rts rlst sn clk)    = Some clk" |
  "ev_clk (RDone cl kv_map sn u'' clk)       = Some clk" |
  "ev_clk (WInvoke cl kv_map sn clk)         = Some clk" |
  "ev_clk (WCommit cl kv_map cts sn u'' clk) = Some clk" |
  "ev_clk (WDone cl kv_map sn clk)           = Some clk" |
  "ev_clk (RegR svr t t_wr rts clk)          = Some clk" |
  "ev_clk (PrepW svr t v clk)                = Some clk" |
  "ev_clk (CommitW svr t v cts clk)          = Some clk" |
  "ev_clk Skip2                              = None" \<comment> \<open>dummy value\<close>

definition ects :: "tstmp \<Rightarrow> cl_id \<Rightarrow> tstmp \<times> cl_id" where
  "ects cts cl = (cts, Suc cl)"

lemma ects_inj: "ects cts cl = ects cts' cl' \<Longrightarrow> cts = cts' \<and> cl = cl'"
  by (simp add: ects_def)

lemma min_ects: "(0, 0) < ects x y" by (auto simp add: less_prod_def ects_def)

fun ev_ects :: "'v ev \<Rightarrow> (tstmp \<times> cl_id) option" where
  "ev_ects (WCommit cl kv_map cts sn u'' clk) = Some (ects cts cl)" |
  "ev_ects _ = None"

lemma ev_ects_Some:
  "ev_ects e = Some (cts, Suc_cl)
  \<Longrightarrow> \<exists>cl kv_map sn u'' clk. e = WCommit cl kv_map cts sn u'' clk \<and> Suc_cl = Suc cl"
  by (cases e, simp_all add: ects_def)

definition unique_ts :: "(txid \<rightharpoonup> tstmp) \<Rightarrow> txid \<Rightarrow> tstmp \<times> cl_id" where
  "unique_ts wtxn_ctss \<equiv> (\<lambda>t. (the (wtxn_ctss t), if t = T0 then 0 else Suc (get_cl_w t)))"

lemma unique_ts_def':
  "unique_ts wtxn_ctss t =
   (if t = T0 then (the (wtxn_ctss T0), 0) else ects (the (wtxn_ctss t)) (get_cl_w t))"
  by (auto simp add: unique_ts_def ects_def)


subsubsection \<open>Client Events\<close>

definition read_invoke_G where
  "read_invoke_G cl keys sn clk s \<equiv>
    keys \<noteq> {} \<and>
    finite keys \<and>
    sn = cl_sn (cls s cl) \<and>
    clk = Suc (cl_clock (cls s cl)) \<and>
    cl_state (cls s cl) = Idle"

definition read_invoke_U where
  "read_invoke_U cl keys s \<equiv>
    s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := RtxnInProg keys Map.empty,
        cl_clock := Suc (cl_clock (cls s cl)),
        gst := Min (range (lst_map (cls s cl)))
      \<rparr>)
    \<rparr>"

definition read_invoke :: "cl_id \<Rightarrow> key set \<Rightarrow> sqn \<Rightarrow> tstmp \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "read_invoke cl keys sn clk s s' \<equiv>
    read_invoke_G cl keys sn clk s \<and>
    s' = read_invoke_U cl keys s"

definition read_G where
  "read_G cl k v t rts rlst sn clk s \<equiv> 
    \<comment> \<open>reads server k's value v for client transaction, lst, and svr_clock\<close>
    (\<exists>cts ts lst rs. svr_state (svrs s k) t = Commit cts ts lst v rs \<and> rs (get_txn s cl) = Some (rts, rlst)) \<and>
    (\<exists>keys kv_map. cl_state (cls s cl) = RtxnInProg keys kv_map \<and> k \<in> keys \<and> kv_map k = None) \<and>
    sn = cl_sn (cls s cl) \<and>
    clk = Suc (max (cl_clock (cls s cl)) rts)"

definition read_U where
  "read_U cl k v rts rlst s \<equiv>
    s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state :=
          (case cl_state (cls s cl) of RtxnInProg keys kv_map \<Rightarrow> RtxnInProg keys (kv_map (k \<mapsto> v))),
        cl_clock := Suc (max (cl_clock (cls s cl)) rts),
        lst_map := (lst_map (cls s cl)) (k := rlst)
      \<rparr>)
    \<rparr>"

definition read :: "cl_id \<Rightarrow> key \<Rightarrow> 'v \<Rightarrow> txid \<Rightarrow> tstmp \<Rightarrow> tstmp \<Rightarrow> sqn \<Rightarrow> tstmp \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "read cl k v t rts rlst sn clk s s' \<equiv>
    read_G cl k v t rts rlst sn clk s \<and>
    s' = read_U cl k v rts rlst s"

definition read_done_G where
  "read_done_G cl kv_map sn clk s \<equiv>
    sn = cl_sn (cls s cl) \<and>
    clk = Suc (cl_clock (cls s cl)) \<and>
    cl_state (cls s cl) = RtxnInProg (dom kv_map) kv_map"

definition read_done_U where
  "read_done_U cl kv_map s \<equiv>
    s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := Idle,
        cl_sn := Suc (cl_sn (cls s cl)),
        cl_clock := Suc (cl_clock (cls s cl))
        \<comment> \<open>cl_ctx := cl_ctx (cls s cl) \<union> get_ctx s cl (dom kv_map)\<close>
      \<rparr>),
      rtxn_rts := (rtxn_rts s) (get_txn s cl \<mapsto> gst (cls s cl))
    \<rparr>"

definition read_done :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> tstmp \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "read_done cl kv_map sn u'' clk s s' \<equiv>
    read_done_G cl kv_map sn clk s \<and>
    s' = read_done_U cl kv_map s"

definition write_invoke_G where
  "write_invoke_G cl kv_map sn clk s \<equiv> 
    kv_map \<noteq> Map.empty \<and>
    finite (dom kv_map) \<and>
    sn = cl_sn (cls s cl) \<and>
    clk = Suc (cl_clock (cls s cl)) \<and>
    cl_state (cls s cl) = Idle"

definition write_invoke_U where
  "write_invoke_U cl kv_map s \<equiv>
    s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := WtxnPrep kv_map,
        cl_clock := Suc (cl_clock (cls s cl))
      \<rparr>)
    \<rparr>"

definition write_invoke :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> sqn \<Rightarrow> tstmp \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "write_invoke cl kv_map sn clk s s' \<equiv> 
    write_invoke_G cl kv_map sn clk s \<and>
    s' = write_invoke_U cl kv_map s"

definition write_commit_G where
  "write_commit_G cl kv_map cts sn clk s \<equiv>
    sn = cl_sn (cls s cl) \<and>            \<comment> \<open>@{term sn} needed in mediator function, not in event\<close>
    clk = Suc cts \<and>
    cl_state (cls s cl) = WtxnPrep kv_map \<and>
    (\<forall>k \<in> dom kv_map. \<exists>ts v. svr_state (svrs s k) (get_wtxn s cl) = Prep ts v \<and> kv_map k = Some v) \<and>
    cts = max (cl_clock (cls s cl)) (Max {get_ts (svr_state (svrs s k) (get_wtxn s cl)) | k. k \<in> dom kv_map})"

definition write_commit_U where
  "write_commit_U cl kv_map cts s \<equiv>
    s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := WtxnCommit cts kv_map,
        cl_clock := Suc cts
        \<comment> \<open>cl_ctx := insert (get_wtxn s cl) (cl_ctx (cls s cl))\<close>
      \<rparr>), 
      \<comment> \<open>wtxn_deps := (wtxn_deps s) (get_wtxn s cl := cl_ctx (cls s cl)),\<close>
      wtxn_cts := (wtxn_cts s) (get_wtxn s cl \<mapsto> cts),
      cts_order := ext_corder (get_wtxn s cl) kv_map
        (unique_ts ((wtxn_cts s) (get_wtxn s cl \<mapsto> cts))) (cts_order s)
    \<rparr>"

definition write_commit :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> tstmp \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> tstmp \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "write_commit cl kv_map cts sn u'' clk s s' \<equiv>
    write_commit_G cl kv_map cts sn clk s \<and> 
    s' = write_commit_U cl kv_map cts s"

definition clk_WDone where
  "clk_WDone cl kv_map clk s \<equiv> clk =
        Suc (max (cl_clock (cls s cl))
              (Max {get_sclk (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map}))"

definition write_done_G where
  "write_done_G cl kv_map sn clk s \<equiv>
    (\<exists>cts. cl_state (cls s cl) = WtxnCommit cts kv_map \<and>
      (\<forall>k\<in>dom kv_map. \<exists>ts lst v rs. svr_state (svrs s k) (get_wtxn s cl) = Commit cts ts lst v rs \<and>
         kv_map k = Some v)) \<and>
    sn = cl_sn (cls s cl) \<and>
    clk_WDone cl kv_map clk s"

definition write_done_U where
  "write_done_U cl kv_map s \<equiv>
    s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := Idle,
        cl_sn := Suc (cl_sn (cls s cl)),
        cl_clock := Suc (max (cl_clock (cls s cl))
              (Max {get_sclk (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map})),
        lst_map := (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k else get_lst (svr_state (svrs s k) (get_wtxn s cl)))
      \<rparr>)
    \<rparr>"

definition write_done :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> sqn \<Rightarrow> tstmp \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "write_done cl kv_map sn clk s s' \<equiv>
    write_done_G cl kv_map sn clk s \<and>
    s' = write_done_U cl kv_map s"


(* reading cl_clock directly in server events is okay because clients only work on one transaction
  at a time and each event is waiting on the corresponding server events anyways, so it will not
  advance before they are all done. svr_clock, on the other hand, shouldn't be read directly by a
  client event, because during the client's event the involved servers might be answering to
  multiple clients and their clocks will change, so we can only rely on a snapshot of the svr_clock
  before the event begins, i.e., find it in the message from the server. *)

subsubsection \<open>Server Events\<close>

definition register_read_G where
  "register_read_G svr t t_wr rts clk s \<equiv>
    is_curr_t s t \<and>
    (\<exists>keys kv_map. cl_state (cls s (get_cl t)) = RtxnInProg keys kv_map \<and> svr \<in> keys \<and> kv_map svr = None) \<and>
    (\<exists>cts ts lst v rs. svr_state (svrs s svr) t_wr = Commit cts ts lst v rs \<and> rs t = None) \<and> \<comment> \<open>So that RReg is not enabled more than once\<close>
    rts = gst (cls s (get_cl t)) \<and>
    clk = Suc (max (svr_clock (svrs s svr)) (cl_clock (cls s (get_cl t)))) \<and>
    t_wr = read_at (svr_state (svrs s svr)) rts (get_cl t)"

definition register_read_U where
  "register_read_U svr t t_wr s\<equiv>
    s \<lparr> svrs := (svrs s)
      (svr := svrs s svr \<lparr>
        svr_state := add_to_readerset (svr_state (svrs s svr)) t (svr_clock (svrs s svr)) (svr_lst (svrs s svr)) t_wr,
        svr_clock := Suc (max (svr_clock (svrs s svr)) (cl_clock (cls s (get_cl t))))
      \<rparr>)
    \<rparr>"

definition register_read :: "key \<Rightarrow> txid0 \<Rightarrow> txid \<Rightarrow> tstmp \<Rightarrow> tstmp \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "register_read svr t t_wr rts clk s s' \<equiv>
    register_read_G svr t t_wr rts clk s \<and>
    s' = register_read_U svr t t_wr s"

definition prepare_write_G where
  "prepare_write_G svr t v clk s \<equiv>
    is_curr_t s t \<and>
    clk = Suc (max (svr_clock (svrs s svr)) (cl_clock (cls s (get_cl t)))) \<and>
    \<comment> \<open>get client's value v for svr and cl_clock\<close>
    (\<exists>kv_map. cl_state (cls s (get_cl t)) = WtxnPrep kv_map \<and> kv_map svr = Some v) \<and>
    svr_state (svrs s svr) (Tn t) = No_Ver"

definition prepare_write_U where
  "prepare_write_U svr t v s \<equiv>
    s \<lparr> svrs := (svrs s)
      (svr := svrs s svr \<lparr>
        svr_state := (svr_state (svrs s svr))(Tn t := Prep (svr_clock (svrs s svr)) v),
        svr_clock := Suc (max (svr_clock (svrs s svr)) (cl_clock (cls s (get_cl t)))) 
      \<rparr>)
    \<rparr>"

definition prepare_write :: "key \<Rightarrow> txid0 \<Rightarrow> 'v \<Rightarrow> tstmp \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "prepare_write svr t v clk s s' \<equiv>
    prepare_write_G svr t v clk s \<and>
    s' = prepare_write_U svr t v s"

definition commit_write_G where
  "commit_write_G svr t v cts clk s \<equiv>
    is_curr_t s t \<and>
    clk = Suc (max (svr_clock (svrs s svr)) (cl_clock (cls s (get_cl t)))) \<and>
    (\<exists>kv_map. cl_state (cls s (get_cl t)) = WtxnCommit cts kv_map \<and> svr \<in> dom kv_map) \<and>
    (\<exists>ts. svr_state (svrs s svr) (Tn t) = Prep ts v)"

definition commit_write_U where
  "commit_write_U svr t v cts s \<equiv>
    s \<lparr> svrs := (svrs s)
      (svr := svrs s svr \<lparr>
        svr_state := (svr_state (svrs s svr))(Tn t := Commit cts (svr_clock (svrs s svr)) (svr_lst (svrs s svr)) v rs_emp),
        svr_clock := Suc (max (svr_clock (svrs s svr)) (cl_clock (cls s (get_cl t)))),
        svr_lst := if pending_wtxns_ts ((svr_state (svrs s svr)) (Tn t := Commit cts (svr_clock (svrs s svr)) (svr_lst (svrs s svr)) v rs_emp)) = {}
               then svr_clock (svrs s svr)
               else Min (pending_wtxns_ts ((svr_state (svrs s svr))
                      (Tn t := Commit cts (svr_clock (svrs s svr)) (svr_lst (svrs s svr)) v rs_emp)))
      \<rparr>)
    \<rparr>"

definition commit_write :: "key \<Rightarrow> txid0 \<Rightarrow> 'v \<Rightarrow> tstmp \<Rightarrow> tstmp \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "commit_write svr t v cts clk s s' \<equiv>
    commit_write_G svr t v cts clk s \<and>
    s' = commit_write_U svr t v cts s"


subsection \<open>The Event System\<close>

definition state_init :: "'v global_conf" where
  "state_init \<equiv> \<lparr> 
    cls = (\<lambda>cl. \<lparr> cl_state = Idle,
                  cl_sn = 0,
                  cl_clock = 0,
                  gst = 0,
                  lst_map = (\<lambda>svr. 0) \<rparr>),
    svrs = (\<lambda>svr. \<lparr> svr_state = (\<lambda>t. No_Ver) (T0 := Commit 0 0 0 undefined rs_emp),
                    svr_clock = 0,
                    svr_lst = 0 \<rparr>),
    rtxn_rts = Map.empty,
    wtxn_cts = [T0 \<mapsto> 0],
    cts_order = (\<lambda>k. [T0])
  \<rparr>"

fun state_trans :: "('v, 'm) global_conf_scheme \<Rightarrow> 'v ev \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "state_trans s (RInvoke cl keys sn clk)           s' \<longleftrightarrow> read_invoke cl keys sn clk s s'" |
  "state_trans s (Read cl k v t rts rlst sn clk)    s' \<longleftrightarrow> read cl k v t rts rlst sn clk s s'" |
  "state_trans s (RDone cl kv_map sn u'' clk)       s' \<longleftrightarrow> read_done cl kv_map sn u'' clk s s'" |
  "state_trans s (WInvoke cl kv_map sn clk)         s' \<longleftrightarrow> write_invoke cl kv_map sn clk s s'" |
  "state_trans s (WCommit cl kv_map cts sn u'' clk) s' \<longleftrightarrow> write_commit cl kv_map cts sn u'' clk s s'" |
  "state_trans s (WDone cl kv_map sn clk)           s' \<longleftrightarrow> write_done cl kv_map sn clk s s'" |
  "state_trans s (RegR svr t t_wr rts clk)          s' \<longleftrightarrow> register_read svr t t_wr rts clk s s'" |
  "state_trans s (PrepW svr t v clk)                s' \<longleftrightarrow> prepare_write svr t v clk s s'" |
  "state_trans s (CommitW svr t v cts clk)          s' \<longleftrightarrow> commit_write svr t v cts clk s s'" |
  "state_trans s Skip2                              s' \<longleftrightarrow> s' = s"

definition tps :: "('v ev, 'v global_conf) ES" where
  "tps \<equiv> \<lparr>
    init = \<lambda>s. s = state_init,
    trans = state_trans
  \<rparr>"

lemmas tps_trans_top_defs = 
  read_invoke_def read_def read_done_def write_invoke_def write_commit_def
  write_done_def register_read_def prepare_write_def commit_write_def

lemmas tps_trans_GU_defs = 
  read_invoke_G_def read_invoke_U_def
  read_G_def read_U_def 
  read_done_G_def read_done_U_def
  write_invoke_G_def write_invoke_U_def
  write_commit_G_def write_commit_U_def
  write_done_G_def clk_WDone_def write_done_U_def
  register_read_G_def register_read_U_def
  prepare_write_G_def prepare_write_U_def
  commit_write_G_def commit_write_U_def

lemmas tps_trans_defs = tps_trans_top_defs tps_trans_GU_defs

lemmas tps_trans_all_defs = tps_trans_defs ext_corder_def

lemmas tps_defs = tps_def state_init_def

lemma tps_trans [simp]: "trans tps = state_trans" by (simp add: tps_def)

end