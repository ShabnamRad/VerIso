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
  Idle | RtxnInProg (get_cclk: tstmp) "key set" "key \<rightharpoonup> 'v" | WtxnPrep "key \<rightharpoonup> 'v" | WtxnCommit tstmp "key \<rightharpoonup> 'v"

record 'v cl_conf =
  cl_state :: "'v txn_state"
  cl_sn :: sqn
  cl_clock :: tstmp
  gst :: tstmp
  lst_map :: "key \<Rightarrow> tstmp"

\<comment> \<open>Server State\<close>
datatype 'v ver_state = No_Ver | Prep (get_pend: tstmp) (get_ts: tstmp) (get_val: 'v)
  | Commit (get_ts: tstmp) (get_sclk: tstmp) (get_lst: tstmp) (get_val: 'v) readerset

abbreviation rs_emp :: readerset where "rs_emp \<equiv> Map.empty"

fun is_committed :: "'v ver_state \<Rightarrow> bool" where
  "is_committed (Commit _ _ _ _ _) = True" |
  "is_committed _ = False"

fun is_prepared :: "'v ver_state \<Rightarrow> bool" where
  "is_prepared (Prep _ _ _) = True" |
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
  "get_rs (Prep _ _ _) = rs_emp" |
  "get_rs (Commit _ _ _ _ rs) = rs"

lemma get_cl_w_Tn [simp]:
  "get_cl_w (Tn t) = get_cl t"
  by (metis get_cl_w.simps(2) txid0.collapse)

lemma get_sn_w_Tn [simp]:
  "get_sn_w (Tn t) = get_sn t"
  by (metis get_sn_w.simps(2) txid0.collapse)


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


subsubsection \<open>Helper functions\<close>

definition add_to_readerset :: "'v wtxn_state \<Rightarrow> txid0 \<Rightarrow> tstmp \<Rightarrow> tstmp \<Rightarrow> txid \<Rightarrow> 'v wtxn_state" where
  "add_to_readerset wtxns t rclk rlst t_wr \<equiv> (case wtxns t_wr of
    Commit cts ts lst v rs \<Rightarrow> wtxns (t_wr := Commit cts ts lst v (rs (t \<mapsto> (rclk, rlst)))) |
    _ \<Rightarrow> wtxns)"

definition pending_wtxns_ts :: "'v wtxn_state \<Rightarrow> tstmp set" where
  "pending_wtxns_ts wtxns \<equiv> {pend_t. \<exists>t prep_t v. wtxns t = Prep pend_t prep_t v}"

definition ext_corder :: "txid \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> (txid \<Rightarrow> (tstmp \<times> cl_id)) \<Rightarrow> (key \<Rightarrow> txid list) \<Rightarrow> key \<Rightarrow> txid list" where
  "ext_corder t kv_map f corder \<equiv> 
     (\<lambda>k. if kv_map k = None then corder k else insort_key f t (corder k))"

abbreviation is_curr_t :: "('v, 'm) global_conf_scheme \<Rightarrow> txid0 \<Rightarrow> bool" where
  "is_curr_t s t \<equiv> cl_sn (cls s (get_cl t)) = get_sn t"

abbreviation is_curr_wt :: "('v, 'm) global_conf_scheme \<Rightarrow> txid \<Rightarrow> bool" where
  "is_curr_wt s t \<equiv> t \<noteq> T0 \<and> cl_sn (cls s (get_cl_w t)) = get_sn_w t"

definition ects :: "tstmp \<Rightarrow> cl_id \<Rightarrow> tstmp \<times> cl_id" where
  "ects cts cl = (cts, Suc cl)"

lemma ects_inj: "ects cts cl = ects cts' cl' \<Longrightarrow> cts = cts' \<and> cl = cl'"
  by (simp add: ects_def)

lemma min_ects: "(0, 0) < ects x y" by (auto simp add: less_prod_def ects_def)

definition unique_ts :: "(txid \<rightharpoonup> tstmp) \<Rightarrow> txid \<Rightarrow> tstmp \<times> cl_id" where
  "unique_ts wtxn_ctss \<equiv> (\<lambda>t. (the (wtxn_ctss t), if t = T0 then 0 else Suc (get_cl_w t)))"

lemma unique_ts_def':
  "unique_ts wtxn_ctss =
   (\<lambda>t. if t = T0 then (the (wtxn_ctss T0), 0) else ects (the (wtxn_ctss t)) (get_cl_w t))"
  by (auto simp add: unique_ts_def ects_def)

definition full_ts :: "'v wtxn_state \<Rightarrow> txid \<Rightarrow> tstmp \<times> cl_id" where
  "full_ts wtxns \<equiv> (\<lambda>t. (get_ts (wtxns t), if t = T0 then 0 else Suc (get_cl_w t)))"

lemma full_ts_def':
  "full_ts wtxns =
    (\<lambda>t. if t = T0 then (get_ts (wtxns T0), 0) else ects (get_ts (wtxns t)) (get_cl_w t))"
  by (auto simp add: full_ts_def ects_def)


subsubsection \<open>Reading functions\<close>

definition ver_committed_before :: "'v ver_state \<Rightarrow> tstmp \<Rightarrow> bool" where
  "ver_committed_before ver ts \<longleftrightarrow> is_committed ver \<and> get_ts ver \<le> ts" 

definition ver_committed_after :: "'v ver_state \<Rightarrow> tstmp \<Rightarrow> bool" where
  "ver_committed_after ver ts \<longleftrightarrow> is_committed ver \<and> get_ts ver > ts" 


\<comment> \<open>returns the writer transaction id of the version read at read timestamp (highest cts less than ts)\<close>
definition at :: "'v wtxn_state \<Rightarrow> tstmp \<Rightarrow> txid" where 
  "at wtxns rts = (ARG_MAX (full_ts wtxns) t. ver_committed_before (wtxns t) rts)"

definition newest_own_write :: "'v wtxn_state \<Rightarrow> tstmp \<Rightarrow> cl_id \<rightharpoonup> txid" where
  "newest_own_write wtxns ts cl = 
     (if \<exists>t. ver_committed_after (wtxns t) ts \<and> get_cl_w t = cl
     then Some (ARG_MAX (get_ts o wtxns) t. ver_committed_after (wtxns t) ts \<and> get_cl_w t = cl)
     else None)"

definition read_at :: "'v wtxn_state \<Rightarrow> tstmp \<Rightarrow> cl_id \<Rightarrow> txid" where
  "read_at wtxns rts cl \<equiv> case newest_own_write wtxns rts cl of
    None \<Rightarrow> at wtxns rts
  | Some t' \<Rightarrow> t'"


subsection \<open>Events\<close>

datatype 'v ev =
  RInvoke cl_id "key set" sqn tstmp | Read cl_id key 'v txid sqn tstmp "tstmp \<times> tstmp"
  | RDone cl_id "key \<rightharpoonup> 'v" sqn view tstmp | WInvoke cl_id "key \<rightharpoonup> 'v" sqn tstmp
  | WCommit cl_id "key \<rightharpoonup> 'v" tstmp sqn view tstmp "key \<rightharpoonup> tstmp"
  | WDone cl_id "key \<rightharpoonup> 'v" sqn tstmp "key \<rightharpoonup> tstmp \<times> tstmp"
  | RegR key txid0 txid tstmp tstmp tstmp tstmp | PrepW key txid0 'v tstmp tstmp
  | CommitW key txid0 'v tstmp tstmp tstmp tstmp

fun commit_ev :: "'v ev \<Rightarrow> bool" where
  "commit_ev (RDone cl kv_map sn u'' clk) = True" |
  "commit_ev (WCommit cl kv_map cts sn u'' clk mmap) = True" |
  "commit_ev _ = False"

fun v_ext_ev :: "'v ev \<Rightarrow> cl_id \<Rightarrow> bool" where
  "v_ext_ev (RInvoke cl keys sn clk) cl' = (cl' = cl)" |
  "v_ext_ev (WCommit cl kv_map cts sn u'' clk mmap) cl' = (cl' = cl)" |
  "v_ext_ev _ _ = False"

fun ev_cl :: "'v ev \<Rightarrow> cl_id option" where
  "ev_cl (RInvoke cl keys sn clk)                = Some cl" |
  "ev_cl (Read cl k v t sn clk m)                = Some cl" |
  "ev_cl (RDone cl kv_map sn u'' clk)            = Some cl" |
  "ev_cl (WInvoke cl kv_map sn clk)              = Some cl" |
  "ev_cl (WCommit cl kv_map cts sn u'' clk mmap) = Some cl" |
  "ev_cl (WDone cl kv_map sn clk mmap)           = Some cl" |
  "ev_cl _ = None"

fun ev_key :: "'v ev \<Rightarrow> key option" where
  "ev_key (RegR svr t t_wr rts clk lst m)   = Some svr" |
  "ev_key (PrepW svr t v clk m)             = Some svr" |
  "ev_key (CommitW svr t v cts clk lst m)   = Some svr" |
  "ev_key _ = None"

fun ev_txn :: "'v ev \<Rightarrow> txid0" where
  "ev_txn (RInvoke cl keys sn clk)                = Tn_cl sn cl" |
  "ev_txn (Read cl k v t sn clk m)                = Tn_cl sn cl" |
  "ev_txn (RDone cl kv_map sn u'' clk)            = Tn_cl sn cl" |
  "ev_txn (WInvoke cl kv_map sn clk)              = Tn_cl sn cl" |
  "ev_txn (WCommit cl kv_map cts sn u'' clk mmap) = Tn_cl sn cl" |
  "ev_txn (WDone cl kv_map sn clk mmap)           = Tn_cl sn cl" |
  "ev_txn (RegR svr t t_wr rts clk lst m)         = t" |
  "ev_txn (PrepW svr t v clk m)                   = t" |
  "ev_txn (CommitW svr t v cts clk lst m)         = t"

fun ev_clk :: "'v ev \<Rightarrow> tstmp" where
  "ev_clk (RInvoke cl keys sn clk)                = clk" |
  "ev_clk (Read cl k v t sn clk m)                = clk" |
  "ev_clk (RDone cl kv_map sn u'' clk)            = clk" |
  "ev_clk (WInvoke cl kv_map sn clk)              = clk" |
  "ev_clk (WCommit cl kv_map cts sn u'' clk mmap) = clk" |
  "ev_clk (WDone cl kv_map sn clk mmap)           = clk" |
  "ev_clk (RegR svr t t_wr rts clk lst m)         = clk" |
  "ev_clk (PrepW svr t v clk m)                   = clk" |
  "ev_clk (CommitW svr t v cts clk lst m)         = clk"

fun ev_ects :: "'v ev \<Rightarrow> (tstmp \<times> cl_id) option" where
  "ev_ects (WCommit cl kv_map cts sn u'' clk mmap) = Some (ects cts cl)" |
  "ev_ects _ = None"

lemma ev_ects_Some:
  "ev_ects e = Some (cts, Suc_cl)
  \<Longrightarrow> \<exists>cl kv_map sn u'' clk mmap. e = WCommit cl kv_map cts sn u'' clk mmap \<and> Suc_cl = Suc cl"
  by (cases e, simp_all add: ects_def)


subsubsection \<open>Client Events\<close>

definition read_invoke_G where
  "read_invoke_G cl keys sn clk s \<equiv>
    keys \<noteq> {} \<and>
    finite keys \<and>
    sn = cl_sn (cls s cl) \<and>
    clk = Suc (cl_clock (cls s cl)) \<and>
    cl_state (cls s cl) = Idle"

definition read_invoke_U where
  "read_invoke_U cl keys clk s \<equiv>
    s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := RtxnInProg clk keys Map.empty,
        cl_clock := clk,
        gst := Min (range (lst_map (cls s cl)))
      \<rparr>)
    \<rparr>"

definition read_invoke :: "cl_id \<Rightarrow> key set \<Rightarrow> sqn \<Rightarrow> tstmp \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "read_invoke cl keys sn clk s s' \<equiv>
    read_invoke_G cl keys sn clk s \<and>
    s' = read_invoke_U cl keys clk s"

definition read_G where
  "read_G cl k v t_wr sn clk m s \<equiv> 
    \<comment> \<open>reads server k's value v for client transaction, lst, and svr_clock\<close>
    (\<exists>cts ts lst rs. svr_state (svrs s k) t_wr = Commit cts ts lst v rs \<and> rs (get_txn s cl) = Some m) \<and>
    (\<exists>cclk keys kv_map. cl_state (cls s cl) = RtxnInProg cclk keys kv_map \<and> k \<in> keys \<and> kv_map k = None) \<and>
    sn = cl_sn (cls s cl) \<and>
    clk = Suc (max (cl_clock (cls s cl)) (fst m))"

definition read_U where
  "read_U cl k v clk m s \<equiv>
    s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state :=
          (case cl_state (cls s cl)
           of RtxnInProg cclk keys kv_map
           \<Rightarrow> RtxnInProg cclk keys (kv_map (k \<mapsto> v))),
        cl_clock := clk,
        lst_map := (lst_map (cls s cl)) (k := snd m)
      \<rparr>)
    \<rparr>"

definition read :: "cl_id \<Rightarrow> key \<Rightarrow> 'v \<Rightarrow> txid \<Rightarrow> sqn \<Rightarrow> tstmp \<Rightarrow> tstmp \<times> tstmp
   \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "read cl k v t_wr sn clk m s s' \<equiv>
    read_G cl k v t_wr sn clk m s \<and>
    s' = read_U cl k v clk m s"

definition read_done_G where
  "read_done_G cl kv_map sn clk s \<equiv>
    sn = cl_sn (cls s cl) \<and>
    clk = Suc (cl_clock (cls s cl)) \<and>
    (\<exists>cclk. cl_state (cls s cl) = RtxnInProg cclk (dom kv_map) kv_map)"

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
  "write_commit_G cl kv_map cts sn clk mmap s \<equiv>
    sn = cl_sn (cls s cl) \<and>            \<comment> \<open>@{term sn} needed in mediator function, not in event\<close>
    cl_state (cls s cl) = WtxnPrep kv_map \<and>
    (\<forall>k \<in> dom kv_map. \<exists>pd ts v. svr_state (svrs s k) (get_wtxn s cl) = Prep pd ts v \<and> kv_map k = Some v) \<and>
    mmap = (\<lambda>k. if kv_map k = None then None else Some (get_ts (svr_state (svrs s k) (get_wtxn s cl)))) \<and>
    cts = Max {get_ts (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map} \<and>
    clk = Suc cts"

definition write_commit_U where
  "write_commit_U cl kv_map cts s \<equiv>
    s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := WtxnCommit cts kv_map,
        cl_clock := Suc cts
      \<rparr>), 
      wtxn_cts := (wtxn_cts s) (get_wtxn s cl \<mapsto> cts),
      cts_order := ext_corder (get_wtxn s cl) kv_map
        (unique_ts ((wtxn_cts s) (get_wtxn s cl \<mapsto> cts))) (cts_order s)
    \<rparr>"

definition write_commit :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> tstmp \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> tstmp \<Rightarrow> (key \<rightharpoonup> tstmp)
    \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "write_commit cl kv_map cts sn u'' clk mmap s s' \<equiv>
    write_commit_G cl kv_map cts sn clk mmap s \<and> 
    s' = write_commit_U cl kv_map cts s"

definition clk_WDone where
  "clk_WDone cl kv_map clk s \<equiv> clk =
        Suc (max (cl_clock (cls s cl))
              (Max {get_sclk (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map}))"

definition write_done_G where
  "write_done_G cl kv_map sn clk mmap s \<equiv>
    (\<exists>cts. cl_state (cls s cl) = WtxnCommit cts kv_map \<and>
      (\<forall>k\<in>dom kv_map. \<exists>ts lst v rs. svr_state (svrs s k) (get_wtxn s cl) = Commit cts ts lst v rs \<and>
         kv_map k = Some v)) \<and>
    sn = cl_sn (cls s cl) \<and>
    mmap = (\<lambda>k. if kv_map k = None then None else
      Some (get_sclk (svr_state (svrs s k) (get_wtxn s cl)),
            get_lst (svr_state (svrs s k) (get_wtxn s cl)))) \<and>
    clk_WDone cl kv_map clk s"

definition write_done_U where
  "write_done_U cl kv_map clk s \<equiv>
    s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := Idle,
        cl_sn := Suc (cl_sn (cls s cl)),
        cl_clock := clk,
        lst_map := (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k else get_lst (svr_state (svrs s k) (get_wtxn s cl)))
      \<rparr>)
    \<rparr>"

definition write_done :: "cl_id \<Rightarrow> (key \<rightharpoonup> 'v) \<Rightarrow> sqn \<Rightarrow> tstmp \<Rightarrow> (key \<rightharpoonup> tstmp \<times> tstmp)
  \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "write_done cl kv_map sn clk mmap s s' \<equiv>
    write_done_G cl kv_map sn clk mmap s \<and>
    s' = write_done_U cl kv_map clk s"


(* reading cl_clock directly in server events is okay because clients only work on one transaction
  at a time and each event is waiting on the corresponding server events anyways, so it will not
  advance before they are all done. svr_clock, on the other hand, shouldn't be read directly by a
  client event, because during the client's event the involved servers might be answering to
  multiple clients and their clocks will change, so we can only rely on a snapshot of the svr_clock
  after the event ends which it sends to the client in its message (here by reading the version) *)

subsubsection \<open>Server Events\<close>

definition register_read_G where
  "register_read_G svr t t_wr rts clk lst m s \<equiv>
    is_curr_t s t \<and>
    (\<exists>keys kv_map. cl_state (cls s (get_cl t)) = RtxnInProg m keys kv_map \<and> svr \<in> keys \<and> kv_map svr = None) \<and>
    (\<exists>cts ts lst v rs. svr_state (svrs s svr) t_wr = Commit cts ts lst v rs \<and> rs t = None) \<and> \<comment> \<open>So that RReg is not enabled more than once\<close>
    rts = gst (cls s (get_cl t)) \<and>
    t_wr = read_at (svr_state (svrs s svr)) rts (get_cl t) \<and>
    clk = Suc (max (svr_clock (svrs s svr)) m) \<and>
    lst = svr_lst (svrs s svr)"

definition register_read_U where
  "register_read_U svr t t_wr clk lst s\<equiv>
    s \<lparr> svrs := (svrs s)
      (svr := svrs s svr \<lparr>
        svr_state := add_to_readerset (svr_state (svrs s svr)) t clk (svr_lst (svrs s svr)) t_wr,
        svr_clock := clk
      \<rparr>)
    \<rparr>"

definition register_read :: "key \<Rightarrow> txid0 \<Rightarrow> txid \<Rightarrow> tstmp \<Rightarrow> tstmp \<Rightarrow> tstmp \<Rightarrow> tstmp \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "register_read svr t t_wr rts clk lst m s s' \<equiv>
    register_read_G svr t t_wr rts clk lst m s \<and>
    s' = register_read_U svr t t_wr clk lst s"

definition prepare_write_G where
  "prepare_write_G svr t v clk m s \<equiv>
    is_curr_t s t \<and>
    m = cl_clock (cls s (get_cl t)) \<and>
    clk = Suc (max (svr_clock (svrs s svr)) m) \<and>
    \<comment> \<open>get client's value v for svr and cl_clock\<close>
    (\<exists>kv_map. cl_state (cls s (get_cl t)) = WtxnPrep kv_map \<and> kv_map svr = Some v) \<and>
    svr_state (svrs s svr) (Tn t) = No_Ver"

definition prepare_write_U where
  "prepare_write_U svr t v clk s \<equiv>
    s \<lparr> svrs := (svrs s)
      (svr := svrs s svr \<lparr>
        svr_state := (svr_state (svrs s svr))(Tn t := Prep (svr_clock (svrs s svr)) clk v),
        svr_clock := clk 
      \<rparr>)
    \<rparr>"

definition prepare_write :: "key \<Rightarrow> txid0 \<Rightarrow> 'v \<Rightarrow> tstmp \<Rightarrow> tstmp
  \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "prepare_write svr t v clk m s s' \<equiv>
    prepare_write_G svr t v clk m s \<and>
    s' = prepare_write_U svr t v clk s"

definition commit_write_G where
  "commit_write_G svr t v cts clk lst m s \<equiv>
    is_curr_t s t \<and>
    m = cl_clock (cls s (get_cl t)) \<and>
    clk = Suc (max (svr_clock (svrs s svr)) m) \<and>
    lst = (if pending_wtxns_ts ((svr_state (svrs s svr)) (Tn t := Commit cts clk lst v rs_emp)) = {}
           then clk
           else Min (pending_wtxns_ts ((svr_state (svrs s svr)) (Tn t := Commit cts clk lst v rs_emp)))) \<and>
    (\<exists>kv_map. cl_state (cls s (get_cl t)) = WtxnCommit cts kv_map \<and> svr \<in> dom kv_map) \<and>
    (\<exists>pd ts. svr_state (svrs s svr) (Tn t) = Prep pd ts v)"

definition commit_write_U where
  "commit_write_U svr t v cts clk lst s \<equiv>
    s \<lparr> svrs := (svrs s)
      (svr := svrs s svr \<lparr>
        svr_state := (svr_state (svrs s svr))(Tn t := Commit cts clk lst v rs_emp),
        svr_clock := clk,
        svr_lst := lst
      \<rparr>)
    \<rparr>"

definition commit_write :: "key \<Rightarrow> txid0 \<Rightarrow> 'v \<Rightarrow> tstmp \<Rightarrow> tstmp \<Rightarrow> tstmp \<Rightarrow> tstmp
  \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "commit_write svr t v cts clk lst m s s' \<equiv>
    commit_write_G svr t v cts clk lst m s \<and>
    s' = commit_write_U svr t v cts clk lst s"


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
  "state_trans s (RInvoke cl keys sn clk)                s' \<longleftrightarrow> read_invoke cl keys sn clk s s'" |
  "state_trans s (Read cl k v t_wr sn clk m)             s' \<longleftrightarrow> read cl k v t_wr sn clk m s s'" |
  "state_trans s (RDone cl kv_map sn u'' clk)            s' \<longleftrightarrow> read_done cl kv_map sn u'' clk s s'" |
  "state_trans s (WInvoke cl kv_map sn clk)              s' \<longleftrightarrow> write_invoke cl kv_map sn clk s s'" |
  "state_trans s (WCommit cl kv_map cts sn u'' clk mmap) s' \<longleftrightarrow> write_commit cl kv_map cts sn u'' clk mmap s s'" |
  "state_trans s (WDone cl kv_map sn clk mmap)           s' \<longleftrightarrow> write_done cl kv_map sn clk mmap s s'" |
  "state_trans s (RegR svr t t_wr rts clk lst m)         s' \<longleftrightarrow> register_read svr t t_wr rts clk lst m s s'" |
  "state_trans s (PrepW svr t v clk m)                   s' \<longleftrightarrow> prepare_write svr t v clk m s s'" |
  "state_trans s (CommitW svr t v cts clk lst m)         s' \<longleftrightarrow> commit_write svr t v cts clk lst m s s'"

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