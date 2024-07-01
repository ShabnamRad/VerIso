section \<open>Tapir application protocol model\<close>

theory "Tapir"
  imports Execution_Tests "HOL-Library.Multiset"
begin

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

subsection \<open>Event System\<close>

subsubsection \<open>State\<close>

type_synonym tstmp = nat

datatype 'v cl_state =
  cl_init
  | cl_prepared tstmp "key set" "key \<rightharpoonup> 'v \<times> txid" "key \<rightharpoonup> 'v"
  | cl_committed tstmp "key \<rightharpoonup> 'v \<times> txid" "key \<rightharpoonup> 'v"
  | cl_aborted

datatype 'v svr_state =
  idle
  | prep "('v \<times> txid) option" "'v option"
  | occ_s "('v \<times> txid) option" "'v option"
  | occ_f
  | committed_wr (v_val: 'v) "txid0 set" (v_ts: tstmp)
  | committed_rd 'v txid
  | aborted

\<comment>\<open>Client State\<close>
record 'v cl_conf =
  cl_state :: "'v cl_state"
  cl_sn :: nat
  cl_view :: view
  cl_local_time :: tstmp

\<comment>\<open>Server State\<close>
type_synonym 'v txn_state = "txid \<Rightarrow> 'v svr_state"

record 'v svr_conf =
  svr_state :: "'v txn_state"
  svr_ver_order :: "txid list"
  svr_prep_reads :: "txid0 \<rightharpoonup> tstmp"
  svr_prep_writes :: "txid0 \<rightharpoonup> tstmp"
  (* (txid0 \<rightharpoonup> tstmp \<equiv> (txid0 \<times> tstmp) set) where we know there is only one ts per txid *)

\<comment>\<open>System Global State: Clients and key Servers\<close>
record 'v global_conf =
  cls :: "cl_id \<Rightarrow> 'v cl_conf"
  svrs :: "key \<Rightarrow> 'v svr_conf"
  commit_order :: "key \<Rightarrow> txid list"


\<comment> \<open>Translator and helper functions\<close>

fun get_cl_w :: "txid \<Rightarrow> cl_id" where
  "get_cl_w T0 = undefined" |
  "get_cl_w (Tn (Tn_cl sn cl)) = cl"

abbreviation get_txn :: "'v global_conf \<Rightarrow> cl_id \<Rightarrow> txid0" where
  "get_txn s cl \<equiv> Tn_cl (cl_sn (cls s cl)) cl"

abbreviation get_wtxn :: "'v global_conf \<Rightarrow> cl_id \<Rightarrow> txid" where
  "get_wtxn s cl \<equiv> Tn (get_txn s cl)"

fun ver_tstmp :: "(txid \<Rightarrow> 'v svr_state) \<Rightarrow> txid \<Rightarrow> tstmp \<times> cl_id"  where
  "ver_tstmp wtxns t = (v_ts (wtxns t), case t of T0 \<Rightarrow> 0 | Tn t \<Rightarrow> Suc (get_cl t))"

definition add_to_readerset :: "'v txn_state \<Rightarrow> txid0 \<Rightarrow> txid \<Rightarrow> 'v txn_state" where
  "add_to_readerset wtxns t t_wr \<equiv> (case wtxns t_wr of
    committed_wr v rs ts \<Rightarrow>
      wtxns (Tn t := committed_rd v t_wr, t_wr := committed_wr v (insert t rs) ts) |
    _ \<Rightarrow> wtxns)"

subsubsection \<open>Simulation function\<close>
definition ready_to_commit_reads where
  "ready_to_commit_reads s t_wr \<equiv> {t_rd. \<exists>ts r_map w_map k v.
    cl_state (cls s (get_cl t_rd)) = cl_committed ts r_map w_map \<and>
    svr_state (svrs s k) (Tn t_rd) = occ_s (Some (v, t_wr)) None}"

definition txn_to_vers :: "('v, 'm) global_conf_scheme \<Rightarrow> key \<Rightarrow> txid \<Rightarrow> 'v version" where
  "txn_to_vers s k = (\<lambda>t. case svr_state (svrs s k) t of
    occ_s None (Some v) \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = {}\<rparr> |
    committed_wr v rs ts \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = rs \<union> ready_to_commit_reads s t\<rparr>)"

definition kvs_of_s :: "'v global_conf \<Rightarrow> 'v kv_store" where
  "kvs_of_s s \<equiv> (\<lambda>k. map (txn_to_vers s k) (commit_order s k))"

lemmas kvs_of_s_defs = kvs_of_s_def txn_to_vers_def ready_to_commit_reads_def

definition views_of_s :: "'v global_conf \<Rightarrow> (cl_id \<Rightarrow> view)" where
  "views_of_s gs = (\<lambda>cl. cl_view (cls gs cl))"

definition sim :: "'v global_conf \<Rightarrow> 'v config" where         
  "sim gs = (kvs_of_s gs, views_of_s gs)"

lemmas sim_defs = sim_def kvs_of_s_defs views_of_s_def


subsubsection \<open>Events\<close>

datatype 'v ev =
    Cl_Prep cl_id tstmp "key set" "key \<rightharpoonup> 'v"
  | Cl_Read_Resp cl_id key 'v txid
  | Cl_Commit cl_id sqn view "'v fingerpr" tstmp "key \<rightharpoonup> ('v \<times> txid)" "key \<rightharpoonup> 'v"
  | Cl_Abort cl_id
  | Cl_ReadyC cl_id tstmp
  | Cl_ReadyA cl_id tstmp
  | Prep key txid0 "('v \<times> txid) option" "'v option"
  | OCCCheck key txid0 tstmp "('v \<times> txid) option" "'v option" "'v svr_state"
  | CommitW key 'v txid0 tstmp
  | CommitR key 'v txid txid0
  | Abort key txid0
  | Skip2

abbreviation is_curr_t :: "('v, 'm) global_conf_scheme \<Rightarrow> txid0 \<Rightarrow> bool" where
  "is_curr_t s t \<equiv> cl_sn (cls s (get_cl t)) = get_sn t"

definition cl_prepare where
  "cl_prepare cl ts r_set w_map s s' \<equiv>
    cl_state (cls s cl) = cl_init \<and>
    ts = cl_local_time (cls s cl) \<and>  \<comment> \<open>The timestamp ts is proposed by the client\<close>
    r_set \<inter> dom w_map = {} \<and>
    (r_set \<noteq> {} \<or> dom w_map \<noteq> {}) \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := cl_prepared ts r_set (Map.empty) w_map
        \<comment> \<open>The proposed ts, read set, and write map of the transaction is sent to the servers\<close>
      \<rparr>)
    \<rparr>"

definition cl_read_resp where
  "cl_read_resp cl k v t_wr s s' \<equiv>
    (\<exists>ts r_set r_map w_map. cl_state (cls s cl) = cl_prepared ts r_set r_map w_map \<and>
      k \<in> r_set \<and> r_map k = None) \<and>
    svr_state (svrs s k) (get_wtxn s cl) = prep (Some (v, t_wr)) None \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := case cl_state (cls s cl) of
                    cl_prepared ts r_set r_map w_map \<Rightarrow>
                    cl_prepared ts r_set (r_map (k \<mapsto> (v, t_wr))) w_map
      \<rparr>)
    \<rparr>"

definition cl_commit where
  "cl_commit cl sn u'' F ts r_map w_map s s' \<equiv>
    sn = cl_sn (cls s cl) \<and>
    u'' = full_view o (kvs_of_s s) \<and>
    cl_state (cls s cl) = cl_prepared ts (dom r_map) r_map w_map \<and>
    (\<forall>k \<in> dom r_map \<union> dom w_map. \<exists>r_vto w_vo.
      svr_state (svrs s k) (get_wtxn s cl) = occ_s r_vto w_vo \<and> 
      F k R = map_option fst r_vto \<and>
      F k W = w_vo) \<and>
    (\<forall>k. k \<notin> dom r_map \<union> dom w_map \<longrightarrow> F k = Map.empty) \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := cl_committed ts r_map w_map,
        cl_view := full_view o (kvs_of_s s')
      \<rparr>),
      commit_order := (\<lambda>k. if w_map k = None then commit_order s k else commit_order s k @ [get_wtxn s cl])
    \<rparr>"

definition cl_abort where
  "cl_abort cl s s' \<equiv>
    (\<exists>ts r_map w_map. cl_state (cls s cl) = cl_prepared ts (dom r_map) r_map w_map \<and>
    (\<exists>k \<in> dom r_map \<union> dom w_map.
      svr_state (svrs s k) (get_wtxn s cl) = occ_f) \<and>
    (\<forall>k \<in> dom r_map \<union> dom w_map.
      \<exists>r_vto w_vo. svr_state (svrs s k) (get_wtxn s cl) \<in> {occ_s r_vto w_vo, occ_f})) \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := cl_aborted
      \<rparr>)
    \<rparr>"

definition cl_ready_c where
  "cl_ready_c cl clk s s' \<equiv>
    (\<exists>ts r_map w_map. cl_state (cls s cl) = cl_committed ts r_map w_map \<and>
      (\<forall>k \<in> dom r_map. \<exists>v t. svr_state (svrs s k) (get_wtxn s cl) = committed_rd v t) \<and>
      (\<forall>k \<in> dom w_map. \<exists>v. svr_state (svrs s k) (get_wtxn s cl) = committed_wr v {} ts)) \<and>
    clk > cl_local_time (cls s cl) \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := cl_init,
        cl_sn := Suc (cl_sn (cls s cl)),
        cl_local_time := clk
      \<rparr>)
    \<rparr>"

definition cl_ready_a where
  "cl_ready_a cl clk s s' \<equiv>
    cl_state (cls s cl) = cl_aborted \<and>
    (\<forall>k. svr_state (svrs s k) (get_wtxn s cl) = aborted) \<and>
    clk > cl_local_time (cls s cl) \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := cl_init,
        cl_sn := Suc (cl_sn (cls s cl)),
        cl_local_time := clk
      \<rparr>)
    \<rparr>"

definition prepare where
  "prepare k t r_vto w_vo s s' \<equiv>
    is_curr_t s t \<and>
    (\<exists>ts r_set r_map w_map. cl_state (cls s (get_cl t)) = cl_prepared ts r_set r_map w_map \<and>
      ((k \<in> r_set \<and> k \<notin> dom r_map) \<or> k \<in> dom w_map) \<and>
      r_vto = (if k \<in> r_set
             then Some ((\<lambda>t. (v_val (svr_state (svrs s k) t), t)) (last (svr_ver_order (svrs s k))))
             else None) \<and>
      w_vo = w_map k) \<and>
    svr_state (svrs s k) (Tn t) = idle \<and>
    s' = s \<lparr> svrs := (svrs s)
      (k := svrs s k \<lparr>
        svr_state := (svr_state (svrs s k)) (Tn t := prep r_vto w_vo)
      \<rparr>)
    \<rparr>"

definition occ_check :: "key \<Rightarrow> txid0 \<Rightarrow> tstmp \<Rightarrow> ('v \<times> txid) option \<Rightarrow> 'v option
  \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> 'v svr_state" where
  "occ_check k t ts r_vto w_vo s =
    (let prep_rd_ts = {(ts', Suc (get_cl t')) | t' ts'. svr_prep_reads (svrs s k) t' = Some ts'};
        prep_wr_ts = {(ts', Suc (get_cl t')) | t' ts'. svr_prep_writes (svrs s k) t' = Some ts'} in
    (if (\<exists>ver_v ver_wr. r_vto = Some (ver_v, ver_wr) \<and>
         ver_tstmp (svr_state (svrs s k)) ver_wr <
         Max {ver_tstmp (svr_state (svrs s k)) t_wr | t_wr. t_wr \<in> set (svr_ver_order (svrs s k))})
     then occ_f
     else (
      if (r_vto \<noteq> None \<and> prep_wr_ts \<noteq> {} \<and> (ts, Suc (get_cl t)) > Min prep_wr_ts)
      then occ_f
      else (
        if (w_vo \<noteq> None \<and> prep_rd_ts \<noteq> {} \<and> (ts, Suc (get_cl t)) < Max prep_rd_ts)
        then occ_f
        else (
          if (w_vo \<noteq> None \<and>
              (ts, Suc (get_cl t)) <
              Max {ver_tstmp (svr_state (svrs s k)) t_wr | t_wr. t_wr \<in> set (svr_ver_order (svrs s k))})
          then occ_f
          else occ_s r_vto w_vo)))))"

definition tapir_occ_check where
  "tapir_occ_check k t ts r_vto w_vo occ_res s s' \<equiv>
    is_curr_t s t \<and>
    (\<exists>r_map w_map. cl_state (cls s (get_cl t)) = cl_prepared ts (dom r_map) r_map w_map) \<and>
    svr_state (svrs s k) (Tn t) = prep r_vto w_vo \<and>
    occ_res = occ_check k t ts r_vto w_vo s \<and>
    s' = s \<lparr> svrs := (svrs s) (k := svrs s k \<lparr>
      svr_state := (svr_state (svrs s k)) (Tn t := occ_res),
      svr_prep_reads := if occ_res = occ_f \<or> r_vto = None
                        then svr_prep_reads (svrs s k)
                        else (svr_prep_reads (svrs s k)) (t := Some ts),
      svr_prep_writes := if occ_res = occ_f \<or> w_vo = None
                         then svr_prep_writes (svrs s k)
                         else (svr_prep_writes (svrs s k)) (t := Some ts)
      \<rparr>)
    \<rparr>"

definition commit_rd where
  "commit_rd k v t_wr t s s' \<equiv>
    is_curr_t s t \<and>
    (\<exists>ts r_map w_map. cl_state (cls s (get_cl t)) = cl_committed ts r_map w_map) \<and>
    svr_state (svrs s k) (Tn t) = occ_s (Some (v, t_wr)) None \<and>
    s' = s \<lparr> svrs := (svrs s)
      (k := svrs s k \<lparr>
        svr_state := add_to_readerset (svr_state (svrs s k)) t t_wr
      \<rparr>)                                             
    \<rparr>"

definition commit_wr where
  "commit_wr k v t ts s s' \<equiv>
    is_curr_t s t \<and>
    (\<exists>r_map w_map. cl_state (cls s (get_cl t)) = cl_committed ts r_map w_map) \<and>
    svr_state (svrs s k) (Tn t) = occ_s None (Some v) \<and>
    s' = s \<lparr> svrs := (svrs s)
      (k := svrs s k \<lparr>
        svr_state := ((svr_state (svrs s k)) (Tn t := committed_wr v {} ts)),
        svr_ver_order := svr_ver_order (svrs s k) @ [Tn t]
      \<rparr>)                                             
    \<rparr>"

definition abort where
  "abort k t s s' \<equiv>
    is_curr_t s t \<and>
    cl_state (cls s (get_cl t)) = cl_aborted \<and>
    (\<exists>r_vto w_vo. svr_state (svrs s k) (Tn t) \<in> {occ_s r_vto w_vo, occ_f}) \<and>
    s' = s \<lparr> svrs := (svrs s)
      (k := svrs s k \<lparr>
        svr_state := (svr_state (svrs s k)) (Tn t := aborted)
      \<rparr>)
    \<rparr>"


subsubsection \<open>The Event System\<close>

definition s_init :: "'v global_conf" where
  "s_init \<equiv> \<lparr> 
    cls = (\<lambda>cl. \<lparr> cl_state = cl_init,
                  cl_sn = 0,
                  cl_view = view_init,
                  cl_local_time = 0 \<rparr>),
    svrs = (\<lambda>k. \<lparr> svr_state = (\<lambda>t. idle) (T0 := committed_wr undefined {} 0),
                  svr_ver_order = [T0],
                  svr_prep_reads = Map.empty,
                  svr_prep_writes = Map.empty\<rparr>),
    commit_order = (\<lambda>k. [T0])
  \<rparr>"

fun s_trans :: "'v global_conf \<Rightarrow> 'v ev \<Rightarrow> 'v global_conf \<Rightarrow> bool" where
  "s_trans s (Cl_Prep cl ts rs wm)            s' \<longleftrightarrow> cl_prepare cl ts rs wm s s'" |
  "s_trans s (Cl_Read_Resp cl k v t_wr)       s' \<longleftrightarrow> cl_read_resp cl k v t_wr s s'" |
  "s_trans s (Cl_Commit cl sn u F ts rm wm)   s' \<longleftrightarrow> cl_commit cl sn u F ts rm wm s s'" |
  "s_trans s (Cl_Abort cl)                    s' \<longleftrightarrow> cl_abort cl s s'" |
  "s_trans s (Cl_ReadyC cl clk)               s' \<longleftrightarrow> cl_ready_c cl clk s s'" |
  "s_trans s (Cl_ReadyA cl clk)               s' \<longleftrightarrow> cl_ready_a cl clk s s'" |
  "s_trans s (Prep k t r_vto w_vo)            s' \<longleftrightarrow> prepare k t r_vto w_vo s s'" |
  "s_trans s (OCCCheck k t ts r_vto w_vo res) s' \<longleftrightarrow> tapir_occ_check k t ts r_vto w_vo res s s'" |
  "s_trans s (CommitR k v t_wr t)             s' \<longleftrightarrow> commit_rd k v t_wr t s s'" |
  "s_trans s (CommitW k v t ts)               s' \<longleftrightarrow> commit_wr k v t ts s s'" |
  "s_trans s (Abort k t)                      s' \<longleftrightarrow> abort k t s s'" |
  "s_trans s Skip2                            s' \<longleftrightarrow> s' = s"

definition tapir :: "('v ev, 'v global_conf) ES" where
  "tapir \<equiv> \<lparr>
    init = (=) s_init,
    trans = s_trans
  \<rparr>"

lemmas tapir_trans_defs =
  cl_prepare_def cl_read_resp_def cl_commit_def cl_abort_def cl_ready_c_def cl_ready_a_def
  prepare_def tapir_occ_check_def commit_rd_def commit_wr_def abort_def

lemmas tapir_defs = tapir_def s_init_def

lemma tapir_trans [simp]: "trans tapir = s_trans" by (simp add: tapir_def)

subsubsection \<open>Mediator function\<close>

fun med :: "'v ev \<Rightarrow> 'v label" where
  "med (Cl_Commit cl sn u'' F ts rm wm) = ET cl sn u'' F" |
  "med _ = ETSkip"

end