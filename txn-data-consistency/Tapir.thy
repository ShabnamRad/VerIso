section \<open>Tapir application protocol model\<close>

theory "Tapir"
  imports Execution_Tests
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

\<comment>\<open>Client State\<close>

datatype 'v cl_state =
  cl_init
  | cl_reading "key set" "key \<rightharpoonup> txid" "key set"
  | cl_prepared tstmp "key \<rightharpoonup> txid" "key \<rightharpoonup> 'v"
  | cl_committed tstmp "key \<rightharpoonup> txid" "key \<rightharpoonup> 'v"
  | cl_aborted

record 'v cl_conf =
  cl_state :: "'v cl_state"
  cl_sn :: nat
  cl_local_time :: tstmp


\<comment>\<open>Server State\<close>
datatype 'v svr_state =
  idle
  | read (v_rd: "txid option")
  | prepared (v_ts: tstmp) (v_rd: "txid option") (v_val: "'v option")
  | committed (v_ts: tstmp) (v_rd: "txid option") (v_val: "'v option")
  | aborted

type_synonym 'v txn_state = "txid \<Rightarrow> 'v svr_state"

record 'v svr_conf =
  svr_state :: "'v txn_state"


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

abbreviation is_curr_t :: "'v global_conf \<Rightarrow> txid0 \<Rightarrow> bool" where
  "is_curr_t s t \<equiv> cl_sn (cls s (get_cl t)) = get_sn t"

fun ver_tstmp :: "(txid \<Rightarrow> 'v svr_state) \<Rightarrow> txid \<Rightarrow> tstmp \<times> cl_id"  where
  "ver_tstmp svrst t = (v_ts (svrst t), case t of T0 \<Rightarrow> 0 | Tn t \<Rightarrow> Suc (get_cl t))"

fun is_committed_wr :: "'v svr_state \<Rightarrow> bool" where
  "is_committed_wr (committed _ _ (Some _)) = True" |
  "is_committed_wr _ = False"

definition ext_corder where
  "ext_corder t w_map corder \<equiv> (\<lambda>k. if w_map k = None then corder k else corder k @ [t])"

definition prepared_rd_tstmps where
  "prepared_rd_tstmps s k \<equiv>
    {(ts, Suc (get_cl t)) | t ts vt wvo. svr_state (svrs s k) (Tn t) = prepared ts (Some vt) wvo}"

definition prepared_wr_tstmps where
  "prepared_wr_tstmps s k \<equiv>
    {(ts, Suc (get_cl t)) | t ts rto v. svr_state (svrs s k) (Tn t) = prepared ts rto (Some v)}"

definition committed_wr_tstmps where
  "committed_wr_tstmps s k \<equiv>
    {(ts, case t of T0 \<Rightarrow> 0 | Tn t \<Rightarrow> Suc (get_cl t)) |
      t ts rto v. svr_state (svrs s k) t = committed ts rto (Some v)}"


subsubsection \<open>Simulation function\<close>
definition abs_committed_reads where
  "abs_committed_reads s k t_wr \<equiv> {t_rd. \<exists>ts wvo r_map w_map.
    svr_state (svrs s k) (Tn t_rd) = committed ts (Some t_wr) wvo \<or>
    cl_state (cls s (get_cl t_rd)) = cl_committed ts r_map w_map \<and>
    svr_state (svrs s k) (Tn t_rd) = prepared ts (Some t_wr) wvo}"

definition txn_to_vers :: "'v global_conf \<Rightarrow> key \<Rightarrow> txid \<Rightarrow> 'v version" where
  "txn_to_vers s k = (\<lambda>t. case svr_state (svrs s k) t of
    prepared ts rto (Some v) \<Rightarrow> new_vers t v |
    committed ts rto (Some v) \<Rightarrow> \<lparr>v_value = v, v_writer = t, v_readerset = abs_committed_reads s k t\<rparr>)"

definition kvs_of_s :: "'v global_conf  \<Rightarrow> 'v kv_store" where
  "kvs_of_s s \<equiv> (\<lambda>k. map (txn_to_vers s k) (commit_order s k))"

lemmas kvs_of_s_defs = kvs_of_s_def txn_to_vers_def abs_committed_reads_def

definition views_of_s :: "'v global_conf \<Rightarrow> (cl_id \<Rightarrow> view)" where
  "views_of_s gs = (\<lambda>cl. view_init)"

definition sim :: "'v global_conf \<Rightarrow> 'v config" where         
  "sim gs = (kvs_of_s gs, views_of_s gs)"

lemmas sim_defs = sim_def kvs_of_s_def txn_to_vers_def views_of_s_def
lemmas sim_all_defs = sim_def kvs_of_s_defs views_of_s_def


subsubsection \<open>Events\<close>

datatype 'v ev =
    Cl_Issue cl_id "key set" "key set"
  | Cl_Read_Resp cl_id key 'v txid
  | Cl_Prep cl_id tstmp "key \<rightharpoonup> txid" "key \<rightharpoonup> 'v"
  | Cl_Commit cl_id sqn view "'v fingerpr" tstmp "key \<rightharpoonup> txid" "key \<rightharpoonup> 'v"
  | Cl_Abort cl_id
  | Cl_ReadyC cl_id tstmp
  | Cl_ReadyA cl_id tstmp
  | Read_Resp key txid0 "txid option"
  | Prep key txid0 tstmp "txid option" "'v option"
  | Commit key txid0 tstmp "txid option" "'v option"
  | Abort key txid0
  | Skip2


definition cl_issue where
  "cl_issue cl r_keys w_keys s s' \<equiv>
    cl_state (cls s cl) = cl_init \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := cl_reading r_keys Map.empty w_keys
      \<rparr>)
    \<rparr>"

abbreviation latest_committed_wtxn where
  "latest_committed_wtxn s k t \<equiv>
    is_arg_max (\<lambda>t. v_ts (svr_state (svrs s k) t)) (\<lambda>t. is_committed_wr (svr_state (svrs s k) t)) t"

definition read_resp where
  "read_resp k t rto s s' \<equiv>
    is_curr_t s t \<and>
    (\<exists>r_keys r_map w_keys. cl_state (cls s (get_cl t)) = cl_reading r_keys r_map w_keys \<and>
      k \<in> r_keys \<union> w_keys \<and>
      rto =
        (if k \<in> r_keys
         then Some (SOME t. latest_committed_wtxn s k t)
         else None)) \<and>
    svr_state (svrs s k) (Tn t) = idle \<and>
    s' = s \<lparr> svrs := (svrs s)
      (k := svrs s k \<lparr>
        svr_state := (svr_state (svrs s k)) (Tn t := read rto)
      \<rparr>)
    \<rparr>"

definition cl_read_resp where
  "cl_read_resp cl k v t_wr s s' \<equiv>
    (\<exists>r_keys r_map w_keys. cl_state (cls s cl) = cl_reading r_keys r_map w_keys \<and>
      k \<in> r_keys \<and> r_map k = None) \<and>
    svr_state (svrs s k) (get_wtxn s cl) = read (Some t_wr) \<and>
    (\<exists>ts' rto'. svr_state (svrs s k) t_wr = committed ts' rto' (Some v)) \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := case cl_state (cls s cl) of
                    cl_reading r_keys r_map w_keys \<Rightarrow>
                    cl_reading r_keys (r_map (k \<mapsto> t_wr)) w_keys
      \<rparr>)
    \<rparr>"

definition cl_prepare where
  "cl_prepare cl ts r_map w_map s s' \<equiv>
    cl_state (cls s cl) = cl_reading (dom r_map) r_map (dom w_map) \<and>
    (\<forall>k \<in> dom r_map \<union> dom w_map. \<exists>rto. svr_state (svrs s k) (get_wtxn s cl) = read rto) \<and>
    ts = cl_local_time (cls s cl) \<and>  \<comment> \<open>The timestamp ts is proposed by the client\<close>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := cl_prepared ts r_map w_map
      \<rparr>)
    \<rparr>"

definition occ_check_journal :: "key \<Rightarrow> txid0 \<Rightarrow> tstmp \<Rightarrow> txid option \<Rightarrow> 'v option \<Rightarrow> 'v global_conf \<Rightarrow> 'v svr_state" where
  "occ_check_journal k t ts rto wvo s =
    (if (\<exists>r_t_wr. rto = Some r_t_wr \<and>
         ver_tstmp (svr_state (svrs s k)) r_t_wr < Max (committed_wr_tstmps s k))
     then aborted
     else (
      if (rto \<noteq> None \<and> prepared_wr_tstmps s k \<noteq> {} \<and> (ts, Suc (get_cl t)) > Min (prepared_wr_tstmps s k))
      then aborted
      else (
        if (wvo \<noteq> None \<and> prepared_rd_tstmps s k \<noteq> {} \<and> (ts, Suc (get_cl t)) < Max (prepared_rd_tstmps s k))
        then aborted
        else (
          if (wvo \<noteq> None \<and>
              (ts, Suc (get_cl t)) < Max (committed_wr_tstmps s k))
          then aborted
          else prepared ts rto wvo))))"

definition occ_check_conference :: "key \<Rightarrow> txid0 \<Rightarrow> tstmp \<Rightarrow> txid option \<Rightarrow> 'v option \<Rightarrow> 'v global_conf \<Rightarrow> 'v svr_state" where
  "occ_check_conference k t ts rto wvo s =
    (if (\<exists>r_t_wr. rto = Some r_t_wr \<and>
      ver_tstmp (svr_state (svrs s k)) r_t_wr < Max (committed_wr_tstmps s k))
     then aborted
     else (
      if (\<exists>r_t_wr. rto = Some r_t_wr \<and> prepared_wr_tstmps s k \<noteq> {} \<and>
       ver_tstmp (svr_state (svrs s k)) r_t_wr < Min (prepared_wr_tstmps s k))
      then aborted
      else (
       if (wvo \<noteq> None \<and> prepared_rd_tstmps s k \<noteq> {} \<and>
        (ts, Suc (get_cl t)) < Max (prepared_rd_tstmps s k))
       then aborted
       else (
        if (wvo \<noteq> None \<and>
         (ts, Suc (get_cl t)) < Max (committed_wr_tstmps s k))
        then aborted
        else prepared ts rto wvo))))"

definition occ_check :: "key \<Rightarrow> txid0 \<Rightarrow> tstmp \<Rightarrow> txid option \<Rightarrow> 'v option \<Rightarrow> 'v global_conf \<Rightarrow> 'v svr_state" where
  "occ_check k t ts rto wvo s =
    (if (\<exists>r_t_wr. rto = Some r_t_wr \<and>
      ver_tstmp (svr_state (svrs s k)) r_t_wr < Max (committed_wr_tstmps s k))
     then aborted
     else (
      if (\<exists>r_t_wr. rto = Some r_t_wr \<and> prepared_wr_tstmps s k \<noteq> {} \<and>
       ver_tstmp (svr_state (svrs s k)) r_t_wr < Max (prepared_wr_tstmps s k))
      then aborted
      else (
       if (wvo \<noteq> None \<and> prepared_rd_tstmps s k \<noteq> {} \<and>
        (ts, Suc (get_cl t)) < Max (prepared_rd_tstmps s k))
       then aborted
       else (
        if (wvo \<noteq> None \<and>
         (ts, Suc (get_cl t)) < Max (committed_wr_tstmps s k))
        then aborted
        else prepared ts rto wvo))))"

definition prepare where
  "prepare k t ts rto wvo s s' \<equiv>
    is_curr_t s t \<and>
    (\<exists>r_map w_map. cl_state (cls s (get_cl t)) = cl_prepared ts r_map w_map \<and>
      rto = r_map k \<and>
      wvo = w_map k) \<and>
    svr_state (svrs s k) (Tn t) = read rto \<and>
    s' = s \<lparr> svrs := (svrs s)
      (k := svrs s k \<lparr>
        svr_state := (svr_state (svrs s k)) (Tn t := occ_check k t ts rto wvo s)
      \<rparr>)
    \<rparr>"

definition cl_commit where
  "cl_commit cl sn u'' F ts r_map w_map s s' \<equiv>
    sn = cl_sn (cls s cl) \<and>
    u'' = full_view o kvs_of_s s \<and>
    F = (\<lambda>k. Map.empty
              (R := map_option (\<lambda>t. the (v_val (svr_state (svrs s k) t))) (r_map k),
               W := w_map k)) \<and>
    cl_state (cls s cl) = cl_prepared ts r_map w_map \<and>
    (\<forall>k \<in> dom r_map \<union> dom w_map.
      svr_state (svrs s k) (get_wtxn s cl) = prepared ts (r_map k) (w_map k)) \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := cl_committed ts r_map w_map
      \<rparr>),
      commit_order := ext_corder (get_wtxn s cl) w_map (commit_order s)
    \<rparr>"

definition commit where
  "commit k t ts rto wvo s s' \<equiv>
    is_curr_t s t \<and>
    (\<exists>r_map w_map. cl_state (cls s (get_cl t)) = cl_committed ts r_map w_map \<and>
      rto = r_map k \<and>
      wvo = w_map k) \<and>
    svr_state (svrs s k) (Tn t) = prepared ts rto wvo \<and>
    s' = s \<lparr> svrs := (svrs s)
      (k := svrs s k \<lparr>
        svr_state := (svr_state (svrs s k)) (Tn t := committed ts rto wvo)
      \<rparr>)
    \<rparr>"

definition cl_ready_c where
  "cl_ready_c cl clk s s' \<equiv>
    (\<exists>ts r_map w_map. cl_state (cls s cl) = cl_committed ts r_map w_map \<and>
      (\<forall>k \<in> dom r_map \<union> dom w_map.
        \<exists>ts rto wvo. svr_state (svrs s k) (get_wtxn s cl) = committed ts rto wvo)) \<and>
    clk > cl_local_time (cls s cl) \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := cl_init,
        cl_sn := Suc (cl_sn (cls s cl)),
        cl_local_time := clk
      \<rparr>)
    \<rparr>"

definition cl_abort where
  "cl_abort cl s s' \<equiv>
    (\<exists>ts r_map w_map. cl_state (cls s cl) = cl_prepared ts r_map w_map \<and>
    (\<exists>k \<in> dom r_map \<union> dom w_map. svr_state (svrs s k) (get_wtxn s cl) = aborted) \<and>
    (\<forall>k \<in> dom r_map \<union> dom w_map.
      \<exists>rto wvo. svr_state (svrs s k) (get_wtxn s cl) \<in> {prepared ts rto wvo, aborted})) \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := cl_aborted
      \<rparr>)
    \<rparr>"

definition abort where
  "abort k t s s' \<equiv>
    is_curr_t s t \<and>
    cl_state (cls s (get_cl t)) = cl_aborted \<and>
    (\<exists>ts rto wvo. svr_state (svrs s k) (Tn t) \<in> {prepared ts rto wvo, aborted}) \<and>
    s' = s \<lparr> svrs := (svrs s)
      (k := svrs s k \<lparr>
        svr_state := (svr_state (svrs s k)) (Tn t := aborted)
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


subsubsection \<open>The Event System\<close>

definition s_init :: "'v global_conf" where
  "s_init \<equiv> \<lparr> 
    cls = (\<lambda>cl. \<lparr> cl_state = cl_init,
                  cl_sn = 0,
                  cl_local_time = 0 \<rparr>),
    svrs = (\<lambda>k. \<lparr> svr_state = (\<lambda>t. idle) (T0 := committed 0 None (Some undefined))\<rparr>),
    commit_order = (\<lambda>k. [T0])
  \<rparr>"

fun s_trans :: "'v global_conf \<Rightarrow> 'v ev \<Rightarrow> 'v global_conf \<Rightarrow> bool" where
  "s_trans s (Cl_Issue cl rs ws)            s' \<longleftrightarrow> cl_issue cl rs ws s s'" |
  "s_trans s (Cl_Read_Resp cl k v t_wr)     s' \<longleftrightarrow> cl_read_resp cl k v t_wr s s'" |
  "s_trans s (Cl_Prep cl ts rm wm)          s' \<longleftrightarrow> cl_prepare cl ts rm wm s s'" |
  "s_trans s (Cl_Commit cl sn u F ts rm wm) s' \<longleftrightarrow> cl_commit cl sn u F ts rm wm s s'" |
  "s_trans s (Cl_Abort cl)                  s' \<longleftrightarrow> cl_abort cl s s'" |
  "s_trans s (Cl_ReadyC cl clk)             s' \<longleftrightarrow> cl_ready_c cl clk s s'" |
  "s_trans s (Cl_ReadyA cl clk)             s' \<longleftrightarrow> cl_ready_a cl clk s s'" |
  "s_trans s (Read_Resp k t rto)            s' \<longleftrightarrow> read_resp k t rto s s'" |
  "s_trans s (Prep k t ts rto wvo)          s' \<longleftrightarrow> prepare k t ts rto wvo s s'" |
  "s_trans s (Commit k t ts rto wvo)        s' \<longleftrightarrow> commit k t ts rto wvo s s'" |
  "s_trans s (Abort k t)                    s' \<longleftrightarrow> abort k t s s'" |
  "s_trans s Skip2                          s' \<longleftrightarrow> s' = s"

definition tapir :: "('v ev, 'v global_conf) ES" where
  "tapir \<equiv> \<lparr>
    init = (=) s_init,
    trans = s_trans
  \<rparr>"

lemmas tapir_trans_defs =
  cl_issue_def cl_read_resp_def cl_prepare_def cl_commit_def cl_abort_def cl_ready_c_def cl_ready_a_def
  read_resp_def prepare_def commit_def abort_def
lemmas tapir_trans_all_defs =
  tapir_trans_defs ext_corder_def

lemmas tapir_defs = tapir_def s_init_def

lemma tapir_trans [simp]: "trans tapir = s_trans" by (simp add: tapir_def)

subsubsection \<open>Mediator function\<close>

fun med :: "'v ev \<Rightarrow> 'v label" where
  "med (Cl_Commit cl sn u'' F ts rm wm) = ET cl sn u'' F" |
  "med _ = ETSkip"

end