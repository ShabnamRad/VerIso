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
datatype state_svr = idle | try_prep tstmp | occ_s | occ_f | committed | aborted
datatype state_cl = cl_init | cl_prepared tstmp | cl_committed tstmp | cl_aborted

\<comment>\<open>Client State\<close>
record cl_conf =
  cl_state :: state_cl
  cl_sn :: nat
  cl_view :: view

\<comment>\<open>Server State\<close>
type_synonym 'v key_fp_ts = "op_type \<rightharpoonup> 'v \<times> tstmp"
record 'v version_t = "'v version" + v_ts :: tstmp

record 'v svr_conf =
  svr_state :: "txid0 \<Rightarrow> state_svr"
  svr_vl :: "'v version_t list" \<comment> \<open>not ordered by ts; ts is accessible by v_ts\<close>
  svr_fp :: "txid0 \<Rightarrow> 'v key_fp_ts"
  svr_prep_reads :: "txid0 \<rightharpoonup> tstmp"
  svr_prep_writes :: "txid0 \<rightharpoonup> tstmp"

\<comment>\<open>System Global State: Clients and key Servers\<close>
record 'v global_conf =
  cls :: "cl_id \<Rightarrow> cl_conf"
  svrs :: "key \<Rightarrow> 'v svr_conf"

\<comment> \<open>Translator and helper functions\<close>

abbreviation get_txn :: "cl_id \<Rightarrow> 'v global_conf \<Rightarrow> txid0" where
  "get_txn cl s \<equiv> Tn_cl (cl_sn (cls s cl)) cl"

abbreviation get_fp :: "(txid0 \<Rightarrow> 'v key_fp_ts) \<Rightarrow> txid0 \<Rightarrow> 'v key_fp" where
  "get_fp svrfp \<equiv> (\<lambda>t op. map_option fst (svrfp t op))"

abbreviation get_ver :: "'v version_t \<Rightarrow> 'v version" where
  "get_ver v \<equiv> \<lparr> v_value = v_value v, v_writer = v_writer v, v_readerset = v_readerset v\<rparr>"

abbreviation read_set :: "('v, 'm) global_conf_scheme \<Rightarrow> txid0 \<Rightarrow> key \<rightharpoonup> ('v \<times> tstmp)" where
  "read_set s t \<equiv> (\<lambda>k. svr_fp (svrs s k) t R)"

abbreviation write_set :: "('v, 'm) global_conf_scheme \<Rightarrow> txid0 \<Rightarrow> key \<rightharpoonup> ('v \<times> tstmp)" where
  "write_set s t \<equiv> (\<lambda>k. svr_fp (svrs s k) t W)"

fun ver_tstmp where
  "ver_tstmp ver = (v_ts ver, case v_writer ver of T0 \<Rightarrow> 0 | Tn t \<Rightarrow> Suc (get_cl t))"

abbreviation new_vers_t :: "txid \<Rightarrow> 'v \<Rightarrow> tstmp \<Rightarrow> 'v version_t" where
  "new_vers_t t v ts \<equiv> \<lparr>v_value = v, v_writer = t, v_readerset = {}, v_ts = ts\<rparr>"

fun update_kv_key_writes_t :: "txid0 \<Rightarrow> 'v option \<Rightarrow> tstmp \<Rightarrow> 'v version_t list \<Rightarrow> 'v version_t list" where
  "update_kv_key_writes_t t None ts vl = vl" |
  "update_kv_key_writes_t t (Some v) ts vl = vl @ [new_vers_t (Tn t) v ts]"

definition update_kv_key_t :: "txid0 \<Rightarrow> 'v key_fp \<Rightarrow> tstmp \<Rightarrow> key_view \<Rightarrow> 'v version_t list \<Rightarrow> 'v version_t list" where
  "update_kv_key_t t Fk ts uk = update_kv_key_writes_t t (Fk W) ts o update_kv_key_reads t (Fk R) uk"

subsubsection \<open>Simulation function\<close>

definition eligible_reads :: "(txid0 \<Rightarrow> state_cl) \<Rightarrow> (txid0 \<Rightarrow> state_svr) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> txid0 set" where
  "eligible_reads tCls tSvrs tFk \<equiv> {t.
     \<exists>ts. tCls t = cl_committed ts \<and> tSvrs t \<in> {occ_s} \<and> tFk t R \<noteq> None}"

definition update_kv_key_reads_all_txn :: "(txid0 \<Rightarrow> state_cl) \<Rightarrow> (txid0 \<Rightarrow> state_svr) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_key_reads_all_txn tCls tSvrs tFk vl =
    (let uk = full_view vl; lv = last_version vl uk in
     vl [Max uk := lv \<lparr>v_readerset := (v_readerset lv) \<union> eligible_reads tCls tSvrs tFk\<rparr>])"

abbreviation the_wr_t :: "(txid0 \<Rightarrow> state_svr) \<Rightarrow> txid0" where
  "the_wr_t tSvrs \<equiv> (THE t. tSvrs t = occ_s)"

definition update_kv_key_writes_all_txn :: "(txid0 \<Rightarrow> state_cl) \<Rightarrow> (txid0 \<Rightarrow> state_svr) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_key_writes_all_txn tCls tSvrs tFk vl =
    (if (\<exists>t ts. tCls t = cl_committed ts \<and> tSvrs t = occ_s) then
        update_kv_key_writes (the_wr_t tSvrs) (tFk (the_wr_t tSvrs) W) vl
     else vl)"

definition update_kv_all_txn :: "(txid0 \<Rightarrow> state_cl) \<Rightarrow> (txid0 \<Rightarrow> state_svr) \<Rightarrow>
  (txid0 \<Rightarrow> 'v key_fp) \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_all_txn tCls tSvrs tFk =
    (update_kv_key_writes_all_txn tCls tSvrs tFk) o (update_kv_key_reads_all_txn tCls tSvrs tFk)"

definition kvs_of_gs :: "'v global_conf \<Rightarrow> 'v kv_store" where
  "kvs_of_gs gs = (\<lambda>k.
   update_kv_all_txn (\<lambda>t. cl_state (cls gs (get_cl t)))
    (svr_state (svrs gs k)) (get_fp (svr_fp (svrs gs k))) (map get_ver (svr_vl (svrs gs k))))"

definition views_of_gs :: "'v global_conf \<Rightarrow> (cl_id \<Rightarrow> view)" where
  "views_of_gs gs = (\<lambda>cl. cl_view (cls gs cl))"

definition sim :: "'v global_conf \<Rightarrow> 'v config" where         
  "sim gs = (kvs_of_gs gs, views_of_gs gs)"

lemmas update_kv_key_reads_all_defs = update_kv_key_reads_all_txn_def Let_def 
lemmas update_kv_all_defs = update_kv_key_reads_all_defs update_kv_key_writes_all_txn_def update_kv_all_txn_def
lemmas sim_defs = sim_def kvs_of_gs_def views_of_gs_def


subsubsection \<open>Events\<close>

datatype 'v ev = TryPrep key txid0 tstmp | OCCCheck key txid0 tstmp | Commit key txid0 tstmp | Abort key txid0 |
  Cl_Prep cl_id tstmp | Cl_Commit cl_id sqn view "'v fingerpr" tstmp | Cl_Abort cl_id | Cl_ReadyC cl_id |
  Cl_ReadyA cl_id | Skip2

abbreviation is_curr_t :: "('v, 'm) global_conf_scheme \<Rightarrow> txid0 \<Rightarrow> bool" where
  "is_curr_t s t \<equiv> cl_sn (cls s (get_cl t)) = get_sn t"

definition updated_kvs :: "'v global_conf \<Rightarrow> cl_id \<Rightarrow> tstmp \<Rightarrow> 'v kv_store" where
  "updated_kvs s cl ts \<equiv> (\<lambda>k. update_kv_all_txn
    (\<lambda>t. cl_state (cls (s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr> cl_state := cl_committed ts \<rparr> ) \<rparr>) (get_cl t)))
    (svr_state (svrs s k)) (get_fp (svr_fp (svrs s k))) (map get_ver (svr_vl (svrs s k))))"

definition prepare where
  "prepare k t ts s s' \<equiv>
    is_curr_t s t \<and>
    cl_state (cls s (get_cl t)) = cl_prepared ts \<and>
    svr_state (svrs s k) t = idle \<and>
    s' = s \<lparr> svrs := (svrs s)
      (k := svrs s k \<lparr>
        svr_state := (svr_state (svrs s k)) (t := try_prep ts)
      \<rparr>)
    \<rparr>"

definition occ_check :: "key \<Rightarrow> txid0 \<Rightarrow> tstmp \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> state_svr" where
  "occ_check k t ts s =
    (let prep_rd_ts = {(ts', Suc (get_cl t')) | t' ts'. svr_prep_reads (svrs s k) t' = Some ts'};
        prep_wr_ts = {(ts', Suc (get_cl t')) | t' ts'. svr_prep_writes (svrs s k) t' = Some ts'} in
    (if (\<exists>ver_v ver_ts. read_set s t k = Some (ver_v, ver_ts) \<and>
         (ver_ts, Suc (get_cl t)) < Max {ver_tstmp ver | ver. ver \<in> set (svr_vl (svrs s k))})
     then occ_f
     else (
      if (k \<in> dom (read_set s t) \<and> prep_wr_ts \<noteq> {} \<and> (ts, Suc (get_cl t)) > Min prep_wr_ts)
      then occ_f
      else (
        if (k \<in> dom (write_set s t) \<and> prep_rd_ts \<noteq> {} \<and> (ts, Suc (get_cl t)) < Max prep_rd_ts)
        then occ_f
        else (
          if (k \<in> dom (write_set s t) \<and> (ts, Suc (get_cl t)) < Max {ver_tstmp ver | ver. ver \<in> set (svr_vl (svrs s k))})
          then occ_f
          else occ_s)))))"

definition tapir_occ_check :: "key \<Rightarrow> txid0 \<Rightarrow> tstmp \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "tapir_occ_check k t ts s s' \<equiv>
    is_curr_t s t \<and>
    svr_state (svrs s k) t = try_prep ts \<and>
    s' = s \<lparr> svrs := (svrs s) (k := svrs s k \<lparr>
      svr_state := (svr_state (svrs s k)) (t := occ_check k t ts s)
      \<rparr>)
    \<rparr>"

definition commit where
  "commit k t ts s s' \<equiv>
    is_curr_t s t \<and>
    cl_state (cls s (get_cl t)) = cl_committed ts \<and>
    svr_state (svrs s k) t = occ_s \<and>
    s' = s \<lparr> svrs := (svrs s)
      (k := svrs s k \<lparr>
        svr_vl :=
          update_kv_key_t t (get_fp (svr_fp (svrs s k)) t) ts (full_view (svr_vl (svrs s k))) (svr_vl (svrs s k)),
        svr_state := (svr_state (svrs s k)) (t := committed)
      \<rparr>)
    \<rparr>"

definition abort where
  "abort k t s s' \<equiv>
    is_curr_t s t \<and>
    cl_state (cls s (get_cl t)) = cl_aborted \<and>
    svr_state (svrs s k) t \<in> {occ_s, occ_f} \<and>
    s' = s \<lparr> svrs := (svrs s)
      (k := svrs s k \<lparr>
        svr_state := (svr_state (svrs s k)) (t := aborted)
      \<rparr>)
    \<rparr>"

definition cl_prepare where
  "cl_prepare cl ts s s' \<equiv> \<comment> \<open>The timestamp ts is proposed by the client\<close>
    cl_state (cls s cl) = cl_init \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := cl_prepared ts \<comment> \<open>The proposed ts is sent to the servers\<close>
      \<rparr>)
    \<rparr>"

definition cl_commit where
  "cl_commit cl sn u'' F ts s s' \<equiv>
    sn = cl_sn (cls s cl) \<and>
    u'' = full_view o (kvs_of_gs s) \<and>
    F = (\<lambda>k. get_fp (svr_fp (svrs s k)) (get_txn cl s)) \<and>
    cl_state (cls s cl) = cl_prepared ts \<and>
    (\<forall>k. svr_state (svrs s k) (get_txn cl s) = occ_s) \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := cl_committed ts,
        cl_view := full_view o (updated_kvs s cl ts)
      \<rparr>)
    \<rparr>"

definition cl_abort where
  "cl_abort cl s s' \<equiv>
    (\<exists>ts. cl_state (cls s cl) = cl_prepared ts) \<and>
    (\<exists>k. svr_state (svrs s k) (get_txn cl s) = occ_f) \<and>
    (\<forall>k. svr_state (svrs s k) (get_txn cl s) \<in> {occ_s, occ_f}) \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := cl_aborted
      \<rparr>)
    \<rparr>"

definition cl_ready_c where
  "cl_ready_c cl s s' \<equiv>
    (\<exists>ts. cl_state (cls s cl) = cl_committed ts) \<and>
    (\<forall>k. svr_state (svrs s k) (get_txn cl s) = committed) \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := cl_init,
        cl_sn := Suc (cl_sn (cls s cl))
      \<rparr>)
    \<rparr>"

definition cl_ready_a where
  "cl_ready_a cl s s' \<equiv>
    cl_state (cls s cl) = cl_aborted \<and>
    (\<forall>k. svr_state (svrs s k) (get_txn cl s) = aborted) \<and>
    s' = s \<lparr> cls := (cls s)
      (cl := cls s cl \<lparr>
        cl_state := cl_init,
        cl_sn := Suc (cl_sn (cls s cl))
      \<rparr>)
    \<rparr>"


subsubsection \<open>The Event System\<close>

definition s_init :: "'v global_conf" where
  "s_init \<equiv> \<lparr> 
    cls = (\<lambda>cl. \<lparr> cl_state = cl_init,
                 cl_sn = 0,
                 cl_view = view_init \<rparr>),
    svrs = (\<lambda>k. \<lparr> svr_state = (\<lambda>t. idle),
                 svr_vl = [new_vers_t T0 undefined 0],
                 svr_fp = (\<lambda>t. Map.empty),
                 svr_prep_reads = Map.empty,
                 svr_prep_writes = Map.empty\<rparr>)
  \<rparr>"

fun s_trans :: "'v global_conf \<Rightarrow> 'v ev \<Rightarrow> 'v global_conf \<Rightarrow> bool" where
  "s_trans s (TryPrep k t ts)         s' \<longleftrightarrow> prepare k t ts s s'" |
  "s_trans s (OCCCheck k t ts)        s' \<longleftrightarrow> tapir_occ_check k t ts s s'" |
  "s_trans s (Commit k t ts)          s' \<longleftrightarrow> commit k t ts s s'" |
  "s_trans s (Abort k t)              s' \<longleftrightarrow> abort k t s s'" |
  "s_trans s (Cl_Prep cl ts)          s' \<longleftrightarrow> cl_prepare cl ts s s'" |
  "s_trans s (Cl_Commit cl sn u F ts) s' \<longleftrightarrow> cl_commit cl sn u F ts s s'" |
  "s_trans s (Cl_Abort cl)            s' \<longleftrightarrow> cl_abort cl s s'" |
  "s_trans s (Cl_ReadyC cl)           s' \<longleftrightarrow> cl_ready_c cl s s'" |
  "s_trans s (Cl_ReadyA cl)           s' \<longleftrightarrow> cl_ready_a cl s s'" |
  "s_trans s Skip2                    s' \<longleftrightarrow> s' = s"

definition tapir :: "('v ev, 'v global_conf) ES" where
  "tapir \<equiv> \<lparr>
    init = (=) s_init,
    trans = s_trans
  \<rparr>"

lemmas tapir_trans_defs = prepare_def tapir_occ_check_def commit_def abort_def
                        cl_prepare_def cl_commit_def cl_abort_def cl_ready_c_def cl_ready_a_def

lemmas tapir_defs = tapir_def s_init_def

lemma tapir_trans [simp]: "trans tapir = s_trans" by (simp add: tapir_def)

subsubsection \<open>Mediator function\<close>

fun med :: "'v ev \<Rightarrow> 'v label" where
  "med (Cl_Commit cl sn u'' F ts) = ET cl sn u'' F" |
  "med _ = ETSkip"

end