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
type_synonym op_id = nat
type_synonym rep_id = nat
datatype func = Prepare | Commit
datatype result = PREPARE_OK | ABSTAIN | ABORT | RETRY "tstmp \<times> cl_id" | OCC_CHECK txid0 tstmp
datatype optype = inconsistent | consensus
datatype opstat = TENTATIVE | FINALIZED
datatype txn_status = COMMITTED | ABORTED

record operation =
  op_ts :: tstmp
  op_txid :: txid0
  op_func :: func
  op_res :: result
  op_type :: optype
  op_status :: opstat

record 'v txn_state =
  read_set :: "key \<rightharpoonup> tstmp"
  write_set :: "key \<rightharpoonup> tstmp"
  status :: "txn_status option"
  
\<comment> \<open>Client State\<close>
record 'v cl_conf =
  cl_state :: "result option"
  cl_sn :: sqn

\<comment> \<open>Replica State\<close>
record 'v object =
  obj_wr :: txid0
  obj_v :: 'v
  obj_ts :: tstmp

function obj_tstmp where
  "obj_tstmp obj = (obj_ts obj, get_cl (obj_wr obj))"
  by simp_all

record 'v rep_conf =
  r_state :: "operation \<rightharpoonup> result"
  r_prep_list :: "txid0 \<rightharpoonup> tstmp"
  r_prep_writes :: "key \<Rightarrow> txid0 \<rightharpoonup> tstmp"
  r_prep_reads :: "key \<Rightarrow> txid0 \<rightharpoonup> tstmp"
  r_txn_log :: "txid0 list" (* needs to be ordered by txn timestamp *)
  r_store :: "key \<Rightarrow> 'v object list" (* needs to be ordered by txn timestamp *)

\<comment> \<open>Global State\<close>
record 'v global_conf =
  cls :: "cl_id \<Rightarrow> 'v cl_conf"
  reps :: "rep_id \<Rightarrow> 'v rep_conf"
  ops :: "op_id \<rightharpoonup> operation"
  txns :: "txid0 \<Rightarrow> 'v txn_state"

consts data_loc :: "key \<Rightarrow> rep_id set"

subsubsection \<open>Events\<close>

\<comment> \<open>Replica Prepare Event\<close>
definition tapir_exec_consensus :: "rep_id \<Rightarrow> operation \<Rightarrow> txid0 \<Rightarrow> tstmp
  \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "tapir_exec_consensus r op t ts s s' \<equiv>
    r_state (reps s r) op = None \<and>
    t = op_txid op \<and>
    ts = op_ts op \<and>
    s' = s \<lparr> reps := (reps s) (r := reps s r \<lparr>
      r_state := (r_state (reps s r)) (op \<mapsto>
        (let t = op_txid op; ts = op_ts op in
        (if t \<in> set (r_txn_log (reps s r))
         then (
          if status (txns s t) = Some (COMMITTED)
          then PREPARE_OK
          else ABORT)
         else (
          if t \<in> dom (r_prep_list (reps s r))
          then PREPARE_OK
          else OCC_CHECK t ts)))
      )\<rparr>)
    \<rparr>"

\<comment> \<open>Replica OCC Check event\<close>
definition tapir_occ_check :: "rep_id \<Rightarrow> operation \<Rightarrow> txid0 \<Rightarrow> tstmp \<Rightarrow> result
  \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "tapir_occ_check r op t ts res s s' \<equiv>
    r_state (reps s r) op = Some (OCC_CHECK t ts) \<and>
    t = op_txid op \<and>
    ts = op_ts op \<and>
    res =
      (if (\<exists>k ver_ts. read_set (txns s t) k = Some ver_ts \<and>
         (ver_ts, get_cl t) < obj_tstmp (last (r_store (reps s r) k)))
       then ABORT
       else (
        if (\<exists>k \<in> dom (read_set (txns s t)).
          (ts, get_cl t) > Min {(ts', get_cl t') | t' ts'. r_prep_writes (reps s r) k t' = Some ts'})
        then ABSTAIN
        else (
          if (\<exists>k \<in> dom (write_set (txns s t)).
            (ts, get_cl t) < Max {(ts', get_cl t') | t' ts'. r_prep_reads (reps s r) k t' = Some ts'})
          then (let k = (SOME k. k \<in> dom (write_set (txns s t)) \<and>
            (ts, get_cl t) < Max {(ts', get_cl t') | t' ts'. r_prep_reads (reps s r) k t' = Some ts'}) in
            RETRY (Max {(ts', get_cl t') | t' ts'. r_prep_reads (reps s r) k t' = Some ts'}))
          else (
            if (\<exists>k \<in> dom (write_set (txns s t)).
            (ts, get_cl t) < obj_tstmp (last (r_store (reps s r) k)))
            then (let k = (SOME k. k \<in> dom (write_set (txns s t)) \<and>
              (ts, get_cl t) < obj_tstmp (last (r_store (reps s r) k))) in
              RETRY (obj_tstmp (last (r_store (reps s r) k))))
            else PREPARE_OK)))) \<and>
    s' = s \<lparr> reps := (reps s) (r := reps s r \<lparr>
      r_state := (r_state (reps s r)) (op \<mapsto> res),
      r_prep_list :=
        if res = PREPARE_OK
        then (r_prep_list (reps s r)) (t \<mapsto> ts)
        else r_prep_list (reps s r)\<rparr>)
    \<rparr>"

\<comment> \<open>Client Decide Event\<close>
definition tapir_decide :: "cl_id \<Rightarrow> operation \<Rightarrow> txid0 \<Rightarrow> tstmp \<Rightarrow> rep_id list \<Rightarrow> nat \<Rightarrow> result list \<Rightarrow>
  ('v, 'm) global_conf_scheme \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "tapir_decide cl op t ts repls f results s s' \<equiv>
    cl_state (cls s cl) = None \<and>
    repls = sorted_list_of_set (\<Union>k \<in> dom (read_set (txns s t)) \<union> dom (write_set (txns s t)). data_loc k) \<and>
    f = length repls \<and>
    results = map (\<lambda>r. the (r_state (reps s r) op)) repls \<and>
    t = op_txid op \<and>
    ts = op_ts op \<and>
    s' = s \<lparr> cls := (cls s) (cl := cls s cl \<lparr>
      cl_state := Some
    (if ABORT \<in> set (results)
    then ABORT
    else (
      if count_list results PREPARE_OK \<ge> f + 1
      then PREPARE_OK
      else (
        if count_list results ABSTAIN \<ge> f + 1
        then ABORT
        else (
          if \<exists>i. RETRY i \<in> set (results)
          then RETRY (Max {i. RETRY i \<in> set (results)})
          else ABORT))))
    \<rparr>)
  \<rparr>"

definition tapir_merge where
  "tapir_merge cl d u s s' \<equiv>
    True"

subsection \<open>The Event System\<close>

definition obj_init :: "'v object" where
  "obj_init \<equiv> \<lparr> obj_wr = undefined, obj_v = undefined, obj_ts = 0 \<rparr>"

definition txn_init :: "'v txn_state" where
  "txn_init \<equiv> \<lparr> read_set = Map.empty, write_set = Map.empty, status = None \<rparr>"

definition state_init :: "'v global_conf" where
  "state_init \<equiv> \<lparr> 
    cls = (\<lambda>cl. \<lparr> cl_state = None,
                  cl_sn = 0 \<rparr>),
    reps = (\<lambda>r. \<lparr> r_state = Map.empty,
                  r_prep_list = Map.empty,
                  r_prep_writes = (\<lambda>k. Map.empty),
                  r_prep_reads = (\<lambda>k. Map.empty),
                  r_txn_log = [],
                  r_store = (\<lambda>k. [obj_init]) \<rparr>),
    ops = Map.empty,
    txns = (\<lambda>t. txn_init)
  \<rparr>"

datatype 'v ev = Cl_Begin cl_id | Cl_Read cl_id key "'v object" | Cl_Write cl_id key "'v object"
  | Cl_Decide cl_id operation txid0 tstmp "rep_id list" nat "result list"
  | Cl_Commit cl_id | Cl_Abort cl_id | R_Read key "'v object" | R_Prepare rep_id operation txid0 tstmp
  | R_OCC rep_id operation txid0 tstmp result | R_Commit txid0 tstmp | R_Abort txid0 tstmp


fun state_trans :: "('v, 'm) global_conf_scheme \<Rightarrow> 'v ev \<Rightarrow> ('v, 'm) global_conf_scheme \<Rightarrow> bool" where
  "state_trans s (Cl_Begin cl_id)                       s' \<longleftrightarrow> True" |
  "state_trans s (Cl_Read cl k obj)                     s' \<longleftrightarrow> True" |
  "state_trans s (Cl_Write cl k obj)                    s' \<longleftrightarrow> True" |
  "state_trans s (Cl_Decide cl op t ts repls f results) s' \<longleftrightarrow> tapir_decide cl op t ts repls f results s s'" |
  "state_trans s (Cl_Commit cl)                         s' \<longleftrightarrow> True" |
  "state_trans s (Cl_Abort cl)                          s' \<longleftrightarrow> True" |
  "state_trans s (R_Read k obj)                         s' \<longleftrightarrow> True" |
  "state_trans s (R_Prepare r op t ts)                  s' \<longleftrightarrow> tapir_exec_consensus r op t ts s s'" |
  "state_trans s (R_OCC r op t ts res)                  s' \<longleftrightarrow> tapir_occ_check r op t ts res s s'" |
  "state_trans s (R_Commit t ts)                        s' \<longleftrightarrow> True" |
  "state_trans s (R_Abort t ts)                         s' \<longleftrightarrow> True"

definition tapir :: "('v ev, 'v global_conf) ES" where
  "tapir \<equiv> \<lparr>
    init = \<lambda>s. s = state_init,
    trans = state_trans
  \<rparr>"

lemmas tapir_trans_defs =
  tapir_decide_def
  tapir_occ_check_def
  tapir_exec_consensus_def

lemmas tapir_defs = tapir_def state_init_def

lemma tapir_trans [simp]: "trans tapir = state_trans" by (simp add: tapir_def)

end