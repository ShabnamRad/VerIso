section \<open>Programming Language\<close>

theory ProgrammingLanguage
  imports "HOL-IMP.AExp"
begin

subsection \<open>Syntax\<close>

datatype cmd_p = Assign vname aexp | Assume aexp
datatype txn_p = TCp cmd_p | Lookup vname aexp | Mutate aexp aexp
datatype txn = TSkip | Tp txn_p | TSeq txn txn (infixr ";" 60) |
               TChoice txn txn (infixr "[+]" 65) | TItr txn
datatype cmd = Skip | Cp cmd_p | Atomic txn | Seq cmd cmd (infixr ";;" 60) |
               Choice cmd cmd (infixr "[[+]]" 65) | Itr cmd

type_synonym cl_session = nat
typedecl cl_id
datatype txid0 = Tn_cl cl_session cl_id
datatype txid = T0 | txid0

type_synonym key = int \<comment>\<open>Should it stay like this? It's implied by the ECOOP paper\<close>
type_synonym val = int
consts val0 :: val

record version =
  v_value :: val
  v_writer :: txid
  v_readerset :: "txid0 set"

type_synonym v_id = nat

definition version_init :: version where
  "version_init \<equiv> \<lparr>v_value = val0, v_writer = T0, v_readerset = {}\<rparr>"

type_synonym kv_store = "key \<Rightarrow> v_id \<rightharpoonup> version"
definition kvs_init :: kv_store where
  "kvs_init _ \<equiv> (\<lambda>k. None)(0 := Some version_init)"

type_synonym views = "key \<Rightarrow> v_id set"
definition views_init :: views where
  "views_init _ \<equiv> {0}"

record config =
  c_kvs :: kv_store
  c_conf :: "cl_id \<rightharpoonup> views"

definition conf_init :: "cl_id \<rightharpoonup> views" where
  "conf_init _ \<equiv> Some views_init" \<comment>\<open>how should the partial function be handled?\<close>
definition config_init :: config where
  "config_init \<equiv> \<lparr>c_kvs = kvs_init, c_conf = conf_init\<rparr>"

type_synonym snapshot = "key \<Rightarrow> val"
\<comment>\<open>Should we return version0 for unknown keys?\<close>
definition last_version :: "kv_store \<Rightarrow> views \<Rightarrow> key \<Rightarrow> version" where
  "last_version kvs u k \<equiv> (case kvs k (Max (u k)) of None \<Rightarrow> version_init | Some ver \<Rightarrow> ver)"

definition view_snapshot :: "kv_store \<Rightarrow> views \<Rightarrow> snapshot" where
  "view_snapshot kvs u k \<equiv> v_value (last_version kvs u k)"

definition txn_snapshot :: "config \<Rightarrow> cl_id \<rightharpoonup> snapshot" where
  "txn_snapshot cfg cl \<equiv>
        (case ((c_conf cfg) cl) of
           None \<Rightarrow> None |
           Some u \<Rightarrow> Some (\<lambda>k. v_value (last_version (c_kvs cfg) u k)))"

datatype op_type = R | W
datatype op = Read key val | Write key val | Eps

type_synonym fingerprint = "key \<times> op_type \<rightharpoonup> val"

fun update_fp :: "fingerprint \<Rightarrow> op \<Rightarrow> fingerprint" where
  "update_fp fp (Read k v)  = (case fp (k, R) of
                                None \<Rightarrow> (case fp (k, W) of
                                          None \<Rightarrow> fp ((k, R) := Some v) |
                                          Some _ \<Rightarrow> fp) |
                                Some _ \<Rightarrow> fp)" |
  "update_fp fp (Write k v) = fp ((k, W) := Some v)" |
  "update_fp fp Eps         = fp"

type_synonym stack = state
fun t_primitive :: "stack \<Rightarrow> snapshot \<Rightarrow> txn_p \<Rightarrow> stack \<Rightarrow> snapshot \<Rightarrow> bool" where
  "t_primitive s \<sigma> (TCp (Assign x E)) s' \<sigma>' \<longleftrightarrow> s' = s(x := aval E s) \<and> \<sigma>' = \<sigma>" |
  "t_primitive s \<sigma> (TCp (Assume E)) s' \<sigma>'   \<longleftrightarrow> s' = s \<and> \<sigma>' = \<sigma> \<and> aval E s \<noteq> 0" |
  "t_primitive s \<sigma> (Lookup x E) s' \<sigma>'       \<longleftrightarrow> s' = s(x := \<sigma>(aval E s)) \<and> \<sigma>' = \<sigma>" |
  "t_primitive s \<sigma> (Mutate E1 E2) s' \<sigma>'     \<longleftrightarrow> s' = s \<and> \<sigma>' = \<sigma>((aval E1 s) := aval E2 s)"

fun get_op :: "stack \<Rightarrow> snapshot \<Rightarrow> txn_p \<Rightarrow> op" where
  "get_op s \<sigma> (TCp (Assign x E)) = Eps" |
  "get_op s \<sigma> (TCp (Assume E))   = Eps" |
  "get_op s \<sigma> (Lookup x E)       = Read (aval E s) (\<sigma>(aval E s))" |
  "get_op s \<sigma> (Mutate E1 E2)     = Write (aval E1 s) (aval E2 s)"

fun c_primitive :: "stack \<Rightarrow> cmd_p \<Rightarrow> stack \<Rightarrow> bool" where
  "c_primitive s (Assign x E) s' \<longleftrightarrow> s' = s(x := aval E s)" |
  "c_primitive s (Assume E) s'   \<longleftrightarrow> s' = s \<and> aval E s \<noteq> 0"

(*fun update_kv :: "kv_store \<Rightarrow> views \<Rightarrow> fingerprint \<Rightarrow> txid \<Rightarrow> kv_store" where
  "update_kv kvs u fp t k \<equiv> (kvs k)((Max (u k)) := \<lparr>v_value=)" \<comment>\<open>How to append a new version\<close>

fun c_atomic_trans :: "kv_store \<Rightarrow> views \<Rightarrow> stack \<Rightarrow> txn \<Rightarrow> cl_id \<Rightarrow> fingerprint \<Rightarrow> kv_store \<Rightarrow> views \<Rightarrow> stack"*)
end