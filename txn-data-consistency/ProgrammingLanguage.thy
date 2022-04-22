section \<open>Programming Language\<close>

theory ProgrammingLanguage
  imports "HOL-IMP.AExp"
begin

subsection \<open>Syntax\<close>

datatype cmd_p = Assign vname aexp | Assume aexp
datatype txn_p = cmd_p | Lookup vname aexp | Mutate aexp aexp
datatype txn = TSkip | TSeq txn txn (infixr ";" 60) |
               TChoice txn txn (infixr "[+]" 65) | TItr txn
datatype cmd = Skip | Atomic txn | Seq cmd cmd (infixr ";;" 60) |
               Choice cmd cmd (infixr "[[+]]" 65) | Itr cmd

type_synonym cl_session = nat
typedecl cl_id
datatype txid0 = Tn_cl cl_session cl_id
datatype txid = T0 | txid0

type_synonym key = string
typedecl val
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

type_synonym snapshot = "key \<rightharpoonup> version"
definition view_snapshot :: "kv_store \<Rightarrow> views \<Rightarrow> snapshot" where
  "view_snapshot kvs u k \<equiv> kvs k (Max (u k))"
definition txn_snapshot :: "config \<Rightarrow> cl_id \<rightharpoonup> snapshot" where
  "txn_snapshot cfg cl \<equiv>
        (case ((c_conf cfg) cl) of
           None \<Rightarrow> None |
           Some u \<Rightarrow> Some (\<lambda>k. ((c_kvs cfg) k (Max (u k)))))"

datatype op_type = R | W

record fp_elem =
  f_op :: op_type
  f_key :: key
  f_val :: val

type_synonym fingerprint = "key \<rightharpoonup> fp_elem"

fun update_fp :: "fingerprint \<Rightarrow> op_type \<Rightarrow> key \<Rightarrow> val \<Rightarrow> fingerprint" where
  "update_fp fp R k v = (if fp k = None
                          then fp (k := Some \<lparr>f_op=R, f_key=k, f_val=v\<rparr>)
                          else fp)" |
  "update_fp fp W k v = fp (k := Some \<lparr>f_op=W, f_key=k, f_val=v\<rparr>)"

type_synonym stack = state
fun t_primitive :: "stack \<Rightarrow> snapshot \<Rightarrow> txn_p \<Rightarrow> stack \<Rightarrow> snapshot" where
  "t_primitive s \<sigma> (Assign x E) s' \<sigma>' \<equiv> s' = s(x := aval E s) \<and> \<sigma>' = \<sigma>"

end