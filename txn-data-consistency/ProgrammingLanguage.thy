section \<open>Programming Language\<close>

theory ProgrammingLanguage
  imports "HOL-IMP.AExp"
begin

subsection \<open>Syntax\<close>

type_synonym key = nat
typedecl val
consts val0 :: val

datatype 'a cmd_p = Assign "'a \<Rightarrow> 'a"| Assume "'a \<Rightarrow> bool"
datatype 'a txn_p = TCp "'a cmd_p"| Lookup key "val \<Rightarrow>'a \<Rightarrow> 'a"| Mutate key "'a \<Rightarrow> val"
datatype 'a txn   = TSkip| Tp "'a txn_p"| TSeq "'a txn" "'a txn" (infixr ";" 60)|
                    TChoice "'a txn" "'a txn" (infixr "[+]" 65)| TItr "'a txn"
datatype 'a cmd   = Skip| Cp "'a cmd_p"| Atomic "'a txn"| Seq "'a cmd" "'a cmd" (infixr ";;" 60)|
                    Choice "'a cmd" "'a cmd" (infixr "[[+]]" 65)| Itr "'a cmd"

type_synonym cl_session = nat
typedecl cl_id
datatype txid0 = Tn_cl cl_session cl_id
datatype txid = T0 | Tn txid0

record version =
  v_value :: val
  v_writer :: txid
  v_readerset :: "txid0 set"

type_synonym v_id = nat

definition version_init :: version where
  "version_init \<equiv> \<lparr>v_value = val0, v_writer = T0, v_readerset = {}\<rparr>"

type_synonym kv_store = "key \<Rightarrow> version list"
definition kvs_init :: kv_store where
  "kvs_init _ \<equiv> [version_init]"

type_synonym views = "key \<Rightarrow> v_id set"
definition views_init :: views where
  "views_init _ \<equiv> {0}"

record config =
  c_kvs :: kv_store
  c_conf :: "cl_id \<Rightarrow> views"

definition conf_init :: "cl_id \<Rightarrow> views" where
  "conf_init _ \<equiv> views_init"
definition config_init :: config where
  "config_init \<equiv> \<lparr>c_kvs = kvs_init, c_conf = conf_init\<rparr>"

type_synonym snapshot = "key \<Rightarrow> val"
definition last_version :: "kv_store \<Rightarrow> views \<Rightarrow> key \<Rightarrow> version" where
  "last_version kvs u k \<equiv> kvs k!(Max (u k))"

definition view_snapshot :: "kv_store \<Rightarrow> views \<Rightarrow> snapshot" where
  "view_snapshot kvs u k \<equiv> v_value (last_version kvs u k)"

definition txn_snapshot :: "config \<Rightarrow> cl_id \<Rightarrow> snapshot" where
  "txn_snapshot cfg cl k \<equiv> v_value (last_version (c_kvs cfg) ((c_conf cfg) cl) k)"

datatype op_type = R | W
datatype op = Read key val | Write key val | Eps

type_synonym fingerpr = "key \<times> op_type \<rightharpoonup> val"

fun update_fp :: "fingerpr \<Rightarrow> op \<Rightarrow> fingerpr" where
  "update_fp fp (Read k v)  = (if fp (k, R) = None \<and> fp (k, W) = None
                               then fp ((k, R) \<mapsto> v)
                               else fp)" |
  "update_fp fp (Write k v) = fp ((k, W) \<mapsto> v)" |
  "update_fp fp Eps         = fp"

fun tp_step :: "'a \<Rightarrow> snapshot \<Rightarrow> 'a txn_p \<Rightarrow> 'a \<Rightarrow> snapshot \<Rightarrow> bool" where
  "tp_step s \<sigma> (TCp (Assign f)) s' \<sigma>' \<longleftrightarrow> s' = f s \<and> \<sigma>' = \<sigma>" |
  "tp_step s \<sigma> (TCp (Assume t)) s' \<sigma>' \<longleftrightarrow> s' = s \<and> \<sigma>' = \<sigma> \<and> t s" |
  "tp_step s \<sigma> (Lookup k f_rd) s' \<sigma>'  \<longleftrightarrow> s' = f_rd (\<sigma> k) s \<and> \<sigma>' = \<sigma>" |
  "tp_step s \<sigma> (Mutate k f_wr) s' \<sigma>'  \<longleftrightarrow> s' = s \<and> \<sigma>' = \<sigma>(k := f_wr s)"

fun get_op :: "'a \<Rightarrow> snapshot \<Rightarrow> 'a txn_p \<Rightarrow> op" where
  "get_op s \<sigma> (TCp (Assign f)) = Eps" |
  "get_op s \<sigma> (TCp (Assume t)) = Eps" |
  "get_op s \<sigma> (Lookup k f_rd)  = Read k (\<sigma> k)" |
  "get_op s \<sigma> (Mutate k f_wr)  = Write k (f_wr s)"

type_synonym 'a t_state = "'a \<times> snapshot \<times> fingerpr"
fun t_step :: "'a t_state \<Rightarrow> 'a txn \<Rightarrow> 'a t_state \<Rightarrow> 'a txn \<Rightarrow> bool"  where
  "t_step (s,\<sigma>,fp) (Tp tp) (s',\<sigma>',fp') T' \<longleftrightarrow>
                tp_step s \<sigma> tp s' \<sigma>' \<and> fp' = update_fp fp (get_op s \<sigma> tp) \<and> T' = TSkip"|
  "t_step ts (T1[+]T2)  ts' T'         \<longleftrightarrow> ts' = ts \<and> (T' = T1 \<or> T' = T2)"|
  "t_step ts (TSkip; T) ts' T'         \<longleftrightarrow> ts' = ts \<and> T' = T"|
  "t_step ts (T1; T2)   ts' (T1'; T2') \<longleftrightarrow> t_step ts T1 ts' T1' \<and> T2' = T2"|
  "t_step ts (T1; T2)   ts' _          \<longleftrightarrow> False"|
  "t_step ts (TItr T)   ts' T'         \<longleftrightarrow> ts' = ts \<and> T' = TSkip[+](T; TItr T)"|
  "t_step _   TSkip     _   _          \<longleftrightarrow> False"

(*inductive t_multi_step :: "'a t_state \<Rightarrow> 'a txn \<Rightarrow> 'a t_state \<Rightarrow> bool" where
  "t_multi_step s T s' \<Longrightarrow> "*)

fun cp_step :: "'a \<Rightarrow> 'a cmd_p \<Rightarrow> 'a \<Rightarrow> bool" where
  "cp_step s (Assign f) s' \<longleftrightarrow> s' = f s"|
  "cp_step s (Assume t) s' \<longleftrightarrow> s' = s \<and> t s"

fun update_kv :: "kv_store \<Rightarrow> views \<Rightarrow> fingerpr \<Rightarrow> txid0 \<Rightarrow> kv_store" where
  "update_kv kvs u fp t k =
    (let kvs_k_R =
      (let lv = last_version kvs u k in
       (case fp (k, R) of
         None   \<Rightarrow> kvs k|
         Some v \<Rightarrow> (if v = v_value lv then
                    list_update (kvs k) (Max (u k)) (lv \<lparr>v_readerset := insert t (v_readerset lv)\<rparr>)
                    else kvs k) \<comment>\<open>Throwing an exception? t has read the wrong value\<close>
       )) in
    (case fp (k, W) of
      None   \<Rightarrow> kvs_k_R |
      Some v \<Rightarrow> kvs_k_R @ [\<lparr>v_value=v, v_writer=Tn t, v_readerset={}\<rparr>]))"

(*fun c_atomic_trans :: "kv_store \<Rightarrow> views \<Rightarrow> stack \<Rightarrow> txn \<Rightarrow> cl_id \<Rightarrow> fingerpr \<Rightarrow> kv_store \<Rightarrow> views \<Rightarrow> stack"*)
end