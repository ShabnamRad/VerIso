section \<open>Programming Language\<close>

theory ProgrammingLanguage
  imports Main
begin

subsection \<open>Syntax\<close>

type_synonym key = nat

datatype 'a       cmd_p = Assign "'a \<Rightarrow> 'a"| Assume "'a \<Rightarrow> bool"
datatype ('a, 'v) txn_p = TCp "'a cmd_p"| Lookup key "'v \<Rightarrow>'a \<Rightarrow> 'a"| Mutate key "'a \<Rightarrow> 'v"
datatype ('a, 'v) txn   = TSkip| Tp "('a, 'v) txn_p"| TItr "('a, 'v) txn"|
                          TSeq "('a, 'v) txn" "('a, 'v) txn" (infixr ";" 60)|
                          TChoice "('a, 'v) txn" "('a, 'v) txn" (infixr "[+]" 65)
datatype ('a, 'v) cmd   = Skip| Cp "'a cmd_p"| Atomic "('a, 'v) txn"| Itr "('a, 'v) cmd"|
                          Seq "('a, 'v) cmd" "('a, 'v) cmd" (infixr ";;" 60)|
                          Choice "('a, 'v) cmd" "('a, 'v) cmd" (infixr "[[+]]" 65)

type_synonym cl_session = nat
typedecl cl_id
datatype txid0 = Tn_cl cl_session cl_id
datatype txid = T0 | Tn txid0

record 'v version =
  v_value :: 'v
  v_writer :: txid
  v_readerset :: "txid0 set"

type_synonym v_id = nat

definition version_init :: "'v version" where
  "version_init \<equiv> \<lparr>v_value = undefined, v_writer = T0, v_readerset = {}\<rparr>"

type_synonym 'v kv_store = "key \<Rightarrow> 'v version list"
definition kvs_init :: "'v kv_store" where
  "kvs_init _ \<equiv> [version_init]"

type_synonym views = "key \<Rightarrow> v_id set"
definition views_init :: views where
  "views_init _ \<equiv> {0}"
definition view_order :: "views \<Rightarrow> views \<Rightarrow> bool" where
  "view_order u1 u2 \<equiv> \<forall>k. u1 k \<subseteq> u2 k"

record 'v config =
  c_kvs :: "'v kv_store"
  c_conf :: "cl_id \<Rightarrow> views"

definition conf_init :: "cl_id \<Rightarrow> views" where
  "conf_init _ \<equiv> views_init"
definition config_init :: "'v config" where
  "config_init \<equiv> \<lparr>c_kvs = kvs_init, c_conf = conf_init\<rparr>"

type_synonym 'v snapshot = "key \<Rightarrow> 'v"
definition last_version :: "'v kv_store \<Rightarrow> views \<Rightarrow> key \<Rightarrow> 'v version" where
  "last_version kvs u k \<equiv> kvs k!(Max (u k))"

definition view_snapshot :: "'v kv_store \<Rightarrow> views \<Rightarrow> 'v snapshot" where
  "view_snapshot kvs u k \<equiv> v_value (last_version kvs u k)"

definition txn_snapshot :: "'v config \<Rightarrow> cl_id \<Rightarrow> 'v snapshot" where
  "txn_snapshot cfg cl k \<equiv> v_value (last_version (c_kvs cfg) ((c_conf cfg) cl) k)"

datatype op_type = R | W
datatype 'v op = Read key 'v | Write key 'v | Eps

type_synonym 'v fingerpr = "key \<times> op_type \<rightharpoonup> 'v"

fun update_fp :: "'v fingerpr \<Rightarrow> 'v op \<Rightarrow> 'v fingerpr" where
  "update_fp fp (Read k v)  = (if fp (k, R) = None \<and> fp (k, W) = None
                               then fp ((k, R) \<mapsto> v)
                               else fp)" |
  "update_fp fp (Write k v) = fp ((k, W) \<mapsto> v)" |
  "update_fp fp Eps         = fp"

inductive tp_step :: "'a \<Rightarrow> 'v snapshot \<Rightarrow> ('a, 'v) txn_p \<Rightarrow> 'a \<Rightarrow> 'v snapshot \<Rightarrow> bool" where
  "tp_step s \<sigma> (TCp (Assign f)) (f s) \<sigma>" |
  "t s \<Longrightarrow> tp_step s \<sigma> (TCp (Assume t)) s \<sigma>" |
  "tp_step s \<sigma> (Lookup k f_rd) (f_rd (\<sigma> k) s) \<sigma>" |
  "\<sigma>' = \<sigma>(k := f_wr s) \<Longrightarrow> tp_step s \<sigma> (Mutate k f_wr) s \<sigma>'"

fun get_op :: "'a \<Rightarrow> 'v snapshot \<Rightarrow> ('a, 'v) txn_p \<Rightarrow> 'v op" where
  "get_op s \<sigma> (TCp (Assign f)) = Eps" |
  "get_op s \<sigma> (TCp (Assume t)) = Eps" |
  "get_op s \<sigma> (Lookup k f_rd)  = Read k (\<sigma> k)" |
  "get_op s \<sigma> (Mutate k f_wr)  = Write k (f_wr s)"

type_synonym ('a, 'v) t_state = "('a \<times> 'v snapshot \<times> 'v fingerpr) \<times> ('a, 'v) txn"
inductive t_step :: "('a, 'v) t_state \<Rightarrow> ('a, 'v) t_state \<Rightarrow> bool"  where
  "tp_step s \<sigma> tp s' \<sigma>' \<and> fp' = update_fp fp (get_op s \<sigma> tp)
    \<Longrightarrow> t_step ((s,\<sigma>,fp), Tp tp) ((s',\<sigma>',fp'), TSkip)"|
  "t_step (ts, T1[+]T2) (ts, T1)"|
  "t_step (ts, T1[+]T2) (ts, T2)"|
  "t_step (ts, TSkip; T) (ts, T)"|
  "t_step (ts, T1) (ts', T1') \<Longrightarrow> t_step (ts, T1; T2) (ts', T1'; T2)"|
  "t_step (ts, TItr T) (ts, TSkip[+](T; TItr T))"

fun t_multi_step :: "('a, 'v) t_state \<Rightarrow> ('a, 'v) t_state \<Rightarrow> bool" where
  "t_multi_step s s' \<longleftrightarrow> t_step^** s s'"

inductive cp_step :: "'a \<Rightarrow> 'a cmd_p \<Rightarrow> 'a \<Rightarrow> bool" where
  "cp_step s (Assign f) (f s)"|
  "t s \<Longrightarrow> cp_step s (Assume t) s"

fun update_kv :: "'v kv_store \<Rightarrow> views \<Rightarrow> 'v fingerpr \<Rightarrow> txid0 \<Rightarrow> 'v kv_store" where
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

type_synonym 'v label = "cl_id \<times> views \<times> 'v fingerpr"
type_synonym ('a, 'v) c_state = "('v kv_store \<times> views \<times> 'a) \<times> ('a, 'v) cmd"
inductive c_step :: "('a, 'v) c_state \<Rightarrow> 'v label \<Rightarrow> ('a, 'v) c_state \<Rightarrow> bool" where
  "cp_step s cp s' \<Longrightarrow> c_step ((K, u, s), (Cp cp)) (cl, _, _) ((K, u, s'), Skip)"|
  "view_order u u'' \<and> \<sigma> = view_snapshot K u'' \<and>
    t_multi_step ((s, \<sigma>, (\<lambda>k. None)), T) ((s', _, F), TSkip) \<and> (K' = update_kv K u'' F t)
    \<Longrightarrow> c_step ((K, u, s), Atomic T) (cl, u'', F) ((K', u', s'), Skip)"| \<comment>\<open>TODO: Add CanCommit ViewShift and NextTxID\<close>
  "c_step ((K, u, s), C1[[+]]C2) (cl, _, _) ((K, u, s), C1)"|
  "c_step ((K, u, s), C1[[+]]C2) (cl, _, _) ((K, u, s), C2)"|
  "c_step ((K, u, s), Skip;; C) (cl, _, _) ((K, u, s), C)"|
  "c_step ((K, u, s), C1) _ ((K', u', s'), C1')
    \<Longrightarrow> c_step ((K, u, s), C1;; C2) _ ((K', u', s'), C1';; C2)"|
  "c_step ((K, u, s), Itr C) (cl, _, _) ((K, u, s), Skip[[+]](C;; Itr C))"

end