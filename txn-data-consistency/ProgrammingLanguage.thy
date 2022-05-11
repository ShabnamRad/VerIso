section \<open>Programming Language\<close>

theory ProgrammingLanguage
  imports Main Event_Systems
begin

subsection \<open>Syntax\<close>

type_synonym key = nat

datatype 'a       cmd_p = Assign "'a \<Rightarrow> 'a" | Assume "'a \<Rightarrow> bool"

datatype ('a, 'v) txn_p = TCp "'a cmd_p" | Lookup key "'v \<Rightarrow>'a \<Rightarrow> 'a" | Mutate key "'a \<Rightarrow> 'v"

datatype ('a, 'v) txn   = TSkip| Tp "('a, 'v) txn_p" | TItr "('a, 'v) txn" |
                          TSeq "('a, 'v) txn" "('a, 'v) txn" (infixr "[;]" 60) |
                          TChoice "('a, 'v) txn" "('a, 'v) txn" (infixr "[+]" 65)

datatype ('a, 'v) cmd   = Skip| Cp "'a cmd_p" | Atomic "('a, 'v) txn" | Itr "('a, 'v) cmd" |
                          Seq "('a, 'v) cmd" "('a, 'v) cmd" (infixr ";;" 60) |
                          Choice "('a, 'v) cmd" "('a, 'v) cmd" (infixr "[[+]]" 65)


subsection \<open>Key-value stores\<close>

type_synonym sqn = nat
typedecl cl_id
datatype txid0 = Tn_cl sqn cl_id
datatype txid = T0 | Tn txid0

record 'v version =
  v_value :: 'v
  v_writer :: txid
  v_readerset :: "txid0 set"

definition version_init :: "'v version" where
  "version_init \<equiv> \<lparr>v_value = undefined, v_writer = T0, v_readerset = {}\<rparr>"

type_synonym 'v kv_store = "key \<Rightarrow> 'v version list"

definition kvs_init :: "'v kv_store" where
  "kvs_init _ \<equiv> [version_init]"


\<comment> \<open>predicates on kv stores\<close>

definition snapshot_property :: "'v kv_store \<Rightarrow> bool" where
  "snapshot_property K \<equiv>
    \<forall>k i j. v_readerset (K k!i) \<inter> v_readerset (K k!j) \<noteq> {} \<or>
            v_writer (K k!i) = v_writer (K k!i) \<longrightarrow> i = j"

definition SO0 :: "txid0 rel" where
  "SO0 \<equiv> {(t, t'). \<exists>cl n m. t = Tn_cl n cl \<and> t' = Tn_cl m cl \<and> n < m}"

definition SO :: "txid rel" where
  "SO \<equiv> {(Tn t, Tn t')| t t'. (t, t') \<in> SO0}"

definition wr_so :: "'v kv_store \<Rightarrow> bool" where
  "wr_so K \<equiv> \<forall>k i t t'. t = v_writer (K k!i) \<and> t' \<in> Tn ` v_readerset (K k!i) \<longrightarrow> (t', t) \<notin> SO^="

definition ww_so :: "'v kv_store \<Rightarrow> bool" where
  "ww_so K \<equiv> \<forall>k i j t t'. t = v_writer (K k!i) \<and> t' = v_writer (K k!j) \<and> i < j \<longrightarrow> (t', t) \<notin> SO^="

definition wellformed :: "'v kv_store \<Rightarrow> bool" where
 "wellformed K \<equiv> snapshot_property K \<and> wr_so K \<and> ww_so K \<and> (\<forall>k. v_value (K k!0) = undefined)"


\<comment> \<open>functions on kv stores\<close>

definition kvs_writers :: "'v kv_store \<Rightarrow> txid set" where
  "kvs_writers K \<equiv> (\<Union>k. v_writer ` (set (K k)))"

definition kvs_readers :: "'v kv_store \<Rightarrow> txid0 set" where
  "kvs_readers K \<equiv> (\<Union>k. \<Union>(v_readerset ` (set (K k))))"

definition kvs_txids :: "'v kv_store \<Rightarrow> txid set" where
  "kvs_txids K \<equiv> kvs_writers K  \<union> Tn ` kvs_readers K"

definition get_sqns :: "'v kv_store \<Rightarrow> cl_id \<Rightarrow> sqn set" where
  "get_sqns K cl \<equiv> {n. Tn (Tn_cl n cl) \<in> kvs_txids K}"

definition next_txids :: "'v kv_store \<Rightarrow> cl_id \<Rightarrow> txid0 set" where
  "next_txids K cl \<equiv> {Tn_cl n cl | n cl. \<forall>m \<in> get_sqns K cl. m < n}"


subsection \<open>Views\<close>

type_synonym v_id = nat

type_synonym view = "key \<Rightarrow> v_id set"

definition view_init :: view where
  "view_init _ \<equiv> {0}"

definition view_order :: "view \<Rightarrow> view \<Rightarrow> bool" (infix "\<sqsubseteq>" 60) where
  "u1 \<sqsubseteq> u2 \<equiv> \<forall>k. u1 k \<subseteq> u2 k"

definition view_in_range :: "'v kv_store \<Rightarrow> view \<Rightarrow> bool" where
  "view_in_range K u \<equiv> \<forall>k i. 0 \<in> u k \<and>  (i \<in> u k \<longrightarrow> 0 \<le> i \<and> i < length (K k))"

definition view_atomic :: "'v kv_store \<Rightarrow> view \<Rightarrow> bool" where
  "view_atomic K u \<equiv> \<forall>k k' i i'. i \<in> u k \<and> v_writer (K k!i) = v_writer (K k'!i') \<longrightarrow> i' \<in> u k'"

definition view_wellformed :: "'v kv_store \<Rightarrow> view \<Rightarrow> bool" where
  "view_wellformed K u \<equiv> view_in_range K u \<and> view_atomic K u"


subsection \<open>Operational semantics\<close>

type_synonym 'v snapshot = "key \<Rightarrow> 'v"

definition last_version :: "'v kv_store \<Rightarrow> view \<Rightarrow> key \<Rightarrow> 'v version" where
  "last_version K u k \<equiv> K k!(Max (u k))"

definition view_snapshot :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v snapshot" where
  "view_snapshot K u k \<equiv> v_value (last_version K u k)"

datatype op_type = R | W
datatype 'v op = Read key 'v | Write key 'v | Eps

type_synonym 'v fingerpr = "key \<times> op_type \<rightharpoonup> 'v"

fun update_fp :: "'v fingerpr \<Rightarrow> 'v op \<Rightarrow> 'v fingerpr" where
  "update_fp fp (Read k v)  = (if fp (k, R) = None \<and> fp (k, W) = None
                               then fp ((k, R) \<mapsto> v)
                               else fp)" |
  "update_fp fp (Write k v) = fp ((k, W) \<mapsto> v)" |
  "update_fp fp Eps         = fp"

fun update_kv_reads :: "txid0 \<Rightarrow> 'v fingerpr \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> 'v kv_store" where
  "update_kv_reads t fp u K k =
    (case fp (k, R) of
      None   \<Rightarrow> K k |
      Some v \<Rightarrow> let lv = last_version K u k in \<comment> \<open>We are ignoring v =? v_value lv\<close>
                  (K k)[Max (u k) := lv\<lparr>v_readerset := insert t (v_readerset lv)\<rparr>])"

fun update_kv_writes :: "txid0 \<Rightarrow> 'v fingerpr \<Rightarrow> 'v kv_store \<Rightarrow> 'v kv_store" where
  "update_kv_writes t fp K k =
    (case fp (k, W) of
      None   \<Rightarrow> K k |
      Some v \<Rightarrow> K k @ [\<lparr>v_value=v, v_writer=Tn t, v_readerset={}\<rparr>])"

definition update_kv :: "txid0 \<Rightarrow> 'v fingerpr \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> 'v kv_store" where
  "update_kv t fp u = (update_kv_writes t fp) o (update_kv_reads t fp u)"


\<comment> \<open>primitive commands\<close>

inductive cp_step :: "'a \<Rightarrow> 'a cmd_p \<Rightarrow> 'a \<Rightarrow> bool" where
  "cp_step s (Assign f) (f s)" |
  "t s \<Longrightarrow> cp_step s (Assume t) s"

\<comment> \<open>primitives transactions\<close>

inductive tp_step :: "'a \<Rightarrow> 'v snapshot \<Rightarrow> ('a, 'v) txn_p \<Rightarrow> 'a \<Rightarrow> 'v snapshot \<Rightarrow> bool" where
  "tp_step s \<sigma> (Lookup k f_rd) (f_rd (\<sigma> k) s) \<sigma>" |
  "\<sigma>' = \<sigma>(k := f_wr s) \<Longrightarrow> tp_step s \<sigma> (Mutate k f_wr) s \<sigma>'"|
  "cp_step s cp s' \<Longrightarrow> tp_step s \<sigma> (TCp cp) s' \<sigma>"

fun get_op :: "'a \<Rightarrow> 'v snapshot \<Rightarrow> ('a, 'v) txn_p \<Rightarrow> 'v op" where
  "get_op s \<sigma> (Lookup k f_rd)  = Read k (\<sigma> k)" |
  "get_op s \<sigma> (Mutate k f_wr)  = Write k (f_wr s)"|
  "get_op s \<sigma> _ = Eps"

type_synonym ('a, 'v) t_state = "('a \<times> 'v snapshot \<times> 'v fingerpr) \<times> ('a, 'v) txn"

inductive t_step :: "('a, 'v) t_state \<Rightarrow> ('a, 'v) t_state \<Rightarrow> bool"  where
  "\<lbrakk>tp_step s \<sigma> tp s' \<sigma>'; fp' = update_fp fp (get_op s \<sigma> tp)\<rbrakk>
    \<Longrightarrow> t_step ((s,\<sigma>,fp), Tp tp) ((s',\<sigma>',fp'), TSkip)" |
  "t_step (ts, T1 [+] T2) (ts, T1)" |
  "t_step (ts, T1 [+] T2) (ts, T2)" |
  "t_step (ts, TSkip [;] T) (ts, T)" |
  "t_step (ts, T1) (ts', T1') \<Longrightarrow> t_step (ts, T1[;] T2) (ts', T1'[;] T2)" |
  "t_step (ts, TItr T) (ts, TSkip [+] (T [;] TItr T))"

fun t_multi_step :: "('a, 'v) t_state \<Rightarrow> ('a, 'v) t_state \<Rightarrow> bool" where
  "t_multi_step s s' \<longleftrightarrow> t_step^** s s'"



subsection \<open>Execution tests and command-, program semantics\<close>

definition visTx :: "'v kv_store \<Rightarrow> view \<Rightarrow> txid set" where
  "visTx K u \<equiv> {v_writer (K k!i) | i k. i \<in> u k}"

definition read_only_Txs :: "'v kv_store \<Rightarrow> txid set" where
  "read_only_Txs K \<equiv> kvs_txids K - kvs_writers K"

definition closed :: "'v kv_store \<Rightarrow> view \<Rightarrow> txid rel \<Rightarrow> bool" where
  "closed K u r \<longleftrightarrow> visTx K u = (((r^*)^-1) `` (visTx K u)) - (read_only_Txs K)" 

locale ExecutionTest =
  fixes R_ET :: "'v kv_store \<Rightarrow> 'v fingerpr \<Rightarrow> txid rel"
    and vShift :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> view \<Rightarrow> bool"
   \<comment>\<open>We need some assumptions from Definition 8 of ECOOP paper\<close>
begin

definition canCommit :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v fingerpr \<Rightarrow> bool" where
  "canCommit K u F \<equiv> closed K u (R_ET K F)"

end

                                      
datatype 'v label = NA cl_id | CF cl_id view "'v fingerpr"

type_synonym ('a, 'v) c_state = "('v kv_store \<times> view \<times> 'a) \<times> ('a, 'v) cmd"

record 'v config =
  c_kvs :: "'v kv_store"
  c_views :: "cl_id \<Rightarrow> view"

definition c_views_init :: "cl_id \<Rightarrow> view" where
  "c_views_init _ \<equiv> view_init"

definition config_init :: "'v config" where
  "config_init \<equiv> \<lparr>c_kvs = kvs_init, c_views = c_views_init\<rparr>"

definition txn_snapshot :: "'v config \<Rightarrow> cl_id \<Rightarrow> 'v snapshot" where \<comment>\<open>Is this needed?\<close>
  "txn_snapshot cfg cl k \<equiv> v_value (last_version (c_kvs cfg) (c_views cfg cl) k)"

type_synonym 'a c_env = "cl_id \<Rightarrow> 'a"

definition c_env_init :: "'a c_env" where
  "c_env_init \<equiv> \<lambda>cl. undefined"

type_synonym ('a, 'v) progs = "cl_id \<Rightarrow> ('a, 'v) cmd"

type_synonym ('a, 'v) p_state = "('v config \<times> 'a c_env) \<times> ('a, 'v) progs"


context ExecutionTest
begin

\<comment> \<open>command semantics\<close>

definition c_init :: "('a, 'v) c_state \<Rightarrow> bool" where
  "c_init cs \<equiv> fst cs = (kvs_init, view_init, undefined)"

inductive c_step :: "('a, 'v) c_state \<Rightarrow> 'v label \<Rightarrow> ('a, 'v) c_state \<Rightarrow> bool" where
  "cp_step s cp s' \<Longrightarrow> c_step ((K, u, s), (Cp cp)) (NA cl) ((K, u, s'), Skip)" |
  "\<lbrakk> u \<sqsubseteq> u''; view_wellformed K u; view_wellformed K u'';
     \<sigma> = view_snapshot K u'';
     t_multi_step ((s, \<sigma>, \<lambda>k. None), T) ((s', _, F), TSkip);
     t \<in> next_txids K cl;
     K' = update_kv t F u'' K;
     view_wellformed K' u';
     canCommit K u F; vShift K u'' K' u' \<rbrakk>
    \<Longrightarrow> c_step ((K, u, s), Atomic T) (CF cl u'' F) ((K', u', s'), Skip)" |
  "c_step ((K, u, s), C1 [[+]] C2) (NA cl) ((K, u, s), C1)" |
  "c_step ((K, u, s), C1 [[+]] C2) (NA cl) ((K, u, s), C2)" |
  "c_step ((K, u, s), Skip;; C) (NA cl) ((K, u, s), C)" |
  "c_step ((K, u, s), C1) l ((K', u', s'), C1')
    \<Longrightarrow> c_step ((K, u, s), C1;; C2) l ((K', u', s'), C1';; C2)" |
  "c_step ((K, u, s), Itr C) (NA cl) ((K, u, s), Skip [[+]] (C;; Itr C))"

inductive c_multi_step :: "('a, 'v) c_state \<Rightarrow> ('a, 'v) c_state \<Rightarrow> bool" where
  "c_multi_step s s" |
  "\<lbrakk> c_multi_step s s';
     c_multi_step s' s'' \<rbrakk>
    \<Longrightarrow> c_multi_step s s''" |
  "c_step s _ s' \<Longrightarrow> c_multi_step s s'"

definition cES :: "('v label, ('a, 'v) c_state) ES" where
  "cES \<equiv> \<lparr>
    init = c_init,
    trans = c_step
  \<rparr>"


\<comment> \<open>program semantics\<close>

definition PProg_init :: "('a, 'v) p_state \<Rightarrow> bool" where
  "PProg_init ps \<equiv> fst ps = (config_init, c_env_init)"

inductive PProg_trans :: "('a, 'v) p_state \<Rightarrow>'v label \<Rightarrow> ('a, 'v) p_state \<Rightarrow> bool" where
  "\<lbrakk> u = U cl;
     s = E cl;
     C = P cl;
     c_step ((K, u, s), C) l ((K', u', s'), C') \<rbrakk>
    \<Longrightarrow> PProg_trans ((\<lparr> c_kvs = K , c_views = U \<rparr>, E), P) l
                    ((\<lparr> c_kvs = K', c_views = U(cl := u') \<rparr>, E(cl := s')), P(cl := C'))"

definition PProgES :: "('v label, ('a, 'v) p_state) ES" where
  "PProgES \<equiv> \<lparr>
    init = PProg_init,
    trans = PProg_trans
  \<rparr>"

end

subsection \<open>Dependency Relations\<close>

type_synonym 'v dep_rel = "'v kv_store \<Rightarrow> key \<Rightarrow> txid rel"

abbreviation in_range :: "nat \<Rightarrow> 'v kv_store \<Rightarrow> key \<Rightarrow> bool" where
  "in_range i K k \<equiv> 0 \<le> i \<and> i < length (K k)"

definition WR :: "'v dep_rel" where
  "WR K k \<equiv> {(t, t'). \<exists>i. in_range i K k \<and> t = v_writer (K k!i) \<and> t' \<in> Tn ` v_readerset (K k!i)}"

definition WW :: "'v dep_rel" where
  "WW K k \<equiv> {(t, t'). \<exists>i i'. in_range i K k \<and> in_range i' K k \<and>
                             t = v_writer (K k!i) \<and> t' = v_writer (K k!i') \<and> i < i'}"

definition RW :: "'v dep_rel" where
  "RW K k \<equiv> {(t, t'). \<exists>i i'. in_range i K k \<and> in_range i' K k \<and>
                              t \<in> Tn ` v_readerset (K k!i) \<and> t' = v_writer (K k!i') \<and> i < i' \<and> t \<noteq> t'}"

definition R_onK :: "'v dep_rel \<Rightarrow> 'v kv_store \<Rightarrow> txid rel" where
  "R_onK r K \<equiv> \<Union>k. r K k"

subsection \<open>Consistency models' execution tests\<close>

definition R_CC :: "'v kv_store \<Rightarrow> 'v fingerpr \<Rightarrow> txid rel" where
  "R_CC K F \<equiv> SO \<union> R_onK WR K"

definition R_UA :: "'v kv_store \<Rightarrow> 'v fingerpr \<Rightarrow> txid rel" where
  "R_UA K F \<equiv> \<Union>k. if (k, W) \<in> dom F then (WW K k)^-1 else {}"

definition R_PSI :: "'v kv_store \<Rightarrow> 'v fingerpr \<Rightarrow> txid rel" where
  "R_PSI K F \<equiv> R_UA K F \<union> R_CC K F \<union> R_onK WW K"

definition R_CP :: "'v kv_store \<Rightarrow> 'v fingerpr \<Rightarrow> txid rel" where
  "R_CP K F \<equiv> SO O (R_onK RW K)^= \<union> (R_onK WR K) O (R_onK RW K)^= \<union> (R_onK WW K)"

definition R_SI :: "'v kv_store \<Rightarrow> 'v fingerpr \<Rightarrow> txid rel" where
  "R_SI K F \<equiv> R_UA K F \<union> R_CP K F \<union> (R_onK WW K) O (R_onK RW K)"

definition R_SER :: "'v kv_store \<Rightarrow> 'v fingerpr \<Rightarrow> txid rel" where
  "R_SER K F \<equiv> R_onK WW K"

definition vShift_MR :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> view \<Rightarrow> bool" where
  "vShift_MR K u K' u' \<equiv> u \<sqsubseteq> u'"

definition vShift_RYW :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> view \<Rightarrow> bool" where
  "vShift_RYW K u K' u' \<equiv>
    \<forall>t \<in> kvs_txids K' - kvs_txids K. \<forall>k i. (v_writer (K' k!i) , t) \<in> SO^= \<longrightarrow> i \<in> u' k"

definition vShift_MR_RYW :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> view \<Rightarrow> bool" where
  "vShift_MR_RYW K u K' u' \<equiv> vShift_MR K u K' u' \<and> vShift_RYW K u K' u'"

interpretation ET_MR: ExecutionTest "\<lambda>K F. {}" vShift_MR .

interpretation ET_RYW: ExecutionTest "\<lambda>K F. {}"  vShift_RYW .

interpretation ET_CC: ExecutionTest R_CC vShift_MR_RYW .

interpretation ET_UA: ExecutionTest R_UA "\<lambda>K u K' u'. True" .

interpretation ET_PSI: ExecutionTest R_PSI vShift_MR_RYW .

interpretation ET_CP: ExecutionTest R_CP vShift_MR_RYW .

interpretation ET_SI: ExecutionTest R_SI vShift_MR_RYW .

interpretation ET_SER: ExecutionTest R_SER "\<lambda>K u K' u'. True" .

end