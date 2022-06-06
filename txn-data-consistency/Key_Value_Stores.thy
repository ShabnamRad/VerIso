section \<open>Key-Value Stores\<close>

theory Key_Value_Stores
  imports Event_Systems
begin

subsection \<open>Key-value stores\<close>

type_synonym key = nat

type_synonym sqn = nat

typedecl cl_id

datatype txid0 = Tn_cl sqn cl_id
datatype txid = T0 | Tn txid0

definition SO0 :: "txid0 rel" where
  "SO0 \<equiv> {(t, t'). \<exists>cl n m. t = Tn_cl n cl \<and> t' = Tn_cl m cl \<and> n < m}"

definition SO :: "txid rel" where
  "SO \<equiv> {(Tn t, Tn t')| t t'. (t, t') \<in> SO0}"


record 'v version =
  v_value :: 'v
  v_writer :: txid
  v_readerset :: "txid0 set"

definition version_init :: "'v version" where
  "version_init \<equiv> \<lparr>v_value = undefined, v_writer = T0, v_readerset = {}\<rparr>"

type_synonym 'v kv_store = "key \<Rightarrow> 'v version list"

definition kvs_init :: "'v kv_store" where
  "kvs_init k \<equiv> [version_init]"

lemmas kvs_init_defs = kvs_init_def version_init_def


\<comment> \<open>index range for a kvs and key\<close>

definition in_range :: "'v kv_store \<Rightarrow> key \<Rightarrow> nat set" where  
  "in_range K k \<equiv> {..<length (K k)}"

thm nth_list_update_eq nth_list_update_neq

lemma in_range_finite [simp, intro!]: "finite (in_range K k)"
  by (simp add: in_range_def)

lemma in_range_nth_list_update_eq [simp]:     (* special case of nth_list_update_eq *)
  "i \<in> in_range K k \<Longrightarrow> (K k)[i := x] ! i = x"
  by (simp add: in_range_def)

lemma in_range_append [simp]:
  "i \<in> in_range K k \<Longrightarrow> (K k @ vs) ! i = K k ! i"
  by (auto simp add: in_range_def nth_append)

lemma in_range_kvs_init [simp]:
  "i \<in> in_range kvs_init k \<longleftrightarrow> i = 0"
  by (simp add: kvs_init_defs in_range_def)

(*
  TODO: there are too many uses of in_range_def below; 
  try to find the relevant properties and reduce the use of in_range_def below
*)


subsubsection  \<open>Wellformedness of KV stores\<close>

definition snapshot_property :: "'v kv_store \<Rightarrow> bool" where
  "snapshot_property K \<longleftrightarrow> (\<forall>k. \<forall>i \<in> in_range K k. \<forall>j \<in> in_range K k.
                                 (v_readerset (K k!i) \<inter> v_readerset (K k!j) \<noteq> {} \<or>
                                  v_writer (K k!i) = v_writer (K k!j)) \<longrightarrow> i = j)"

lemmas snapshot_propertyI = snapshot_property_def [THEN iffD2, rule_format]
lemmas snapshot_propertyE [elim] = snapshot_property_def [THEN iffD1, elim_format, rule_format]

lemma snapshot_property_kvs_init [simp, intro]: "snapshot_property kvs_init"
  by (intro snapshot_propertyI) (auto)

definition wr_so :: "'v kv_store \<Rightarrow> bool" where
  "wr_so K \<longleftrightarrow> (\<forall>k t t'. \<forall>i \<in> in_range K k.
                  t = v_writer (K k!i) \<and> t' \<in> Tn ` v_readerset (K k!i) \<longrightarrow> (t', t) \<notin> SO^=)"

lemmas wr_soI = wr_so_def [THEN iffD2, rule_format]
lemmas wr_soE [elim] = wr_so_def [THEN iffD1, elim_format, rule_format]

lemma wr_so_kvs_init [simp, intro]: "wr_so kvs_init"
  by (intro wr_soI) (auto simp add: kvs_init_defs)


definition ww_so :: "'v kv_store \<Rightarrow> bool" where
  "ww_so K \<longleftrightarrow> (\<forall>k t t'. \<forall>i \<in> in_range K k. \<forall>j \<in> in_range K k.
                  t = v_writer (K k!i) \<and> t' = v_writer (K k!j) \<and> i < j \<longrightarrow> (t', t) \<notin> SO^=)"

lemmas ww_soI = ww_so_def [THEN iffD2, rule_format]
lemmas ww_soE [elim] = ww_so_def [THEN iffD1, elim_format, rule_format]

lemma ww_so_kvs_init [simp, intro]: "ww_so kvs_init"
  by (intro ww_soI) (auto simp add: kvs_init_defs)


definition kvs_initialized :: "'v kv_store \<Rightarrow> bool" where
  "kvs_initialized K \<longleftrightarrow> (\<forall>k. v_value (K k!0) = undefined)"

lemmas kvs_initializedI = kvs_initialized_def [THEN iffD2, rule_format]
lemmas kvs_initializedE [elim] = kvs_initialized_def [THEN iffD1, elim_format, rule_format]

lemma kvs_initialized_kvs_init [simp, intro]: "kvs_initialized kvs_init"
  by (intro kvs_initializedI) (auto simp add: kvs_init_defs)


definition kvs_wellformed :: "'v kv_store \<Rightarrow> bool"  where
  "kvs_wellformed K \<equiv> snapshot_property K \<and> wr_so K \<and> ww_so K \<and> kvs_initialized K"

lemmas kvs_wellformed_intros = snapshot_propertyI wr_soI ww_soI kvs_initializedI

(*
lemmas kvs_wellformed_defs = 
  kvs_wellformed_def snapshot_property_def ww_so_def wr_so_def (* SO_def SO0_def *) 
  kvs_initialized_def
*)

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

lemmas fresh_txid_defs = next_txids_def get_sqns_def kvs_txids_def kvs_readers_def kvs_writers_def

\<comment> \<open>txid freshness lemmas\<close>

lemma fresh_txid_v_writer:
  assumes "t \<in> next_txids K cl"
  shows "\<forall>i \<in> in_range K k. v_writer (K k!i) \<noteq> Tn t"
  using assms nth_mem
  apply (auto simp add: fresh_txid_defs image_iff in_range_def)
  by fastforce

lemma fresh_txid_v_reader_set:
  assumes "t \<in> next_txids K cl"
  shows "\<forall>i \<in> in_range K k. t \<notin> v_readerset (K k!i)"
  using assms nth_mem
  apply (auto simp add: fresh_txid_defs image_iff in_range_def)
  by blast

lemma fresh_txid_writer_so:
  assumes "t \<in> next_txids K cl"
  shows "\<forall>i \<in> in_range K k. (Tn t, v_writer (K k ! i)) \<notin> SO"
  using assms nth_mem
  apply (auto simp add: fresh_txid_defs SO_def SO0_def image_iff in_range_def)
  by fastforce


subsection \<open>Views\<close>

type_synonym v_id = nat

type_synonym view = "key \<Rightarrow> v_id set"

definition view_init :: view where
  "view_init _ \<equiv> {0}"

definition view_order :: "view \<Rightarrow> view \<Rightarrow> bool" (infix "\<sqsubseteq>" 60) where
  "u1 \<sqsubseteq> u2 \<equiv> \<forall>k. u1 k \<subseteq> u2 k"

definition view_in_range :: "'v kv_store \<Rightarrow> view \<Rightarrow> bool" where
  "view_in_range K u \<equiv> \<forall>k. 0 \<in> u k \<and> u k \<subseteq> in_range K k"

definition view_atomic :: "'v kv_store \<Rightarrow> view \<Rightarrow> bool" where
  "view_atomic K u \<equiv> \<forall>k k' i i'. i \<in> u k \<and> v_writer (K k!i) = v_writer (K k'!i') \<longrightarrow> i' \<in> u k'"

definition view_wellformed :: "'v kv_store \<Rightarrow> view \<Rightarrow> bool" where
  "view_wellformed K u \<longleftrightarrow> view_in_range K u \<and> view_atomic K u"

lemmas view_wellformedD1 [dest] = view_wellformed_def [THEN iffD1, THEN conjunct1]
lemmas view_wellformedD2 [dest] = view_wellformed_def [THEN iffD1, THEN conjunct2]

lemmas view_wellformed_defs = 
  view_wellformed_def view_in_range_def view_atomic_def 


\<comment> \<open>view lemmas\<close>

lemma view_non_empty [simp]:
  assumes "view_in_range K u"
  shows "u k \<noteq> {}"
  using assms 
  by (auto simp add: view_in_range_def)

lemma view_finite [simp]:
  assumes "view_in_range K u"
  shows "finite (u k)"
  using assms 
  by (auto simp add: view_in_range_def intro: rev_finite_subset)

lemma view_Max_in_range [simp]:
  assumes "view_in_range K u"
  shows "Max (u k) \<in> in_range K k"
proof -
  have "Max (u k) \<in> u k" using assms by auto
  then show ?thesis using assms by (auto simp add: view_in_range_def)
qed

lemma view_zero_in_range:
  assumes "view_in_range K u"
  shows "0 \<in> in_range K k" 
  using assms
  by (auto simp add: view_in_range_def)



subsection \<open>Snapshots and Configs\<close>

type_synonym 'v snapshot = "key \<Rightarrow> 'v"

definition last_version :: "'v kv_store \<Rightarrow> view \<Rightarrow> key \<Rightarrow> 'v version" where
  "last_version K u k \<equiv> K k!(Max (u k))"

definition view_snapshot :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v snapshot" where
  "view_snapshot K u k \<equiv> v_value (last_version K u k)"

type_synonym 'v config = "'v kv_store \<times> (cl_id \<Rightarrow> view)"

abbreviation kvs where "kvs \<equiv> fst"
abbreviation views where "views \<equiv> snd"

abbreviation c_views_init :: "cl_id \<Rightarrow> view" where
  "c_views_init _ \<equiv> view_init"

definition config_init :: "'v config" where
  "config_init \<equiv> (kvs_init, c_views_init)"

lemmas config_init_defs = config_init_def (* kvs_init_defs *) view_init_def


subsection \<open>Fingerprints\<close>

datatype op_type = R | W
datatype 'v op = Read key 'v | Write key 'v | Eps

type_synonym 'v fingerpr = "key \<times> op_type \<rightharpoonup> 'v"

fun update_fp :: "'v fingerpr \<Rightarrow> 'v op \<Rightarrow> 'v fingerpr" where
  "update_fp F (Read k v)  = (if F (k, R) = None \<and> F (k, W) = None
                               then F ((k, R) \<mapsto> v)
                               else F)" |
  "update_fp F (Write k v) = F ((k, W) \<mapsto> v)" |
  "update_fp F Eps         = F"

 \<comment>\<open>The Fingerprint condition was originally in Execution Test\<close>
definition fingerprint_condition :: "'v fingerpr \<Rightarrow> 'v kv_store \<Rightarrow> view \<Rightarrow> bool" where
  "fingerprint_condition F K u \<equiv>
    (\<forall>k. (k, R) \<in> dom F \<longrightarrow> F (k, R) = Some (v_value (last_version K u k)))"

definition update_kv_reads :: "txid0 \<Rightarrow> 'v fingerpr \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> 'v kv_store" where
  "update_kv_reads t F u K k =
    (case F (k, R) of
      None   \<Rightarrow> K k |
      Some v \<Rightarrow> let lv = last_version K u k in \<comment> \<open>We are ignoring v =? v_value lv\<close>
                  (K k)[Max (u k) := lv\<lparr>v_readerset := insert t (v_readerset lv)\<rparr>])"

definition update_kv_writes :: "txid0 \<Rightarrow> 'v fingerpr \<Rightarrow> 'v kv_store \<Rightarrow> 'v kv_store" where
  "update_kv_writes t F K k =
    (case F (k, W) of
      None   \<Rightarrow> K k |
      Some v \<Rightarrow> K k @ [\<lparr>v_value=v, v_writer=Tn t, v_readerset={}\<rparr>])"

definition update_kv :: "txid0 \<Rightarrow> 'v fingerpr \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> 'v kv_store" where
  "update_kv t F u = (update_kv_writes t F) o (update_kv_reads t F u)"

lemmas update_kv_reads_defs = update_kv_reads_def Let_def last_version_def

\<comment> \<open>update_kv lemmas about version list length and in_range\<close>

lemma update_kv_reads_length:
  "length (update_kv_reads t F u K k) = length (K k)"
proof (cases "F (k, R)")
  case (Some a)
  then show ?thesis apply (auto simp add: update_kv_reads_def)
    by (meson length_list_update)
qed (auto simp add: update_kv_reads_def)

lemma update_kv_writes_none_length:
  assumes "F (k, W) = None"
  shows "length (update_kv_writes t F K k) = length (K k)"
  using assms by (auto simp add: update_kv_writes_def)

lemma update_kv_writes_some_length:
  assumes "F (k, W) = Some v"
  shows "length (update_kv_writes t F K k) = Suc (length (K k))"
  using assms by (auto simp add: update_kv_writes_def)

lemma update_kv_writes_length:
  shows "length (update_kv_writes t F K k) = Suc (length (K k)) \<or> 
         length (update_kv_writes t F K k) = length (K k)"
  by (cases "F (k, W)") (auto simp add: update_kv_writes_def)

lemma update_kv_writes_length_increasing:
  "length (K k) \<le> length (update_kv_writes t F K k)"
  using update_kv_writes_length [of t F K k]   
  by auto

lemma update_kv_length:
  shows "length (update_kv t F u K k) = Suc (length (K k)) \<or>
         length (update_kv t F u K k) = length (K k)"
  using update_kv_writes_length [where K="update_kv_reads t F u K"]
  by (simp add: update_kv_def update_kv_reads_length)
 
lemma update_kv_length_increasing:
  "length (K k) \<le> length (update_kv t F u K k)"
  using update_kv_length [of t F u K k]   
  by auto

lemma in_range_update_kv_reads [simp]:
  "in_range (update_kv_reads t F u K) k = in_range K k"
  by (simp add: update_kv_reads_length in_range_def)

lemma in_range_update_kv_writes [dest]:
  "i \<in> in_range K k \<Longrightarrow> i \<in> in_range (update_kv_writes t F K) k"
  using update_kv_writes_length_increasing [of K k t F] 
  by (simp add: in_range_def)

lemma in_range_update_kv [dest]:
  "i \<in> in_range K k \<Longrightarrow> i \<in> in_range (update_kv t F u K) k"
  using update_kv_length_increasing [of K k t F u] 
  by (simp add: in_range_def)

lemma not_in_range_update_kv:
  assumes "i \<in> in_range (update_kv t F u K) k" and "i \<notin> in_range K k"
  shows "i = length (K k) \<and> length (update_kv t F u K k) = Suc (length (K k))"
  using assms update_kv_length [of t F u K k]
  by (auto simp add: less_Suc_eq_le in_range_def)

lemma update_kv_writes_decides_length:
  shows "length (update_kv t F u K k) = length (update_kv_writes t F K k)"
  by (cases "F (k, W)") (auto simp add: update_kv_def update_kv_writes_def update_kv_reads_length)

\<comment> \<open>update_kv lemmas about changing the versions\<close>

lemma update_kv_writes_version_inv:
  assumes "i \<in> in_range K k"
  shows "update_kv_writes t F K k!i = K k!i"
proof (cases "F (k, W)")
  case (Some a)
  then show ?thesis using assms
    by (auto simp add: update_kv_writes_def)
qed (auto simp add: update_kv_writes_def)

(* v_value *)
lemma update_kv_reads_v_value_inv:
  assumes "i \<in> in_range K k"
  shows "v_value (update_kv_reads t F u K k!i) = v_value (K k!i)"
proof (cases "F (k, R)")
  case (Some a)
  then show ?thesis using assms
    by (cases "i = Max (u k)") 
       (auto simp add: update_kv_reads_defs)
qed (auto simp add: update_kv_reads_def)

thm update_kv_writes_version_inv update_kv_reads_v_value_inv

lemma update_kv_v_value_inv:
  assumes "i \<in> in_range K k"
  shows "v_value (update_kv t F u K k!i) = v_value (K k!i)"
  using assms
  by (auto simp add: update_kv_def update_kv_writes_version_inv update_kv_reads_v_value_inv)

(* v_writer *)
lemma update_kv_reads_v_writer_inv:
  assumes "i \<in> in_range K k"
  shows "v_writer (update_kv_reads t F u K k!i) = v_writer (K k!i)"
proof (cases "F (k, R)")
  case (Some a)
  then show ?thesis using assms
    by (cases "i = Max (u k)")
       (auto simp add: update_kv_reads_defs split: option.splits)
qed (simp add: update_kv_reads_def)

lemma update_kv_v_writer_inv:
  assumes "i \<in> in_range K k"
  shows "v_writer (update_kv t F u K k!i) = v_writer (K k!i)"
  using assms
  by (auto simp add: update_kv_def update_kv_writes_version_inv update_kv_reads_v_writer_inv)

lemma update_kv_writes_new_version_v_writer:
  assumes  "length (update_kv t F u K k) = Suc (length (K k))"
  shows "v_writer (update_kv_writes t F K k ! length (K k)) = Tn t"
  using assms
  by (auto simp add: update_kv_writes_decides_length update_kv_writes_def split: option.split)

lemma update_kv_new_version_v_writer:
  assumes  "length (update_kv t F u K k) = Suc (length (K k))"
  shows "v_writer (update_kv t F u K k ! length (K k)) = Tn t"
  using assms apply (auto simp add: update_kv_def)
  by (metis update_kv_reads_length update_kv_writes_decides_length update_kv_writes_new_version_v_writer)


(* v_readerset *)
lemma v_readerset_update_kv_reads_max_u:
  assumes "x \<in> v_readerset (update_kv_reads t F u K k!i)"
      and "i \<in> in_range K k" and "i = Max (u k)" 
    shows "x \<in> v_readerset (K k!i) \<or> x = t"
  using assms
  by (cases "F (k, R)") (auto simp add: update_kv_reads_defs)

lemma v_readerset_update_kv_reads_rest_inv:
  assumes "i \<in> in_range K k" and "i \<noteq> Max (u k) "
  shows "v_readerset (update_kv_reads t F u K k!i) = v_readerset (K k!i)"
proof (cases "F (k, R)")
  case (Some a)
  then show ?thesis using assms
    by (auto simp add: update_kv_reads_def; metis assms(2) nth_list_update_neq)
qed (auto simp add: update_kv_reads_def)

lemma v_readerset_update_kv_writes:
  assumes "i \<in> in_range K k"
    shows "v_readerset (update_kv_writes t F K k ! i) = v_readerset (K k ! i)"
  using assms
  by (auto simp add: update_kv_writes_def split: option.splits)

lemma v_readerset_update_kv_max_u:
  assumes "x \<in> v_readerset (update_kv t F u K k ! Max (u k))"
      and "view_in_range K u"
    shows "x \<in> v_readerset (K k ! Max (u k)) \<or> x = t"
  using assms
  by (auto simp add: update_kv_def v_readerset_update_kv_writes
           dest: v_readerset_update_kv_reads_max_u)

lemma v_readerset_update_kv_rest_inv:
  assumes "i \<noteq> Max (u k)" and  "i \<in> in_range K k"
  shows "v_readerset (update_kv t F u K k!i) = v_readerset (K k!i)"
  using assms update_kv_writes_version_inv [of i "update_kv_reads t F u K" k t F]
  by (auto simp add: v_readerset_update_kv_reads_rest_inv update_kv_def update_kv_reads_length)


lemma update_kv_writes_new_version_v_readerset:
  assumes  "length (update_kv t F u K k) = Suc (length (K k))"
  shows "v_readerset (update_kv_writes t F K k ! length (K k)) = {}"
  using assms
  by (auto simp add: update_kv_writes_decides_length update_kv_writes_def split: option.split)

lemma update_kv_new_version_v_readerset:
  assumes  "length (update_kv t F u K k) = Suc (length (K k))"
  shows "v_readerset (update_kv t F u K k ! length (K k)) = {}"
  using assms
  apply (auto simp add: update_kv_def update_kv_writes_def update_kv_reads_length split: option.split)
  by (metis update_kv_reads_length equals0D nth_append_length version.select_convs(3))

subsection \<open>Execution Tests as Transition Systems\<close>

definition visTx :: "'v kv_store \<Rightarrow> view \<Rightarrow> txid set" where
  "visTx K u \<equiv> {v_writer (K k!i) | i k. i \<in> u k}"

definition read_only_Txs :: "'v kv_store \<Rightarrow> txid set" where
  "read_only_Txs K \<equiv> kvs_txids K - kvs_writers K"

definition closed :: "'v kv_store \<Rightarrow> view \<Rightarrow> txid rel \<Rightarrow> bool" where
  "closed K u r \<longleftrightarrow> visTx K u = (((r^*)^-1) `` (visTx K u)) - (read_only_Txs K)" 



subsection \<open>Execution Tests\<close>

datatype 'v label = ET cl_id view "'v fingerpr" 

locale ExecutionTest =
  fixes R_ET :: "'v kv_store \<Rightarrow> 'v fingerpr \<Rightarrow> txid rel"
    and vShift :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> view \<Rightarrow> bool"
   \<comment>\<open>We need some assumptions from Definition 8 of ECOOP paper\<close>
begin

definition canCommit :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v fingerpr \<Rightarrow> bool" where
  "canCommit K u F \<equiv> closed K u (R_ET K F)"

fun ET_cl_txn :: "cl_id \<Rightarrow> view \<Rightarrow> 'v fingerpr \<Rightarrow> ('v kv_store \<times> view) \<Rightarrow> ('v kv_store \<times> view) \<Rightarrow> bool" where
  "ET_cl_txn cl u'' F (K, u) (K', u') \<longleftrightarrow> (\<exists>t.
    view_wellformed K u'' \<and>
    view_wellformed K u' \<and>
    canCommit K u'' F \<and> vShift K u'' K' u' \<and> \<comment>\<open>From here is not in Execution Test of the thesis\<close>
    u \<sqsubseteq> u'' \<and>
    view_wellformed K u \<and>
    t \<in> next_txids K cl \<and>
    K' = update_kv t F u'' K)"

declare ET_cl_txn.simps [simp del]
lemmas ET_cl_txn_def = ET_cl_txn.simps

fun ET_trans_and_fp :: "'v config \<Rightarrow> 'v label \<Rightarrow> 'v config \<Rightarrow> bool" where
  "ET_trans_and_fp (K , U) (ET cl u F) (K', U') \<longleftrightarrow> ET_cl_txn cl u F (K, U cl) (K', U' cl) \<and>
    fingerprint_condition F K u"

lemmas ET_trans_induct = ET_trans_and_fp.induct [case_names ET_txn]

definition ET_ES :: "('v label, 'v config) ES" where
  "ET_ES \<equiv> \<lparr>
    init = (=) config_init,
    trans = ET_trans_and_fp
  \<rparr>"

lemmas ET_init_def = config_init_defs
lemmas ET_trans_def = ET_cl_txn_def
lemmas ET_ES_defs = ET_ES_def ET_init_def

lemma trans_ET_ES_eq [simp]: "(ET_ES: s \<midarrow>e\<rightarrow> s') \<longleftrightarrow> ET_trans_and_fp s e s'"
  by (auto simp add: ET_ES_def)


subsubsection \<open>Wellformedness Invariants\<close>

\<comment> \<open>Invariant\<close>

lemma reach_snapshot_property [simp, dest]:
  assumes "reach ET_ES s"
  shows "snapshot_property (kvs s)"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: ET_ES_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction s e s' rule: ET_trans_induct)
    case (ET_txn K U cl u F K' U')
    then show ?case
      apply (auto simp add: ET_trans_def intro!: kvs_wellformed_intros)
      subgoal for k i j t x \<comment> \<open>subgoal for the readerset case\<close>
        apply (cases "i \<in> in_range K k"; cases "j \<in> in_range K k";
               auto dest!: not_in_range_update_kv update_kv_new_version_v_readerset)
        by (cases "i = Max (u k)"; cases "j = Max (u k)";
               auto simp add: snapshot_property_def v_readerset_update_kv_rest_inv
                    dest!: v_readerset_update_kv_max_u fresh_txid_v_reader_set)
      subgoal for k i j t  \<comment> \<open>subgoal for the writer case\<close>
        using update_kv_length [of t F u K k]
        by (cases "i \<in> in_range K k"; cases "j \<in> in_range K k";
            auto simp add: snapshot_property_def less_Suc_eq_le in_range_def update_kv_v_writer_inv
                 dest!: update_kv_new_version_v_writer fresh_txid_v_writer)
      done
  qed
qed


lemma reach_wr_so [simp, dest]:
  assumes "reach ET_ES s"
  shows "wr_so (kvs s)"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case 
    by (auto simp add: ET_ES_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction s e s' rule: ET_trans_induct)
    case (ET_txn K U cl u F K' U')
    then show ?case 
      apply (auto simp add: ET_trans_def intro!: kvs_wellformed_intros)
      subgoal for k i x t apply (cases "i \<in> in_range K k")
        subgoal by (cases "i = Max (u k)")
                   (auto simp add: v_readerset_update_kv_rest_inv update_kv_v_writer_inv
                         dest!: v_readerset_update_kv_max_u fresh_txid_writer_so)
        subgoal by (auto simp add: update_kv_new_version_v_readerset dest!: not_in_range_update_kv)
        done
      subgoal for k i x t apply (cases "i \<in> in_range K k")
        subgoal apply (auto simp add: wr_so_def)
          by (metis fresh_txid_v_writer update_kv_v_writer_inv v_readerset_update_kv_max_u
              v_readerset_update_kv_rest_inv image_eqI view_wellformedD1)
        subgoal by (auto simp add: update_kv_new_version_v_readerset dest!: not_in_range_update_kv)
        done
      done
  qed
qed


lemma reach_ww_so [simp, dest]:
  assumes "reach ET_ES s"
  shows "ww_so (kvs s)"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case 
    by (auto simp add: ET_ES_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction s e s' rule: ET_trans_induct)
    case (ET_txn K U cl u F K' U')
    then show ?case 
      apply (auto simp add: ET_trans_def intro!: kvs_wellformed_intros)
      subgoal for k i x t apply (cases "x \<in> in_range K k")
        subgoal by (auto simp add: update_kv_v_writer_inv in_range_def)
        subgoal by (auto simp add: update_kv_new_version_v_writer update_kv_v_writer_inv
                            dest!: not_in_range_update_kv fresh_txid_writer_so)
        done
      subgoal for k i x t apply (cases "x \<in> in_range K k")
        subgoal by (auto simp add: ww_so_def update_kv_v_writer_inv in_range_def)
        subgoal by (auto simp add: update_kv_new_version_v_writer update_kv_v_writer_inv
                            dest!: not_in_range_update_kv fresh_txid_v_writer)
        done
      done
  qed
qed


lemma reach_kvs_initialized [simp, dest]:
  assumes "reach ET_ES s"
  shows "kvs_initialized (kvs s)"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case 
    by (auto simp add: ET_ES_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction s e s' rule: ET_trans_induct)
    case (ET_txn K U cl u F K' U')
    then show ?case 
      by (auto 4 3 simp add: ET_trans_def update_kv_v_value_inv view_zero_in_range
                   intro!: kvs_wellformed_intros)
  qed
qed

lemma reach_kvs_wellformed [simp, dest]:
  assumes "reach ET_ES s"
  shows "kvs_wellformed (kvs s)"
  using assms
  by (simp add: kvs_wellformed_def)

end

end