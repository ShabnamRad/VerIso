section \<open>Key-Value Stores\<close>

theory Key_Value_Stores
  imports Event_Systems "HOL-Library.Sublist"
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

type_synonym 'v v_list = "'v version list"
type_synonym 'v kv_store = "key \<Rightarrow> 'v v_list"

definition v_list_init :: "'v v_list" where
  "v_list_init \<equiv> [version_init]"

definition kvs_init :: "'v kv_store" where
  "kvs_init k \<equiv> v_list_init"

lemmas kvs_init_defs = kvs_init_def v_list_init_def version_init_def


\<comment> \<open>index range for a kvs and key\<close>

definition full_view :: "'v v_list \<Rightarrow> nat set" where  
  "full_view vl \<equiv> {..<length vl}"

thm nth_list_update_eq nth_list_update_neq

lemma full_view_finite [simp, intro!]: "finite (full_view vl)"
  by (simp add: full_view_def)

lemma full_view_nth_list_update_eq [simp]:     (* special case of nth_list_update_eq *)
  "i \<in> full_view vl \<Longrightarrow> vl[i := x] ! i = x"
  by (simp add: full_view_def)

lemma full_view_append [simp]:
  "i \<in> full_view vl \<Longrightarrow> (vl @ vs) ! i = vl ! i"
  by (auto simp add: full_view_def nth_append)

lemma full_view_kvs_init [simp]:
  "i \<in> full_view (kvs_init k) \<longleftrightarrow> i = 0"
  by (simp add: kvs_init_defs full_view_def)

(*
  TODO: there are too many uses of full_view_def below; 
  try to find the relevant properties and reduce the use of full_view_def below
*)


subsubsection  \<open>Wellformedness of KV stores\<close>

definition snapshot_property :: "'v kv_store \<Rightarrow> bool" where
  "snapshot_property K \<longleftrightarrow> (\<forall>k. \<forall>i \<in> full_view (K k). \<forall>j \<in> full_view (K k).
                                 (v_readerset (K k!i) \<inter> v_readerset (K k!j) \<noteq> {} \<or>
                                  v_writer (K k!i) = v_writer (K k!j)) \<longrightarrow> i = j)"

lemmas snapshot_propertyI = snapshot_property_def [THEN iffD2, rule_format]
lemmas snapshot_propertyE [elim] = snapshot_property_def [THEN iffD1, elim_format, rule_format]

lemma snapshot_property_kvs_init [simp, intro]: "snapshot_property kvs_init"
  by (intro snapshot_propertyI) (auto)

definition wr_so :: "'v kv_store \<Rightarrow> bool" where
  "wr_so K \<longleftrightarrow> (\<forall>k t t'. \<forall>i \<in> full_view (K k).
                  t = v_writer (K k!i) \<and> t' \<in> Tn ` v_readerset (K k!i) \<longrightarrow> (t', t) \<notin> SO^=)"

lemmas wr_soI = wr_so_def [THEN iffD2, rule_format]
lemmas wr_soE [elim] = wr_so_def [THEN iffD1, elim_format, rule_format]

lemma wr_so_kvs_init [simp, intro]: "wr_so kvs_init"
  by (intro wr_soI) (auto simp add: kvs_init_defs full_view_def)


definition ww_so :: "'v kv_store \<Rightarrow> bool" where
  "ww_so K \<longleftrightarrow> (\<forall>k t t'. \<forall>i \<in> full_view (K k). \<forall>j \<in> full_view (K k).
                  t = v_writer (K k!i) \<and> t' = v_writer (K k!j) \<and> i < j \<longrightarrow> (t', t) \<notin> SO^=)"

lemmas ww_soI = ww_so_def [THEN iffD2, rule_format]
lemmas ww_soE [elim] = ww_so_def [THEN iffD1, elim_format, rule_format]

lemma ww_so_kvs_init [simp, intro]: "ww_so kvs_init"
  by (intro ww_soI) (auto simp add: kvs_init_defs full_view_def)


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
  "next_txids K cl \<equiv> {Tn_cl n cl | n. \<forall>m \<in> get_sqns K cl. m < n}"

lemmas fresh_txid_defs = next_txids_def get_sqns_def kvs_txids_def kvs_readers_def kvs_writers_def

\<comment> \<open>functions on version\<close>

definition version_order :: "'v version \<Rightarrow> 'v version \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r" 60) where
  "v1 \<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r v2 \<equiv>
    v_value v2 = v_value v1 \<and>
    v_writer v2 = v_writer v1 \<and>
    v_readerset v1 \<subseteq> v_readerset v2"

\<comment> \<open>functions on version list\<close>

definition vlist_order :: "'v v_list \<Rightarrow> 'v v_list \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>v\<^sub>l" 60) where
  "vl1 \<sqsubseteq>\<^sub>v\<^sub>l vl2 \<equiv> prefix vl1 vl2"

\<comment> \<open>txid freshness lemmas\<close>

lemma fresh_txid_v_writer:
  assumes "t \<in> next_txids K cl"
  shows "\<forall>i \<in> full_view (K k). v_writer (K k!i) \<noteq> Tn t"
  using assms nth_mem
  apply (auto simp add: fresh_txid_defs image_iff full_view_def)
  by fastforce

lemma fresh_txid_v_reader_set:
  assumes "t \<in> next_txids K cl"
  shows "\<forall>i \<in> full_view (K k). t \<notin> v_readerset (K k!i)"
  using assms nth_mem
  apply (auto simp add: fresh_txid_defs image_iff full_view_def)
  by blast

lemma fresh_txid_writer_so:
  assumes "t \<in> next_txids K cl"
  shows "\<forall>i \<in> full_view (K k). (Tn t, v_writer (K k ! i)) \<notin> SO"
  using assms nth_mem
  apply (auto simp add: fresh_txid_defs SO_def SO0_def image_iff full_view_def)
  by fastforce


subsection \<open>Views\<close>

type_synonym v_id = nat

type_synonym key_view = "v_id set"
type_synonym view = "key \<Rightarrow> key_view"

definition view_init :: view where
  "view_init \<equiv> (\<lambda>k. {0})"

definition view_order :: "view \<Rightarrow> view \<Rightarrow> bool" (infix "\<sqsubseteq>" 60) where
  "u1 \<sqsubseteq> u2 \<equiv> \<forall>k. u1 k \<subseteq> u2 k"

definition key_view_in_range :: "'v v_list \<Rightarrow> key_view \<Rightarrow> bool" where
  "key_view_in_range vl uk \<equiv> 0 \<in> uk \<and> uk \<subseteq> full_view vl"

definition view_in_range :: "'v kv_store \<Rightarrow> view \<Rightarrow> bool" where
  "view_in_range K u \<equiv> \<forall>k. key_view_in_range (K k) (u k)"

lemmas view_in_range_defs = view_in_range_def key_view_in_range_def

definition view_atomic :: "'v kv_store \<Rightarrow> view \<Rightarrow> bool" where
  "view_atomic K u \<equiv> \<forall>k k'.  \<forall>i \<in> u k. \<forall>i' \<in> full_view (K k').
    v_writer (K k!i) = v_writer (K k'!i') \<longrightarrow> i' \<in> u k'"

definition view_wellformed :: "'v kv_store \<Rightarrow> view \<Rightarrow> bool" where
  "view_wellformed K u \<longleftrightarrow> view_in_range K u \<and> view_atomic K u"

lemmas view_wellformedD1 [dest] = view_wellformed_def [THEN iffD1, THEN conjunct1]
lemmas view_wellformedD2 [dest] = view_wellformed_def [THEN iffD1, THEN conjunct2]

lemmas view_wellformed_defs = 
  view_wellformed_def view_in_range_defs view_atomic_def 

\<comment> \<open>key_view lemmas\<close>

lemma key_view_non_empty [simp]:
  assumes "key_view_in_range vl uk"
  shows "uk \<noteq> {}"
  using assms 
  by (auto simp add: key_view_in_range_def)

lemma key_view_finite [simp]:
  assumes "key_view_in_range vl uk"
  shows "finite uk"
  using assms 
  by (auto simp add: key_view_in_range_def intro: rev_finite_subset)

lemma key_view_Max_full_view [simp]:
  assumes "key_view_in_range vl uk"
  shows "Max uk \<in> full_view vl"
proof -
  have "Max uk \<in> uk" using assms by auto
  then show ?thesis using assms by (auto simp add: key_view_in_range_def)
qed

lemma key_view_zero_full_view:
  assumes "key_view_in_range vl uk"
  shows "0 \<in> full_view vl" 
  using assms
  by (auto simp add: key_view_in_range_def)

\<comment> \<open>view lemmas\<close>

lemma view_non_empty [simp]:
  assumes "view_in_range K u"
  shows "u k \<noteq> {}"
  using assms 
  by (auto simp add: view_in_range_defs)

lemma view_finite [simp]:
  assumes "view_in_range K u"
  shows "finite (u k)"
  using assms 
  by (auto simp add: view_in_range_defs intro: rev_finite_subset)

lemma view_Max_full_view [simp]:
  assumes "view_in_range K u"
  shows "Max (u k) \<in> full_view (K k)"
proof -
  have "Max (u k) \<in> u k" using assms by auto
  then show ?thesis using assms by (auto simp add: view_in_range_defs)
qed

lemma view_zero_full_view:
  assumes "view_in_range K u"
  shows "0 \<in> full_view (K k)" 
  using assms
  by (auto simp add: view_in_range_defs)

lemma max_in_range_non_empty:
  assumes "vl \<noteq> []"
  shows "Max (full_view vl) < length vl"
  by (metis assms(1) full_view_def key_view_Max_full_view
      key_view_in_range_def length_greater_0_conv lessThan_iff order_refl)


subsection \<open>Snapshots and Configs\<close>

type_synonym 'v snapshot = "key \<Rightarrow> 'v"

definition last_version :: "'v v_list \<Rightarrow> key_view \<Rightarrow> 'v version" where
  "last_version vl uk \<equiv> vl!(Max uk)"

definition view_snapshot :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v snapshot" where
  "view_snapshot K u k \<equiv> v_value (last_version (K k) (u k))"

type_synonym 'v config = "'v kv_store \<times> (cl_id \<Rightarrow> view)"

abbreviation kvs where "kvs \<equiv> fst"
abbreviation views where "views \<equiv> snd"

abbreviation c_views_init :: "cl_id \<Rightarrow> view" where
  "c_views_init \<equiv> (\<lambda>cl. view_init)"

definition config_init :: "'v config" where
  "config_init \<equiv> (kvs_init, c_views_init)"

lemmas config_init_defs = config_init_def (* kvs_init_defs *) view_init_def


subsection \<open>Fingerprints\<close>

datatype op_type = R | W
datatype 'v op = Read key 'v | Write key 'v | Eps

type_synonym 'v key_fp = "op_type \<rightharpoonup> 'v"
type_synonym 'v fingerpr = "key \<Rightarrow> 'v key_fp"

definition empty_fp :: "'v fingerpr" where
  "empty_fp \<equiv> (\<lambda>k. Map.empty)"

fun update_key_fp :: "'v key_fp \<Rightarrow> op_type \<Rightarrow> 'v \<Rightarrow> 'v key_fp" where
  "update_key_fp Fk R v = (if Fk R = None \<and> Fk W = None then Fk (R \<mapsto> v) else Fk)" |
  "update_key_fp Fk W v = Fk(W \<mapsto> v)"

fun update_fp :: "'v fingerpr \<Rightarrow> 'v op \<Rightarrow> 'v fingerpr" where
  "update_fp F (Read k v)  = F (k := update_key_fp (F k) R v)" |
  "update_fp F (Write k v) = F (k := update_key_fp (F k) W v)" |
  "update_fp F Eps         = F"

 \<comment>\<open>The Fingerprint condition was originally in Execution Test\<close>
definition fp_property :: "'v fingerpr \<Rightarrow> 'v kv_store \<Rightarrow> view \<Rightarrow> bool" where
  "fp_property F K u \<equiv>
    (\<forall>k. R \<in> dom (F k) \<longrightarrow> F k R = Some (view_snapshot K u k))"

definition update_kv_reads :: "txid0 \<Rightarrow> 'v key_fp \<Rightarrow> key_view \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_reads t Fk uk vl =
    (case Fk R of
      None   \<Rightarrow> vl |
      Some v \<Rightarrow> let lv = last_version vl uk in
                vl[Max uk := lv\<lparr>v_readerset := insert t (v_readerset lv)\<rparr>])"

definition update_kv_writes :: "txid0 \<Rightarrow> 'v key_fp \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_writes t Fk vl =
    (case Fk W of
      None   \<Rightarrow> vl |
      Some v \<Rightarrow> vl @ [\<lparr>v_value=v, v_writer=Tn t, v_readerset={}\<rparr>])"

definition update_kv_key :: "txid0 \<Rightarrow> 'v key_fp \<Rightarrow> key_view \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_key t Fk uk = (update_kv_writes t Fk) o (update_kv_reads t Fk uk)"

definition update_kv :: "txid0 \<Rightarrow> 'v fingerpr \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> 'v kv_store" where
  "update_kv t F u K k = update_kv_key t (F k) (u k) (K k)"

lemmas update_kv_reads_defs = update_kv_reads_def Let_def last_version_def

lemmas update_kv_defs = update_kv_def update_kv_key_def

\<comment> \<open>update_kv_key lemmas about fingerprint and full_view\<close>

lemma update_kv_key_empty_fp [simp]:
  assumes "Fk R = None" and "Fk W = None"
  shows "update_kv_key t Fk uk vl = vl"
  using assms
  by (auto simp add: update_kv_key_def update_kv_reads_def update_kv_writes_def)

lemma update_kv_key_ro_full_view [simp]:
  assumes "Fk W = None"
  shows "full_view (update_kv_key t Fk uk vl) = full_view vl"
  using assms
  by (auto simp add: update_kv_key_def update_kv_writes_def update_kv_reads_defs
      full_view_def split: option.split)

lemma update_kv_key_rw_full_view [simp]:
  assumes "Fk W \<noteq> None"
  shows "full_view (update_kv_key t Fk uk vl) = full_view vl \<union> {length vl}"
  using assms
  by (auto simp add: update_kv_key_def update_kv_writes_def update_kv_reads_defs
      full_view_def split: option.split)

lemma update_kv_key_ro_set_v_readerset:
  assumes "Fk W = None"
    and "vl \<noteq> []"
  shows "(update_kv_key t Fk (full_view vl) vl) [Max (full_view vl) :=
    last_version (update_kv_key t Fk (full_view vl) vl) (full_view vl) \<lparr> v_readerset := x \<rparr>] =
    vl [Max (full_view vl) := last_version vl (full_view vl) \<lparr> v_readerset := x \<rparr>]"
  using assms
  by (auto simp add: update_kv_key_def update_kv_writes_def update_kv_reads_defs
      split: option.split dest: max_in_range_non_empty)

lemma update_kv_key_ro_v_readerset[simp]:
  assumes "Fk W = None" and "Fk R \<noteq> None"
    and "vl \<noteq> []"
  shows "v_readerset (last_version (update_kv_key t Fk (full_view vl) vl) (full_view vl)) =
   insert t (v_readerset (last_version vl (full_view vl)))"
  using assms
  by (auto simp add: update_kv_key_def update_kv_writes_def update_kv_reads_defs
      dest: max_in_range_non_empty)

\<comment> \<open>update_kv lemmas about version list length and full_view\<close>

lemma update_kv_reads_length:
  "length (update_kv_reads t Fk uk vl) = length vl"
proof (cases "Fk R")
  case (Some a)
  then show ?thesis apply (auto simp add: update_kv_reads_def)
    by (meson length_list_update)
qed (auto simp add: update_kv_reads_def)

lemma update_kv_writes_none_length:
  assumes "Fk W = None"
  shows "length (update_kv_writes t Fk vl) = length vl"
  using assms by (auto simp add: update_kv_writes_def)

lemma update_kv_writes_some_length:
  assumes "Fk W = Some v"
  shows "length (update_kv_writes t Fk vl) = Suc (length vl)"
  using assms by (auto simp add: update_kv_writes_def)

lemma update_kv_writes_length:
  shows "length (update_kv_writes t Fk vl) = Suc (length vl) \<or> 
         length (update_kv_writes t Fk vl) = length vl"
  by (cases "Fk W") (auto simp add: update_kv_writes_def)

lemma update_kv_writes_length_increasing:
  "length vl \<le> length (update_kv_writes t Fk vl)"
  using update_kv_writes_length [of t Fk vl]
  by auto

lemma update_kv_length:
  shows "length (update_kv t F u K k) = Suc (length (K k)) \<or>
         length (update_kv t F u K k) = length (K k)"
  using update_kv_writes_length [of t "F k" "update_kv_reads t (F k) (u k) (K k)"]
  by (simp add: update_kv_defs update_kv_reads_length [of t "F k" "u k" "K k"])
 
lemma update_kv_length_increasing:      
  "length (K k) \<le> length (update_kv t F u K k)"
  using update_kv_length [of t F u K k]
  by auto

lemma full_view_update_kv_reads [simp]:
  "full_view (update_kv_reads t Fk uk vl) = full_view vl"
  by (simp add: update_kv_reads_length full_view_def)

lemma full_view_update_kv_writes [dest]:
  "i \<in> full_view vl \<Longrightarrow> i \<in> full_view (update_kv_writes t Fk vl)"
  using update_kv_writes_length_increasing [of vl t Fk] 
  by (simp add: full_view_def)

lemma full_view_update_kv [dest]:
  "i \<in> full_view (K k) \<Longrightarrow> i \<in> full_view (update_kv t F u K k)"
  using update_kv_length_increasing [of K k t F u] 
  by (simp add: full_view_def)

lemma not_full_view_update_kv:
  assumes "i \<in> full_view (update_kv t F u K k)" and "i \<notin> full_view (K k)"
  shows "i = length (K k) \<and> length (update_kv t F u K k) = Suc (length (K k))"
  using assms update_kv_length [of t F u K k]
  by (auto simp add: less_Suc_eq_le full_view_def)

lemma update_kv_writes_key_decides_length:
  shows "length (update_kv_key t Fk uk vl) = length (update_kv_writes t Fk vl)"
  by (cases "Fk W") (auto simp add: update_kv_key_def update_kv_writes_def update_kv_reads_length)

lemma update_kv_writes_decides_length:
  shows "length (update_kv t F u K k) = length (update_kv_writes t (F k) (K k))"
  by (simp add: update_kv_def update_kv_writes_key_decides_length)

\<comment> \<open>update_kv lemmas about changing the versions\<close>

lemma update_kv_writes_version_inv:
  assumes "i \<in> full_view vl"
  shows "update_kv_writes t Fk vl!i = vl!i"
proof (cases "Fk W")
  case (Some a)
  then show ?thesis using assms
    by (auto simp add: update_kv_writes_def)
qed (auto simp add: update_kv_writes_def)

(* v_value *)
lemma update_kv_reads_v_value_inv:
  assumes "i \<in> full_view vl"
  shows "v_value (update_kv_reads t Fk uk vl!i) = v_value (vl!i)"
proof (cases "Fk R")
  case (Some a)
  then show ?thesis using assms
    by (cases "i = Max uk") 
       (auto simp add: update_kv_reads_defs)
qed (auto simp add: update_kv_reads_def)

lemma update_kv_v_value_inv:
  assumes "i \<in> full_view (K k)"
  shows "v_value (update_kv t F u K k!i) = v_value (K k!i)"
  using assms
  by (auto simp add: update_kv_defs update_kv_writes_version_inv update_kv_reads_v_value_inv)

(* v_writer *)
lemma update_kv_reads_v_writer_inv:
  assumes "i \<in> full_view vl"
  shows "v_writer (update_kv_reads t Fk uk vl!i) = v_writer (vl!i)"
proof (cases "Fk R")
  case (Some a)
  then show ?thesis using assms
    by (cases "i = Max uk")
       (auto simp add: update_kv_reads_defs split: option.splits)
qed (simp add: update_kv_reads_def)

lemma update_kv_v_writer_inv:
  assumes "i \<in> full_view (K k)"
  shows "v_writer (update_kv t F u K k!i) = v_writer (K k!i)"
  using assms
  by (auto simp add: update_kv_defs update_kv_writes_version_inv update_kv_reads_v_writer_inv)

lemma update_kv_writes_key_new_version_v_writer:
  assumes  "length (update_kv_key t Fk uk vl) = Suc (length vl)"
  shows "v_writer (update_kv_writes t Fk vl ! length vl) = Tn t"
  using assms
  by (auto simp add: update_kv_writes_key_decides_length update_kv_writes_def split: option.split)

lemma update_kv_writes_new_version_v_writer:
  assumes  "length (update_kv t F u K k) = Suc (length (K k))"
  shows "v_writer (update_kv_writes t (F k) (K k) ! length (K k)) = Tn t"
  using assms
  by (simp add: update_kv_def update_kv_writes_key_new_version_v_writer)

lemma update_kv_key_new_version_v_writer:
  assumes  "length (update_kv_key t Fk uk vl) = Suc (length vl)"
  shows "v_writer (update_kv_key t Fk uk vl ! length vl) = Tn t"
  using assms apply (auto simp add: update_kv_key_def)
  by (metis update_kv_reads_length update_kv_writes_key_decides_length
            update_kv_writes_key_new_version_v_writer)

lemma update_kv_new_version_v_writer:
  assumes  "length (update_kv t F u K k) = Suc (length (K k))"
  shows "v_writer (update_kv t F u K k ! length (K k)) = Tn t"
  using assms
  apply (auto simp add: update_kv_defs)
  by (metis comp_apply update_kv_key_def update_kv_key_new_version_v_writer)
            


(* v_readerset *)
lemma v_readerset_update_kv_reads_max_u:
  assumes "x \<in> v_readerset (update_kv_reads t Fk uk vl!i)"
      and "i \<in> full_view vl" and "i = Max uk" 
    shows "x \<in> v_readerset (vl!i) \<or> x = t"
  using assms
  by (cases "Fk R") (auto simp add: update_kv_reads_defs)

lemma v_readerset_update_kv_reads_rest_inv:
  assumes "i \<in> full_view vl" and "i \<noteq> Max uk"
  shows "v_readerset (update_kv_reads t Fk uk vl!i) = v_readerset (vl!i)"
proof (cases "Fk R")
  case (Some a)
  then show ?thesis using assms
    by (auto simp add: update_kv_reads_def; metis assms(2) nth_list_update_neq)
qed (auto simp add: update_kv_reads_def)

lemma v_readerset_update_kv_writes:
  assumes "i \<in> full_view vl"
    shows "v_readerset (update_kv_writes t Fk vl ! i) = v_readerset (vl ! i)"
  using assms
  by (auto simp add: update_kv_writes_def split: option.splits)

lemma v_readerset_update_kv_max_u:
  assumes "x \<in> v_readerset (update_kv t F u K k ! Max (u k))"
      and "view_in_range K u"
    shows "x \<in> v_readerset (K k ! Max (u k)) \<or> x = t"
  using assms
  by (auto simp add: update_kv_defs v_readerset_update_kv_writes
           dest: v_readerset_update_kv_reads_max_u)

lemma v_readerset_update_kv_rest_inv:
  assumes "i \<noteq> Max (u k)" and  "i \<in> full_view (K k)"
  shows "v_readerset (update_kv t F u K k!i) = v_readerset (K k!i)"
  using assms update_kv_writes_version_inv [of i "update_kv_reads t (F k) (u k) (K k)"]
  by (auto simp add: v_readerset_update_kv_reads_rest_inv update_kv_defs update_kv_reads_length)


lemma update_kv_writes_new_version_v_readerset:
  assumes  "length (update_kv t F u K k) = Suc (length (K k))"
  shows "v_readerset (update_kv_writes t (F k) (K k) ! length (K k)) = {}"
  using assms
  by (auto simp add: update_kv_writes_decides_length update_kv_writes_def split: option.split)

lemma update_kv_new_version_v_readerset:
  assumes  "length (update_kv t F u K k) = Suc (length (K k))"
  shows "v_readerset (update_kv t F u K k ! length (K k)) = {}"
  using assms
  apply (auto simp add: update_kv_defs update_kv_writes_def update_kv_reads_length split: option.split)
  by (metis update_kv_reads_length equals0D nth_append_length version.select_convs(3))

subsection \<open>Execution Tests as Transition Systems\<close>

definition visTx :: "'v kv_store \<Rightarrow> view \<Rightarrow> txid set" where
  "visTx K u \<equiv> {v_writer (K k!i) | i k. i \<in> u k}"

definition read_only_Txs :: "'v kv_store \<Rightarrow> txid set" where
  "read_only_Txs K \<equiv> kvs_txids K - kvs_writers K"

definition closed :: "'v kv_store \<Rightarrow> view \<Rightarrow> txid rel \<Rightarrow> bool" where
  "closed K u r \<longleftrightarrow> visTx K u = (((r^*)^-1) `` (visTx K u)) - (read_only_Txs K)" 



subsection \<open>Execution Tests\<close>

datatype 'v label = ET cl_id sqn view "'v fingerpr" | ETSkip

locale ExecutionTest =
  fixes R_ET :: "'v kv_store \<Rightarrow> 'v fingerpr \<Rightarrow> txid rel"
    and vShift :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> view \<Rightarrow> bool"
   \<comment>\<open>We need some assumptions from Definition 8 of ECOOP paper\<close>
begin

definition canCommit :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v fingerpr \<Rightarrow> bool" where
  "canCommit K u F \<equiv> closed K u (R_ET K F)"

fun ET_cl_txn :: "cl_id \<Rightarrow> sqn \<Rightarrow> view \<Rightarrow> 'v fingerpr \<Rightarrow> ('v kv_store \<times> view) \<Rightarrow> ('v kv_store \<times> view) \<Rightarrow> bool" where
  "ET_cl_txn cl sn u'' F (K, u) (K', u') \<longleftrightarrow> (\<exists>t.
    view_wellformed K u'' \<and>
    view_wellformed K' u' \<and>
    canCommit K u'' F \<and> vShift K u'' K' u' \<and> \<comment>\<open>From here is not in Execution Test of the thesis\<close>
    u \<sqsubseteq> u'' \<and>
    view_wellformed K u \<and>
    t = Tn_cl sn cl \<and>
    t \<in> next_txids K cl \<and>
    K' = update_kv t F u'' K)"

declare ET_cl_txn.simps [simp del]
lemmas ET_cl_txn_def = ET_cl_txn.simps

fun ET_trans_and_fp :: "'v config \<Rightarrow> 'v label \<Rightarrow> 'v config \<Rightarrow> bool" where
  "ET_trans_and_fp (K , U) (ET cl sn u'' F) (K', U') \<longleftrightarrow>
    (\<exists>u'. ET_cl_txn cl sn u'' F (K, U cl) (K', u') \<and> U' = U (cl := u')) \<and> fp_property F K u''" |
  "ET_trans_and_fp c ETSkip c' \<longleftrightarrow> c' = c"

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
    case (ET_txn K U cl sn u'' F K' U')
    then show ?case
      apply (auto simp add: ET_trans_def intro!: kvs_wellformed_intros)
      subgoal for k i j u' x \<comment> \<open>subgoal for the readerset case\<close>
        apply (cases "i \<in> full_view (K k)"; cases "j \<in> full_view (K k)";
               auto dest!: not_full_view_update_kv update_kv_new_version_v_readerset)
        by (cases "i = Max (u'' k)"; cases "j = Max (u'' k)";
               auto simp add: snapshot_property_def v_readerset_update_kv_rest_inv
                    dest!: v_readerset_update_kv_max_u fresh_txid_v_reader_set)
      subgoal for k i j u'  \<comment> \<open>subgoal for the writer case\<close>
        using update_kv_length [of "Tn_cl sn cl" F u'' K k]
        by (cases "i \<in> full_view (K k)"; cases "j \<in> full_view (K k)";
            auto simp add: snapshot_property_def less_Suc_eq_le full_view_def update_kv_v_writer_inv
                 dest!: update_kv_new_version_v_writer fresh_txid_v_writer)
      done
  qed simp
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
    case (ET_txn K U cl sn u'' F K' U')
    then show ?case 
      apply (auto simp add: ET_trans_def intro!: kvs_wellformed_intros)
      subgoal for k i x t apply (cases "i \<in> full_view (K k)")
        subgoal by (cases "i = Max (u'' k)")
                   (auto simp add: v_readerset_update_kv_rest_inv update_kv_v_writer_inv
                         dest!: v_readerset_update_kv_max_u fresh_txid_writer_so)
        subgoal by (auto simp add: update_kv_new_version_v_readerset dest!: not_full_view_update_kv)
        done
      subgoal for k i x t apply (cases "i \<in> full_view (K k)")
        subgoal apply (auto simp add: wr_so_def)
          by (metis fresh_txid_v_writer update_kv_v_writer_inv v_readerset_update_kv_max_u
              v_readerset_update_kv_rest_inv image_eqI view_wellformedD1)
        subgoal by (auto simp add: update_kv_new_version_v_readerset dest!: not_full_view_update_kv)
        done
      done
  qed simp
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
    case (ET_txn K U cl sn u'' F K' U')
    then show ?case 
      apply (auto simp add: ET_trans_def intro!: kvs_wellformed_intros)
      subgoal for k i x t apply (cases "x \<in> full_view (K k)")
        subgoal by (auto simp add: update_kv_v_writer_inv full_view_def)
        subgoal by (auto simp add: update_kv_new_version_v_writer update_kv_v_writer_inv
                            dest!: not_full_view_update_kv fresh_txid_writer_so)
        done
      subgoal for k i x t apply (cases "x \<in> full_view (K k)")
        subgoal by (auto simp add: ww_so_def update_kv_v_writer_inv full_view_def)
        subgoal by (auto simp add: update_kv_new_version_v_writer update_kv_v_writer_inv
                            dest!: not_full_view_update_kv fresh_txid_v_writer)
        done
      done
  qed simp
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
    case (ET_txn K U cl sn u'' F K' U')
    then show ?case 
      by (auto 4 3 simp add: ET_trans_def update_kv_v_value_inv view_zero_full_view
                   intro!: kvs_wellformed_intros)
  qed simp
qed

lemma reach_kvs_wellformed [simp, dest]:
  assumes "reach ET_ES s"
  shows "kvs_wellformed (kvs s)"
  using assms
  by (simp add: kvs_wellformed_def)

end

end