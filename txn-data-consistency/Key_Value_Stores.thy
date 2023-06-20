section \<open>Key-Value Stores\<close>

theory Key_Value_Stores
  imports Event_Systems "HOL-Library.Sublist" Closedness
begin

subsection \<open>Transaction IDs and session order\<close>

typedecl cl_id

type_synonym sqn = nat

datatype txid0 = Tn_cl (get_sn: sqn) (get_cl: cl_id)
datatype txid = T0 | Tn txid0

definition SO0 :: "txid0 rel" where
  "SO0 \<equiv> {(t, t'). \<exists>cl n m. t = Tn_cl n cl \<and> t' = Tn_cl m cl \<and> n < m}"

definition SO :: "txid rel" where
  "SO \<equiv> {(Tn t, Tn t')| t t'. (t, t') \<in> SO0}"

lemma SO_irreflexive: "(t, t) \<notin> SO"
  by (simp add: SO_def SO0_def)


subsection \<open>Key-value stores\<close>

type_synonym key = nat

record 'v version =
  v_value :: 'v
  v_writer :: txid
  v_readerset :: "txid0 set"

abbreviation new_vers :: "txid \<Rightarrow> 'a \<Rightarrow> 'a version" where
  "new_vers t v \<equiv> \<lparr>v_value = v, v_writer = t, v_readerset = {}\<rparr>"

definition version_init :: "'v version" where
  "version_init \<equiv> new_vers T0 undefined"

type_synonym 'v v_list = "'v version list"
type_synonym ('v, 'm) vs_list = "('v, 'm) version_scheme list"
type_synonym 'v kv_store = "key \<Rightarrow> 'v v_list"
type_synonym ('v, 'm) kvs_store = "key \<Rightarrow> ('v, 'm) vs_list"

definition v_list_init :: "'v v_list" where
  "v_list_init \<equiv> [version_init]"

definition kvs_init :: "'v kv_store" where
  "kvs_init \<equiv> (\<lambda>k. v_list_init)"

lemmas kvs_init_defs = kvs_init_def v_list_init_def version_init_def


subsubsection \<open>Full view on a version list\<close>

\<comment> \<open>index range for a kvs and key\<close>

definition full_view :: "('v, 'm) vs_list \<Rightarrow> nat set" where  
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

lemma full_view_update [simp]:
  "full_view (vl [i := x]) = full_view vl"
  by (simp add: full_view_def)

lemma full_view_update_append [simp]:
  "full_view (vl[i := x] @ vs) = full_view (vl @ vs)"
  by (simp add: full_view_def)

lemma full_view_grows: 
  "i \<in> full_view vl \<Longrightarrow> i \<in> full_view (vl @ vs)"
  by (simp add: full_view_def)

lemma zero_in_full_view:
  " vl\<noteq> [] \<Longrightarrow> 0 \<in> full_view vl"
  by (simp add: full_view_def)

lemma full_view_kvs_init [simp]:
  "i \<in> full_view (kvs_init k) \<longleftrightarrow> i = 0"
  by (simp add: kvs_init_defs full_view_def)
  
lemma length_vl_in_appended:
  "length vl \<in> full_view (vl @ [v])"
  by (simp add: full_view_def)

lemma full_view_x_in_append [simp]:
  assumes "i \<in> full_view (vl @ [v])"
    and "i \<notin> full_view vl"
  shows "i = length vl"
  using assms by (simp add: full_view_def)

lemma full_view_same_length:
  assumes "length vl = length vl'"
    and "i \<in> full_view vl"
  shows "i \<in> full_view vl'"
  using assms by (simp add: full_view_def)

lemma full_view_length_increasing:
  assumes "length vl \<le> length vl'"
    and "i \<in> full_view vl"
  shows "i \<in> full_view vl'"
  using assms by (simp add: full_view_def)

(*
  TODO: there are too many uses of full_view_def below; 
  try to find the relevant properties and reduce the use of full_view_def below
*)

subsubsection  \<open>Wellformedness of KV stores\<close>

definition snapshot_property :: "('v, 'm) kvs_store \<Rightarrow> bool" where
  "snapshot_property K \<longleftrightarrow> (\<forall>k. \<forall>i \<in> full_view (K k). \<forall>j \<in> full_view (K k).
                                 (v_readerset (K k!i) \<inter> v_readerset (K k!j) \<noteq> {} \<or>
                                  v_writer (K k!i) = v_writer (K k!j)) \<longrightarrow> i = j)"

lemmas snapshot_propertyI = snapshot_property_def [THEN iffD2, rule_format]
lemmas snapshot_propertyE [elim] = snapshot_property_def [THEN iffD1, elim_format, rule_format]

lemma snapshot_property_kvs_init [simp, intro]: "snapshot_property kvs_init"
  by (intro snapshot_propertyI) (auto)

definition wr_so :: "('v, 'm) kvs_store \<Rightarrow> bool" where
  "wr_so K \<longleftrightarrow> (\<forall>k t t'. \<forall>i \<in> full_view (K k).
                  t = v_writer (K k!i) \<and> t' \<in> Tn ` v_readerset (K k!i) \<longrightarrow> (t', t) \<notin> SO^=)"

lemmas wr_soI = wr_so_def [THEN iffD2, rule_format]
lemmas wr_soE [elim] = wr_so_def [THEN iffD1, elim_format, rule_format]

lemma wr_so_kvs_init [simp, intro]: "wr_so kvs_init"
  by (intro wr_soI) (auto simp add: kvs_init_defs full_view_def)


definition ww_so :: "('v, 'm) kvs_store \<Rightarrow> bool" where
  "ww_so K \<longleftrightarrow> (\<forall>k t t'. \<forall>i \<in> full_view (K k). \<forall>j \<in> full_view (K k).
                  t = v_writer (K k!i) \<and> t' = v_writer (K k!j) \<and> i < j \<longrightarrow> (t', t) \<notin> SO^=)"

lemmas ww_soI = ww_so_def [THEN iffD2, rule_format]
lemmas ww_soE [elim] = ww_so_def [THEN iffD1, elim_format, rule_format]

lemma ww_so_kvs_init [simp, intro]: "ww_so kvs_init"
  by (intro ww_soI) (auto simp add: kvs_init_defs full_view_def)


definition kvs_initialized :: "('v, 'm) kvs_store \<Rightarrow> bool" where
  "kvs_initialized K \<longleftrightarrow> (\<forall>k. K k \<noteq> [] \<and> v_value (K k!0) = undefined)"

lemmas kvs_initializedI = kvs_initialized_def [THEN iffD2, rule_format]
lemmas kvs_initializedE [elim] = kvs_initialized_def [THEN iffD1, elim_format, rule_format]

lemma kvs_initialized_kvs_init [simp, intro]: "kvs_initialized kvs_init"
  by (intro kvs_initializedI) (auto simp add: kvs_init_defs)

definition kvs_wellformed :: "('v, 'm) kvs_store \<Rightarrow> bool"  where
  "kvs_wellformed K \<equiv> snapshot_property K \<and> wr_so K \<and> ww_so K \<and> kvs_initialized K"

lemmas kvs_wellformed_intros = snapshot_propertyI wr_soI ww_soI kvs_initializedI

(*
lemmas kvs_wellformed_defs = 
  kvs_wellformed_def snapshot_property_def ww_so_def wr_so_def (* SO_def SO0_def *) 
  kvs_initialized_def
*)


subsubsection \<open>Transaction sets: readers, writers, fresh txids\<close>

\<comment> \<open>Readers, writers, and all txids in a KVS\<close>

definition vl_writers :: "('v, 'm) vs_list \<Rightarrow> txid set" where
  "vl_writers vl \<equiv> v_writer ` (set vl)"

definition vl_readers :: "('v, 'm) vs_list \<Rightarrow> txid0 set" where
  "vl_readers vl \<equiv> \<Union>(v_readerset ` (set vl))"

definition kvs_writers :: "('v, 'm) kvs_store \<Rightarrow> txid set" where
  "kvs_writers K \<equiv> (\<Union>k. vl_writers (K k))"

definition kvs_readers :: "('v, 'm) kvs_store \<Rightarrow> txid0 set" where
  "kvs_readers K \<equiv> (\<Union>k. vl_readers (K k))"

definition kvs_txids :: "('v, 'm) kvs_store \<Rightarrow> txid set" where
  "kvs_txids K \<equiv> kvs_writers K  \<union> Tn ` kvs_readers K"

lemma vl_writers_append [simp]: 
  "vl_writers (vl @ [\<lparr>v_value = x, v_writer = t, v_readerset = s\<rparr>]) = insert t (vl_writers vl)"
  by (simp add: vl_writers_def)

lemma vl_readers_append [simp]: 
  "vl_readers (vl @ [\<lparr>v_value = x, v_writer = t, v_readerset = s\<rparr>]) = vl_readers vl \<union> s"
  by (auto simp add: vl_readers_def)


text \<open>Sequence numbers and fresh txids\<close>

definition vl_writers_sqns :: "('v, 'm) vs_list \<Rightarrow> cl_id \<Rightarrow> sqn set" where
  "vl_writers_sqns vl cl \<equiv> {n. Tn (Tn_cl n cl) \<in> vl_writers vl}"

definition kvs_writers_sqns :: "('v, 'm) kvs_store \<Rightarrow> cl_id \<Rightarrow> sqn set" where
  "kvs_writers_sqns K cl \<equiv> (\<Union>k. vl_writers_sqns (K k) cl)"

definition vl_readers_sqns :: "('v, 'm) vs_list \<Rightarrow> cl_id \<Rightarrow> sqn set" where
  "vl_readers_sqns vl cl \<equiv> {n. Tn_cl n cl \<in> vl_readers vl}"

definition kvs_readers_sqns :: "('v, 'm) kvs_store \<Rightarrow> cl_id \<Rightarrow> sqn set" where
  "kvs_readers_sqns K cl \<equiv> (\<Union>k. vl_readers_sqns (K k) cl)"

definition get_sqns :: "('v, 'm) kvs_store \<Rightarrow> cl_id \<Rightarrow> sqn set" where
  "get_sqns K cl \<equiv> kvs_writers_sqns K cl \<union> kvs_readers_sqns K cl"

definition next_txids :: "('v, 'm) kvs_store \<Rightarrow> cl_id \<Rightarrow> txid0 set" where
  "next_txids K cl \<equiv> {Tn_cl n cl | n. \<forall>m \<in> get_sqns K cl. m < n}"

lemmas get_sqns_defs = get_sqns_def vl_writers_sqns_def kvs_writers_sqns_def
  vl_readers_sqns_def kvs_readers_sqns_def vl_readers_def vl_writers_def

lemma get_sqns_old_def:
  "get_sqns K cl = {n. Tn (Tn_cl n cl) \<in> kvs_txids K}"
  by (auto simp add: get_sqns_defs kvs_txids_def kvs_readers_def kvs_writers_def) (blast)

lemmas txid_defs = kvs_txids_def kvs_readers_def kvs_writers_def vl_readers_def vl_writers_def
lemmas fresh_txid_defs = next_txids_def get_sqns_old_def txid_defs

\<comment> \<open>txid freshness lemmas\<close>

lemma fresh_txid_v_writer:
  assumes "t \<in> next_txids K cl"
    and "i \<in> full_view (K k)"
  shows "v_writer (K k!i) \<noteq> Tn t"
  using assms nth_mem
  apply (auto simp add: fresh_txid_defs image_iff full_view_def)
  by fastforce

lemma fresh_txid_v_reader_set:
  assumes "t \<in> next_txids K cl"
    and "i \<in> full_view (K k)"
  shows "t \<notin> v_readerset (K k!i)"
  using assms nth_mem
  apply (auto simp add: fresh_txid_defs image_iff full_view_def)
  by blast

lemma fresh_txid_writer_so:
  assumes "t \<in> next_txids K cl"
    and "i \<in> full_view (K k)"
  shows "(Tn t, v_writer (K k ! i)) \<notin> SO"
  using assms nth_mem
  apply (auto simp add: fresh_txid_defs SO_def SO0_def image_iff full_view_def)
  by fastforce


subsection \<open>Views\<close>

type_synonym v_id = nat

type_synonym key_view = "v_id set"
type_synonym view = "key \<Rightarrow> key_view"

definition view_init :: view where
  "view_init \<equiv> (\<lambda>k. {0})"

definition view_order (infix "\<sqsubseteq>" 60) where
  "u1 \<sqsubseteq> u2 \<equiv> \<forall>k. u1 k \<subseteq> u2 k"

definition key_view_in_range :: "('v, 'm) vs_list \<Rightarrow> key_view \<Rightarrow> bool" where
  "key_view_in_range vl uk \<equiv> 0 \<in> uk \<and> uk \<subseteq> full_view vl"

definition view_in_range :: "('v, 'm) kvs_store \<Rightarrow> view \<Rightarrow> bool" where
  "view_in_range K u \<equiv> \<forall>k. key_view_in_range (K k) (u k)"

lemmas view_in_range_defs = view_in_range_def key_view_in_range_def

definition view_atomic :: "('v, 'm) kvs_store \<Rightarrow> view \<Rightarrow> bool" where
  "view_atomic K u \<equiv> \<forall>k k'.  \<forall>i \<in> u k. \<forall>i' \<in> full_view (K k').
    v_writer (K k!i) = v_writer (K k'!i') \<longrightarrow> i' \<in> u k'"

definition view_wellformed :: "('v, 'm) kvs_store \<Rightarrow> view \<Rightarrow> bool" where
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

lemma full_view_atomic [simp]:
  "view_atomic K (full_view o K)"
  by (simp add: view_atomic_def)

lemma full_view_wellformed:
  assumes "\<And>k. K k \<noteq> []"
  shows "view_wellformed K (full_view o K)"
  using assms
  by (auto simp add: view_wellformed_defs kvs_initialized_def zero_in_full_view)

\<comment> \<open>view lemmas\<close>
lemma view_order_transitive:
  "u \<sqsubseteq> u' \<Longrightarrow> u' \<sqsubseteq> u'' \<Longrightarrow> u \<sqsubseteq> u''"
  by (auto simp add: view_order_def)

lemma view_order_refl [simp]:
  "u \<sqsubseteq> u" by (simp add: view_order_def)

lemma view_order_full_view_increasing:
  assumes "\<And>k. length (K k) \<le> length (K' k)"
  shows "(\<lambda>k. full_view (K k)) \<sqsubseteq> (\<lambda>k. full_view (K' k))"
  using assms
  by (simp add: full_view_def view_order_def)

lemma view_finite [simp]:
  assumes "view_in_range K u"
  shows "finite (u k)"
  using assms 
  by (auto simp add: view_in_range_defs intro: rev_finite_subset)

lemma view_non_empty [simp]:
  assumes "view_in_range K u"
  shows "u k \<noteq> {}"
  using assms 
  by (auto simp add: view_in_range_defs)

lemma view_elem_full_view [simp]:
  assumes "view_in_range K u" "i \<in> u k"
  shows "i \<in> full_view (K k)"
  using assms
  by (auto simp add: view_in_range_defs)   

lemma view_Max_full_view [simp]:
  assumes "view_in_range K u"
  shows "Max (u k) \<in> full_view (K k)"
proof -
  have "Max (u k) \<in> u k" using assms by auto
  then show ?thesis using assms by simp
qed

lemma view_zero_full_view:
  assumes "view_in_range K u"
  shows "0 \<in> full_view (K k)" 
  using assms
  by (auto simp add: view_in_range_defs)

lemma max_in_full_view [simp]:
  assumes "vl \<noteq> []"
  shows "Max (full_view vl) \<in> full_view vl"
  using assms
  by (metis full_view_def key_view_Max_full_view key_view_in_range_def
      length_greater_0_conv lessThan_iff set_eq_subset)

\<comment> \<open>Order lemmas\<close>

definition version_order :: "('v, 'm) version_scheme \<Rightarrow> ('v, 'm) version_scheme \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r" 60) where
  "v1 \<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r v2 \<equiv>
    v_value v1 = v_value v2 \<and>
    v_writer v1 = v_writer v2 \<and>
    v_readerset v1 \<subseteq> v_readerset v2"

lemma version_order_refl [simp]: "v \<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r v" by (simp add: version_order_def)
lemma version_order_trans: "v1 \<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r v2 \<Longrightarrow> v2 \<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r v3 \<Longrightarrow> v1 \<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r v3"
  by (auto simp add: version_order_def)

definition vlist_order :: "('v, 'm) vs_list \<Rightarrow> ('v, 'm) vs_list \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>v\<^sub>l" 60) where
  "vl1 \<sqsubseteq>\<^sub>v\<^sub>l vl2 \<equiv> length vl1 \<le> length vl2 \<and> (\<forall>i \<in> full_view vl1. vl1!i \<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r vl2!i)"

lemma vlist_order_refl [simp]: "vl \<sqsubseteq>\<^sub>v\<^sub>l vl" by (simp add: vlist_order_def)
lemma vlist_order_trans: "vl1 \<sqsubseteq>\<^sub>v\<^sub>l vl2 \<Longrightarrow> vl2 \<sqsubseteq>\<^sub>v\<^sub>l vl3 \<Longrightarrow> vl1 \<sqsubseteq>\<^sub>v\<^sub>l vl3"
  apply (simp add: vlist_order_def) using full_view_length_increasing version_order_trans by blast

definition kvs_expands :: "('v, 'm) kvs_store \<Rightarrow> ('v, 'm) kvs_store \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s" 60) where
  "K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K2 \<equiv> (\<forall>k. (K1 k) \<sqsubseteq>\<^sub>v\<^sub>l (K2 k)) \<and> view_atomic K2 (\<lambda>k. full_view (K1 k))"

lemma kvs_exnpands_length_increasing:
  "K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K2 \<Longrightarrow> length (K1 k) \<le> length (K2 k)"
  by (simp add: kvs_expands_def vlist_order_def)

lemma kvs_exnpands_still_in_full_view:
  "K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K2 \<Longrightarrow> i \<in> full_view (K1 k) \<Longrightarrow> i \<in> full_view (K2 k)"
  using full_view_length_increasing kvs_exnpands_length_increasing by blast

lemma kvs_expanded_view_wellformed:
  assumes "view_wellformed K1 u"
    and "K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K2"
  shows "view_wellformed K2 u"
  using assms
  apply (auto simp add: view_wellformed_defs kvs_expands_def vlist_order_def full_view_def)
   apply (metis in_mono lessThan_iff order.strict_trans order_le_less)
  unfolding lessThan_def version_order_def
  subgoal for k k' i i' apply (cases "i' < length (K1 k')")
  apply (metis (no_types, lifting) in_mono mem_Collect_eq)
    by (metis (no_types, lifting) mem_Collect_eq subset_iff).

lemma view_is_atomic:
  assumes "\<forall>k k'. \<forall>i\<in>full_view (K1 k). \<forall>i'\<in>full_view (K2 k').
    v_writer (K2 k ! i) = v_writer (K2 k' ! i') \<longrightarrow> i' \<in> full_view (K1 k')"
    and "i \<in> full_view (K1 k)"
    and "i' \<in> full_view (K2 k')"
    and "v_writer (K2 k ! i) = v_writer (K2 k' ! i')"
  shows "i' \<in> full_view (K1 k')"
  using assms
  by simp

lemma kvs_expands_refl [simp]: "K \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K" by (simp add: kvs_expands_def view_atomic_def)
lemma kvs_expands_trans: "K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K2 \<Longrightarrow> K2 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K3 \<Longrightarrow> K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K3"
  apply (auto simp add: kvs_expands_def view_atomic_def)
  using vlist_order_trans apply blast
  subgoal for k k' i i'   
    apply (auto dest!: view_is_atomic[of K1 K2 i k i' k'])
    apply (auto dest!: view_is_atomic[of K2 K3 i k i' k'])
    using full_view_length_increasing vlist_order_def apply blast
    using full_view_length_increasing vlist_order_def apply blast
    by (metis (no_types) full_view_length_increasing version_order_def vlist_order_def).


\<comment> \<open>List updates and membership lemmas\<close>

lemma list_nth_in_set [simp]:
  assumes "i \<in> full_view vl"
  shows "vl ! i \<in> set vl"
  using assms
  by (auto simp add: full_view_def)

lemma in_set_before_update [simp]:
  assumes "a \<noteq> vl [i := x] ! i"
    and "a \<in> set (vl [i := x])"
  shows "a \<in> set vl"
  using assms
  apply (simp add: in_set_conv_nth)
  apply (rule bexE [where A="{..<length vl}" and P="\<lambda>i'. vl[i := x] ! i' = a"])
   apply auto subgoal for i' i'' by (cases "i' = i"; auto).

lemma in_set_after_update [simp]:
  assumes "a \<noteq> vl ! i"
    and "a \<in> set vl"
  shows "a \<in> set (vl [i := x])"
  using assms
  apply (simp add: in_set_conv_nth)
  apply (rule bexE [where A="{..<length vl}" and P="\<lambda>i'. vl ! i' = a"])
   apply auto subgoal for i' i'' by (cases "i' = i"; auto).

lemma in_set_update [simp]:
  assumes "i \<in> full_view vl"
  shows "x \<in> set (vl [i := x])"
  using assms
  by (metis (full_types) full_view_nth_list_update_eq list_nth_in_set
      list_update_beyond set_update_memI verit_comp_simplify1(3))

lemma the_update:
  assumes "a \<in> set (vl [i := x])"
    and "a \<notin> set vl"
  shows "x = a"
  using assms
  apply (simp add: in_set_conv_nth)
  by (metis nth_list_update_eq nth_list_update_neq)

lemma not_in_image:
  assumes "f a \<notin> f ` b"
  shows "a \<notin> b"
  using assms by auto

lemma in_set_bigger:
  assumes "x \<in> v_readerset (vl ! i)"
    and "i \<in> full_view vl"
  shows "x \<in> v_readerset (vl[i := (vl ! i) \<lparr>v_readerset := v_readerset (vl ! i) \<union> el \<rparr>] ! i)"
  using assms by simp

lemma non_changing_feature [simp]:
  assumes "i \<in> full_view vl"
  shows "v_value (vl[j := (vl ! j) \<lparr>v_readerset := y\<rparr>] ! i) = v_value (vl ! i)"
  using assms
  by (metis full_view_nth_list_update_eq nth_list_update_neq version.ext_inject
      version.surjective version.update_convs(3))

lemma non_changing_feature2 [simp]:
  assumes "i \<in> full_view vl"
  shows "v_writer (vl[j := (vl ! j) \<lparr>v_readerset := y\<rparr>] ! i) = v_writer (vl ! i)"
  using assms
  by (metis full_view_nth_list_update_eq nth_list_update_neq version.ext_inject
      version.surjective version.update_convs(3))

lemma expanding_feature3:
  assumes "i \<in> full_view vl"
    and "x \<in> v_readerset (vl ! i)"
  shows "x \<in> v_readerset (vl[j := (vl ! j) \<lparr>v_readerset := (v_readerset (vl ! j)) \<union> y\<rparr>] ! i)"
  using assms
  by (metis UnCI full_view_nth_list_update_eq nth_list_update_neq version.select_convs(3)
      version.surjective version.update_convs(3))

lemma longer_list_not_empty:
  "vl \<noteq> [] \<Longrightarrow> length vl \<le> length vl' \<Longrightarrow> vl' \<noteq> []"
  by auto


subsection \<open>Snapshots and Configs\<close>

type_synonym 'v snapshot = "key \<Rightarrow> 'v"

definition last_version :: "('v, 'm) vs_list \<Rightarrow> key_view \<Rightarrow> ('v, 'm) version_scheme" where
  "last_version vl uk \<equiv> vl ! Max uk"

definition view_snapshot :: "('v, 'm) kvs_store \<Rightarrow> view \<Rightarrow> 'v snapshot" where
  "view_snapshot K u k \<equiv> v_value (last_version (K k) (u k))"

type_synonym 'v config = "'v kv_store \<times> (cl_id \<Rightarrow> view)"

abbreviation c_views_init :: "cl_id \<Rightarrow> view" where
  "c_views_init \<equiv> (\<lambda>cl. view_init)"

definition config_init :: "'v config" where
  "config_init \<equiv> (kvs_init, c_views_init)"

lemmas config_init_defs = config_init_def (* kvs_init_defs *) view_init_def

\<comment> \<open>Lemmas about last_version\<close>

lemma [simp]: "last_version [v] {..<Suc 0} = v"        (* CHSP: seems very specialized *)
  by (auto simp add: last_version_def lessThan_def)

lemma Max_less_than_Suc [simp]: "Max {..<Suc n} = n" 
  apply (simp add: lessThan_Suc)
  by (meson Max_insert2 finite_lessThan lessThan_iff less_imp_le_nat)


subsection \<open>Fingerprints\<close>

datatype op_type = R | W
datatype 'v op = Read key 'v | Write key 'v | Eps

type_synonym 'v key_fp = "op_type \<rightharpoonup> 'v"
type_synonym 'v fingerpr = "key \<Rightarrow> 'v key_fp"

subsubsection \<open>Special fingerprints\<close>

definition empty_fp :: "'v fingerpr" where
  "empty_fp \<equiv> (\<lambda>k. Map.empty)"

definition read_only_fp :: "(key \<rightharpoonup> 'v) \<Rightarrow> 'v fingerpr" where
  "read_only_fp kv_map k \<equiv> case_op_type (kv_map k) None" 

definition write_only_fp :: "(key \<rightharpoonup> 'v) \<Rightarrow> 'v fingerpr" where
  "write_only_fp kv_map k \<equiv> case_op_type None (kv_map k)" 

\<comment> \<open>Lemmas about special fingerprints\<close>

lemma write_only_fp_write [simp]: "write_only_fp kv_map k W = kv_map k"
  by (simp add: write_only_fp_def)

lemma write_only_fp_no_reads [simp]: "write_only_fp kv_map k R = None"
  by (simp add: write_only_fp_def)

lemma write_only_fp_empty [simp]: "write_only_fp kv_map k = Map.empty \<longleftrightarrow> kv_map k = None"
  by (metis (full_types) op_type.exhaust op_type.simps(3) op_type.simps(4) write_only_fp_def)

lemma read_only_fp_read [simp]: "read_only_fp kv_map k R = kv_map k"
  by (simp add: read_only_fp_def)

lemma read_only_fp_no_writes [simp]: "read_only_fp kv_map k W = None"
  by (simp add: read_only_fp_def)

lemma read_only_fp_empty [simp]: "read_only_fp kv_map k = Map.empty \<longleftrightarrow> kv_map k = None"
  by (metis (full_types) op_type.exhaust op_type.simps(3) op_type.simps(4) read_only_fp_def)


subsubsection \<open>Fingerprint updates\<close>

fun update_key_fp :: "'v key_fp \<Rightarrow> op_type \<Rightarrow> 'v \<Rightarrow> 'v key_fp" where
  "update_key_fp Fk R v = (if Fk R = None \<and> Fk W = None then Fk (R \<mapsto> v) else Fk)" |
  "update_key_fp Fk W v = Fk(W \<mapsto> v)"

fun update_fp :: "'v fingerpr \<Rightarrow> 'v op \<Rightarrow> 'v fingerpr" where
  "update_fp F (Read k v)  = F (k := update_key_fp (F k) R v)" |
  "update_fp F (Write k v) = F (k := update_key_fp (F k) W v)" |
  "update_fp F Eps         = F"


subsubsection \<open>Fingerprint property\<close>

 \<comment>\<open>The Fingerprint condition was originally in Execution Test\<close>
definition fp_property :: "'v fingerpr \<Rightarrow> ('v, 'm) kvs_store \<Rightarrow> view \<Rightarrow> bool" where
  "fp_property F K u \<equiv> \<forall>k. R \<in> dom (F k) \<longrightarrow> F k R = Some (view_snapshot K u k)"



subsection \<open>KVS updates\<close>

definition update_kv_key_reads :: 
  "txid0 \<Rightarrow> 'v key_fp \<Rightarrow> key_view \<Rightarrow> ('v, 'm) vs_list \<Rightarrow> ('v, 'm) vs_list" where
  "update_kv_key_reads t Fk uk vl =
    (case Fk R of
      None   \<Rightarrow> vl |
      Some v \<Rightarrow> let lv = last_version vl uk in
                vl[Max uk := lv\<lparr>v_readerset := insert t (v_readerset lv)\<rparr>])"

definition update_kv_key_writes :: "txid0 \<Rightarrow> 'v key_fp \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_key_writes t Fk vl =
    (case Fk W of
      None   \<Rightarrow> vl |
      Some v \<Rightarrow> vl @ [new_vers (Tn t) v])"

definition update_kv_key :: "txid0 \<Rightarrow> 'v key_fp \<Rightarrow> key_view \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_key t Fk uk = (update_kv_key_writes t Fk) o (update_kv_key_reads t Fk uk)"

definition update_kv :: "txid0 \<Rightarrow> 'v fingerpr \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> 'v kv_store" where
  "update_kv t F u K = (\<lambda>k. update_kv_key t (F k) (u k) (K k))"

lemmas update_kv_key_reads_defs = update_kv_key_reads_def Let_def last_version_def

lemmas update_kv_defs = update_kv_def update_kv_key_def


subsubsection \<open>Version list updates\<close>

lemma update_kv_key_reads_read_latest:
  assumes "Fk R = Some v" "Max uk < length vl"
  shows "update_kv_key_reads t Fk uk vl ! Max uk = 
         (last_version vl uk)\<lparr>v_readerset := insert t (v_readerset (last_version vl uk))\<rparr>"
  using assms
  by (simp add: update_kv_key_reads_def Let_def split: op_type.split)

lemma update_kv_key_reads_read_not_latest:
  assumes "Fk R = Some v" "i \<noteq> Max uk"
  shows "update_kv_key_reads t Fk uk vl ! i = vl ! i"
  using assms
  by (simp add: update_kv_key_reads_def Let_def split: op_type.split)

lemma update_kv_key_reads_no_read:
  assumes "Fk R = None"
  shows "update_kv_key_reads t Fk uk vl = vl"
  using assms
  by (simp add: update_kv_key_reads_def split: op_type.split)

lemmas update_kv_key_reads_simps = 
   update_kv_key_reads_read_latest update_kv_key_reads_read_not_latest update_kv_key_reads_no_read


(*
lemma update_kv_key_writes:
  "update_kv_key_writes t Fk vl = 
   (case Fk W of None \<Rightarrow> vl | Some v \<Rightarrow> vl @ [new_vers t v])"
  by (auto simp add: update_kv_key_writes_def)

lemmas update_kv_key_writes_simps = update_kv_key_writes
*)

lemma update_kv_key_write_only:
  "update_kv_key t (case_op_type None wo) uk vl = 
   (case wo of None \<Rightarrow> vl | Some v \<Rightarrow> vl @ [new_vers (Tn t) v])"
   by (auto simp add: update_kv_key_def update_kv_key_reads_simps update_kv_key_writes_def)




(* next one is about KVS update: *)

lemma update_kv_write_only:
  "update_kv t (write_only_fp kv_map) u K k = 
   (case kv_map k of None \<Rightarrow> K k | Some v \<Rightarrow> K k @ [new_vers (Tn t) v])"
  by (simp add: update_kv_def write_only_fp_def update_kv_key_write_only)












lemma update_kv_key_empty_fp [simp]:
  assumes "Fk R = None" and "Fk W = None"
  shows "update_kv_key t Fk uk vl = vl"
  using assms
  by (auto simp add: update_kv_key_def update_kv_key_reads_def update_kv_key_writes_def)


(* next two are about views *)

lemma update_kv_key_ro_full_view [simp]:
  assumes "Fk W = None"
  shows "full_view (update_kv_key t Fk uk vl) = full_view vl"
  using assms
  by (auto simp add: update_kv_key_def update_kv_key_writes_def update_kv_key_reads_defs
       split: option.split)

lemma update_kv_key_rw_full_view [simp]:
  assumes "Fk W \<noteq> None"
  shows "full_view (update_kv_key t Fk uk vl) = insert (length vl) (full_view vl)"
  using assms
  by (auto simp add: update_kv_key_def update_kv_key_writes_def update_kv_key_reads_defs
      full_view_grows length_vl_in_appended split: option.split)



lemma update_kv_key_ro_set_v_readerset:
  assumes "Fk W = None"
    and "vl \<noteq> []"
  shows "(update_kv_key t Fk (full_view vl) vl) [Max (full_view vl) :=
    last_version (update_kv_key t Fk (full_view vl) vl) (full_view vl) \<lparr> v_readerset := x \<rparr>] =
    vl [Max (full_view vl) := last_version vl (full_view vl) \<lparr> v_readerset := x \<rparr>]"
  using assms
  by (auto simp add: update_kv_key_def update_kv_key_writes_def update_kv_key_reads_defs
      split: option.split)

lemma update_kv_key_ro_v_readerset [simp]:
  assumes "Fk W = None" and "Fk R \<noteq> None"
    and "vl \<noteq> []"
  shows "v_readerset (last_version (update_kv_key t Fk (full_view vl) vl) (full_view vl)) =
         insert t (v_readerset (last_version vl (full_view vl)))"
  using assms
  by (auto simp add: update_kv_key_def update_kv_key_writes_def update_kv_key_reads_defs)




subsubsection \<open>Lemmas about length of version list updates\<close>

\<comment> \<open>update_kv lemmas about version list length and full_view\<close>

lemma update_kv_key_reads_length:
  "length (update_kv_key_reads t Fk uk vl) = length vl"
proof (cases "Fk R")
  case (Some a)
  then show ?thesis apply (auto simp add: update_kv_key_reads_def)
    by (meson length_list_update)
qed (auto simp add: update_kv_key_reads_def)

lemma update_kv_key_writes_none_length:
  assumes "Fk W = None"
  shows "length (update_kv_key_writes t Fk vl) = length vl"
  using assms by (auto simp add: update_kv_key_writes_def)

lemma update_kv_key_writes_some_length:
  assumes "Fk W = Some v"
  shows "length (update_kv_key_writes t Fk vl) = Suc (length vl)"
  using assms by (auto simp add: update_kv_key_writes_def)

lemma update_kv_key_writes_length:
  shows "length (update_kv_key_writes t Fk vl) = Suc (length vl) \<or> 
         length (update_kv_key_writes t Fk vl) = length vl"
  by (cases "Fk W") (auto simp add: update_kv_key_writes_def)

lemma update_kv_key_writes_length_increasing:
  "length vl \<le> length (update_kv_key_writes t Fk vl)"
  using update_kv_key_writes_length [of t Fk vl]
  by auto

lemma update_kv_key_writes_on_diff_len:
  assumes "length vl1 \<le> length vl2"
  shows "length (update_kv_key_writes t Fk vl1) \<le>
         length (update_kv_key_writes t Fk vl2)"
  using assms by (auto simp add: update_kv_key_writes_def split: option.split)

lemma update_kv_key_length:
  "length (update_kv_key t Fk uk vl) = Suc (length vl) \<or>
   length (update_kv_key t Fk uk vl) = length vl"
  using update_kv_key_writes_length [where vl="update_kv_key_reads t Fk uk vl"]
  by (simp add: update_kv_defs update_kv_key_reads_length)

lemma update_kv_key_length_increasing:
  "length vl \<le> length (update_kv_key t Fk uk vl)"
  using update_kv_key_length [of t Fk uk vl]
  by auto

lemma update_kv_length:
  "length (update_kv t F u K k) = Suc (length (K k)) \<or>
   length (update_kv t F u K k) = length (K k)"
  by (simp add: update_kv_def update_kv_key_length)
 
lemma update_kv_length_increasing:      
  "length (K k) \<le> length (update_kv t F u K k)"
  using update_kv_length [of t F u K k]
  by auto



subsubsection \<open>Lemmas about full view\<close>


lemma full_view_update_kv_key_reads [simp]:
  "full_view (update_kv_key_reads t Fk uk vl) = full_view vl"
  by (simp add: update_kv_key_reads_length full_view_def)

lemma full_view_update_kv_key_writes [dest]:
  "i \<in> full_view vl \<Longrightarrow> i \<in> full_view (update_kv_key_writes t Fk vl)"
  using update_kv_key_writes_length_increasing [of vl t Fk] 
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

lemma update_kv_key_writes_key_decides_length:
  shows "length (update_kv_key t Fk uk vl) = length (update_kv_key_writes t Fk vl)"
  by (cases "Fk W") (auto simp add: update_kv_key_def update_kv_key_writes_def update_kv_key_reads_length)

lemma update_kv_key_writes_decides_length:
  shows "length (update_kv t F u K k) = length (update_kv_key_writes t (F k) (K k))"
  by (simp add: update_kv_def update_kv_key_writes_key_decides_length)




\<comment> \<open>update_kv lemmas about changing the versions\<close>

lemma update_kv_key_writes_version_inv:
  assumes "i \<in> full_view vl"
  shows "update_kv_key_writes t Fk vl!i = vl!i"
proof (cases "Fk W")
  case (Some a)
  then show ?thesis using assms
    by (auto simp add: update_kv_key_writes_def)
qed (auto simp add: update_kv_key_writes_def)




subsubsection \<open>Lemmas about version value\<close>

(* v_value *)
lemma update_kv_key_reads_v_value_inv:
  assumes "i \<in> full_view vl"
  shows "v_value (update_kv_key_reads t Fk uk vl!i) = v_value (vl!i)"
proof (cases "Fk R")
  case (Some a)
  then show ?thesis using assms
    by (cases "i = Max uk") 
       (auto simp add: update_kv_key_reads_defs)
qed (auto simp add: update_kv_key_reads_def)

lemma update_kv_key_v_value_inv:
  assumes "i \<in> full_view vl"
  shows "v_value (update_kv_key t Fk uk vl !i) = v_value (vl !i)"
  using assms
  by (auto simp add: update_kv_key_def update_kv_key_writes_version_inv update_kv_key_reads_v_value_inv)

lemma update_kv_v_value_inv:
  assumes "i \<in> full_view (K k)"
  shows "v_value (update_kv t F u K k!i) = v_value (K k!i)"
  using assms
  by (auto simp add: update_kv_def update_kv_key_v_value_inv)



subsubsection \<open>Lemmas about version writer\<close>

(* v_writer *)
lemma update_kv_key_reads_v_writer_inv:
  assumes "i \<in> full_view vl"
  shows "v_writer (update_kv_key_reads t Fk uk vl!i) = v_writer (vl!i)"
proof (cases "Fk R")
  case (Some a)
  then show ?thesis using assms
    by (cases "i = Max uk")
       (auto simp add: update_kv_key_reads_defs split: option.splits)
qed (simp add: update_kv_key_reads_def)

lemma update_kv_v_writer_inv:
  assumes "i \<in> full_view (K k)"
  shows "v_writer (update_kv t F u K k!i) = v_writer (K k!i)"
  using assms
  by (auto simp add: update_kv_defs update_kv_key_writes_version_inv update_kv_key_reads_v_writer_inv)

lemma update_kv_key_writes_key_new_version_v_writer:
  assumes  "length (update_kv_key t Fk uk vl) = Suc (length vl)"
  shows "v_writer (update_kv_key_writes t Fk vl ! length vl) = Tn t"
  using assms
  by (auto simp add: update_kv_key_writes_key_decides_length update_kv_key_writes_def split: option.split)

lemma update_kv_key_writes_new_version_v_writer:
  assumes  "length (update_kv t F u K k) = Suc (length (K k))"
  shows "v_writer (update_kv_key_writes t (F k) (K k) ! length (K k)) = Tn t"
  using assms
  by (simp add: update_kv_def update_kv_key_writes_key_new_version_v_writer)

lemma update_kv_key_new_version_v_writer:
  assumes  "length (update_kv_key t Fk uk vl) = Suc (length vl)"
  shows "v_writer (update_kv_key t Fk uk vl ! length vl) = Tn t"
  using assms apply (auto simp add: update_kv_key_def)
  by (metis update_kv_key_reads_length update_kv_key_writes_key_decides_length
            update_kv_key_writes_key_new_version_v_writer)

lemma update_kv_new_version_v_writer:
  assumes  "length (update_kv t F u K k) = Suc (length (K k))"
  shows "v_writer (update_kv t F u K k ! length (K k)) = Tn t"
  using assms
  apply (auto simp add: update_kv_defs)
  by (metis comp_apply update_kv_key_def update_kv_key_new_version_v_writer)
            
lemma update_kv_key_reads_vl_writers_inv [simp]:
  "vl_writers (update_kv_key_reads t Fk uk vl) = vl_writers vl"
  apply (auto simp add: update_kv_key_reads_defs vl_writers_def in_set_conv_nth split: option.split)
  subgoal for y i by (cases "i = Max uk"; simp)
  subgoal for y i apply (cases "i = Max uk"; auto simp add: image_iff)
    apply (metis set_update_memI version.select_convs(2) version.surjective version.update_convs(3))
    by (metis length_list_update nth_list_update_neq nth_mem)
  done


subsubsection \<open>Lemmas about version reader set\<close>

(* v_readerset *)
lemma v_readerset_update_kv_key_reads_max_u:
  assumes "x \<in> v_readerset (update_kv_key_reads t Fk uk vl!i)"
      and "i \<in> full_view vl" and "i = Max uk" 
    shows "x \<in> v_readerset (vl!i) \<or> x = t"
  using assms
  by (cases "Fk R") (auto simp add: update_kv_key_reads_defs)

lemma v_readerset_update_kv_key_reads_rest_inv:
  assumes "i \<in> full_view vl" and "i \<noteq> Max uk"
  shows "v_readerset (update_kv_key_reads t Fk uk vl!i) = v_readerset (vl!i)"
proof (cases "Fk R")
  case (Some a)
  then show ?thesis using assms
    by (auto simp add: update_kv_key_reads_def; metis assms(2) nth_list_update_neq)
qed (auto simp add: update_kv_key_reads_def)

lemma v_readerset_update_kv_key_writes:
  assumes "i \<in> full_view vl"
    shows "v_readerset (update_kv_key_writes t Fk vl ! i) = v_readerset (vl ! i)"
  using assms
  by (auto simp add: update_kv_key_writes_def split: option.splits)

lemma v_readerset_update_kv_max_u:
  assumes "x \<in> v_readerset (update_kv t F u K k ! Max (u k))"
      and "view_in_range K u"
    shows "x \<in> v_readerset (K k ! Max (u k)) \<or> x = t"
  using assms
  by (auto simp add: update_kv_defs v_readerset_update_kv_key_writes
           dest: v_readerset_update_kv_key_reads_max_u)

lemma v_readerset_update_kv_rest_inv:
  assumes "i \<noteq> Max (u k)" and  "i \<in> full_view (K k)"
  shows "v_readerset (update_kv t F u K k!i) = v_readerset (K k!i)"
  using assms update_kv_key_writes_version_inv [of i "update_kv_key_reads t (F k) (u k) (K k)"]
  by (auto simp add: v_readerset_update_kv_key_reads_rest_inv update_kv_defs update_kv_key_reads_length)


lemma update_kv_key_writes_new_version_v_readerset:
  assumes  "length (update_kv t F u K k) = Suc (length (K k))"
  shows "v_readerset (update_kv_key_writes t (F k) (K k) ! length (K k)) = {}"
  using assms
  by (auto simp add: update_kv_key_writes_decides_length update_kv_key_writes_def split: option.split)

lemma update_kv_new_version_v_readerset:
  assumes  "length (update_kv t F u K k) = Suc (length (K k))"
  shows "v_readerset (update_kv t F u K k ! length (K k)) = {}"
  using assms
  apply (auto simp add: update_kv_defs update_kv_key_writes_def update_kv_key_reads_length split: option.split)
  by (metis update_kv_key_reads_length equals0D nth_append_length version.select_convs(3))

lemma update_kv_key_reads_vl_readers_inv:
  "vl \<noteq> [] \<Longrightarrow> vl_readers (update_kv_key_reads t Fk (full_view vl) vl) =
    (case Fk R of None \<Rightarrow> vl_readers vl | Some _ \<Rightarrow> vl_readers vl \<union> {t})"
  apply (auto simp add: update_kv_key_reads_defs vl_readers_def in_set_conv_nth split: option.split)
  subgoal for y ver i by (cases "i = Max (full_view vl)"; simp)
  apply (rule bexI [where x="update_kv_key_reads t Fk (full_view vl) vl ! Max (full_view vl)"])
    apply (auto simp add: update_kv_key_reads_defs)
  subgoal for y ver i apply (cases "i = Max (full_view vl)", simp)
     apply (metis in_set_update insert_iff max_in_full_view version.select_convs(3)
        version.surjective version.update_convs(3))
    by (metis length_list_update nth_list_update_neq nth_mem)
  done


(************************************)
(* INTEGRATE STUFF BELOW INTO ABOVE *)
(************************************)





lemma length_update_kv:
  "length (update_kv t F u K k) = (if F k W = None then length (K k) else  Suc (length (K k)))"
  by (auto simp add: update_kv_key_writes_decides_length update_kv_key_writes_def)


lemma v_writer_in_kvs_txids:
  "i < length (K k) \<Longrightarrow> v_writer (K k ! i) \<in> kvs_txids K"
  by (auto simp add: kvs_txids_def kvs_writers_def vl_writers_def intro: exI[where x=k])


(*****)

lemma vl_writers_update_kv_key_writes:
  "vl_writers (update_kv_key_writes t Fk vl) = 
   (if Fk W = None then vl_writers vl else insert (Tn t) (vl_writers vl))"
  by (simp add: update_kv_key_writes_def vl_writers_def split: option.split)

thm update_kv_key_reads_vl_writers_inv

lemma vl_writers_update_kv_key_reads:  (* same as update_kv_key_reads_vl_writers_inv *)
  "vl_writers (update_kv_key_reads t Fk uk vl) = vl_writers vl"  
  apply (auto simp add: update_kv_key_reads_def vl_writers_def last_version_def Let_def split: option.split)
   apply (metis image_eqI list_update_beyond nth_mem the_update verit_comp_simplify1(3) 
                version.select_convs(2) version.surjective version.update_convs(3))
  by (metis (mono_tags, lifting) image_iff in_set_after_update list_update_beyond set_update_memI 
            verit_comp_simplify1(3) version.select_convs(2) version.surjective version.update_convs(3))

lemma vl_readers_update_kv_key_writes:
  "vl_readers (update_kv_key_writes t Fk vl) = vl_readers vl"
  by (auto simp add: update_kv_key_writes_def vl_readers_def split: option.split)

lemma vl_readers_update_kv_key_reads:
  assumes "\<And>v. Fk R = Some v \<Longrightarrow> Max uk < length vl"
  shows "vl_readers (update_kv_key_reads t Fk uk vl) = 
         (if Fk R = None then vl_readers vl else insert t (vl_readers vl))"
  using assms
  apply (auto simp add: vl_readers_def update_kv_key_reads_simps)
    apply (metis (no_types, lifting) full_view_def in_set_conv_nth lessThan_iff update_kv_key_reads_length 
                 update_kv_key_reads_simps(2) v_readerset_update_kv_key_reads_max_u)
   apply (rule bexI[where x="update_kv_key_reads t Fk uk vl ! Max uk"], 
          simp add: update_kv_key_reads_simps, simp add: update_kv_key_reads_length)
  by (smt (verit, best) in_set_after_update insert_iff last_version_def option.case(2) 
          set_update_memI update_kv_key_reads_defs(1) version.select_convs(3) version.surjective 
          version.update_convs(3))


(***)


lemma kvs_writers_update_kv:
  "kvs_writers (update_kv t fp u K) = 
   (if \<forall>k. fp k W = None then kvs_writers K else insert (Tn t) (kvs_writers K))"
  by (auto 4 3 simp add: update_kv_def update_kv_key_def kvs_writers_def 
                         vl_writers_update_kv_key_writes)

lemma kvs_readers_update_kv:
  assumes "\<And>k v. fp k R = Some v \<Longrightarrow> Max (u k) < length (K k)"
  shows "kvs_readers (update_kv t fp u K) = 
         (if \<forall>k. fp k R = None then kvs_readers K else insert t (kvs_readers K))"
  using assms
  by (auto 4 3 simp add: update_kv_def update_kv_key_def kvs_readers_def 
                         vl_readers_update_kv_key_writes vl_readers_update_kv_key_reads) 

text \<open>Useful special case of above; simp does not prove it directly.\<close>

lemma kvs_readers_update_kv_write_only:
  "kvs_readers (update_kv t (write_only_fp kv_map) u K) = kvs_readers K"
  by (fact kvs_readers_update_kv[where fp="write_only_fp kv_map" for kv_map, simplified])




lemma kvs_txids_update_kv: 
  assumes "\<And>k v. fp k R = Some v \<Longrightarrow> Max (u k) < length (K k)" 
  shows "kvs_txids (update_kv t fp u K) = 
         (if \<forall>k. fp k = Map.empty then kvs_txids K else insert (Tn t) (kvs_txids K))"
  using assms
  by (auto simp add: kvs_txids_def kvs_writers_update_kv kvs_readers_update_kv del: equalityI)
     (metis (full_types) op_type.exhaust)

text \<open>Useful special case of above; simp does not prove it directly.\<close>

lemma kvs_txids_update_kv_write_only:       
  "kvs_txids (update_kv t (write_only_fp kv_map) u K) = 
   (if \<forall>k. kv_map k = None then kvs_txids K else insert (Tn t) (kvs_txids K))"
  by (fact kvs_txids_update_kv[where fp="write_only_fp kv_map" for kv_map, simplified])


(************************************)
(************************************)
(************************************)



end