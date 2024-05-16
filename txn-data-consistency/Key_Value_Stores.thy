section \<open>Key-Value Stores\<close>

theory Key_Value_Stores
  imports Event_Systems "HOL-Library.Sublist" Closedness
begin


subsection \<open>General lemmas about sets, lists, etc. [MOVE]\<close>

lemma UN_eq_insert_UN:
  assumes "A x = insert a (B x)" 
  and "\<And>y. y \<noteq> x \<Longrightarrow> A y = insert a (B y) \<or> A y = B y"
  shows "(\<Union>x. A x) = insert a (\<Union>x. B x)"
  using assms
  by fastforce

lemma Max_less_than_Suc [simp]: "Max {..<Suc n} = n" 
  by (simp add: lessThan_Suc)
     (meson Max_insert2 finite_lessThan lessThan_iff less_imp_le_nat)

lemma Max_list_index_set: "l \<noteq> [] \<Longrightarrow> Max {..<length l} = length l - 1"
  by (metis Max_less_than_Suc One_nat_def Suc_pred length_greater_0_conv)

lemma nth_append_length':   \<comment> \<open>to replace @{thm "List.nth_append_length"} in Isabelle library?\<close>
  assumes "i = length xs" 
  shows "(xs @ x # ys) ! i = x"
  using assms by simp

lemma image_set_equality_iff:
  assumes 
    "length l = length l'" 
    "\<And>i. f (l ! i)  = f (l' ! i)"
  shows "f ` set l = f ` set l'"
  using assms
  by (metis list.set_map map_equality_iff)

lemma set_update:          \<comment> \<open>add to Isabelle library? (cf. @{thm "List.set_update_distinct"}\<close>
  assumes "i < length l"
  shows "set (l[i := a]) = insert a {l!j | j. j \<noteq> i \<and> j < length l}"
  using assms 
proof (induction l arbitrary: i rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  then show ?case using snoc
    by (cases "i < length xs") (auto simp add: list_update_append nth_append in_set_conv_nth)
qed


subsection \<open>Transaction IDs and session order\<close>

type_synonym cl_id = nat

type_synonym sqn = nat

datatype txid0 = Tn_cl (get_sn: sqn) (get_cl: cl_id)
datatype txid = T0 | Tn txid0

definition SO0 :: "txid0 rel" where
  "SO0 \<equiv> {(t, t'). \<exists>cl n m. t = Tn_cl n cl \<and> t' = Tn_cl m cl \<and> n < m}"

definition SO :: "txid rel" where
  "SO \<equiv> {(Tn t, Tn t')| t t'. (t, t') \<in> SO0}"

lemma SO_irreflexive: "(t, t) \<notin> SO"
  by (simp add: SO_def SO0_def)

lemma get_sn_singleton_simp [simp]:
  "{n. Tn_cl n (get_cl t) = t} = {get_sn t}"
  by (cases t) auto


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

lemma length_kvs_init [simp]: "length \<circ> kvs_init = (\<lambda>k. 1)"
  by (simp add: kvs_init_defs o_def)


subsubsection \<open>Full view on a version list\<close>

text \<open>The full view is the index range for a version list (or kvs and key)\<close>  

definition full_view :: "('v, 'm) vs_list \<Rightarrow> nat set" where   (* CHSP: DROP OR CHANGE THIS DEF? *)
  "full_view = (\<lambda>vl. {..<length vl})"

lemma full_view_elemI [intro]: "i < length vl \<Longrightarrow> i \<in> full_view vl"    (* AUT-ADDED *)
  by (simp add: full_view_def)

lemma full_view_elemD: "i \<in> full_view vl \<Longrightarrow> i < length vl"
  by (simp add: full_view_def)

thm nth_list_update_eq nth_list_update_neq

lemma full_view_singleton [simp]: "full_view [vers] = {0}"
  by (simp add: full_view_def lessThan_Suc)

lemma full_view_kvs_init_k [simp]: "full_view (kvs_init k) = {0}"
  by (auto simp add: kvs_init_defs full_view_def dest: le_funD)

lemma full_view_kvs_init [simp]: "full_view o kvs_init = (\<lambda>k. {0})"
  by (simp add: o_def)


text \<open>Full view and list length\<close>

lemma full_view_eq_is_length_eq: 
  "full_view vl = full_view vl' \<longleftrightarrow> length vl = length vl'"
  by (simp add: full_view_def)

lemma full_view_subset_is_length_leq: 
  "full_view vl \<subseteq> full_view vl' \<longleftrightarrow> length vl \<le> length vl'"
  by (simp add: full_view_def)

lemma full_view_length_increasing: 
  assumes "length vl \<le> length vl'"
    and "i \<in> full_view vl"
  shows "i \<in> full_view vl'"
  using assms 
  by (simp add: full_view_def)

lemma full_view_same_length:
  assumes "length vl = length vl'"
    and "i \<in> full_view vl"
  shows "i \<in> full_view vl'"
  using assms 
  by (simp add: full_view_def)


text \<open>Full view as set\<close>

lemma full_view_finite [simp, intro!]: "finite (full_view vl)"
  by (simp add: full_view_def)

lemma full_view_snoc [simp]:  
  "full_view (vl @ [ver]) = insert (length vl) (full_view vl)"
  by (auto simp add: full_view_def)

lemma full_view_vl_update [simp]:
  "full_view (vl[i := ver]) = full_view vl"
  by (simp add: full_view_eq_is_length_eq)

lemma full_view_update_append [simp]:
  "full_view (vl[i := x] @ vs) = full_view (vl @ vs)"
  by (simp add: full_view_eq_is_length_eq)


text \<open>Elements of full view\<close>

lemma zero_in_full_view [simp]: "vl \<noteq> [] \<Longrightarrow> 0 \<in> full_view vl"         (* AUT-ADDED *)
  by (simp add: full_view_def)

lemma max_in_full_view [simp]: "vl \<noteq> [] \<Longrightarrow> Max (full_view vl) \<in> full_view vl"
  using Max_in zero_in_full_view by auto

lemma full_view_grows: 
  "i \<in> full_view vl \<Longrightarrow> i \<in> full_view (vl @ vs)"
  by (simp add: full_view_def)


text \<open>Indexing version list elements in full view\<close>

lemma full_view_nth_list_update_eq [simp]:     (* special case of nth_list_update_eq *)
  "i \<in> full_view vl \<Longrightarrow> vl[i := x] ! i = x"
  by (simp add: full_view_def)

lemma full_view_append [simp]:
  "i \<in> full_view vl \<Longrightarrow> (vl @ vs) ! i = vl ! i"
  by (auto simp add: full_view_def nth_append)


(* SUBSUMED BY LEMMA full_view_snoc:

lemma length_vl_in_appended:
  "length vl \<in> full_view (vl @ [v])"
  by (simp)

lemma full_view_x_in_append [simp]:
  assumes "i \<in> full_view (vl @ [v])"
    and "i \<notin> full_view vl"
  shows "i = length vl"
  using assms by (simp add: full_view_def)
*)


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

lemma snapshot_propertyD1:
    "\<lbrakk> t \<in> v_readerset (K k ! i); t \<in> v_readerset (K k ! j);
       i \<in> full_view (K k); j \<in> full_view (K k); snapshot_property K \<rbrakk> 
   \<Longrightarrow> i = j"
  by (auto simp add: snapshot_property_def)

lemma snapshot_propertyD2:
    "\<lbrakk> v_writer (K k ! i) = v_writer (K k ! j); 
       i \<in> full_view (K k); j \<in> full_view (K k); snapshot_property K \<rbrakk> 
   \<Longrightarrow> i = j"
  by (auto simp add: snapshot_property_def)

lemma snapshot_property_kvs_init [simp, intro]: "snapshot_property kvs_init"
  by (intro snapshot_propertyI) (auto)

definition wr_so :: "('v, 'm) kvs_store \<Rightarrow> bool" where
  "wr_so K \<longleftrightarrow> (\<forall>k t t'. \<forall>i \<in> full_view (K k).
                  t = v_writer (K k!i) \<longrightarrow> t' \<in> Tn ` v_readerset (K k!i) \<longrightarrow> (t', t) \<notin> SO^=)"

lemmas wr_soI = wr_so_def [THEN iffD2, rule_format]
lemmas wr_soE [elim] = wr_so_def [THEN iffD1, elim_format, rule_format]
lemmas wr_soD = wr_so_def [THEN iffD1, rule_format]

lemma wr_so_kvs_init [simp, intro]: "wr_so kvs_init"
  by (intro wr_soI) (auto simp add: kvs_init_defs full_view_def)


definition ww_so :: "('v, 'm) kvs_store \<Rightarrow> bool" where
  "ww_so K \<longleftrightarrow> (\<forall>k t t'. \<forall>i \<in> full_view (K k). \<forall>j \<in> full_view (K k).
                  t = v_writer (K k!i) \<longrightarrow> t' = v_writer (K k!j) \<longrightarrow> i < j \<longrightarrow> (t', t) \<notin> SO^=)"

lemmas ww_soI = ww_so_def [THEN iffD2, rule_format]
lemmas ww_soE [elim] = ww_so_def [THEN iffD1, elim_format, rule_format]
lemmas ww_soD = ww_so_def [THEN iffD1, rule_format]

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

lemma vl_writers_nil [simp]: 
  "vl_writers [] = {}"
  by (simp add: vl_writers_def)

lemma vl_writers_cons [simp]:
  "vl_writers (vrs # vl) = insert (v_writer vrs) (vl_writers vl)"
  by (simp add: vl_writers_def)

lemma vl_writers_append [simp]: 
  "vl_writers (vl @ vl') = vl_writers vl \<union> vl_writers vl'"
  by (auto simp add: vl_writers_def)

lemma vl_readers_nil [simp]: "vl_readers [] = {}"
  by (simp add: vl_readers_def)

lemma vl_readers_cons [simp]: 
  "vl_readers (vrs # vl) = v_readerset vrs \<union> vl_readers vl"
  by (simp add: vl_readers_def)

lemma vl_readers_append [simp]: 
  "vl_readers (vl @ vl') = vl_readers vl \<union> vl_readers vl'"
  by (simp add: vl_readers_def)


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

lemma vl_writers_sqns_nil [simp]:
  "vl_writers_sqns [] cl = {}"
  by (simp add: vl_writers_sqns_def)

lemma vl_writers_sqns_cons [simp]:
  "vl_writers_sqns (vers # vl) cl = {n. Tn (Tn_cl n cl) = v_writer vers} \<union> vl_writers_sqns vl cl"
  by (auto simp add: vl_writers_sqns_def)

lemma vl_writers_sqns_append [simp]:
  "vl_writers_sqns (vl @ vl') cl = vl_writers_sqns vl cl \<union> vl_writers_sqns vl' cl"
  by (auto simp add: vl_writers_sqns_def)

lemma vl_readers_sqns_nil [simp]:
  "vl_readers_sqns [] cl = {}"
  by (simp add: vl_readers_sqns_def)

lemma vl_readers_sqns_cons [simp]:
  "vl_readers_sqns (vers # vl) cl = {n. Tn_cl n cl \<in> v_readerset vers} \<union> vl_readers_sqns vl cl"
  by (auto simp add: vl_readers_sqns_def)

lemma vl_readers_sqns_append [simp]:
  "vl_readers_sqns (vl @ vl') cl = vl_readers_sqns vl cl \<union> vl_readers_sqns vl' cl"
  by (auto simp add: vl_readers_sqns_def)

(*
lemma vl_readers_sqns_from_vl_readers:  (* useful? lead to looping *)
  "vl_readers vl = vl_readers vl' \<Longrightarrow> vl_readers_sqns vl cl = vl_readers_sqns vl' cl"
  by (simp add: vl_readers_sqns_def)

lemma vl_writers_sqns_from_vl_writers:  (* useful? leads to looping *)
  "vl_writers vl = vl_writers vl' \<Longrightarrow> vl_writers_sqns vl cl = vl_writers_sqns vl' cl"
  by (simp add: vl_writers_sqns_def)
*)

text \<open>Proof rules to show reader and writer sequence number equalities with and without insert\<close>

lemma kvs_readers_sqns_eq [intro!]:
  assumes "\<And>k. vl_readers_sqns (K' k) cl = vl_readers_sqns (K k) cl"
  shows "kvs_readers_sqns K' cl = kvs_readers_sqns K cl"
  using assms
  by (simp add: kvs_readers_sqns_def)

lemma kvs_writers_sqns_eq [intro!]:
  assumes "\<And>k. vl_writers_sqns (K' k) cl = vl_writers_sqns (K k) cl"
  shows "kvs_writers_sqns K' cl = kvs_writers_sqns K cl"
  using assms
  by (simp add: kvs_writers_sqns_def)

lemma kvs_readers_sqns_eq_insert:
  assumes 
    "vl_readers_sqns (K' k) cl = insert t (vl_readers_sqns (K k) cl)"
    "\<And>k'. k' \<noteq> k 
      \<Longrightarrow> vl_readers_sqns (K' k') cl = insert t (vl_readers_sqns (K k') cl) \<or>
          vl_readers_sqns (K' k') cl = vl_readers_sqns (K k') cl"
  shows "kvs_readers_sqns K' cl = insert t (kvs_readers_sqns K cl)"
  using assms
  by (auto simp add: kvs_readers_sqns_def intro!: UN_eq_insert_UN)

lemma kvs_writers_sqns_eq_insert:
  assumes 
    "vl_writers_sqns (K' k) cl = insert t (vl_writers_sqns (K k) cl)"
    "\<And>k'. k' \<noteq> k 
      \<Longrightarrow> vl_writers_sqns (K' k') cl = insert t (vl_writers_sqns (K k') cl) \<or>
          vl_writers_sqns (K' k') cl = vl_writers_sqns (K k') cl"
  shows "kvs_writers_sqns K' cl = insert t (kvs_writers_sqns K cl)"
  using assms
  by (auto simp add: kvs_writers_sqns_def intro!: UN_eq_insert_UN)


\<comment> \<open>txid freshness lemmas\<close>

lemma fresh_txid_v_writer:
  assumes "t \<in> next_txids K cl"
    and "i \<in> full_view (K k)"
  shows "v_writer (K k!i) \<noteq> Tn t"
  using assms nth_mem
  apply (auto 4 3 simp add: fresh_txid_defs image_iff full_view_def)
  by (fastforce)

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


subsubsection \<open>View order\<close>

definition view_order (infix "\<sqsubseteq>" 60) where
  "u1 \<sqsubseteq> u2 \<equiv> \<forall>k. u1 k \<subseteq> u2 k"

lemma view_order_refl [simp]: "u \<sqsubseteq> u"
  by (simp add: view_order_def)

lemma view_order_trans: "\<lbrakk> u1 \<sqsubseteq> u2; u2 \<sqsubseteq> u3 \<rbrakk> \<Longrightarrow> u1 \<sqsubseteq> u3"
  by (auto simp add: view_order_def)

lemma view_order_full_view_increasing:
  assumes "length o K \<le> length o K'"
  shows "(full_view o K) \<sqsubseteq> (full_view o K')"
  using assms
  by (auto simp add: full_view_def view_order_def dest: le_funD)


subsubsection \<open>View well-formedness\<close>

text \<open>View in range\<close>

definition key_view_in_range :: "('v, 'm) vs_list \<Rightarrow> key_view \<Rightarrow> bool" where
  "key_view_in_range vl uk \<equiv> 0 \<in> uk \<and> uk \<subseteq> full_view vl"

definition view_in_range :: "('v, 'm) kvs_store \<Rightarrow> view \<Rightarrow> bool" where
  "view_in_range K u \<equiv> \<forall>k. key_view_in_range (K k) (u k)"

lemmas view_in_range_defs = view_in_range_def key_view_in_range_def

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


text \<open>Atomic views\<close>

definition view_atomic :: "('v, 'm) kvs_store \<Rightarrow> view \<Rightarrow> bool" where
  "view_atomic K u \<longleftrightarrow> (\<forall>k k'. \<forall>i \<in> full_view (K k). \<forall>i' \<in> full_view (K k').
      v_writer (K k!i) = v_writer (K k'!i') \<longrightarrow> i \<in> u k \<longrightarrow> i' \<in> u k')"

lemmas view_atomicI = view_atomic_def [THEN iffD2, rule_format]
lemmas view_atomicE [elim] = view_atomic_def [THEN iffD1, elim_format, rule_format]
(* lemmas view_atomicD = view_atomic_def [THEN iffD1, rule_format, unfolded view_atomic_def] *)

lemma view_atomic_full_view [simp]: "view_atomic K (full_view o K)"
  by (simp add: view_atomic_def)


text \<open>View well-formedness\<close>

definition view_wellformed :: "('v, 'm) kvs_store \<Rightarrow> view \<Rightarrow> bool" where
  "view_wellformed K u \<longleftrightarrow> view_in_range K u \<and> view_atomic K u"

lemmas view_wellformedI = view_wellformed_def [THEN iffD2, OF conjI]
lemmas view_wellformedE [elim] = view_wellformed_def [THEN iffD1, elim_format]
(*
lemmas view_wellformedD1 [dest] = view_wellformed_def [THEN iffD1, THEN conjunct1]
lemmas view_wellformedD2 [dest] = view_wellformed_def [THEN iffD1, THEN conjunct2]
*)

lemmas view_wellformed_defs = 
  view_wellformed_def view_in_range_defs view_atomic_def 

lemma full_view_wellformed:
  assumes "\<And>k. K k \<noteq> []"
  shows "view_wellformed K (full_view o K)"
  using assms
  by (auto simp add: view_wellformed_defs kvs_initialized_def)


subsubsection \<open>Version and KVS orders\<close>

text \<open>Version order\<close>

definition version_order :: "('v, 'm) version_scheme \<Rightarrow> ('v, 'm) version_scheme \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r" 60) where
  "v1 \<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r v2 \<longleftrightarrow>
    v_value v1 = v_value v2 \<and>
    v_writer v1 = v_writer v2 \<and>
    v_readerset v1 \<subseteq> v_readerset v2"

lemma version_order_refl [simp]: "v \<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r v" 
  by (simp add: version_order_def)

lemma version_order_trans: "v1 \<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r v2 \<Longrightarrow> v2 \<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r v3 \<Longrightarrow> v1 \<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r v3"
  by (auto simp add: version_order_def)


text \<open>Version list order\<close>

definition vlist_order :: "('v, 'm) vs_list \<Rightarrow> ('v, 'm) vs_list \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>v\<^sub>l" 60) where
  "vl1 \<sqsubseteq>\<^sub>v\<^sub>l vl2 \<longleftrightarrow> full_view vl1 \<subseteq> full_view vl2 \<and> (\<forall>i \<in> full_view vl1. vl1!i \<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r vl2!i)"

lemma vlist_order_refl [simp]: "vl \<sqsubseteq>\<^sub>v\<^sub>l vl" 
  by (simp add: vlist_order_def)

lemma vlist_order_trans: "\<lbrakk> vl1 \<sqsubseteq>\<^sub>v\<^sub>l vl2; vl2 \<sqsubseteq>\<^sub>v\<^sub>l vl3 \<rbrakk> \<Longrightarrow> vl1 \<sqsubseteq>\<^sub>v\<^sub>l vl3"
  by (meson dual_order.trans in_mono version_order_trans vlist_order_def)


text \<open>KVS order\<close>

definition kvs_expands :: "('v, 'm) kvs_store \<Rightarrow> ('v, 'm) kvs_store \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s" 60) where
  "K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K2 \<longleftrightarrow> (\<forall>k. K1 k \<sqsubseteq>\<^sub>v\<^sub>l K2 k) \<and> view_atomic K2 (full_view o K1)"

lemmas kvs_expandsI = kvs_expands_def[THEN iffD2, OF conjI]  (* why isn't rule_format doing this?*)

lemma kvs_expandsE [elim]: 
  "\<lbrakk> K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K2; 
     \<lbrakk> \<And>k. (K1 k) \<sqsubseteq>\<^sub>v\<^sub>l (K2 k); view_atomic K2 (full_view o K1) \<rbrakk> \<Longrightarrow> P \<rbrakk> 
   \<Longrightarrow> P"
  by (simp add: kvs_expands_def)


lemma kvs_expands_refl [simp]: "K \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K"
  by (simp add: kvs_expands_def)

lemma kvs_expands_trans: 
  assumes "K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K2" and "K2 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K3"
  shows "K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K3"
  using assms
proof (intro kvs_expandsI allI)
  show "view_atomic K3 (full_view \<circ> K1)" using assms
    by (intro view_atomicI)     (* MAYBE PROVE LEMMAS ABOUT view_atomic? *)
       (smt (verit) comp_def full_view_length_increasing full_view_subset_is_length_leq 
            kvs_expands_def version_order_def view_atomic_def vlist_order_def)
qed (auto intro: vlist_order_trans)

(*
lemma kvs_expands_length_increasing:
  "K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K2 \<Longrightarrow> length (K1 k) \<le> length (K2 k)"
  by (simp add: kvs_expands_def vlist_order_def)

lemma kvs_expands_still_in_full_view:
  "K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K2 \<Longrightarrow> i \<in> full_view (K1 k) \<Longrightarrow> i \<in> full_view (K2 k)"
  using full_view_length_increasing kvs_expands_length_increasing by blast
*)

lemma kvs_expands_view_in_range:
  assumes 
    "K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K2" 
    "view_in_range K1 u" 
  shows 
    "view_in_range K2 u"
  using assms
  by (auto simp add: view_in_range_defs kvs_expands_def vlist_order_def)

lemma kvs_expands_view_atomic:
  assumes 
    "K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K2" 
    "view_wellformed K1 u"
  shows 
    "view_atomic K2 u"
  using assms
proof (intro view_atomicI, elim view_wellformedE conjE)
  fix i i' k k'
  assume 
    \<open>view_atomic K1 u\<close> \<open>view_in_range K1 u\<close> 
    \<open>K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K2\<close> 
    \<open>i' \<in> full_view (K2 k')\<close>
    \<open>v_writer (K2 k ! i) = v_writer (K2 k' ! i')\<close> 
    \<open>i \<in> u k\<close>  
  have \<open>view_atomic K2 (full_view \<circ> K1)\<close> \<open>full_view (K1 k) \<subseteq> full_view (K2 k)\<close> 
    using \<open>K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K2\<close> 
    by (simp_all add: kvs_expands_def vlist_order_def)
  then have \<open>i \<in> full_view (K1 k)\<close> \<open>i \<in> full_view (K2 k)\<close> 
    using \<open>i \<in> u k\<close> \<open>view_in_range K1 u\<close> \<open>full_view (K1 k) \<subseteq> full_view (K2 k)\<close> 
    by (auto simp add: view_in_range_defs)
  then have \<open>i' \<in> full_view (K1 k')\<close> 
    using \<open>i' \<in> full_view (K2 k')\<close> \<open>view_atomic K2 (full_view \<circ> K1)\<close> 
          \<open>v_writer (K2 k ! i) = v_writer (K2 k' ! i')\<close> 
    by (unfold view_atomic_def) (drule spec[where x=k], auto)  \<comment> \<open>instance needed, simp loops\<close>   
  moreover
  have \<open>v_writer (K2 k ! i) = v_writer (K1 k ! i)\<close> 
    using \<open>i \<in> full_view (K1 k)\<close> \<open>K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K2\<close> 
    by (simp add: kvs_expands_def vlist_order_def version_order_def)
  moreover
  have \<open>v_writer (K2 k' ! i') = v_writer (K1 k' ! i')\<close> 
    using \<open>i' \<in> full_view (K1 k')\<close> \<open>K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K2\<close> 
    by (simp add: kvs_expands_def vlist_order_def version_order_def)
  ultimately
  show \<open>i' \<in> u k'\<close> 
    using \<open>i \<in> full_view (K1 k)\<close>
          \<open>view_atomic K1 u\<close> 
          \<open>v_writer (K2 k ! i) = v_writer (K2 k' ! i')\<close> \<open>i \<in> u k\<close>
    by (unfold view_atomic_def) (drule spec[where x=k], auto)   \<comment> \<open>instance needed, simp loops\<close> 
qed

lemma kvs_expands_view_wellformed:
  assumes 
    "K1 \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K2"  
    "view_wellformed K1 u" 
  shows 
    "view_wellformed K2 u"
  using assms
  by (auto simp add: view_wellformed_def elim: kvs_expands_view_in_range kvs_expands_view_atomic)


\<comment> \<open>List updates and membership lemmas\<close>

(* chsp: these lemmas seem really low-level; do we need them all? *)

thm set_update   (* check whether this subsumes some lemmas below *)

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
  assumes "f a \<notin> f ` A"
  shows "a \<notin> A"
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

(*
lemma longer_list_not_empty:
  "vl \<noteq> [] \<Longrightarrow> length vl \<le> length vl' \<Longrightarrow> vl' \<noteq> []"
  by auto
*)

subsection \<open>Snapshots\<close>

(* REMOVE last_version? *)

abbreviation last_version :: "('v, 'm) vs_list \<Rightarrow> key_view \<Rightarrow> ('v, 'm) version_scheme" where
  "last_version vl uk \<equiv> vl ! Max uk"

\<comment> \<open>Lemmas about last_version\<close>

lemma [simp]: "last_version [v] {..<Suc 0} = v"   (* REMOVE? seems very specialized *)
  by (auto simp add: lessThan_def)


type_synonym 'v snapshot = "key \<Rightarrow> 'v"

definition view_snapshot :: "('v, 'm) kvs_store \<Rightarrow> view \<Rightarrow> 'v snapshot" where
  "view_snapshot K u k \<equiv> v_value (last_version (K k) (u k))"


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

lemma fp_property_write_only_fp: "fp_property (write_only_fp kv_map) K u"
  by (auto simp add: fp_property_def)


subsection \<open>KVS updates\<close>

fun update_kv_key_reads :: "txid0 \<Rightarrow> 'v option \<Rightarrow> key_view \<Rightarrow> ('v, 'm) vs_list \<Rightarrow> ('v, 'm) vs_list" where
  "update_kv_key_reads t None uk vl = vl" |
  "update_kv_key_reads t (Some _) uk vl = 
     (let lv = last_version vl uk in vl[Max uk := lv\<lparr>v_readerset := insert t (v_readerset lv)\<rparr>])"

fun update_kv_key_writes :: "txid0 \<Rightarrow> 'v option \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_key_writes t None vl = vl" |
  "update_kv_key_writes t (Some v) vl = vl @ [new_vers (Tn t) v]"

definition update_kv_key :: "txid0 \<Rightarrow> 'v key_fp \<Rightarrow> key_view \<Rightarrow> 'v v_list \<Rightarrow> 'v v_list" where
  "update_kv_key t Fk uk = update_kv_key_writes t (Fk W) o update_kv_key_reads t (Fk R) uk"

definition update_kv :: "txid0 \<Rightarrow> 'v fingerpr \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> 'v kv_store" where
  "update_kv t F u K = (\<lambda>k. update_kv_key t (F k) (u k) (K k))"

(*
lemmas update_kv_key_reads_defs = Let_def
*)
lemmas update_kv_defs = update_kv_def update_kv_key_def


subsubsection \<open>Lemmas about length of updates\<close>

lemma length_update_kv_key_reads [simp]:
  "length (update_kv_key_reads t vo uk vl) = length vl"
  by (cases vo) (simp_all add: Let_def)

lemma length_update_kv_key_writes [simp]:
  "length (update_kv_key_writes t vo vl) = (if vo = None then length vl else Suc (length vl))"
  by (auto)

lemma length_update_kv_key [simp]:
  "length (update_kv_key t Fk uk vl) = (if Fk W = None then length vl else Suc (length vl))"
  by (simp add: update_kv_key_def)

lemma length_update_kv [simp]:
  "length (update_kv t F u K k) = (if F k W = None then length (K k) else Suc (length (K k)))"
  by (simp add: update_kv_def)


subsubsection \<open>Lemmas about full view of updates\<close>

lemma full_view_update_kv_key_reads [simp]:
  "full_view (update_kv_key_reads t Fk uk vl) = full_view vl"
  by (simp add: full_view_eq_is_length_eq)

lemma full_view_update_kv_key_writes [dest]:
  "i \<in> full_view vl \<Longrightarrow> i \<in> full_view (update_kv_key_writes t Fk vl)"
  by (simp add: full_view_def)

lemma full_view_update_kv_incl [dest]:
  "i \<in> full_view (K k) \<Longrightarrow> i \<in> full_view (update_kv t F u K k)"
  by (simp add: full_view_def)


lemma full_view_update_kv_key_no_write [simp]:     (* remove from simp set? *)
  assumes "Fk W = None"
  shows "full_view (update_kv_key t Fk uk vl) = full_view vl"
  using assms
  by (simp add: full_view_eq_is_length_eq)

lemma full_view_update_kv_key_write [simp]:     (* remove from simp set? *)
  assumes "Fk W \<noteq> None"
  shows "full_view (update_kv_key t Fk uk vl) = insert (length vl) (full_view vl)"
  using assms
  by (auto simp add: update_kv_key_def)

lemma full_view_update_kv:                   (* add to simp set? NO. *)
  "full_view (update_kv t F u K k) = 
   (if F k W = None then full_view (K k) else insert (length (K k)) (full_view (K k)))"
  by (simp add: update_kv_def)


subsubsection \<open>Accessing updated version lists\<close>   (* where used?*)

text \<open>Reads\<close>

lemma update_kv_key_reads_not_latest:
  assumes "i \<noteq> Max uk"
  shows "update_kv_key_reads t vo uk vl!i = vl!i"
  using assms
  by  (cases vo) (simp_all add: Let_def)

lemma update_kv_key_reads_latest:
  assumes "i = Max uk" "i \<in> full_view vl" "vo = Some v"
  shows "update_kv_key_reads t vo uk vl!i = (vl!i)\<lparr>v_readerset := insert t (v_readerset (vl!i))\<rparr>"
  using assms
  by (simp add: Let_def)

text \<open>Note: case of no read, @{prop "vo = None"} goes by simp.\<close>

lemmas update_kv_key_reads_simps = 
   update_kv_key_reads_latest update_kv_key_reads_not_latest 


text \<open>Writes\<close>

lemma update_kv_key_writes_old:
  assumes "i \<in> full_view vl" 
  shows "update_kv_key_writes t vo vl!i = vl!i"
  using assms
  by (cases vo) auto

text \<open>Note: cases of no write and accessing last write go by simp.\<close>

(* redundant, goes by simp

lemma update_kv_key_writes_new:
  assumes "i = length vl" "vo = Some v" 
  shows "update_kv_key_writes t vo vl!i = new_vers (Tn t) v"
  using assms
  by simp
*)

lemmas update_kv_key_writes_simps = update_kv_key_writes_old


text \<open>Reads and writes\<close>

lemma update_kv_key_nop [simp]:
  assumes "Fk W = None" "Fk R = None" 
  shows "update_kv_key t Fk uk vl = vl"
  using assms
  by (simp add: update_kv_key_def)

lemma update_kv_key_read_only:
  "update_kv_key t (case_op_type ro None) uk vl = 
   (case ro of None \<Rightarrow> vl
    | Some v \<Rightarrow> (let lv = last_version vl uk in
                  vl[Max uk := lv\<lparr>v_readerset := insert t (v_readerset lv)\<rparr>]))"
  by (auto simp add: update_kv_key_def split: option.split)

lemma update_kv_key_write_only:
  "update_kv_key t (case_op_type None wo) uk vl = 
   (case wo of None \<Rightarrow> vl | Some v \<Rightarrow> vl @ [new_vers (Tn t) v])"
   by (auto simp add: update_kv_key_def split: option.split)

lemma update_kv_key_old_no_read:
  assumes "i \<in> full_view vl" "Fk R = None" 
  shows "update_kv_key t Fk uk vl!i = vl!i"
  using assms
  by (simp add: update_kv_key_def update_kv_key_writes_simps)

lemma update_kv_key_old_not_latest:
  assumes "i \<in> full_view vl" "i \<noteq> Max uk"
  shows "update_kv_key t Fk uk vl!i = vl!i"
  using assms
  by (simp add: update_kv_key_def update_kv_key_writes_simps update_kv_key_reads_simps)

lemma update_kv_key_old_latest:
  assumes "i \<in> full_view vl" "i = Max uk" "Fk R = Some v" 
  shows "update_kv_key t Fk uk vl!i = (vl!i)\<lparr>v_readerset := insert t (v_readerset (vl!i))\<rparr>"
  using assms
  by (simp add: update_kv_key_def Let_def update_kv_key_writes_simps)

lemma update_kv_key_new:
  assumes "i = length vl" "Fk W = Some v" 
  shows "update_kv_key t Fk uk vl!i = new_vers (Tn t) v"
  using assms
  by (simp add: update_kv_key_def update_kv_key_writes_simps update_kv_key_reads_simps 
                nth_append_length')

lemmas update_kv_key_simps = 
  update_kv_key_old_no_read update_kv_key_old_latest update_kv_key_old_not_latest update_kv_key_new

(* TODO: check whether to add to update_kv_key_simps above *)

lemma update_kv_key_ro_set_v_readerset:
  assumes "Fk W = None" and "vl \<noteq> []"
  shows "(update_kv_key t Fk (full_view vl) vl) [Max (full_view vl) :=
    last_version (update_kv_key t Fk (full_view vl) vl) (full_view vl) \<lparr> v_readerset := x \<rparr>] =
    vl [Max (full_view vl) := last_version vl (full_view vl) \<lparr> v_readerset := x \<rparr>]"
  using assms
  by (cases "Fk R") (simp_all add: update_kv_key_def Let_def)


text \<open>KVS\<close>

lemma update_kv_empty:
  "update_kv t F u K k = [] \<Longrightarrow> K k = []"
  using length_update_kv[of t F u K k]
  by (simp split: if_split_asm)

lemma update_kv_old_nop [simp]:
  assumes "F k W = None" "F k R = None"
  shows "update_kv t F u K k = K k"
  using assms
  by (simp add: update_kv_def)

lemma update_kv_read_only:
  "update_kv t (read_only_fp kv_map) u K k = 
   (case kv_map k of
     None \<Rightarrow> K k |
     Some v \<Rightarrow> (let lv = last_version (K k) (u k) in
                (K k) [Max (u k) := lv\<lparr>v_readerset := insert t (v_readerset lv)\<rparr>]))"
  by (simp add: update_kv_def read_only_fp_def update_kv_key_read_only)

lemma update_kv_write_only:
  "update_kv t (write_only_fp kv_map) u K k = 
   (case kv_map k of None \<Rightarrow> K k | Some v \<Rightarrow> K k @ [new_vers (Tn t) v])"
  by (simp add: update_kv_def write_only_fp_def update_kv_key_write_only)

lemma update_kv_old_no_read:
  assumes "i \<in> full_view (K k)" "F k R = None"
  shows "update_kv t F u K k!i = K k!i"
  using assms
  by (simp add: update_kv_def update_kv_key_simps)

lemma update_kv_old_not_latest:
  assumes "i \<in> full_view (K k)" "i \<noteq> Max (u k)"
  shows "update_kv t F u K k!i = K k!i"
  using assms
  by (simp add: update_kv_def update_kv_key_simps)

lemma update_kv_old_latest:
  assumes "i \<in> full_view (K k)" "i = Max (u k)" "F k R = Some v"
  shows "update_kv t F u K k!i = (K k!i)\<lparr>v_readerset := insert t (v_readerset (K k!i))\<rparr>"
  using assms
  by (simp add: update_kv_def update_kv_key_simps)

lemma update_kv_new:
  assumes "i = length (K k)" "F k W = Some v"
  shows "update_kv t F u K k!i = new_vers (Tn t) v"
  using assms
  by (simp add: update_kv_def update_kv_key_simps)

lemmas update_kv_simps =
  update_kv_old_no_read update_kv_old_not_latest update_kv_old_latest update_kv_new





subsubsection \<open>Lemmas about version value\<close>

(* v_value *)
lemma update_kv_key_reads_v_value_inv:
  assumes "i \<in> full_view vl"
  shows "v_value (update_kv_key_reads t vo uk vl ! i) = v_value (vl ! i)"
  using assms
  by (cases vo) (simp_all add: Let_def)

lemma update_kv_key_v_value_inv:
  assumes "i \<in> full_view vl"
  shows "v_value (update_kv_key t Fk uk vl ! i) = v_value (vl ! i)"
  using assms
  by (auto simp add: update_kv_key_def update_kv_key_writes_simps update_kv_key_reads_v_value_inv)

lemma update_kv_v_value_inv:
  assumes "i \<in> full_view (K k)"
  shows "v_value (update_kv t F u K k ! i) = v_value (K k ! i)"
  using assms
  by (auto simp add: update_kv_def update_kv_key_v_value_inv)

lemmas update_kv_v_value_simps = update_kv_v_value_inv


subsubsection \<open>Lemmas about version writer\<close>

(* v_writer *)
lemma update_kv_key_reads_v_writer_old:
  assumes "i \<in> full_view vl"
  shows "v_writer (update_kv_key_reads t vo uk vl!i) = v_writer (vl!i)"
  using assms
  by (cases vo) (simp_all add: Let_def)

lemma update_kv_v_writer_old: 
  assumes "i \<in> full_view (K k)"
  shows "v_writer (update_kv t F u K k!i) = v_writer (K k!i)"
  using assms
  by (auto simp add: update_kv_defs update_kv_key_writes_simps update_kv_key_reads_v_writer_old)

lemma update_kv_v_writer_new: 
  assumes "i = length (K k)" "F k W = Some v"
  shows "v_writer (update_kv t F u K k!i) = Tn t"
  using assms
  by (auto simp add: update_kv_simps)

lemmas update_kv_v_writer_simps = 
  update_kv_v_writer_old update_kv_v_writer_new

(*  REPLACE PREMISES IN LEMMAS BELOW? (with sth about fingerprint)

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
*)


(*
lemma update_kv_key_reads_vl_writers_inv [simp]:
  "vl_writers (update_kv_key_reads t Fk uk vl) = vl_writers vl"
  apply (auto simp add: update_kv_key_reads_defs vl_writers_def in_set_conv_nth split: option.split)
  subgoal for y i by (cases "i = Max uk"; simp)
  subgoal for y i apply (cases "i = Max uk"; auto simp add: image_iff)
    apply (metis set_update_memI version.select_convs(2) version.surjective version.update_convs(3))
    by (metis length_list_update nth_list_update_neq nth_mem)
  done
*)


subsubsection \<open>Lemmas about version reader set\<close>

(* SUBSUMED BY NEXT LEMMA
lemma v_readerset_update_kv_key_reads_max_u':
  assumes "x \<in> v_readerset (update_kv_key_reads t vo uk vl!i)"
      and "i \<in> full_view vl" and "i = Max uk" 
    shows "x \<in> v_readerset (vl!i) \<or> x = t"
  using assms
  by (auto simp add: v_readerset_update_kv_key_reads_max_u split: if_split_asm)
*)

lemma v_readerset_update_kv_key_reads_max_u:
  assumes "i \<in> full_view vl" and "i = Max uk" 
  shows "v_readerset (update_kv_key_reads t vo uk vl!i) =
         (if vo = None then v_readerset (vl!i) else insert t (v_readerset (vl!i)))"
  using assms
  by (auto simp add: Let_def)

lemma v_readerset_update_kv_key_reads_not_max:
  assumes "i \<in> full_view vl" and "i \<noteq> Max uk"
  shows "v_readerset (update_kv_key_reads t vo uk vl!i) = v_readerset (vl!i)"
  using assms
  by (cases vo) (auto simp add: Let_def)

lemma v_readerset_update_kv_key_writes:
  assumes "i \<in> full_view vl \<or> vo = None"
  shows "v_readerset (update_kv_key_writes t vo vl!i) = v_readerset (vl!i)"
  using assms
  by (cases vo) (simp_all)

(* redundant (goes by simp): 
lemma v_readerset_update_kv_key_writes_new:
  assumes "i = length vl" "vo = Some v"
  shows "v_readerset (update_kv_key_writes t vo vl!i) = {}"
  using assms
  by (simp)
*)

lemma v_readerset_update_kv_old:
  assumes "i \<in> full_view (K k)"
  shows "v_readerset (update_kv t F u K k ! i) =
         (if i \<noteq> Max (u k) \<or> F k R = None 
          then v_readerset (K k!i) else insert t (v_readerset (K k!i)))"
  using assms
  by (auto simp add: update_kv_defs v_readerset_update_kv_key_writes 
                     v_readerset_update_kv_key_reads_not_max Let_def)

lemma v_readerset_update_kv_new:
  assumes "i = length (K k)" "F k W = Some v"
  shows "v_readerset (update_kv t F u K k!i) = {}"
  using assms
  by (simp add: update_kv_defs nth_append_length')

lemmas v_readerset_update_kv_simps = 
  v_readerset_update_kv_old v_readerset_update_kv_new


(* INTEGRATE TWO LEMMAS BELOW: *)

(* new lemma *)
lemma v_readerset_update_kv_reads_subset_insert:
  assumes "i \<in> full_view vl"
    shows "v_readerset (update_kv_key_reads t vo uk vl!i) \<subseteq> insert t (v_readerset (vl!i))"
  using assms
  by (metis subset_insertI update_kv_key_reads_not_latest 
            v_readerset_update_kv_key_reads_max_u verit_comp_simplify1(2))

(* new lemma *)
lemma v_readerset_update_kv_reads_subset:
  assumes "i \<in> full_view vl"
    shows "v_readerset (vl!i) \<subseteq> v_readerset (update_kv_key_reads t vo uk vl!i)"
proof (cases vo)
  case (Some a)
  then show ?thesis apply (auto simp add: Let_def)
    by (metis Un_absorb Un_insert_right assms expanding_feature3)
qed (simp)



(* new lemma *)
lemma view_stays_atomic:
  assumes "t \<in> next_txids K cl"
  shows "view_atomic (update_kv t F u K) (\<lambda>k. full_view (K k))"
  using assms
  apply (simp add: view_atomic_def)
  by (metis fresh_txid_v_writer full_view_update_kv insertE not_None_eq 
            update_kv_v_writer_new update_kv_v_writer_old)

(* new lemma *)
lemma kvs_expands_through_update:
  assumes "K' = update_kv t F u K"
    and "t \<in> next_txids K cl"
  shows "K \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s K'"
  using assms
  apply (auto simp add: kvs_expands_def vlist_order_def update_kv_defs version_order_def
                        update_kv_key_reads_v_value_inv update_kv_key_reads_v_writer_old 
                        update_kv_key_writes_simps)
  apply (metis (no_types, lifting) in_mono v_readerset_update_kv_reads_subset)
  by (metis (mono_tags, lifting) assms(1) comp_apply view_atomic_def view_stays_atomic)


text \<open>Other lemmas: case analyses, ...\<close>

lemma v_readerset_update_kv_old_cases:
  assumes "t' \<in> v_readerset (update_kv t F u K k ! i)" and "i \<in> full_view (K k)"
  shows "t' = t \<or> t' \<in> v_readerset (K k!i)"
  using assms
  by (simp add: v_readerset_update_kv_old split: if_split_asm)

lemma update_kv_key_ro_v_readerset [simp]:        (* REMOVE from simpset? *)
  assumes "Fk W = None" and "Fk R = Some v"
    and "vl \<noteq> []"
  shows "v_readerset (last_version (update_kv_key t Fk (full_view vl) vl) (full_view vl)) =
         insert t (v_readerset (last_version vl (full_view vl)))"
  using assms
  by (simp add: update_kv_key_def Let_def)


lemmas update_kv_version_field_simps = 
  update_kv_v_value_simps update_kv_v_writer_simps v_readerset_update_kv_simps


(* SUBSUMED BY LEMMA v_readerset_update_kv_old_cases (modulo if_split_asm):

lemma v_readerset_update_kv_max_u:
  assumes "x \<in> v_readerset (update_kv t F u K k ! Max (u k))"
      and "view_in_range K u"
    shows "x \<in> v_readerset (K k ! Max (u k)) \<or> x = t"
  using assms
  by (auto simp add: v_readerset_update_kv split: if_split_asm)

  by (auto simp add: update_kv_defs v_readerset_update_kv_key_writes
           dest: v_readerset_update_kv_key_reads_max_u)
*)

(* REDUNDANT: use update_kv_nth_version

lemma v_readerset_update_kv_rest_inv:
  assumes "i \<in> full_view (K k)" and "i \<noteq> Max (u k)" 
  shows "v_readerset (update_kv t F u K k!i) = v_readerset (K k!i)"
  using assms
  by (simp add: update_kv_nth_version)
*)

(* REPLACE BY STH WITH DIFFERENT PREMISES?:

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
*)


subsubsection \<open>Lemmas about readers, writers, and all txids\<close>

text \<open>Writers\<close>

lemma vl_writers_update_kv_key_writes [simp]:
  "vl_writers (update_kv_key_writes t vo vl) = 
   (if vo = None then vl_writers vl else insert (Tn t) (vl_writers vl))"
  by (auto simp add: vl_writers_def)

lemma vl_writers_update_kv_key_reads [simp]:
  "vl_writers (update_kv_key_reads t vo uk vl) = vl_writers vl"  
  apply (cases vo)
   apply (auto simp add: Let_def vl_writers_def)
   apply (metis (mono_tags, lifting) image_iff list_update_beyond nth_mem the_update 
                verit_comp_simplify1(3) version.select_convs(2) version.surjective 
                version.update_convs(3))
  by (metis (mono_tags, lifting) image_iff in_set_after_update list_update_beyond set_update_memI 
      verit_comp_simplify1(3) version.select_convs(2) version.surjective version.update_convs(3))

lemma kvs_writers_update_kv:
  "kvs_writers (update_kv t F u K) = 
   (if \<forall>k. F k W = None then kvs_writers K else insert (Tn t) (kvs_writers K))"
  by (auto 4 3 simp add: update_kv_def update_kv_key_def kvs_writers_def)

text \<open>Readers\<close>

lemma vl_readers_update_kv_key_writes [simp]:
  "vl_readers (update_kv_key_writes t vo vl) = vl_readers vl"
  by (cases vo) (simp_all add: vl_readers_def)

lemma vl_readers_update_kv_key_reads [simp]:
  assumes "vo = None \<or> Max uk < length vl"        (* FIX: MODIFY PREMISE [Done] *)
  shows "vl_readers (update_kv_key_reads t vo uk vl) = 
         (if vo = None then vl_readers vl else insert t (vl_readers vl))"
  using assms
  by (auto simp add: vl_readers_def Let_def set_update) (metis in_set_conv_nth)

lemma vl_readers_update_kv_key_reads_full_view [simp]:
  "vl \<noteq> [] \<Longrightarrow> 
   vl_readers (update_kv_key_reads t vo (full_view vl) vl) =
   (if vo = None then vl_readers vl else insert t (vl_readers vl))"
  by (simp add: full_view_elemD)

lemma kvs_readers_update_kv:
  assumes "\<And>k. fp k R = None \<or> Max (u k) < length (K k)"   (* FIX: MODIFY PREMISE [Done] *)
  shows "kvs_readers (update_kv t fp u K) = 
         (if \<forall>k. fp k R = None then kvs_readers K else insert t (kvs_readers K))"
  using assms
  by (auto 4 3 simp add: update_kv_def update_kv_key_def kvs_readers_def) 

(*
text \<open>Useful special case of above; simp does not prove it directly [now it does].\<close>

lemma kvs_readers_update_kv_write_only:
  "kvs_readers (update_kv t (write_only_fp kv_map) u K) = kvs_readers K"
  by (simp add: kvs_readers_update_kv)
*)

text \<open>All txids in KVS\<close>

lemma kvs_txids_update_kv: 
  assumes "\<And>k. fp k R = None \<or> Max (u k) < length (K k)" 
  shows "kvs_txids (update_kv t fp u K) = 
         (if \<forall>k. fp k = Map.empty then kvs_txids K else insert (Tn t) (kvs_txids K))"
  using assms
  by (auto simp add: kvs_txids_def kvs_writers_update_kv kvs_readers_update_kv del: equalityI)
     (metis (full_types) op_type.exhaust)

(*
text \<open>Useful special case of above; simp does not prove it directly [now it does].\<close>

lemma kvs_txids_update_kv_write_only:       
  "kvs_txids (update_kv t (write_only_fp kv_map) u K) = 
   (if \<forall>k. kv_map k = None then kvs_txids K else insert (Tn t) (kvs_txids K))"
  by (simp add: kvs_txids_update_kv)
*)

text \<open>Other lemmas\<close>   (* move up *)

lemma v_writer_in_kvs_writers:
  "i < length (K k) \<Longrightarrow> v_writer (K k ! i) \<in> kvs_writers K"
  by (auto simp add: kvs_writers_def vl_writers_def intro: exI[where x=k])

lemma v_writer_in_kvs_txids:
  "i < length (K k) \<Longrightarrow> v_writer (K k ! i) \<in> kvs_txids K"
  by (auto simp add: kvs_txids_def v_writer_in_kvs_writers)


(* TODO: move lemma below to appropriate place*)

lemma vl_writers_sqns_update_kv_key_writes: 
  "vl_writers_sqns (update_kv_key_writes t vo vl) cl =
   (if get_cl t \<noteq> cl \<or> vo = None 
    then vl_writers_sqns vl cl else insert (get_sn t) (vl_writers_sqns vl cl))"
  by (cases t) (auto simp add: vl_writers_sqns_def)


end