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

record 'v version =
  v_value :: 'v
  v_writer :: txid
  v_readerset :: "txid0 set"

definition version_init :: "'v version" where
  "version_init \<equiv> \<lparr>v_value = undefined, v_writer = T0, v_readerset = {}\<rparr>"

type_synonym 'v kv_store = "key \<Rightarrow> 'v version list"

definition kvs_init :: "'v kv_store" where
  "kvs_init k \<equiv> [version_init]"


\<comment> \<open>predicates on kv stores\<close>

definition in_range :: "'v kv_store \<Rightarrow> key \<Rightarrow> nat set" where
  "in_range K k \<equiv> {x. x<length (K k)}"

definition snapshot_property :: "'v kv_store \<Rightarrow> bool" where
  "snapshot_property K \<equiv> \<forall>k. \<forall>i \<in> in_range K k. \<forall>j \<in> in_range K k.
                                 (v_readerset (K k!i) \<inter> v_readerset (K k!j) \<noteq> {} \<or>
                                  v_writer (K k!i) = v_writer (K k!j)) \<longrightarrow> i = j"

definition SO0 :: "txid0 rel" where
  "SO0 \<equiv> {(t, t'). \<exists>cl n m. t = Tn_cl n cl \<and> t' = Tn_cl m cl \<and> n < m}"

definition SO :: "txid rel" where
  "SO \<equiv> {(Tn t, Tn t')| t t'. (t, t') \<in> SO0}"

definition wr_so :: "'v kv_store \<Rightarrow> bool" where
  "wr_so K \<equiv> \<forall>k t t'. \<forall>i \<in> in_range K k.
              t = v_writer (K k!i) \<and> t' \<in> Tn ` v_readerset (K k!i) \<longrightarrow> (t', t) \<notin> SO^="

definition ww_so :: "'v kv_store \<Rightarrow> bool" where
  "ww_so K \<equiv> \<forall>k t t'. \<forall>i \<in> in_range K k. \<forall>j \<in> in_range K k.
              t = v_writer (K k!i) \<and> t' = v_writer (K k!j) \<and> i < j \<longrightarrow> (t', t) \<notin> SO^="

definition initialized :: "'v kv_store \<Rightarrow> bool" where
  "initialized K \<equiv> \<forall>k. v_value (K k!0) = undefined"

lemmas wellformed_defs = ww_so_def wr_so_def snapshot_property_def SO_def SO0_def initialized_def


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

lemmas view_wellformed_defs = view_wellformed_def view_in_range_def view_atomic_def

subsection \<open>Snapshots and Configs\<close>

type_synonym 'v snapshot = "key \<Rightarrow> 'v"

definition last_version :: "'v kv_store \<Rightarrow> view \<Rightarrow> key \<Rightarrow> 'v version" where
  "last_version K u k \<equiv> K k!(Max (u k))"

definition view_snapshot :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v snapshot" where
  "view_snapshot K u k \<equiv> v_value (last_version K u k)"

type_synonym 'v config = "'v kv_store \<times> (cl_id \<Rightarrow> view)"

definition c_views_init :: "cl_id \<Rightarrow> view" where
  "c_views_init _ \<equiv> view_init"

definition config_init :: "'v config" where
  "config_init \<equiv> (kvs_init, c_views_init)"

subsection \<open>Fingerprints\<close>

datatype op_type = R | W
datatype 'v op = Read key 'v | Write key 'v | Eps

type_synonym 'v fingerpr = "key \<times> op_type \<rightharpoonup> 'v"

fun update_fp :: "'v fingerpr \<Rightarrow> 'v op \<Rightarrow> 'v fingerpr" where
  "update_fp fp (Read k v)  = (if fp (k, R) = None \<and> fp (k, W) = None
                               then fp ((k, R) \<mapsto> v)
                               else fp)" |
  "update_fp fp (Write k v) = fp ((k, W) \<mapsto> v)" |
  "update_fp fp Eps         = fp"

definition update_kv_reads :: "txid0 \<Rightarrow> 'v fingerpr \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> 'v kv_store" where
  "update_kv_reads t fp u K k =
    (case fp (k, R) of
      None   \<Rightarrow> K k |
      Some v \<Rightarrow> let lv = last_version K u k in \<comment> \<open>We are ignoring v =? v_value lv\<close>
                  (K k)[Max (u k) := lv\<lparr>v_readerset := insert t (v_readerset lv)\<rparr>])"

definition update_kv_writes :: "txid0 \<Rightarrow> 'v fingerpr \<Rightarrow> 'v kv_store \<Rightarrow> 'v kv_store" where
  "update_kv_writes t fp K k =
    (case fp (k, W) of
      None   \<Rightarrow> K k |
      Some v \<Rightarrow> K k @ [\<lparr>v_value=v, v_writer=Tn t, v_readerset={}\<rparr>])"

definition update_kv :: "txid0 \<Rightarrow> 'v fingerpr \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> 'v kv_store" where
  "update_kv t fp u = (update_kv_writes t fp) o (update_kv_reads t fp u)"

lemmas update_kv_reads_defs = update_kv_reads_def Let_def last_version_def

subsection \<open>Execution Tests as Transition Systems\<close>

type_synonym 'v label = "cl_id \<times> view \<times> 'v fingerpr"

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

fun ET_cl_trans :: "('v kv_store \<times> view) \<Rightarrow> 'v fingerpr \<Rightarrow> ('v kv_store \<times> view) \<Rightarrow> bool" where
  "ET_cl_trans (K, u) F (K', u') \<longleftrightarrow>
    view_wellformed K u \<and>
    view_wellformed K u' \<and>
    (\<forall>k. (k, R) \<in> dom F \<longrightarrow> F (k, R) = Some (v_value (last_version K u k))) \<and>
    canCommit K u F \<and> vShift K u K' u'"

inductive ET_trans :: "'v config \<Rightarrow> 'v label \<Rightarrow> 'v config \<Rightarrow> bool" where
 "\<lbrakk> U cl \<sqsubseteq> u'';
    view_wellformed K (U cl);
    ET_cl_trans (K, u'') F (K', U' cl);
    t \<in> next_txids K cl;
    K' = update_kv t F u'' K \<rbrakk>
  \<Longrightarrow> ET_trans (K, U) (cl, u'', F) (K', U')"

thm "ET_trans.cases"

(*Alternatively:

fun ET_trans :: "'v config \<Rightarrow> 'v label \<Rightarrow> 'v config \<Rightarrow> bool" where
 "ET_trans (K, U) (cl, u'', F) (K', U') \<longleftrightarrow>
    U cl \<sqsubseteq> u'' \<and>
    view_wellformed K (U cl) \<and>
    ET_cl_trans (K, u'') F (K', U' cl) \<and>
    (\<exists>t \<in> next_txids K cl. K' = update_kv t F u'' K)"
declare ET_trans.simps [simp del]
*)

definition ET_ES :: "('v label, 'v config) ES" where
  "ET_ES \<equiv> \<lparr>
    init = (=) config_init,
    trans = ET_trans
  \<rparr>"

lemmas ET_ES_defs = config_init_def ET_ES_def

subsection \<open>Wellformedness Invariants and Lemmas\<close>

\<comment> \<open>view lemmas\<close>
lemma finite_view:
  assumes "view_wellformed K u"
  shows "finite (u k)"
  using assms apply (auto simp add: view_wellformed_defs)
  using finite_nat_set_iff_bounded by auto

lemma max_view_in_range:
  assumes "i = Max (u k)" and "view_wellformed K u"
  shows "i \<in> in_range K k"
proof -
  have "u k \<noteq> {}" using assms by (auto simp add: view_wellformed_defs)
  then show ?thesis using assms finite_view [of K u k] Max_less_iff
    by (auto simp add: view_wellformed_defs in_range_def)
qed

lemma zero_in_range:
  assumes "view_wellformed K u"
  shows "0 \<in> in_range K k"
  using assms
  by (auto simp add: view_wellformed_defs in_range_def)

\<comment> \<open>update_kv lemmas about version list length\<close>
lemma update_kv_reads_length:
  "length (update_kv_reads t F u K k) = length (K k)"
proof (cases "F (k, R)")
  case (Some a)
  then show ?thesis apply (auto simp add: update_kv_reads_def)
    by (meson length_list_update)
qed (auto simp add: update_kv_reads_def)

lemma update_kv_writes_length:
  shows "length (update_kv_writes t F K k) = Suc (length (K k)) \<or> 
         length (update_kv_writes t F K k) = length (K k)"
  by (cases "F (k, W)") (auto simp add: update_kv_writes_def)


lemma update_kv_length:
  shows "length (update_kv t F u K k) = Suc (length (K k)) \<or>
         length (update_kv t F u K k) = length (K k)"
  using update_kv_writes_length [where K="update_kv_reads t F u K"]
  by (simp add: update_kv_def update_kv_reads_length)

\<comment> \<open>update_kv lemmas about changing the versions\<close>
lemma update_kv_writes_version_inv:
  assumes "i \<in> in_range K k"
  shows "update_kv_writes t F K k!i = K k!i"
proof (cases "F (k, W)")
  case (Some a)
  then show ?thesis using assms
    apply (auto simp add: update_kv_writes_def in_range_def)
    by (metis butlast_snoc nth_butlast)
qed (auto simp add: update_kv_writes_def)

(* v_value *)
lemma update_kv_reads_v_value_inv:
  assumes "i \<in> in_range K k"
  shows "v_value (update_kv_reads t F u K k!i) = v_value (K k!i)"
proof (cases "F (k, R)")
  case (Some a)
  then show ?thesis using assms
    by (cases "i = Max (u k)")
       (auto simp add: update_kv_reads_defs update_kv_reads_length in_range_def)
qed (auto simp add: update_kv_reads_def)

lemma v_value_inv:
  "i \<in> in_range K k \<Longrightarrow> v_value (update_kv t F u K k!i) = v_value (K k!i)"
  by (auto simp add: update_kv_writes_version_inv update_kv_reads_v_value_inv update_kv_def
      update_kv_reads_length in_range_def)

(* v_writer *)
lemma update_kv_reads_v_writer_inv:
  assumes "i \<in> in_range K k"
  shows "v_writer (update_kv_reads t F u K k!i) = v_writer (K k!i)"
proof (cases "F (k, R)")
  case (Some a)
  then show ?thesis using assms
    apply (auto simp add: update_kv_reads_defs in_range_def)
    by (metis last_version_def nth_list_update_eq nth_list_update_neq
        version.select_convs(2) version.surjective version.update_convs(3))
qed (auto simp add: update_kv_reads_def)

lemma v_writer_inv:
  "i \<in> in_range K k \<Longrightarrow> v_writer (update_kv t F u K k!i) = v_writer (K k!i)"
  by (auto simp add: update_kv_writes_version_inv update_kv_reads_v_writer_inv update_kv_def
      update_kv_reads_length in_range_def)

(* v_readerset *)
lemma update_kv_reads_v_readerset_max_u:
  assumes "x \<in> v_readerset (update_kv_reads t F u K k!i)"
      and "i = Max (u k)" and "view_wellformed K u"
    shows "x \<in> v_readerset (K k!i) \<or> x = t"
  using assms
proof (cases "F (k, R)")
  case (Some _)
  then show ?thesis using assms
    apply (auto simp add: update_kv_reads_defs dest!: max_view_in_range)
    by (simp add: assms in_range_def)
qed (auto simp add: update_kv_reads_def)

lemma update_kv_reads_v_readerset_rest_inv:
  assumes "i \<in> in_range K k" and "Max (u k) \<noteq> i"
  shows "v_readerset (update_kv_reads t F u K k!i) = v_readerset (K k!i)"
proof (cases "F (k, R)")
  case (Some a)
  then show ?thesis by (auto simp add: update_kv_reads_def; metis assms(2) nth_list_update_neq)
qed (auto simp add: update_kv_reads_def)

lemma v_readerset_max_u:
  assumes "x \<in> v_readerset (update_kv t F u K k!i)"
      and "i = Max (u k)" and "view_wellformed K u"
    shows "x \<in> v_readerset (K k!i) \<or> x = t"
  using assms update_kv_writes_version_inv [of i "update_kv_reads t F u K" k t F]
  apply (auto simp add: update_kv_def update_kv_reads_length in_range_def dest!: max_view_in_range)
  using update_kv_reads_v_readerset_max_u assms(2) by fastforce

lemma v_readerset_rest_inv:
  assumes "i \<in> in_range K k" and "Max (u k) \<noteq> i"
  shows "v_readerset (update_kv t F u K k!i) = v_readerset (K k!i)"
  using assms update_kv_writes_version_inv [of i "update_kv_reads t F u K" k t F]
  by (auto simp add: update_kv_reads_v_readerset_rest_inv update_kv_def update_kv_reads_length
      in_range_def)

\<comment> \<open>txid freshness lemmas\<close>
lemma fresh_txid_reader_set:
  assumes "t \<in> next_txids K cl" and "i \<in> in_range K k"
  shows "t \<notin> v_readerset (K k!i)"
  using assms nth_mem
  apply (auto simp add: fresh_txid_defs image_iff [where f=Tn] in_range_def)
  by blast


(*declare [[simp_trace_new mode=full]]*)
\<comment> \<open>Invariant\<close>
definition Snapshot_Property_Inv :: "'v config \<Rightarrow> bool" where
  "Snapshot_Property_Inv conf \<longleftrightarrow> snapshot_property (fst conf)"

lemmas Snapshot_Property_InvI = Snapshot_Property_Inv_def[THEN iffD2, rule_format]
lemmas Snapshot_Property_InvE[elim] = Snapshot_Property_Inv_def[THEN iffD1, elim_format, rule_format]

definition WR_SO_Inv :: "'v config \<Rightarrow> bool" where
  "WR_SO_Inv conf \<longleftrightarrow> wr_so (fst conf)"

lemmas WR_SO_InvI = WR_SO_Inv_def[THEN iffD2, rule_format]
lemmas WR_SO_InvE[elim] = WR_SO_Inv_def[THEN iffD1, elim_format, rule_format]

definition WW_SO_Inv :: "'v config \<Rightarrow> bool" where
  "WW_SO_Inv conf \<longleftrightarrow> ww_so (fst conf)"

lemmas WW_SO_InvI = WW_SO_Inv_def[THEN iffD2, rule_format]
lemmas WW_SO_InvE[elim] = WW_SO_Inv_def[THEN iffD1, elim_format, rule_format]

definition Initialized_Inv :: "'v config \<Rightarrow> bool" where
  "Initialized_Inv conf \<longleftrightarrow> initialized (fst conf)"

lemmas Initialized_InvI = Initialized_Inv_def[THEN iffD2, rule_format]
lemmas Initialized_InvE[elim] = Initialized_Inv_def[THEN iffD1, elim_format, rule_format]

definition KVWellformed :: "'v config \<Rightarrow> bool" where
  "KVWellformed conf \<longleftrightarrow>
   Snapshot_Property_Inv conf \<and> WR_SO_Inv conf \<and> WW_SO_Inv conf \<and> Initialized_Inv conf"

lemmas KVWellformedI = KVWellformed_def[THEN iffD2, rule_format]
lemmas KVWellformedE[elim] = KVWellformed_def[THEN iffD1, elim_format, rule_format]

lemmas KVWellformed_defs = KVWellformed_def Snapshot_Property_Inv_def WR_SO_Inv_def WW_SO_Inv_def Initialized_Inv_def

lemma reach_kv_wellformed [simp, dest]:
  assumes "reach ET_ES s"
  shows "KVWellformed s"
  using assms
  proof(induction s rule: reach.induct)
    case (reach_init s)
    then show ?case
      by (auto simp add: KVWellformed_defs ET_ES_defs wellformed_defs kvs_init_def
          version_init_def in_range_def)
  next
    case (reach_trans s e s')
    then show ?case (*unfolding ET_ES_def apply simp
    proof (cases rule: ET_trans.cases)
      sorry*)
      apply (auto simp add: KVWellformed_defs ET_ES_def)
      subgoal apply (induction rule: ET_trans.induct)
        apply (auto simp add: snapshot_property_def)
        subgoal for U cl u'' K F U' t k i j x
          apply (cases "i = Max (u'' k)")
           apply (auto simp add: update_kv_reads_v_readerset_max_u view_wellformed_def view_in_range_def) sorry
        subgoal sorry done
      subgoal sorry
      subgoal apply (cases rule: ET_trans.cases)
        apply (auto simp add: ww_so_def SO_def SO0_def) sorry
      subgoal apply (cases rule: ET_trans.cases) apply auto
        apply (auto simp add: initialized_def)
        subgoal for U cl u'' K F U' t k
          apply (auto simp add: v_value_inv dest!: zero_in_range [of K u'' k]) done
        done
      done
qed

end

end