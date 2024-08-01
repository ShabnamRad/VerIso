section \<open>Execution Tests\<close>

theory Execution_Tests
  imports Key_Value_Stores
begin

subsection \<open>Visible transactions, read-only transactions, and closedness\<close>

definition visTx :: "('v, 'm) kvs_store \<Rightarrow> view \<Rightarrow> txid set" where
  "visTx K u \<equiv> {v_writer (K k!i) | i k. i \<in> u k}"

definition read_only_Txs :: "('v, 'm) kvs_store \<Rightarrow> txid set" where
  "read_only_Txs K \<equiv> Tn ` kvs_readers K - kvs_writers K"

lemma visTx_subset_kvs_writers: "view_in_range K u \<Longrightarrow> visTx K u \<subseteq> kvs_writers K"
  by (auto simp add: visTx_def)

lemma visTx_full_view_eq_kvs_writers: "visTx K (full_view o K) = kvs_writers K"
  by (simp add: visTx_def kvs_writers_equiv)

lemma union_write_read_only [simp]: "kvs_writers K \<union> read_only_Txs K = kvs_txids K"
  by (simp add: read_only_Txs_def kvs_txids_def)

lemma inter_write_read_only [simp]: "kvs_writers K \<inter> read_only_Txs K = {}"
  by (simp add: read_only_Txs_def Diff_triv)

lemma inter_visTx_read_only [simp]: "view_in_range K u \<Longrightarrow> visTx K u \<inter> read_only_Txs K = {}"
  using visTx_subset_kvs_writers inter_write_read_only by blast


text \<open>Closedness: Here is the original definition from the ECOOP paper.\<close>

abbreviation closed_orig :: "('v, 'm) kvs_store \<Rightarrow> view \<Rightarrow> txid rel \<Rightarrow> bool" where
  "closed_orig K u r \<equiv> closed_general' (visTx K u) (r^-1) (read_only_Txs K)"

lemma closed_orig_is_orig_indeed:
  "closed_orig K u r \<longleftrightarrow> visTx K u = (((r\<^sup>*)^-1) `` (visTx K u)) - (read_only_Txs K)"
  by (simp add: closed_general'_def rtrancl_converse)


text \<open>Closedness, modified definition: @{term "visTx K u"} closed under @{term "(r^-1)\<^sup>+"}} up to
@{term "read_only_Txs K"}.\<close>

abbreviation closed :: "('v, 'm) kvs_store \<Rightarrow> view \<Rightarrow> txid rel \<Rightarrow> bool" where
  "closed K u r \<equiv> closed_general (visTx K u) (r^-1) (read_only_Txs K)"

lemma closed_equiv_closed_orig: 
  shows "view_in_range K u \<Longrightarrow> closed K u r \<longleftrightarrow> closed_orig K u r"
  by (simp add: closed_general_equiv)


subsection \<open>Configurations\<close>

type_synonym 'v config = "'v kv_store \<times> (cl_id \<Rightarrow> view)"

abbreviation c_views_init :: "cl_id \<Rightarrow> view" where
  "c_views_init \<equiv> (\<lambda>cl. view_init)"

definition config_init :: "'v config" where
  "config_init \<equiv> (kvs_init, c_views_init)"

lemmas config_init_defs = config_init_def view_init_def


subsection \<open>Execution Tests as transition system\<close>

datatype 'v label = ET cl_id sqn view "'v fingerpr" | ETViewExt cl_id view | ETSkip

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
    view_wellformed K u \<and>       \<comment> \<open>chsp: do we need this one?\<close>
    t = Tn_cl sn cl \<and>
    t \<in> next_txids K cl \<and>
    K' = update_kv t F u'' K)"

fun ET_cl_view_ext :: "('v kv_store \<times> view) \<Rightarrow> ('v kv_store \<times> view) \<Rightarrow> bool" where
  "ET_cl_view_ext (K, u) (K', u') \<longleftrightarrow>
    view_wellformed K u \<and>       \<comment> \<open>chsp: do we need this one?\<close>
    view_wellformed K u' \<and>
    u \<sqsubseteq> u' \<and>
    K' = K"

declare ET_cl_txn.simps [simp del]
lemmas ET_cl_txn_def = ET_cl_txn.simps

fun ET_trans_and_fp :: "'v config \<Rightarrow> 'v label \<Rightarrow> 'v config \<Rightarrow> bool" where
  "ET_trans_and_fp (K, U) (ET cl sn u'' F) (K', U') \<longleftrightarrow>
    (\<exists>u'. ET_cl_txn cl sn u'' F (K, U cl) (K', u') \<and> U' = U (cl := u') \<and> fp_property F K u'')" |
  "ET_trans_and_fp (K, U) (ETViewExt cl u') (K', U') \<longleftrightarrow>
    (\<exists>u'. ET_cl_view_ext (K, U cl) (K', u') \<and> U' = U (cl := u'))" |
  "ET_trans_and_fp c ETSkip c' \<longleftrightarrow> c' = c"

lemmas ET_trans_induct = ET_trans_and_fp.induct [case_names ET_txn ET_view]

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


subsubsection \<open>Proof rule for ET refinement\<close>

text \<open>Simple rule to structure proofs of the ET transition refinement. Note that variable 
@{term "u'"} does not appear in conclusion and should be instantiated appropriately.\<close>

lemma ET_trans_rule:
  assumes 
    \<open>U cl \<sqsubseteq> u''\<close>
    \<open>canCommit K u'' F\<close>
    \<open>vShift K u'' K' u'\<close>
    \<open>view_wellformed K u''\<close> 
    \<open>view_wellformed K' u'\<close>
    \<open>view_wellformed K (U cl)\<close>      
    \<open>Tn_cl sn cl \<in> next_txids K cl\<close>
    \<open>fp_property F K u''\<close>
    \<open>K' = update_kv (Tn_cl sn cl) F u'' K\<close>
    \<open>U' = U(cl := u')\<close>
  shows \<open>ET_trans_and_fp (K , U) (ET cl sn u'' F) (K', U')\<close>
  using assms
  by (auto simp add: ET_cl_txn_def)

lemma ET_view_ext_rule:
  assumes 
    \<open>U cl \<sqsubseteq> u'\<close>
    \<open>view_wellformed K u'\<close>
    \<open>view_wellformed K (U cl)\<close>
    \<open>K' = K\<close>
    \<open>U' = U(cl := u')\<close>
  shows \<open>ET_trans_and_fp (K , U) (ETViewExt cl u') (K', U')\<close>
  using assms
  by (auto simp add: ET_cl_txn_def)


subsubsection \<open>Wellformedness Invariants\<close>

lemma reach_snapshot_property [simp, dest]:
  assumes "reach ET_ES s"
  shows "snapshot_property (fst s)" \<comment> \<open>fst s: kvs part of state\<close>
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: ET_ES_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction s e s' rule: ET_trans_induct)
    case (ET_txn K U cl sn F K' U')
    then show ?case
      apply (auto simp add: ET_trans_def full_view_update_kv 
                  intro!: kvs_wellformed_intros del: equalityI)
      subgoal for k i j u'   \<comment> \<open>subgoal for the readerset case\<close>
        by (auto simp add: v_readerset_update_kv_simps 
                 dest: snapshot_propertyD1 fresh_txid_v_reader_set split: if_split_asm)
      subgoal for k i j u'   \<comment> \<open>subgoal for the writer case\<close>
        by (auto simp add: update_kv_v_writer_simps  
                 dest: snapshot_propertyD2 fresh_txid_v_writer split: if_split_asm)
      done
  qed auto
qed

lemma reach_wr_so [simp, dest]:
  assumes "reach ET_ES s"
  shows "wr_so (fst s)"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case 
    by (auto simp add: ET_ES_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction s e s' rule: ET_trans_induct)
    case (ET_txn K U cl sn F K' U')
    then show ?case 
      apply (auto simp add: ET_trans_def full_view_update_kv intro!: kvs_wellformed_intros)
      subgoal for k i x t   \<comment> \<open>SO case\<close>
        by (auto 0 3 simp add: update_kv_version_field_simps fresh_txid_writer_so 
                 split: if_split_asm)
      subgoal for k i x t  \<comment> \<open>reflexive case\<close>
        by (auto 0 3 simp add: update_kv_version_field_simps dest: fresh_txid_v_writer 
                 split: if_split_asm)
      done
  qed auto
qed

lemma reach_ww_so [simp, dest]:
  assumes "reach ET_ES s"
  shows "ww_so (fst s)"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case 
    by (auto simp add: ET_ES_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction s e s' rule: ET_trans_induct)
    case (ET_txn K U cl sn F K' U')
    then show ?case 
      apply (auto simp add: ET_trans_def full_view_update_kv intro!: kvs_wellformed_intros)
      subgoal for k i j u'  \<comment> \<open>SO case\<close>
        by (auto dest: fresh_txid_writer_so full_view_elemD split: if_split_asm)
      subgoal for k i j u'  \<comment> \<open>reflexive case\<close>
        by (auto  dest: fresh_txid_v_writer split: if_split_asm)
      done
  qed auto
qed

lemma reach_kvs_initialized [simp, dest]:
  assumes "reach ET_ES s"
  shows "kvs_initialized (fst s)"
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
      by (auto simp add: ET_trans_def dest: update_kv_empty intro!: kvs_wellformed_intros)
  qed auto
qed

lemma reach_kvs_T0_init [simp, dest]:
  assumes "reach ET_ES s"
  shows "kvs_T0_init (fst s)"
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
      by (auto simp add: ET_trans_def kvs_T0_init_update_kv)
  qed auto
qed

lemma reach_kvs_wellformed [simp, dest]:
  assumes "reach ET_ES s"
  shows "kvs_wellformed (fst s)"
  using assms
  by (simp add: kvs_wellformed_def)

end


subsection \<open>Dependency Relations\<close>

type_synonym 'v dep_rel = "'v kv_store \<Rightarrow> key \<Rightarrow> txid rel"

definition WR :: "'v dep_rel" where
  "WR K k \<equiv> {(t, t'). \<exists>i. i \<in> full_view (K k) \<and> t = v_writer (K k!i) \<and> t' \<in> Tn ` v_readerset (K k!i)}"

definition WW :: "'v dep_rel" where
  "WW K k \<equiv> {(t, t'). \<exists>i i'. i \<in> full_view (K k) \<and> i' \<in> full_view (K k) \<and>
                             t = v_writer (K k!i) \<and> t' = v_writer (K k!i') \<and> i < i'}"

definition RW :: "'v dep_rel" where
  "RW K k \<equiv> {(t, t'). \<exists>i i'. i \<in> full_view (K k) \<and> i' \<in> full_view (K k) \<and>
                              t \<in> Tn ` v_readerset (K k!i) \<and> t' = v_writer (K k!i') \<and> i < i' \<and> t \<noteq> t'}"

definition R_onK :: "'v dep_rel \<Rightarrow> 'v kv_store \<Rightarrow> txid rel" where
  "R_onK r K \<equiv> \<Union>k. r K k"


lemma WW_relates_writers:      
  "\<lbrakk> (t1, t2) \<in> WW K k \<rbrakk> \<Longrightarrow> t1 \<in> kvs_writers K \<and> t2 \<in> kvs_writers K"
  by (auto simp add: WW_def full_view_def v_writer_in_kvs_writers)


subsection \<open>Consistency models' execution tests\<close>

definition R_CC :: "'v kv_store \<Rightarrow> txid rel" where
  "R_CC K \<equiv> SO \<union> R_onK WR K"

definition R_UA :: "'v kv_store \<Rightarrow> 'v fingerpr \<Rightarrow> txid rel" where
  "R_UA K F \<equiv> \<Union>k. if W \<in> dom (F k) then (WW K k)^-1 else {}"

definition R_PSI :: "'v kv_store \<Rightarrow> 'v fingerpr \<Rightarrow> txid rel" where
  "R_PSI K F \<equiv> R_UA K F \<union> R_CC K \<union> R_onK WW K"

definition R_CP :: "'v kv_store \<Rightarrow> txid rel" where
  "R_CP K \<equiv> SO O (R_onK RW K)^= \<union> (R_onK WR K) O (R_onK RW K)^= \<union> (R_onK WW K)"

definition R_SI :: "'v kv_store \<Rightarrow> 'v fingerpr \<Rightarrow> txid rel" where
  "R_SI K F \<equiv> R_UA K F \<union> R_CP K \<union> (R_onK WW K) O (R_onK RW K)"

definition R_SER :: "'v kv_store \<Rightarrow> txid rel" where
  "R_SER K \<equiv> (R_onK WW K)^-1"

definition vShift_MR :: "view \<Rightarrow> view \<Rightarrow> bool" where
  "vShift_MR u u' \<equiv> u \<sqsubseteq> u'"

definition vShift_RYW :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> view \<Rightarrow> bool" where
  "vShift_RYW K u K' u' \<equiv>
    \<forall>t \<in> kvs_txids K' - kvs_txids K. \<forall>k. \<forall>i < length (K' k). 
      (v_writer (K' k!i) , t) \<in> SO^= \<longrightarrow> i \<in> u' k"

definition vShift_MR_RYW :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> view \<Rightarrow> bool" where
  "vShift_MR_RYW K u K' u' \<equiv> vShift_MR u u' \<and> vShift_RYW K u K' u'"


text \<open>Lemmas about session guarantees\<close>

lemma vShift_MR_I: "u \<sqsubseteq> u' \<Longrightarrow> vShift_MR u u'" 
  by (simp add: vShift_MR_def)

lemma vShift_RYW_I:
  assumes "\<And>t k i. 
     \<lbrakk> t \<in> kvs_txids K'; t \<notin> kvs_txids K; i < length (K' k); t = v_writer (K' k ! i) \<rbrakk>
      \<Longrightarrow> i \<in> u' k"
  and "\<And>t k i. 
     \<lbrakk> t \<in> kvs_txids K'; t \<notin> kvs_txids K; i < length (K' k); (v_writer (K' k ! i), t) \<in> SO \<rbrakk>
      \<Longrightarrow> i \<in> u' k"
  shows "vShift_RYW K u K' u'"
  using assms
  by (auto simp add: vShift_RYW_def)

text \<open>combine the two lemmas above into one\<close>

lemmas vShift_MR_RYW_I = 
  vShift_MR_RYW_def[THEN meta_eq_to_obj_eq, THEN iffD2, OF conjI, OF vShift_MR_I vShift_RYW_I]


subsection \<open>Model Instances\<close>

interpretation ET_MR: ExecutionTest "\<lambda>K F. {}" "\<lambda>K u K' u'. vShift_MR u u'" .

interpretation ET_RYW: ExecutionTest "\<lambda>K F. {}"  vShift_RYW .

interpretation ET_CC: ExecutionTest "\<lambda>K F. R_CC K" vShift_MR_RYW .

interpretation ET_UA: ExecutionTest R_UA "\<lambda>K u K' u'. True" .

interpretation ET_PSI: ExecutionTest R_PSI vShift_MR_RYW .

interpretation ET_CP: ExecutionTest "\<lambda>K F. R_CP K" vShift_MR_RYW .

interpretation ET_SI: ExecutionTest R_SI vShift_MR_RYW .

interpretation ET_SER: ExecutionTest "\<lambda>K F. R_SER K" "\<lambda>K u K' u'. True" .


subsection \<open>Instance-specific lemmas\<close>

lemma R_SER_closed_simplified: "((R_SER K)\<inverse>)\<^sup>+ `` kvs_writers K \<subseteq> kvs_txids K"
proof -
  {
    fix t t'
    assume "(t, t') \<in> (\<Union> (range (WW K)))\<^sup>+" and "t \<in> kvs_writers K"
    then have "t' \<in> kvs_writers K"
      by (induction t t' rule: trancl.induct) (auto dest: WW_relates_writers)
  } 
  then show ?thesis by (auto simp add: R_SER_def R_onK_def kvs_txids_def)
qed

lemma full_view_satisfies_ET_SER_canCommit: "ET_SER.canCommit K (full_view o K) F"
  by (simp add: ET_SER.canCommit_def ExecutionTest.canCommit_def closed_general_def
                visTx_full_view_eq_kvs_writers R_SER_closed_simplified)

subsection \<open>Timestamps\<close>
type_synonym tstmp = nat

\<comment> \<open>For unique transaction timestamps: (tstmp, cl_id)\<close>
instantiation prod :: (linorder, linorder) linorder
begin

definition less_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "p1 < p2 \<longleftrightarrow> fst p1 < fst p2 \<or> (fst p1 = fst p2 \<and> snd p1 < snd p2)" 

definition less_eq_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "p1 \<le> p2 \<longleftrightarrow> fst p1 < fst p2 \<or> (fst p1 = fst p2 \<and> snd p1 \<le> snd p2)"   

instance proof
  fix x y z :: "'a ::linorder \<times> 'b::linorder"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (auto simp add: less_prod_def less_eq_prod_def)
  show "x \<le> x"
    by (auto simp add: less_eq_prod_def)
  show "\<lbrakk>x \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> x \<le> z"
    by (auto simp add: less_eq_prod_def)
  show "\<lbrakk>x \<le> y; y \<le> x\<rbrakk> \<Longrightarrow> x = y"
    by (auto simp add: less_eq_prod_def prod_eq_iff)
  show "x \<le> y \<or> y \<le> x"
    by (auto simp add: less_eq_prod_def)
qed

end


end