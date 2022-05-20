section \<open>Execution Tests\<close>

theory Execution_Tests
  imports Programming_Language
begin

locale ExecutionTest =
  fixes R_ET :: "'v kv_store \<Rightarrow> 'v fingerpr \<Rightarrow> txid rel"
    and vShift :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> view \<Rightarrow> bool"
   \<comment>\<open>We need some assumptions from Definition 8 of ECOOP paper\<close>
begin

definition canCommit :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v fingerpr \<Rightarrow> bool" where
  "canCommit K u F \<equiv> closed K u (R_ET K F)"

end

subsection \<open>Dependency Relations\<close>

type_synonym 'v dep_rel = "'v kv_store \<Rightarrow> key \<Rightarrow> txid rel"

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