section \<open>Execution Tests\<close>

theory Execution_Tests
  imports Key_Value_Stores
begin

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
    \<forall>t \<in> kvs_txids K' - kvs_txids K. \<forall>k i. (v_writer (K' k!i) , t) \<in> SO^= \<longrightarrow> i \<in> u' k"

definition vShift_MR_RYW :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v kv_store \<Rightarrow> view \<Rightarrow> bool" where
  "vShift_MR_RYW K u K' u' \<equiv> vShift_MR u u' \<and> vShift_RYW K u K' u'"

interpretation ET_MR: ExecutionTest "\<lambda>K F. {}" "\<lambda>K u K' u'. vShift_MR u u'" .

interpretation ET_RYW: ExecutionTest "\<lambda>K F. {}"  vShift_RYW .

interpretation ET_CC: ExecutionTest "\<lambda>K F. R_CC K" vShift_MR_RYW .

interpretation ET_UA: ExecutionTest R_UA "\<lambda>K u K' u'. True" .

interpretation ET_PSI: ExecutionTest R_PSI vShift_MR_RYW .

interpretation ET_CP: ExecutionTest "\<lambda>K F. R_CP K" vShift_MR_RYW .

interpretation ET_SI: ExecutionTest R_SI vShift_MR_RYW .

interpretation ET_SER: ExecutionTest "\<lambda>K F. R_SER K" "\<lambda>K u K' u'. True" .

end