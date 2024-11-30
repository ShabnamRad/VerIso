section \<open>Simple Database Transactions\<close>

theory Simple_DB
  imports "../Event_Systems"
begin

text \<open>We provide two models of a simple (sequential) key-value store (KVS) database. 
The abstract model performs transactions in one shot, while the concrete model reads and 
writes one value at a time and then commits the writes to the database in a commit operation.
We prove that the concrete model refines the abstract one. The proof requires an invariant about
the conrete model.\<close>

subsection \<open>Abstract Model: One-shot Transactions\<close>

text \<open>We model a very abstract database, where transactions are executing atomically 
in a single step, which reads the values given in a read fingerprint and updates the KVS
with the key-value mappings given in a write fingerprint.\<close>

type_synonym key = nat
type_synonym 'v kv_store = \<open>key \<rightharpoonup> 'v\<close>

record 'v adb_state = 
  kvs :: \<open>'v kv_store\<close>       \<comment> \<open>main key-value store\<close>

definition adb_init :: \<open>'v adb_state \<Rightarrow> bool\<close> where
  "adb_init = (=) \<lparr> kvs = Map.empty \<rparr>"

datatype 'v adb_events = 
  Txn \<open>'v kv_store\<close> \<open>'v kv_store\<close> |
  Skip 

fun adb_txn :: \<open>'v kv_store \<Rightarrow> 'v kv_store \<Rightarrow>'v adb_state \<Rightarrow> 'v adb_state \<Rightarrow> bool\<close> where
  \<open>adb_txn rdfp wrfp s s' \<longleftrightarrow> 
     rdfp \<subseteq>\<^sub>m kvs s \<and>                     \<comment> \<open>read fingerprint contained in KVS\<close>
     s' = s\<lparr> kvs := kvs s ++ wrfp \<rparr>\<close>      \<comment> \<open>update KVS with write fingerprint\<close>

fun adb_trans :: \<open>'v adb_state \<Rightarrow> 'v adb_events \<Rightarrow> 'v adb_state \<Rightarrow> bool\<close> where
  "adb_trans s (Txn rdfp wrfp) s' \<longleftrightarrow> adb_txn rdfp wrfp s s'" |
  "adb_trans s (Skip) s' \<longleftrightarrow> s' = s"

definition adb :: \<open>('v adb_events, 'v adb_state) ES\<close> where
  "adb = \<lparr> 
    init = adb_init, 
    trans = adb_trans
  \<rparr>"

lemma trans_adb [simp]: \<open>trans adb = adb_trans\<close>  \<comment> \<open>facilitates the handling of events in proofs\<close>
  by (simp add: adb_def)

lemmas adb_defs = adb_def adb_init_def


subsection \<open>Concrete Model: Single-Key Reads and Writes\<close>

text \<open>The concrete DB state record extends the abstract one with two additional fields: a read
and a write fingerprint.\<close>

record 'v cdb_state = \<open>'v adb_state\<close> + 
  rdfp :: \<open>'v kv_store\<close>      \<comment> \<open>read fingerprint\<close>
  wrfp :: \<open>'v kv_store\<close>      \<comment> \<open>write fingerprint\<close>

definition cdb_init :: \<open>'v cdb_state \<Rightarrow> bool\<close> where
  "cdb_init = (=) \<lparr> kvs = Map.empty, rdfp = Map.empty, wrfp = Map.empty \<rparr>"

text \<open>The concrete model has two new events for reading and writing a given key. The read event
collects values read in the read fingerprint, while the write event collects the writte key-value 
mappings in the write fingerprint. The commit event updates the KVS with the write fingerprint.\<close>

datatype 'v cdb_events =
  Read key 'v |
  Write key 'v |
  Commit \<open>'v kv_store\<close> \<open>'v kv_store\<close> |
  Skip2 

fun cdb_read :: \<open>key \<Rightarrow> 'v \<Rightarrow> 'v cdb_state \<Rightarrow> 'v cdb_state \<Rightarrow> bool\<close> where
  \<open>cdb_read k v s s' \<longleftrightarrow> 
     kvs s k = Some v \<and>                   \<comment> \<open>ensure we read the current value of key @{term k}\<close> 
     s' = s\<lparr> rdfp := (rdfp s)(k \<mapsto> v) \<rparr>\<close>   \<comment> \<open>record key-value mapping in read fingerprint\<close> 

fun cdb_write :: \<open>key \<Rightarrow> 'v \<Rightarrow> 'v cdb_state \<Rightarrow> 'v cdb_state \<Rightarrow> bool\<close> where
  \<open>cdb_write k v s s' \<longleftrightarrow> 
     s' = s\<lparr> wrfp := (wrfp s)(k \<mapsto> v) \<rparr>\<close>   \<comment> \<open>update write fingerprint with key-value mapping\<close> 

fun cdb_commit :: \<open>'v kv_store \<Rightarrow> 'v kv_store \<Rightarrow>'v cdb_state \<Rightarrow> 'v cdb_state \<Rightarrow> bool\<close> where
  \<open>cdb_commit rdfp' wrfp' s s' \<longleftrightarrow>
     rdfp' = rdfp s \<and>         \<comment> \<open>bind read and write fingerprint parameters tothose in state\<close>
     wrfp' = wrfp s \<and>
     s' = \<lparr> 
       kvs = kvs s ++ wrfp s,  \<comment> \<open>update KVS with write fingerprint\<close> 
       rdfp = Map.empty,       \<comment> \<open>reset read and write fingerprints\<close>
       wrfp = Map.empty
     \<rparr>\<close>

fun cdb_trans :: \<open>'v cdb_state \<Rightarrow> 'v cdb_events \<Rightarrow> 'v cdb_state \<Rightarrow> bool\<close> where
  \<open>cdb_trans s (Read k v) s' \<longleftrightarrow> cdb_read k v s s'\<close> |
  \<open>cdb_trans s (Write k v) s' \<longleftrightarrow> cdb_write k v s s'\<close> |
  \<open>cdb_trans s (Commit rdfp' wrfp') s' \<longleftrightarrow> cdb_commit rdfp' wrfp' s s'\<close> |
  \<open>cdb_trans s (Skip2) s' \<longleftrightarrow> s' = s\<close>

definition cdb :: \<open>('v cdb_events, 'v cdb_state) ES\<close> where
  "cdb = \<lparr> 
    init = cdb_init, 
    trans = cdb_trans
  \<rparr>"

lemma trans_cdb [simp]: \<open>trans cdb = cdb_trans\<close>  \<comment> \<open>facilitates the handling of events in proofs\<close>
  by (simp add: cdb_def)

lemmas cdb_defs = cdb_def cdb_init_def


subsection \<open>Invariant\<close>

text \<open>We prove an invariant stating the the read fingerprint is always contained in the KVS.\<close>

lemma rdfp_invariant: \<open>reach cdb s \<Longrightarrow> rdfp s \<subseteq>\<^sub>m kvs s\<close>
proof (induction rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: cdb_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Read k v)
    then show ?thesis using reach_trans by (auto simp add: map_le_def)
  qed simp_all
qed


subsection \<open>Refinement proof\<close>

text \<open>Define refinement mappings on events and states. All concrete events except @{term Commit}
are mapped to @{term Skip}.\<close>

fun \<pi> :: \<open>'a cdb_events \<Rightarrow> 'a adb_events\<close> where
  \<open>\<pi> (Read k v) = Skip\<close> |
  \<open>\<pi> (Write k v) = Skip\<close> |
  \<open>\<pi> (Commit rdf wrf) = Txn rdf wrf\<close> |
  \<open>\<pi> (Skip2) = Skip\<close> 

fun h :: \<open>'v cdb_state \<Rightarrow> 'v adb_state\<close> where
  \<open>h s = \<lparr> kvs = kvs s \<rparr>\<close>

text \<open>State and prove the refinement.\<close>

lemma cdb_refines_adb: \<open>cdb \<sqsubseteq>\<^bsub>[h,\<pi>]\<^esub> adb\<close>
proof (rule simulate_ES_fun_h)
  fix s0 :: \<open>'v cdb_state\<close>
  assume \<open>init cdb s0\<close>
  then show \<open>init adb (h s0)\<close>
    by (auto simp add: adb_defs cdb_defs)
next
  fix s :: \<open>'v cdb_state\<close> and e and s' 
  assume *: \<open>cdb: s \<midarrow>e\<rightarrow> s'\<close> and **: \<open>reach cdb s\<close> 
  show \<open>adb: h s \<midarrow>\<pi> e\<rightarrow> h s'\<close> using *
  proof (cases e)
    case (Commit rdf wrf)
    then show ?thesis 
      using * ** rdfp_invariant by auto    \<comment> \<open>requires the read-fingerprint invariant\<close>
  qed simp_all
qed



end
