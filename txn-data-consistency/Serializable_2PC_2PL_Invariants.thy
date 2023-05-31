section \<open>2PL+2PC Refinement Proof Invariants (and important lemmas)\<close>

theory Serializable_2PC_2PL_invariants
  imports Serializable_2PC_2PL
begin

\<comment> \<open>Invariant about future and past transactions svrs\<close>

definition TIDFutureKm where
  "TIDFutureKm s cl \<longleftrightarrow> (\<forall>n k. n > cl_sn (cls s cl) \<longrightarrow> km_state (svrs s k) (Tn_cl n cl) = working)"

definition TIDPastKm where
  "TIDPastKm s cl \<longleftrightarrow> (\<forall>n k. n < cl_sn (cls s cl) \<longrightarrow> km_state (svrs s k) (Tn_cl n cl) \<in> {committed, aborted})"

lemma other_sn_idle:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "get_cl_txn t = cl" and "get_sn_txn t \<noteq> cl_sn (cls s cl)"
  shows "\<And>k. km_state (svrs s k) t \<in> {working, committed, aborted}"
  oops

\<comment> \<open>Lock Invariants\<close>

definition RLockInv where
  "RLockInv s k \<longleftrightarrow> (\<forall>t. km_state (svrs s k) t = read_lock \<longrightarrow> (\<forall>t. km_state (svrs s k) t \<noteq> write_lock))"

definition WLockInv where
  "WLockInv s k \<longleftrightarrow> (\<forall>t. km_state (svrs s k) t \<noteq> write_lock) \<or> (\<exists>! t. km_state (svrs s k) t = write_lock)"

\<comment> \<open>Invariants for fingerprint, knowing the lock (km status)\<close>

definition RLockFpInv where
  "RLockFpInv s k \<longleftrightarrow> (\<forall>t. km_state (svrs s k) t = read_lock \<longrightarrow>
    svr_key_fp (svrs s k) t W = None \<and>
    svr_key_fp (svrs s k) t R \<noteq> None)"

definition WLockFpInv where
  "WLockFpInv s k \<longleftrightarrow> (\<forall>t. km_state (svrs s k) t = write_lock \<longrightarrow> svr_key_fp (svrs s k) t W \<noteq> None)"

definition NoLockFpInv where
  "NoLockFpInv s k \<longleftrightarrow> (\<forall>t. km_state (svrs s k) t = no_lock \<longrightarrow>
    svr_key_fp (svrs s k) t W = None \<and>
    svr_key_fp (svrs s k) t R = None)"

\<comment> \<open>Invariants about kv store\<close>
definition KVSNonEmp where
  "KVSNonEmp s \<longleftrightarrow> (\<forall>k. svr_vl (svrs s k) \<noteq> [])"

definition KVSGSNonEmp where
  "KVSGSNonEmp s \<longleftrightarrow> (\<forall>k. kvs_of_gs s k \<noteq> [])"

definition KVSLen where
  "KVSLen s cl \<longleftrightarrow> (\<forall>k. length (svr_vl (svrs s k)) \<le> length (kvs_of_gs s k))"

subsubsection \<open>Lemmas for kvs_of_gs changing by different events\<close>

lemma kvs_of_gs_km_inv:
  assumes "WLockInv s k" and "RLockInv s k"
    and "(\<forall>t. km_state (svrs s k) t \<noteq> write_lock) \<or> 
              km_state (svrs s' k) t \<noteq> write_lock"
    and "tm_state (cls s (get_cl_txn t)) \<noteq> tm_committed"
    and "\<And>k. svr_vl (svrs s' k) = svr_vl (svrs s k)"
    and "tm_km_k'_t'_unchanged k s s' t"
  shows "kvs_of_gs s' = kvs_of_gs s"
  oops

lemma kvs_of_gs_tm_inv:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "tm_state (cls s cl) \<noteq> tm_committed \<or>
         (\<forall>k. km_state (svrs s k) (get_txn_cl cl s) = committed)"
    and "tm_state (cls s' cl) \<noteq> tm_committed"
    and "km_tm_cl'_unchanged cl s s'"
  shows "kvs_of_gs s' = kvs_of_gs s"
  oops

lemma update_kv_all_tm_commit_no_lock_inv:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "tm_state (cls s cl) = tm_prepared"
    and "tm_state (cls s' cl) = tm_committed"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "km_state (svrs s k) (get_txn_cl cl s) = no_lock"
  shows "update_kv_all_txn (\<lambda>t. tm_state (cls s' (get_cl_txn t))) (km_state (svrs s k))
          (svr_key_fp (svrs s k)) (svr_vl (svrs s k)) =
         update_kv_all_txn (\<lambda>t. tm_state (cls s (get_cl_txn t))) (km_state (svrs s k))
          (svr_key_fp (svrs s k)) (svr_vl (svrs s k))"
  oops

(*All events*)
abbreviation not_tm_commit where
  "not_tm_commit e \<equiv> \<forall>cl sn u F. e \<noteq> TM_Commit cl sn u F"

abbreviation invariant_list_kvs where
  "invariant_list_kvs s \<equiv> \<forall>cl k. TIDFutureKm s cl \<and> TIDPastKm s cl \<and> RLockInv s k \<and> WLockInv s k \<and>
                        RLockFpInv s k \<and> NoLockFpInv s k \<and> KVSNonEmp s"

lemma kvs_of_gs_inv:
  assumes "gs_trans s e s'"
    and "invariant_list_kvs s"
    and "not_tm_commit e"
  shows "kvs_of_gs s' = kvs_of_gs s"
  oops

\<comment> \<open>More specific lemmas about TM commit\<close>
lemma kvs_of_gs_commit_length_increasing:
  assumes "tm_state (cls s cl) = tm_prepared"
    and "tm_state (cls s' cl) = tm_committed"
    and "km_tm_cl'_unchanged cl s s'"
  shows "length (kvs_of_gs s k) \<le> length (kvs_of_gs s' k)"
  oops

lemma kvs_of_gs_length_increasing:
  assumes "gs_trans s e s'"
    and "invariant_list_kvs s"
  shows "\<And>k. length (kvs_of_gs s k) \<le> length (kvs_of_gs s' k)"
  oops

\<comment> \<open>Fingerprint content invariant and Lemmas for proving the fp_property\<close>

lemma svr_vl_read_lock_commit_eq_length:
  assumes "RLockFpInv s k"
    and "km_state (svrs s k) t = read_lock"
    and "svr_vl (svrs s' k) =
          update_kv_key t (svr_key_fp (svrs s k) t) (full_view (svr_vl (svrs s k))) (svr_vl (svrs s k))"
  shows "length (svr_vl (svrs s' k)) = length (svr_vl (svrs s k))"
  oops

definition RLockFpContentInv where
  "RLockFpContentInv s k \<longleftrightarrow> (\<forall>t. km_state (svrs s k) t = read_lock \<longrightarrow>
    svr_key_fp (svrs s k) t R =
      Some (v_value (last_version (svr_vl (svrs s k)) (full_view (svr_vl (svrs s k))))))"

definition WLockFpContentInv where
  "WLockFpContentInv s k \<longleftrightarrow> (\<forall>t. km_state (svrs s k) t = write_lock \<longrightarrow>
    svr_key_fp (svrs s k) t R = None \<or>
    svr_key_fp (svrs s k) t R =
      Some (v_value (last_version (svr_vl (svrs s k)) (full_view (svr_vl (svrs s k))))))"

lemma svr_vl_kvs_eq_length:
  assumes "WLockInv s k" and "RLockInv s k"
    and "tm_state (cls s cl) = tm_prepared"
    and "km_state (svrs s k) (get_txn_cl cl s) \<in> {read_lock, write_lock}"
  shows "length (kvs_of_gs s k) = length (svr_vl (svrs s k))"
  oops

\<comment> \<open>Lemmas for view growth after commit\<close>

lemma committed_kvs_view_grows:
  assumes "tm_state (cls s cl) = tm_prepared"
    and "tm_state (cls s' cl) = tm_committed"
    and "km_tm_cl'_unchanged cl s s'"
  shows "(\<lambda>k. full_view (kvs_of_gs s k)) \<sqsubseteq> (\<lambda>k. full_view (kvs_of_gs s' k))"
  oops
  
lemma updated_vl_view_grows:
  assumes "svr_vl (svrs s' k) =
    update_kv_key t (svr_key_fp (svrs s k) t) (full_view (svr_vl (svrs s k))) (svr_vl (svrs s k))"
    and "other_insts_unchanged k (svrs s) (svrs s')"
  shows "(\<lambda>k. full_view (svr_vl (svrs s k))) \<sqsubseteq> (\<lambda>k. full_view (svr_vl (svrs s' k)))"
  oops

lemma cl_view_inv:
  assumes "gs_trans s e s'"
    and "not_tm_commit e"
  shows "cl_view (cls s' cl) = cl_view (cls s cl)"
  oops

definition TMFullView where
  "TMFullView s cl \<longleftrightarrow> cl_view (cls s cl) \<sqsubseteq> (\<lambda>k. full_view (kvs_of_gs s k))"

\<comment> \<open>TM_commit updating kv\<close>

lemma kvs_of_gs_tm_commit:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "WLockInv s k" and "WLockFpInv s k"
    and "RLockInv s k" and "RLockFpInv s k"
    and "NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_state (cls s cl) = tm_prepared"
    and "km_state (svrs s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock}"
    and "tm_state (cls s' cl) = tm_committed"
    and "other_insts_unchanged cl (cls s) (cls s')"
  shows "update_kv_all_txn (\<lambda>t. tm_state (cls s' (get_cl_txn t))) (km_state (svrs s k))
          (svr_key_fp (svrs s k)) (svr_vl (svrs s k)) =
    update_kv_key (get_txn_cl cl s) (svr_key_fp (svrs s k) (get_txn_cl cl s))
      (full_view (update_kv_all_txn (\<lambda>t. tm_state (cls s (get_cl_txn t))) (km_state (svrs s k))
        (svr_key_fp (svrs s k)) (svr_vl (svrs s k))))
      (update_kv_all_txn (\<lambda>t. tm_state (cls s (get_cl_txn t))) (km_state (svrs s k))
        (svr_key_fp (svrs s k)) (svr_vl (svrs s k)))"
  oops

\<comment> \<open>Lemmas for showing transaction id freshness\<close>

lemma get_sqns_other_cl_inv:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_state (cls s cl) = tm_prepared"
    and "tm_state (cls s' cl) = tm_committed"
    and "\<And>k. km_state (svrs s k) (get_txn_cl cl s) = read_lock \<or>
             km_state (svrs s k) (get_txn_cl cl s) = write_lock \<or> 
             km_state (svrs s k) (get_txn_cl cl s) = no_lock"
    and "km_tm_cl'_unchanged cl s s'"
    and "cl' \<noteq> cl"
  shows "get_sqns (kvs_of_gs s') cl' = get_sqns (kvs_of_gs s) cl'"
  oops

lemma new_t_is_in_writers:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_state (cls s cl) = tm_prepared"
    and "tm_state (cls s' cl) = tm_committed"
    and "km_state (svrs s k) (get_txn_cl cl s) = write_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "vl_writers_sqns (kvs_of_gs s' k) cl = vl_writers_sqns (kvs_of_gs s k) cl \<union> {cl_sn (cls s cl)}"
  oops

lemma new_t_is_in_writers2:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_state (cls s cl) = tm_prepared"
    and "tm_state (cls s' cl) = tm_committed"
    and "km_state (svrs s k) (get_txn_cl cl s) = read_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "vl_writers_sqns (kvs_of_gs s' k) cl = vl_writers_sqns (kvs_of_gs s k) cl"
  oops

lemma new_t_is_in_readers:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_state (cls s cl) = tm_prepared"
    and "tm_state (cls s' cl) = tm_committed"
    and "km_state (svrs s k) (get_txn_cl cl s) = read_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "vl_readers_sqns (kvs_of_gs s' k) cl = vl_readers_sqns (kvs_of_gs s k) cl \<union> {cl_sn (cls s cl)}"
  oops

lemma new_t_is_in_readers2:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_state (cls s cl) = tm_prepared"
    and "tm_state (cls s' cl) = tm_committed"
    and "km_state (svrs s k) (get_txn_cl cl s) = write_lock"
    and "svr_key_fp (svrs s k) (get_txn_cl cl s) R \<noteq> None"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "vl_readers_sqns (kvs_of_gs s' k) cl = vl_readers_sqns (kvs_of_gs s k) cl \<union> {cl_sn (cls s cl)}"
  oops

lemma new_t_is_in_readers3:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_state (cls s cl) = tm_prepared"
    and "tm_state (cls s' cl) = tm_committed"
    and "km_state (svrs s k) (get_txn_cl cl s) = write_lock"
    and "svr_key_fp (svrs s k) (get_txn_cl cl s) R = None"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "vl_readers_sqns (kvs_of_gs s' k) cl = vl_readers_sqns (kvs_of_gs s k) cl"
  oops

lemma kvs_writers_tm_commit_grows:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_state (cls s cl) = tm_prepared"
    and "tm_state (cls s' cl) = tm_committed"
    and "\<forall>k. km_state (svrs s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock}"
    and "km_state (svrs s k) (get_txn_cl cl s) = write_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "kvs_writers_sqns (kvs_of_gs s') cl = kvs_writers_sqns (kvs_of_gs s) cl \<union> {cl_sn (cls s cl)}"
  oops

lemma kvs_writers_tm_commit_doesnt_grow:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_state (cls s cl) = tm_prepared"
    and "tm_state (cls s' cl) = tm_committed"
    and "\<forall>k. km_state (svrs s k) (get_txn_cl cl s) \<in> {read_lock, no_lock}"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "kvs_writers_sqns (kvs_of_gs s') cl = kvs_writers_sqns (kvs_of_gs s) cl"
  oops

lemma kvs_readers_sqns_tm_commit_grows:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_state (cls s cl) = tm_prepared"
    and "tm_state (cls s' cl) = tm_committed"
    and "\<forall>k. km_state (svrs s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock}"
    and "km_state (svrs s k) (get_txn_cl cl s) = read_lock \<or>
         (km_state (svrs s k) (get_txn_cl cl s) = write_lock \<and>
          svr_key_fp (svrs s k) (get_txn_cl cl s) R \<noteq> None)"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "kvs_readers_sqns (kvs_of_gs s') cl = kvs_readers_sqns (kvs_of_gs s) cl \<union> {cl_sn (cls s cl)}"
  oops

lemma kvs_readers_sqns_tm_commit_doesnt_grow:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_state (cls s cl) = tm_prepared"
    and "tm_state (cls s' cl) = tm_committed"
    and "\<forall>k. km_state (svrs s k) (get_txn_cl cl s) \<in> {write_lock, no_lock}"
    and "\<forall>k. km_state (svrs s k) (get_txn_cl cl s) \<noteq> write_lock \<or>
             svr_key_fp (svrs s k) (get_txn_cl cl s) R = None"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "kvs_readers_sqns (kvs_of_gs s') cl = kvs_readers_sqns (kvs_of_gs s) cl"
  oops

lemma get_sqns_tm_commit_grows:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "tm_state (cls s cl) = tm_prepared"
    and "tm_state (cls s' cl) = tm_committed"
    and "\<And>k. km_state (svrs s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock}"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "get_sqns (kvs_of_gs s') cl =
         (if \<forall>k. km_state (svrs s k) (get_txn_cl cl s) = no_lock then
          get_sqns (kvs_of_gs s) cl else
          get_sqns (kvs_of_gs s) cl \<union> {cl_sn (cls s cl)})"
  oops

definition SqnInv where
  "SqnInv s cl \<longleftrightarrow>
    (tm_state (cls s cl) \<noteq> tm_committed \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_gs s) cl. m < cl_sn (cls s cl))) \<and>
    (tm_state (cls s cl) = tm_committed \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_gs s) cl. m \<le> cl_sn (cls s cl)))"


\<comment> \<open>Lemmas for proving view wellformedness of cl_view\<close>

lemma kvs_of_gs_version_order:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl" and "WLockInv s k" and "RLockInv s k" and "KVSNonEmp s"
    and "i \<in> full_view (kvs_of_gs s k)"
    and "tm_state (cls s cl) = tm_prepared"
    and "tm_state (cls s' cl) = tm_committed"
    and "km_state (svrs s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock}"
    and "km_tm_cl'_unchanged cl s s'"
  shows "kvs_of_gs s k ! i \<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r kvs_of_gs s' k ! i"
  oops

lemma new_version_index:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "WLockInv s k" and "KVSNonEmp s"
    and "tm_state (cls s cl) = tm_prepared"
    and "tm_state (cls s' cl) = tm_committed"
    and "km_state (svrs s k) (get_txn_cl cl s) = write_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "i \<in> full_view (update_kv_all_txn (\<lambda>t. tm_state (cls s' (get_cl_txn t)))
    (km_state (svrs s k)) (svr_key_fp (svrs s k)) (svr_vl (svrs s k)))"
    and "i \<notin> full_view (update_kv_all_txn (\<lambda>t. tm_state (cls s (get_cl_txn t)))
    (km_state (svrs s k)) (svr_key_fp (svrs s k)) (svr_vl (svrs s k)))"
  shows "i = length (svr_vl (svrs s k))"
  oops

lemma t_is_fresh:
  assumes "SqnInv s cl"
    and "tm_state (cls s cl) = tm_prepared"
  shows "get_txn_cl cl s \<in> next_txids (kvs_of_gs s) cl"
  oops

lemma kvs_of_gs_view_atomic:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. NoLockFpInv s k"
    and "SqnInv s cl" and "KVSNonEmp s"
    and "tm_state (cls s cl) = tm_prepared"
    and "tm_state (cls s' cl) = tm_committed"
    and "\<forall>k. km_state (svrs s k) (get_txn_cl cl s) \<in> {read_lock, write_lock, no_lock}"
    and "km_tm_cl'_unchanged cl s s'"
  shows "view_atomic (kvs_of_gs s') (\<lambda>k. full_view (kvs_of_gs s k))"
  oops

lemma reach_kvs_expands [simp, intro]:
  assumes "reach tps s" and "gs_trans s e s'"
    and "\<And>cl. TIDFutureKm s cl" and "\<And>cl. TIDPastKm s cl"
    and "\<And>k. RLockInv s k" and "\<And>k. WLockInv s k"
    and "\<And>k. RLockFpInv s k" and "\<And>k. NoLockFpInv s k"
    and "KVSNonEmp s" and "KVSLen s cl"
  shows "kvs_of_gs s \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s kvs_of_gs s'"
  oops

definition KVSView where
  "KVSView s cl \<longleftrightarrow> view_wellformed (kvs_of_gs s) (cl_view (cls s cl))"

\<comment> \<open>CanCommit\<close>

lemma writers_visible:
  assumes "u = (\<lambda>k. full_view (K k))"
  shows "visTx K u = kvs_writers K"
  oops

lemma WW_writers_id_helper:
  assumes "(x, v_writer x') \<in> {(xa, x). \<exists>xb i.
            i \<in> full_view (K xb) \<and>
            (\<exists>i'. i' \<in> full_view (K xb) \<and>
              x = v_writer (K xb ! i) \<and> xa = v_writer (K xb ! i') \<and> i < i')}\<^sup>* "
    and "x' \<in> set (K k)"
  shows "\<exists>xa. x \<in> v_writer ` set (K xa)"
  oops

lemma WW_writers_id:
  "(((\<Union> (range (WW K)))\<inverse>)\<^sup>*)\<inverse> `` kvs_writers K = kvs_writers K"
  oops

lemma full_view_satisfies_ET_SER_canCommit:
  "u = (\<lambda>k. full_view (K k)) \<Longrightarrow> ET_SER.canCommit K u F"
  oops

end