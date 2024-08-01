section \<open>2PC-2PL: State Updates\<close>

theory Serializable_2PC_2PL_State_Updates
  imports Serializable_2PC_2PL_Invariant_Proofs
begin


subsection \<open>Lemmas about version list length and full view under state update\<close>   

(* TODO?: move these down and derive from more general lemmas about state updates? *)

subsubsection \<open>Version list length under updates\<close>

lemma update_kv_key_reads_all_txn_length [simp]:
  "length (update_kv_key_reads_all_txn tStm tSkm tFk vl) = length vl"
  by (auto simp add: update_kv_key_reads_all_defs)

lemma length_update_kv_key_writes_all_txn:
  assumes 
    "(\<forall>t. tSvrs t \<noteq> write_lock) \<or> (\<exists>!t. tSvrs t = write_lock)"
    "\<And>t. tSvrs t = write_lock \<Longrightarrow> tFk t W \<noteq> None"
  shows
    "length (update_kv_key_writes_all_txn tCls tSvrs tFk vl) 
     = (if (\<exists>t. tCls t = cl_committed \<and> tSvrs t = write_lock) 
        then Suc (length vl) else length vl)"
  using assms(1)
  by (auto simp add: update_kv_key_writes_all_txn_def Uniq_I assms(2) the1_equality')

lemma update_kv_key_writes_all_txn_length:
  "length (update_kv_key_writes_all_txn tStm tSkm tFk vl) = Suc (length vl) \<or>
  length (update_kv_key_writes_all_txn tStm tSkm tFk vl) = length vl"
  by (auto simp add: update_kv_key_writes_all_txn_def)

lemma update_kv_key_writes_all_txn_length_increasing [simp]:
  "length vl \<le> length (update_kv_key_writes_all_txn tStm tSkm tFk vl)"
  by (metis Suc_n_not_le_n nat_le_linear update_kv_key_writes_all_txn_length)

lemma update_kv_key_writes_all_txn_on_diff_len:
  assumes "length vl1 \<le> length vl2"
  shows "length (update_kv_key_writes_all_txn tStm tSkm tFk vl1) \<le>
         length (update_kv_key_writes_all_txn tStm tSkm tFk vl2)"
  using assms
  by (auto simp add: update_kv_key_writes_all_txn_def)

lemma update_kv_all_txn_length:
  "length (update_kv_all_txn tStm tSkm tFk vl) = length vl \<or>
  length (update_kv_all_txn tStm tSkm tFk vl) = Suc (length vl)"
  apply (auto simp add: update_kv_all_txn_def)
  by (metis update_kv_key_reads_all_txn_length update_kv_key_writes_all_txn_length)
  
lemma update_kv_all_txn_length_increasing [simp]:
  "length vl \<le> length (update_kv_all_txn tStm tSkm tFk vl)"
  by (metis Suc_n_not_le_n nle_le update_kv_all_txn_length)


subsubsection \<open>Non-emptiness of updated KVS\<close>

lemma update_kv_all_txn_non_empty [simp]:
  assumes "vl \<noteq> []"
  shows "update_kv_all_txn tStm tSkm tFk vl \<noteq> []"
  using assms
  by (metis update_kv_all_txn_length_increasing le_zero_eq length_0_conv)

lemma kvs_non_emp_implies_kvs_gs_non_emp [simp, dest]: "KVSNonEmp s \<Longrightarrow> kvs_initialized (kvs_of_gs s)"
  by (auto simp add: kvs_of_gs_def kvs_initialized_def)

subsubsection \<open>Full view under updates\<close>

lemma full_view_update_kv_all_txnD:
  assumes "i \<in> full_view (update_kv_all_txn tStm tSkm tFk vl)"
  shows "i \<in> full_view vl \<or> (i = length vl \<and> (\<exists>t. tStm t = cl_committed \<and> tSkm t = write_lock))"
  using assms
  by (auto simp add: full_view_def update_kv_all_txn_def update_kv_key_writes_all_txn_def
           split: if_split_asm)

lemma full_view_update_kv_key_reads_all_txn:
  "full_view (update_kv_key_reads_all_txn tStm tSkm tFk vl) = full_view vl"
  by (simp add: full_view_def)


subsection \<open>Writers under version list update\<close>

subsubsection \<open>Writers under version list updates\<close>

lemma v_writer_update_kv_key_reads_all_txn [simp]:
  assumes "i \<in> full_view vl"
  shows "v_writer (update_kv_key_reads_all_txn tStm tSkm tFk vl ! i) = v_writer (vl ! i)"
  using assms
  by (simp add: update_kv_key_reads_all_txn_def Let_def)

lemma v_writer_update_kv_key_writes_all_txn [simp]:
  assumes "i \<in> full_view vl"
  shows "v_writer (update_kv_key_writes_all_txn tStm tSkm tFk vl ! i) = v_writer (vl ! i)"
  using assms
  by (simp add: update_kv_key_writes_all_txn_def update_kv_key_writes_simps)

lemma v_writer_update_kv_all_txn_old:
  assumes "i \<in> full_view vl"
  shows "v_writer (update_kv_all_txn tStm tSkm tFk vl ! i) = v_writer (vl ! i)"
  using assms
  by (simp add: update_kv_all_txn_def full_view_update_kv_key_reads_all_txn)

lemma v_writer_update_kv_all_txn_new:
  assumes "i = length vl" "tStm t = cl_committed" "tSkm t = write_lock" "tFk (the_wr_t tSkm) W \<noteq> None"
  shows "v_writer (update_kv_all_txn tStm tSkm tFk vl ! i) = Tn (the_wr_t tSkm)"
  using assms
  by (auto simp add: update_kv_all_txn_def update_kv_key_writes_all_txn_def 
                     update_kv_key_writes_simps)

lemmas v_writer_update_kv_all_txn_simps = 
  v_writer_update_kv_all_txn_old v_writer_update_kv_all_txn_new


subsubsection \<open>Only initial txn written by @{term "T0"}\<close>

lemma KVS_T0_init_implies_kvs_T0_init:
  assumes "KVS_T0_init gs" "KVSNonEmp gs" "\<And>k. WLockInv gs k"  "\<And>k. WLockFpInv gs k"
  shows "kvs_T0_init (kvs_of_gs gs)"
  using assms
  by (auto simp add: KVS_T0_init_def kvs_T0_init_def kvs_of_gs_def
                     v_writer_update_kv_all_txn_simps WLockFpInv_def the_wr_tI
           dest!: full_view_update_kv_all_txnD)



subsection \<open>General lemmas about version list updates\<close>  

lemma read_only_update [simp]:
  assumes "\<And>t. tSkm t \<noteq> write_lock"
  shows "update_kv_all_txn tStm tSkm tFk vl = update_kv_key_reads_all_txn tStm tSkm tFk vl"
  using assms
  by (auto simp add: update_kv_all_txn_def update_kv_key_writes_all_txn_def)

lemma read_only_update':
  assumes "RLockInv s k"
    and "svr_state (svrs s k) t = read_lock"
  shows "update_kv_all_txn tStm (svr_state (svrs s k)) tFk vl =
         update_kv_key_reads_all_txn tStm (svr_state (svrs s k)) tFk vl"
  using assms
  by (auto simp add: RLockInv_def)

lemma writer_update_before:
  assumes "WLockInv s k"
    and "cl_state (cls s cl) = cl_prepared" 
    and "svr_state (svrs s k) (get_txn cl s) = write_lock"
  shows "update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k)) tFk vl =
         update_kv_key_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k)) tFk vl"
  using assms
  by (auto 4 3 simp add: update_kv_all_txn_def update_kv_key_writes_all_txn_def 
                         WLockInv_def split: option.split)


subsection \<open>Lemmas about state updates for server events\<close>

subsubsection \<open>Eligible reads\<close>

lemma eligible_reads_svr_inv:
  assumes "RLockInv s k"
    and "(svr_state (svrs s k) t \<notin> {write_lock, read_lock} \<and>
          svr_state (svrs s' k) t = svr_state (svrs s k) t) \<or>
          cl_state (cls s (get_cl t)) \<noteq> cl_committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "
  eligible_reads (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s' k)) (svr_fp (svrs s' k)) =
  eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k)) (svr_fp (svrs s k))"
  using assms 
  apply (auto simp add: eligible_reads_def svr_unchanged_defs) 
  by (metis+)

lemma eligible_reads_read_lock_inv:
  assumes "RLockFpInv s k"
    and "svr_state (svrs s k) t = read_lock"
    and "cl_state (cls s (get_cl t)) = cl_committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k))
            (svr_fp (svrs s k)) =
          insert t (eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s' k))
            (svr_fp (svrs s k)))"
  using assms 
  by (auto simp add: eligible_reads_def svr_unchanged_defs)

lemma eligible_reads_write_lock_s_the_t:
  assumes "RLockInv s k" and "WLockInv s k"
    and "svr_state (svrs s k) t = write_lock"
    and "cl_state (cls s (get_cl t)) = cl_committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k))
            (svr_fp (svrs s k)) =
         (case (svr_fp (svrs s k) t R) of None \<Rightarrow> {} | Some y \<Rightarrow> {t})"
  using assms
  apply (auto simp add: eligible_reads_def intro: Collect_empty_eq split: option.split)
  subgoal for t' by (cases "t' = t"; auto simp add: RLockInv_def WLockInv_def svr_unchanged_defs)
  done

lemma eligible_reads_write_lock_s'_empty:
  assumes "RLockInv s k" and "WLockInv s k"
    and "svr_state (svrs s k) t = write_lock"
    and "svr_state (svrs s' k) t = committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s' k))
            (svr_fp (svrs s k)) = {}"
  using assms
  apply (auto simp add: eligible_reads_def intro: Collect_empty_eq)
  subgoal for t' by (cases "t' = t") (auto simp add: RLockInv_def WLockInv_def svr_unchanged_defs)
  subgoal for t' by (cases "t' = t") (auto simp add: RLockInv_def WLockInv_def svr_unchanged_defs)
  done

lemma eligible_reads_no_lock_inv:
  assumes "svr_state (svrs s k) t = no_lock"
    and "svr_state (svrs s' k) t = committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "
  eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s' k)) (svr_fp (svrs s' k)) =
  eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k)) (svr_fp (svrs s k))"
  using assms 
  by (auto simp add: eligible_reads_def svr_unchanged_defs)
     (metis state_svr.distinct(29,33,37,41))+


subsubsection \<open>Read updates\<close>

lemma update_kv_key_reads_commit_w_s_inv:
  assumes "RLockInv s k" and "WLockInv s k"
    and "svr_state (svrs s k) t = write_lock"
    and "cl_state (cls s (get_cl t)) = cl_committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "update_kv_key_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) 
                (svr_state (svrs s k)) (svr_fp (svrs s k)) vl =
        (case (svr_fp (svrs s k) t R) of None \<Rightarrow> vl | Some y \<Rightarrow> 
          vl[Max (full_view vl) := last_version vl (full_view vl)
                \<lparr>v_readerset := v_readerset (last_version vl (full_view vl)) \<union> {t}\<rparr>])"
  using assms eligible_reads_write_lock_s_the_t[of s k t s']
  by (auto simp add: update_kv_key_reads_all_defs split: option.split)

lemma update_kv_key_reads_commit_w_s'_inv:
  assumes "RLockInv s k" and "WLockInv s k"
    and "svr_state (svrs s k) t = write_lock"
    and "svr_state (svrs s' k) t = committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "update_kv_key_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s' k))
    (svr_fp (svrs s k)) vl = vl"
  using assms
  by (simp add: update_kv_key_reads_all_defs eligible_reads_write_lock_s'_empty)


subsubsection \<open>Write updates\<close>

lemma update_kv_key_writes_svr_inv:
  assumes "WLockInv s k"
    and "(\<forall>t. svr_state (svrs s k) t \<noteq> write_lock) \<or> 
              svr_state (svrs s' k) t \<noteq> write_lock"
    and "cl_state (cls s (get_cl t)) \<noteq> cl_committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "update_kv_key_writes_all_txn (\<lambda>t. cl_state (cls s (get_cl t)))
           (svr_state (svrs s' k')) (svr_fp (svrs s' k')) vl =
         update_kv_key_writes_all_txn (\<lambda>t. cl_state (cls s (get_cl t)))
           (svr_state (svrs s k')) (svr_fp (svrs s k')) vl"
  using assms 
  apply (auto simp add: update_kv_key_writes_all_txn_def)
  apply (cases "k' = k"; simp add: svr_unchanged_defs)
  subgoal for t' by (cases "k' = k"; cases "t' = t"; simp add: svr_unchanged_defs)
  apply (cases "k' = k"; simp add: svr_unchanged_defs)
  apply (cases "k' = k", simp_all add: svr_unchanged_defs, smt (verit) WLockInv_def theI)
  subgoal for t' by (cases "k' = k"; cases "t' = t"; simp add: svr_unchanged_defs the_wr_tI)
  by (cases "k' = k"; auto simp add: svr_unchanged_defs the_wr_tI)

lemma update_kv_key_writes_commit_r_inv:
  assumes "RLockInv s k"
    and "svr_state (svrs s k) t = read_lock"
    and "svr_state (svrs s' k) t = committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "update_kv_key_writes_all_txn tStm (svr_state (svrs s' k)) (svr_fp (svrs s k)) vl = 
         update_kv_key_writes_all_txn tStm (svr_state (svrs s k)) (svr_fp (svrs s k)) vl"
  using assms apply (auto simp add: update_kv_key_writes_all_txn_def svr_unchanged_defs)
  by (metis state_svr.distinct(41))

lemma update_kv_key_writes_commit_w_s_inv:
  assumes "WLockInv s k"
    and "svr_state (svrs s k) t = write_lock"
    and "cl_state (cls s (get_cl t)) = cl_committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "update_kv_key_writes_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k))
           (svr_fp (svrs s k)) vl = update_kv_key_writes t (svr_fp (svrs s k) t W) vl"
  using assms apply (auto simp add: update_kv_key_writes_all_txn_def)
  using the_wr_tI by blast

lemma update_kv_key_writes_commit_w_s'_inv:
  assumes "WLockInv s k"
    and "svr_state (svrs s k) t = write_lock"
    and "svr_state (svrs s' k) t = committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "update_kv_key_writes_all_txn tStm (svr_state (svrs s' k)) (svr_fp (svrs s k)) vl = vl"
  using assms apply (auto simp add: update_kv_key_writes_all_txn_def svr_unchanged_defs)
  by (metis state_svr.distinct(41) the_wr_tI)

lemma update_kv_key_writes_commit_n_inv:
  assumes "WLockInv s k"
    and "svr_state (svrs s k) t = no_lock"
    and "svr_state (svrs s' k) t = committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "update_kv_key_writes_all_txn (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s' k))
           (svr_fp (svrs s' k)) vl =
         update_kv_key_writes_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k))
           (svr_fp (svrs s k)) vl"
  using assms apply (auto simp add: update_kv_key_writes_all_txn_def)
  subgoal for t' apply (cases "t' = t"; simp add: svr_unchanged_defs)
    by (smt (verit) state_svr.distinct(41) theI the_wr_tI)
  subgoal for t' by (cases "t' = t"; simp add: svr_unchanged_defs the_wr_tI)
  subgoal for t' by (cases "t' = t"; auto simp add: svr_unchanged_defs the_wr_tI)
  done


subsubsection \<open>Abstracted KVS unchanged\<close>

lemma kvs_of_gs_svr_inv:
  assumes "WLockInv s k" and "RLockInv s k"
    and "(\<forall>t. svr_state (svrs s k) t \<noteq> write_lock) \<or> 
              svr_state (svrs s' k) t \<noteq> write_lock"
    and "cl_state (cls s (get_cl t)) \<noteq> cl_committed"
    and "\<And>k. svr_vl (svrs s' k) = svr_vl (svrs s k)"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "kvs_of_gs s' = kvs_of_gs s"
  using assms 
  apply (auto simp add: kvs_of_gs_def del: disjE) 
  apply (rule ext)
  subgoal for k' using eligible_reads_svr_inv[of s k t s'] 
    by (cases "k' = k") 
       (simp_all add: update_kv_all_txn_def update_kv_key_reads_all_txn_def svr_unchanged_defs
                      update_kv_key_writes_svr_inv)
  done


subsection \<open>Lemmas about state updates for non-commit client events\<close>

subsubsection \<open>Eligible reads\<close>

lemma eligible_reads_cl_inv:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "cl_state (cls s cl) \<noteq> cl_committed \<or>
         (\<forall>k. svr_state (svrs s k) (get_txn cl s) = committed)"
    and "cl_state (cls s' cl) \<noteq> cl_committed"
    and "svr_cl_cl'_unchanged cl s s'"
  shows "
  eligible_reads (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s k)) (svr_fp (svrs s k)) =
  eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k)) (svr_fp (svrs s k))"
  using assms apply (auto simp add: eligible_reads_def cl_unchanged_defs)
  subgoal for t v
    apply (cases "get_cl t = cl"; cases "get_sn t = cl_sn (cls s cl)";
            simp add: cl_unchanged_defs)
    apply (metis txid0.collapse state_svr.distinct(33))
    by (metis empty_iff insert_iff other_sn_idle state_svr.distinct(3)
        state_svr.distinct(33) state_svr.distinct(35))
  subgoal for t v
    apply (cases "get_cl t = cl"; cases "get_sn t = cl_sn (cls s cl)";
            simp add: cl_unchanged_defs)
    apply (metis txid0.collapse state_svr.distinct(41))
    by (metis empty_iff insert_iff other_sn_idle state_svr.distinct(41)
        state_svr.distinct(43) state_svr.distinct(5))
  done

lemma eligible_reads_cl_commit_no_lock_inv:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svr_state (svrs s k) (get_txn cl s) = no_lock"
  shows "
  eligible_reads (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s k)) (svr_fp (svrs s k)) =
  eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k)) (svr_fp (svrs s k))"
  using assms 
  apply (auto simp add: eligible_reads_def other_insts_unchanged_def)
  subgoal for t v
    by (metis insertE other_sn_idle singleton_iff state_svr.distinct(3) state_svr.distinct(35) 
              state_svr.simps(30) state_svr.simps(34) txid0.collapse) 
  subgoal for t v
    by (metis insertE other_sn_idle singleton_iff state_svr.distinct(5) state_svr.simps(38) 
              state_svr.simps(42) state_svr.simps(44) txid0.collapse)
  done


subsubsection \<open>Write updates\<close>

lemma update_kv_key_writes_cl_inv:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "cl_state (cls s cl) \<noteq> cl_committed \<or>
         (\<forall>k. svr_state (svrs s k) (get_txn cl s) = committed)"
    and "cl_state (cls s' cl) \<noteq> cl_committed"
    and "svr_cl_cl'_unchanged cl s s'"
  shows "update_kv_key_writes_all_txn (\<lambda>t. cl_state (cls s' (get_cl t)))
                (svr_state (svrs s k)) (svr_fp (svrs s k)) vl =
         update_kv_key_writes_all_txn (\<lambda>t. cl_state (cls s (get_cl t)))
                (svr_state (svrs s k)) (svr_fp (svrs s k)) vl"
  using assms 
  apply (auto simp add: update_kv_key_writes_all_txn_def cl_unchanged_defs)
  subgoal for t
    apply (cases "get_cl t = cl"; cases "get_sn t = cl_sn (cls s cl)"; simp)
    subgoal by (metis txid0.collapse state_svr.distinct(41))
    subgoal by (metis ex_in_conv insertE other_sn_idle state_svr.distinct(41)
                state_svr.distinct(43) state_svr.distinct(5))
    done
  done


subsubsection \<open>Read and write updates\<close>

lemma update_kv_all_cl_commit_no_lock_inv:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svr_state (svrs s k) (get_txn cl s) = no_lock"
  shows "update_kv_all_txn (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s k))
          (svr_fp (svrs s k)) (svr_vl (svrs s k)) =
         update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k))
          (svr_fp (svrs s k)) (svr_vl (svrs s k))"
  using assms eligible_reads_cl_commit_no_lock_inv[of s cl s' k]
  apply (auto simp add: NoLockFpInv_def update_kv_all_defs other_insts_unchanged_def)
  by (metis (mono_tags, lifting) txid0.collapse insert_compr mem_Collect_eq other_sn_idle singleton_conv2
               state_svr.distinct(37) state_svr.distinct(41) state_svr.distinct(43) state_svr.distinct(5))


subsubsection \<open>Abstracted KVS\<close>

lemma kvs_of_gs_cl_inv:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "cl_state (cls s cl) \<noteq> cl_committed \<or>
         (\<forall>k. svr_state (svrs s k) (get_txn cl s) = committed)"
    and "cl_state (cls s' cl) \<noteq> cl_committed"
    and "svr_cl_cl'_unchanged cl s s'"
  shows "kvs_of_gs s' = kvs_of_gs s"
  using assms
  apply (simp add: kvs_of_gs_def) apply (rule ext)
  using update_kv_key_writes_cl_inv[of s] eligible_reads_cl_inv[of s cl s']
  by (auto simp add: update_kv_all_txn_def update_kv_key_reads_all_txn_def cl_unchanged_defs)


subsection \<open>Abstracted KVS for non-commit events\<close>

lemma kvs_of_gs_not_cl_commit_inv:
  assumes "gs_trans s e s'"
    and "reach tps s"
    and "not_cl_commit e"
  shows "kvs_of_gs s' = kvs_of_gs s"
  using assms
proof (induction e)
  case (Prepare x1 x2)
  then show ?case using kvs_of_gs_svr_inv[of s x1 s' x2]
    by (auto simp add: tps_trans_defs svr_unchanged_defs dest!: svr_vl_eq_all_k)
next
  case (RLock x1 x2 x3)
  then show ?case using kvs_of_gs_svr_inv[of s x1 s' x3]
    by (auto simp add: tps_trans_defs svr_unchanged_defs dest!: svr_vl_eq_all_k)
next
  case (WLock x1 x2 x3 x4)
  then show ?case using kvs_of_gs_svr_inv[of s x1 s' x4]
    by (auto simp add: tps_trans_defs svr_unchanged_defs dest!: svr_vl_eq_all_k)
next
  case (NoLock x1 x2)
  then show ?case using kvs_of_gs_svr_inv[of s x1 s' x2]
    by (auto simp add: tps_trans_defs svr_unchanged_defs dest!: svr_vl_eq_all_k)
next
  case (NOK x1 x2)
  then show ?case using kvs_of_gs_svr_inv[of s x1 s' x2]
    by (auto simp add: tps_trans_defs svr_unchanged_defs dest!: svr_vl_eq_all_k)
next
  case (Commit k t)     (* chsp: we need an additional lemma here *)
  hence "kvs_of_gs s' k = kvs_of_gs s k"
    apply (auto simp add: kvs_of_gs_def commit_def)
    subgoal \<comment> \<open>read lock\<close>
      using eligible_reads_read_lock_inv[of s k t s']
            update_kv_key_writes_commit_r_inv[of s k t s']
            RLockFpInv_def[of s k] KVSNonEmp_def[of s]
      by (auto simp add: update_kv_all_txn_def update_kv_key_reads_all_txn_def Let_def 
                         update_kv_key_ro_v_readerset update_kv_key_ro_set_v_readerset
                         svr_unchanged_defs 
               dest!: eq_for_all_k[where f=svr_fp])   (* loops if not instantiated *)
    subgoal \<comment> \<open>write lock\<close>
      using update_kv_key_reads_commit_w_s_inv[of s k t s']
            update_kv_key_reads_commit_w_s'_inv[of s k t s']
            update_kv_key_writes_commit_w_s_inv[of s k t s']
            update_kv_key_writes_commit_w_s'_inv[of s k t s']
      by (auto simp add: update_kv_all_txn_def update_kv_key_def Let_def
                         svr_unchanged_defs dest: eq_for_all_k split: option.split)
    subgoal \<comment> \<open>no lock\<close>
      using eligible_reads_no_lock_inv[of s k t s']
            update_kv_key_writes_commit_n_inv[of s k t s']
            NoLockFpInv_def[of s k]
      by (auto simp add: update_kv_all_txn_def update_kv_key_reads_all_txn_def
                         svr_unchanged_defs dest: eq_for_all_k) 
    done
  moreover 
  have "\<forall>k'. k' \<noteq> k \<longrightarrow> kvs_of_gs s' k' = kvs_of_gs s k'" using Commit
    by (auto simp add: commit_def svr_unchanged_defs kvs_of_gs_def)
  ultimately show ?case by auto
next
  case (Abort x1 x2)
  then show ?case using kvs_of_gs_svr_inv[of s x1 s' x2]
    by (auto simp add: tps_trans_defs svr_unchanged_defs dest!: svr_vl_eq_all_k)
next
  case (User_Commit x)
  then show ?case using kvs_of_gs_cl_inv[of s x s']
   by (auto simp add: tps_trans_defs cl_unchanged_defs)
next
  case (Cl_Abort x)
  then show ?case using kvs_of_gs_cl_inv[of s x s']
   by (auto simp add: tps_trans_defs cl_unchanged_defs)
next
  case (Cl_ReadyC x)
  then show ?case using kvs_of_gs_cl_inv[of s x s']
   by (auto simp add: tps_trans_defs cl_unchanged_defs)
next
  case (Cl_ReadyA x)
  then show ?case using kvs_of_gs_cl_inv[of s x s']
    by (auto simp add: tps_trans_defs cl_unchanged_defs)
qed auto



subsection \<open>Lemmas about client commit\<close>

lemma cl_commit_expands_eligible_reads:
  assumes "cl_state (cls s' cl) = cl_committed"
    and "other_insts_unchanged cl (cls s) (cls s')"
  shows
  "eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k)) (svr_fp (svrs s k)) \<subseteq>
   eligible_reads (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s k)) (svr_fp (svrs s k))"
  using assms by (auto simp add: eligible_reads_def other_insts_unchanged_def)

lemma cl_commit_expands_eligible_reads':
  assumes "NoLockFpInv s k" and "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "is_locked (svr_state (svrs s k) (get_txn cl s))"
    and "other_insts_unchanged cl (cls s) (cls s')"
  shows 
    "eligible_reads (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s k)) (svr_fp (svrs s k)) 
     = (case svr_fp (svrs s k) (get_txn cl s) R of
   None \<Rightarrow> eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k))
     (svr_fp (svrs s k)) |
   Some _ \<Rightarrow> insert (get_txn cl s) (eligible_reads (\<lambda>t. cl_state (cls s (get_cl t)))
     (svr_state (svrs s k)) (svr_fp (svrs s k))))"
  using assms
  apply (auto simp add: eligible_reads_def other_insts_unchanged_def NoLockFpInv_def 
              split: option.split del: disjE)
  subgoal
    by (metis insertE option.discI other_sn_idle singletonD state_svr.distinct(3,5,33,35,41,43)  
              txid0.collapse)
  subgoal
    by (metis insertE other_sn_idle singletonD state_svr.distinct(3,5,34,36,42,44) txid0.collapse) 
  by auto
  
lemma cl_commit_updates_kv_reads:
  assumes "KVSNonEmp s"
    and "cl_state (cls s' cl) = cl_committed"
    and "other_insts_unchanged cl (cls s) (cls s')"
  shows
  "update_kv_key_reads_all_txn (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s k))
      (svr_fp (svrs s k)) (svr_vl (svrs s k)) = 
   update_kv_key_reads_all_txn (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s k))
      (svr_fp (svrs s k))
        (update_kv_key_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k))
          (svr_fp (svrs s k)) (svr_vl (svrs s k)))"
  using assms cl_commit_expands_eligible_reads[of s' cl s k]
  by (auto simp add: update_kv_key_reads_all_defs Un_assoc subset_Un_eq)

lemma cl_commit_updates_kv_reads':
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "KVSNonEmp s" and "NoLockFpInv s k"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "is_locked (svr_state (svrs s k) (get_txn cl s))"
    and "other_insts_unchanged cl (cls s) (cls s')"
  shows
  "update_kv_key_reads_all_txn (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s k))
      (svr_fp (svrs s k)) (svr_vl (svrs s k)) = 
   update_kv_key_reads (get_txn cl s) (svr_fp (svrs s k) (get_txn cl s) R)
     (full_view (update_kv_key_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k))
          (svr_fp (svrs s k)) (svr_vl (svrs s k))))
        (update_kv_key_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k))
          (svr_fp (svrs s k)) (svr_vl (svrs s k)))"
  using assms cl_commit_expands_eligible_reads'[of s k cl s']
  by (auto simp add: update_kv_key_reads_all_txn_def Let_def
           del: disjE split: option.split)


\<comment> \<open>Cl_commit updating kv\<close>

lemma update_kv_all_txn_cl_commit:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "WLockInv s k" and "WLockFpInv s k"
    and "RLockInv s k" and "RLockFpInv s k"
    and "NoLockFpInv s k" and "KVSNonEmp s"
    and "is_locked (svr_state (svrs s k) (get_txn cl s))"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_cl_cl'_unchanged cl s s'"
  shows "update_kv_all_txn (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s' k))
          (svr_fp (svrs s' k)) (svr_vl (svrs s' k)) =
    update_kv_key (get_txn cl s) (svr_fp (svrs s k) (get_txn cl s))
      (full_view (update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k))
        (svr_fp (svrs s k)) (svr_vl (svrs s k))))
      (update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k))
        (svr_fp (svrs s k)) (svr_vl (svrs s k)))"
  using assms
  apply (auto simp add: update_kv_key_def svr_cl_cl'_unchanged_def)
  subgoal 
    by (auto simp add: read_only_update' cl_commit_updates_kv_reads')
  subgoal
    apply (simp add: writer_update_before)
    by (auto simp add: update_kv_all_txn_def update_kv_key_writes_all_txn_def 
                       cl_commit_updates_kv_reads' the_wr_tI)
  subgoal 
    by (auto simp add: update_kv_all_cl_commit_no_lock_inv)
  done


lemma kvs_of_gs_cl_commit_unfolded:  
  assumes 
    "sn = cl_sn (cls s cl)" 
    "u'' = full_view \<circ> kvs_of_gs s"
    "F = (\<lambda>k. svr_fp (svrs s k) (get_txn cl s))"
    "\<forall>k. is_locked (svr_state (svrs s k) (get_txn cl s))"
    "cl_state (cls s cl) = cl_prepared"
    "cl_state (cls s' cl) = cl_committed"
    "svr_cl_cl'_unchanged cl s s'" 
    "invariant_list_kvs s"
  shows 
    "kvs_of_gs s' = update_kv (Tn_cl sn cl) F u'' (kvs_of_gs s)"
  using assms
  by (auto simp add: update_kv_def kvs_of_gs_def update_kv_all_txn_cl_commit)

lemma kvs_of_gs_cl_commit:  \<comment> \<open>use this whenever possible, rather than low-level lemmas above\<close>
  assumes 
    "cl_commit cl sn u'' F s s'"
    "invariant_list_kvs s"
  shows 
    "kvs_of_gs s' = update_kv (Tn_cl sn cl) F u'' (kvs_of_gs s)"
  using assms
  by (intro kvs_of_gs_cl_commit_unfolded) (simp_all add: cl_commit_def)

(* use these in refinement proof whenever possible: *)
lemmas kvs_of_gs_update_lemmas = kvs_of_gs_not_cl_commit_inv kvs_of_gs_cl_commit


end
