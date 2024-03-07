section \<open>Two Phase Commit (2PC) with Two Phase Locking (2PL)\<close>

theory Serializable_2PC_2PL_Proof
  imports Serializable_2PC_2PL
begin

subsection \<open>Invariants and lemmas\<close>

(*modified version of expanding_feature3 for all txns read update*)
lemma expanding_feature3':
  assumes "i \<in> full_view vl"
    and "x \<in> v_readerset (vl ! i)"
  shows "x \<in> v_readerset (update_kv_key_reads_all_txn tStm tSkm tFk vl ! i)"
  using assms
  by (auto simp add: update_kv_key_reads_all_defs expanding_feature3)

\<comment> \<open>Invariant about future and past transactions svrs\<close>

definition TIDFutureKm where
  "TIDFutureKm s cl \<longleftrightarrow> (\<forall>n k. n > cl_sn (cls s cl) \<longrightarrow> svr_state (svrs s k) (Tn_cl n cl) = working)"

lemmas TIDFutureKmI = TIDFutureKm_def[THEN iffD2, rule_format]
lemmas TIDFutureKmE[elim] = TIDFutureKm_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidfuturekm [simp, dest]: "reach tps s \<Longrightarrow> TIDFutureKm s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: TIDFutureKm_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs tid_match_def TIDFutureKm_def)
      subgoal for n k apply (cases "(Tn_cl n x) = x32"; cases "k = x31", auto) done.
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs TIDFutureKm_def)
      by (metis state_svr.distinct(1))
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs TIDFutureKm_def)
      by (metis state_svr.distinct(1))+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs TIDFutureKm_def)
      by (metis state_svr.distinct(1))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs TIDFutureKm_def)
      by (metis state_svr.distinct(1))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs TIDFutureKm_def)
      apply (metis state_svr.distinct(3))
      apply (metis state_svr.distinct(5))
      by (metis state_svr.distinct(7))
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs TIDFutureKm_def)
      apply (metis state_svr.distinct(3))
      apply (metis state_svr.distinct(5))
      apply (metis state_svr.distinct(7))
      by (metis state_svr.distinct(9))
  next
    case (User_Commit x10)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs cl_unchanged_defs TIDFutureKm_def, metis)
  next
    case (Cl_Commit x111 x112 x113 x114)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs cl_unchanged_defs TIDFutureKm_def, metis)
  next
    case (Cl_Abort x12a)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs cl_unchanged_defs TIDFutureKm_def, metis)
  next
    case (Cl_ReadyC x13a)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs cl_unchanged_defs TIDFutureKm_def)
      by (metis Suc_lessD)
  next
    case (Cl_ReadyA x14)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs cl_unchanged_defs TIDFutureKm_def)
      by (metis Suc_lessD)
  qed simp
qed

definition TIDPastKm where
  "TIDPastKm s cl \<longleftrightarrow> (\<forall>n k. n < cl_sn (cls s cl) \<longrightarrow> svr_state (svrs s k) (Tn_cl n cl) \<in> {committed, aborted})"

lemmas TIDPastKmI = TIDPastKm_def[THEN iffD2, rule_format]
lemmas TIDPastKmE[elim] = TIDPastKm_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidpastkm [simp, dest]: "reach tps s \<Longrightarrow> TIDPastKm s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: TIDPastKm_def tps_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs TIDPastKm_def)
      by (metis state_svr.distinct(11) state_svr.distinct(13))
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs TIDPastKm_def)
      by (metis state_svr.distinct(23) state_svr.distinct(25))
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs TIDPastKm_def)
      by (metis state_svr.distinct(23) state_svr.distinct(25))+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs TIDPastKm_def)
      by (metis state_svr.distinct(23) state_svr.distinct(25))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs TIDPastKm_def)
      by (metis state_svr.distinct(23) state_svr.distinct(25))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs svr_unchanged_defs TIDPastKm_def, fastforce+)
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs svr_unchanged_defs TIDPastKm_def, fastforce+)
  next
    case (User_Commit x10)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs cl_unchanged_defs TIDPastKm_def, metis)
  next
    case (Cl_Commit x111 x112 x113 x114)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs cl_unchanged_defs TIDPastKm_def, metis)
  next
    case (Cl_Abort x12a)
    then show ?thesis using reach_trans
      by (auto simp add: tps_trans_defs cl_unchanged_defs TIDPastKm_def, metis)
  next
    case (Cl_ReadyC x13a)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs cl_unchanged_defs TIDPastKm_def)
        by (metis less_antisym)
  next
    case (Cl_ReadyA x14)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs cl_unchanged_defs TIDPastKm_def)
        by (metis less_antisym)
  qed auto
qed

\<comment> \<open>Lock Invariants\<close>

definition RLockInv where
  "RLockInv s k \<longleftrightarrow> (\<forall>t. svr_state (svrs s k) t = read_lock \<longrightarrow> (\<forall>t. svr_state (svrs s k) t \<noteq> write_lock))"

lemmas RLockInvI = RLockInv_def[THEN iffD2, rule_format]
lemmas RLockInvE[elim] = RLockInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_rlock [simp, dest]: "reach tps s \<Longrightarrow> RLockInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: RLockInv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Prepare x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockInv_def)
      by (metis state_svr.distinct(15) state_svr.distinct(17))
  next
    case (RLock x1 x2 x3)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockInv_def)
      by (metis state_svr.distinct(27))
  next
    case (WLock x1 x2 x3 x4)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockInv_def)
      by (metis state_svr.distinct(27))+
  next
    case (NoLock x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockInv_def)
      by (metis state_svr.distinct(30) state_svr.distinct(38))
  next
    case (NOK x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockInv_def)
      by (metis state_svr.distinct(31) state_svr.distinct(39))
      (*apply (metis state_svr.distinct(31))
      apply (metis state_svr.distinct(31))
      by (metis state_svr.distinct(40))*)
  next
    case (Commit x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockInv_def)
      apply (metis state_svr.distinct(42))
      apply (metis state_svr.distinct(34))
      by (metis state_svr.distinct(34) state_svr.distinct(42))
  next
    case (Abort x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockInv_def)
      apply (metis state_svr.distinct(44))
      apply (metis state_svr.distinct(36))
      apply (metis state_svr.distinct(36) state_svr.distinct(44))
      by (metis state_svr.distinct(35) state_svr.distinct(44))
  qed (auto simp add: tps_trans_defs cl_unchanged_defs RLockInv_def)
qed

definition WLockInv where
  "WLockInv s k \<longleftrightarrow> (\<forall>t. svr_state (svrs s k) t \<noteq> write_lock) \<or> (\<exists>! t. svr_state (svrs s k) t = write_lock)"

lemmas WLockInvI = WLockInv_def[THEN iffD2, rule_format]
lemmas WLockInvE[elim] = WLockInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_wlock [simp, dest]: "reach tps s \<Longrightarrow> WLockInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: WLockInv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockInv_def)
      by (metis state_svr.distinct(17))
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockInv_def)
      by (metis state_svr.distinct(27))
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockInv_def)
      by metis+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockInv_def)
      by (metis state_svr.distinct(37))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockInv_def)
      by (metis state_svr.distinct(39))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockInv_def)
      by (metis state_svr.distinct(41))+
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockInv_def)
      by (metis state_svr.distinct(43))+
  qed (auto simp add: tps_trans_defs cl_unchanged_defs WLockInv_def)
qed

\<comment> \<open>Simulation function lemmas\<close>

lemma the_wr_tI:
  assumes "svr_state (svrs s k) t = write_lock"
      and "WLockInv s k"
  shows "the_wr_t (svr_state (svrs s k)) = t"
  using assms
  by blast

lemma update_kv_key_reads_all_txn_length [simp]:
  "length (update_kv_key_reads_all_txn tStm tSkm tFk vl) = length vl"
  by (auto simp add: update_kv_key_reads_all_defs)

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

lemma index_in_longer_kv':
  assumes  "i \<in> full_view (update_kv_all_txn tStm tSkm tFk vl)"
    and "i \<notin> full_view vl"
  shows "length (update_kv_all_txn tStm tSkm tFk vl) = Suc (length vl)"
  using assms
  using full_view_same_length update_kv_all_txn_length by blast

lemma index_in_longer_kv:
  assumes  "i \<in> full_view (update_kv_all_txn tStm tSkm tFk vl)"
    and "i \<notin> full_view vl"
  shows "i = length vl"
  by (metis assms index_in_longer_kv' full_view_def lessThan_iff less_SucE)

lemma update_kv_all_txn_non_empty [simp]:
  assumes "vl \<noteq> []"
  shows "update_kv_all_txn tStm tSkm tFk vl \<noteq> []"
  using assms
  by (metis update_kv_all_txn_length_increasing le_zero_eq length_0_conv)

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
  by (meson RLockInv_def read_only_update)

lemma writer_update_before:
  assumes "WLockInv s k"
    and "cl_state (cls s cl) = cl_prepared"
    and "svr_state (svrs s k) (get_txn cl s) = write_lock"
  shows "update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k)) tFk vl =
         update_kv_key_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k)) tFk vl"
  using assms
  by (auto 4 3 simp add: update_kv_all_txn_def update_kv_key_writes_all_txn_def 
                         WLockInv_def split: option.split)

\<comment> \<open>lemmas for unchanged elements in svrs\<close>

lemma svr_vl_eq_all_k:
  assumes "svr_vl (svrs s' k) = svr_vl (svrs s k)"
    and "other_insts_unchanged k (svrs s) (svrs s')"
  shows "\<forall>k. svr_vl (svrs s' k) = svr_vl (svrs s k)"
  using assms by (auto simp add: other_insts_unchanged_def)

lemma eq_for_all_k: 
  assumes "f (svrs s' k) t = f (svrs s k) t"
    and "\<And>k'. k' \<noteq> k \<Longrightarrow> svrs s' k' = svrs s k'"
    and "\<And>t'. t' \<noteq> t \<Longrightarrow> f (svrs s' k) t' = f (svrs s k) t'"
  shows "f (svrs s' k) = f (svrs s k)"
  using assms
  apply (auto simp add: fun_eq_iff) 
  subgoal for t' by (cases "t' = t", simp_all)
  done

lemma eq_for_all_cl:
  assumes "f (cls s' cl) = f (cls s cl)"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "f (cls s' cl') = f (cls s cl')"
  using assms 
  by (cases "cl' = cl"; simp)

lemma other_sn_idle:  
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "get_cl t = cl" and "get_sn t \<noteq> cl_sn (cls s cl)"
  shows "\<And>k. svr_state (svrs s k) t \<in> {working, committed, aborted}"
  using assms
  apply (auto simp add: TIDFutureKm_def TIDPastKm_def)
  apply (cases "get_sn t > cl_sn (cls s cl)")
  apply (metis txid0.collapse)
  by (metis linorder_neqE_nat txid0.collapse)

\<comment> \<open>Invariants for fingerprint, knowing the lock (svrs status)\<close>

definition RLockFpInv where
  "RLockFpInv s k \<longleftrightarrow> (\<forall>t. svr_state (svrs s k) t = read_lock \<longrightarrow>
    svr_fp (svrs s k) t W = None \<and>
    svr_fp (svrs s k) t R \<noteq> None)"

lemmas RLockFpInvI = RLockFpInv_def[THEN iffD2, rule_format]
lemmas RLockFpInvE[elim] = RLockFpInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_rlockfp [simp, dest]: "reach tps s \<Longrightarrow> RLockFpInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: RLockFpInv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockFpInv_def)
      by (metis state_svr.distinct(15))+
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockFpInv_def)
      by metis+
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockFpInv_def)
      by (metis state_svr.distinct(27))+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockFpInv_def)
      by (metis state_svr.distinct(29))+
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockFpInv_def)
      by (metis state_svr.distinct(31))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockFpInv_def)
      by (metis state_svr.distinct(33))+
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockFpInv_def)
      by (metis state_svr.distinct(35))+
  qed (auto simp add: tps_trans_defs cl_unchanged_defs RLockFpInv_def)
qed

definition WLockFpInv where
  "WLockFpInv s k \<longleftrightarrow> (\<forall>t. svr_state (svrs s k) t = write_lock \<longrightarrow> svr_fp (svrs s k) t W \<noteq> None)"

lemmas WLockFpInvI = WLockFpInv_def[THEN iffD2, rule_format]
lemmas WLockFpInvE[elim] = WLockFpInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_wlockfp [simp, dest]: "reach tps s \<Longrightarrow> WLockFpInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: WLockFpInv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockFpInv_def)
      by (metis state_svr.distinct(17))
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockFpInv_def)
      by (metis state_svr.distinct(27))
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockFpInv_def)
      by metis+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockFpInv_def)
      by (metis state_svr.distinct(37))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockFpInv_def)
      by (metis state_svr.distinct(39))
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockFpInv_def)
      by (metis state_svr.distinct(41))+
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockFpInv_def)
      by (metis state_svr.distinct(43))+
  qed (auto simp add: tps_trans_defs cl_unchanged_defs WLockFpInv_def)
qed

definition NoLockFpInv where
  "NoLockFpInv s k \<longleftrightarrow> (\<forall>t. svr_state (svrs s k) t = no_lock \<longrightarrow>
    svr_fp (svrs s k) t W = None \<and>
    svr_fp (svrs s k) t R = None)"

lemmas NoLockFpInvI = NoLockFpInv_def[THEN iffD2, rule_format]
lemmas NoLockFpInvE[elim] = NoLockFpInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_nolockfp [simp, dest]: "reach tps s \<Longrightarrow> NoLockFpInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: NoLockFpInv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs NoLockFpInv_def)
      by (metis state_svr.distinct(19))+
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs NoLockFpInv_def)
      by (metis state_svr.distinct(29))+
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs NoLockFpInv_def)
      apply (metis state_svr.distinct(37), metis)
      by (metis state_svr.distinct(37))+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs NoLockFpInv_def)
      by metis+
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs NoLockFpInv_def)
      by (metis state_svr.distinct(45))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs NoLockFpInv_def)
      by (metis state_svr.distinct(47))+
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs NoLockFpInv_def)
      by (metis state_svr.distinct(49))+
  qed (auto simp add: tps_trans_defs cl_unchanged_defs NoLockFpInv_def)
qed

lemma the_wr_t_fp:
  assumes "\<And>k. WLockInv s k"
    and "\<And>k. WLockFpInv s k"
    and "svr_state (svrs s k) t = write_lock"
  shows "svr_fp (svrs s k) (the_wr_t (svr_state (svrs s k))) W \<noteq> None"
  using assms by (auto simp add: WLockInv_def WLockFpInv_def the_wr_tI)

\<comment> \<open>Invariants about kv store\<close>
definition KVSNonEmp where
  "KVSNonEmp s \<longleftrightarrow> (\<forall>k. svr_vl (svrs s k) \<noteq> [])"

lemmas KVSNonEmpI = KVSNonEmp_def[THEN iffD2, rule_format]
lemmas KVSNonEmpE[elim] = KVSNonEmp_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_non_emp [simp, dest]: "reach tps s \<Longrightarrow> KVSNonEmp s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: KVSNonEmp_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Commit x1 x2)
    then show ?case using reach_trans 
      by (auto simp add: KVSNonEmp_def tps_trans_defs svr_unchanged_defs)
         (metis length_greater_0_conv list.size(3) nat.distinct(1) length_update_kv_key)+
  qed (auto simp add: KVSNonEmp_def tps_trans_defs unchanged_defs dest!: svr_vl_eq_all_k)
qed

definition KVSGSNonEmp where    
  "KVSGSNonEmp s \<longleftrightarrow> (\<forall>k. kvs_of_gs s k \<noteq> [])"

lemmas KVSGSNonEmpI = KVSGSNonEmp_def[THEN iffD2, rule_format]
lemmas KVSGSNonEmpE[elim] = KVSGSNonEmp_def[THEN iffD1, elim_format, rule_format]

lemma kvs_non_mp_implies_kvs_gs_non_emp [simp, dest]: "KVSNonEmp s \<Longrightarrow> KVSGSNonEmp s"
  by (auto simp add: KVSGSNonEmp_def kvs_of_gs_def)


subsubsection \<open>Lemmas for kvs_of_gs changing by different events\<close>

(*KM events*)

\<comment> \<open>eligible reads and read updates\<close>
lemma eligible_reads_svr_inv:
  assumes "RLockInv s k"
    and "(svr_state (svrs s k) t \<notin> {write_lock, read_lock} \<and>
          svr_state (svrs s' k) t = svr_state (svrs s k) t) \<or>
          cl_state (cls s (get_cl t)) \<noteq> cl_committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "
  eligible_reads (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s' k)) (svr_fp (svrs s' k)) =
  eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k)) (svr_fp (svrs s k))"
  using assms apply (auto simp add: eligible_reads_def svr_unchanged_defs) 
  by metis+

lemma none_eligible: "vl[Max (full_view vl) := last_version vl (full_view vl)
  \<lparr>v_readerset := v_readerset (last_version vl (full_view vl)) \<union> {}\<rparr>] = vl"
  by (simp)

lemma eligible_reads_read_lock_inv:
  assumes "RLockFpInv s k"
    and "svr_state (svrs s k) t = read_lock"
    and "cl_state (cls s (get_cl t)) = cl_committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k))
            (svr_fp (svrs s k)) =
          insert t (eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s' k))
            (svr_fp (svrs s k)))"
  using assms by (auto simp add: eligible_reads_def svr_unchanged_defs)

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

lemma eligible_reads_write_lock_s'_empty:
  assumes "RLockInv s k" and "WLockInv s k"
    and "svr_state (svrs s k) t = write_lock"
    and "svr_state (svrs s' k) t = committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s' k))
            (svr_fp (svrs s k)) = {}"
  using assms
  apply (auto simp add: eligible_reads_def intro: Collect_empty_eq)
  subgoal for t' by (cases "t' = t"; auto simp add: RLockInv_def WLockInv_def svr_unchanged_defs)
  subgoal for t' by (cases "t' = t"; auto simp add: RLockInv_def WLockInv_def svr_unchanged_defs)
  done

lemma update_kv_key_reads_commit_w_s'_inv:
  assumes "RLockInv s k" and "WLockInv s k"
    and "svr_state (svrs s k) t = write_lock"
    and "svr_state (svrs s' k) t = committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "update_kv_key_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s' k))
    (svr_fp (svrs s k)) vl = vl"
  using assms eligible_reads_write_lock_s'_empty[of s k t s']
  unfolding update_kv_key_reads_all_defs
  by (metis (lifting) none_eligible version.unfold_congs(3))

lemma eligible_reads_no_lock_inv:
  assumes "svr_state (svrs s k) t = no_lock"
    and "svr_state (svrs s' k) t = committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "
  eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s' k)) (svr_fp (svrs s k)) =
  eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k)) (svr_fp (svrs s k))"
  using assms apply (auto simp add: eligible_reads_def svr_unchanged_defs)
  apply (metis state_svr.distinct(33))
  apply (metis state_svr.distinct(41))
  apply (metis state_svr.distinct(29))
  by (metis state_svr.distinct(37))

\<comment> \<open>write updates\<close>
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
  using assms apply (auto simp add: update_kv_key_writes_all_txn_def)
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
  shows "update_kv_key_writes_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s' k))
           (svr_fp (svrs s k)) vl =
         update_kv_key_writes_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k))
           (svr_fp (svrs s k)) vl"
  using assms apply (auto simp add: update_kv_key_writes_all_txn_def)
  subgoal for t' apply (cases "t' = t"; simp add: svr_unchanged_defs)
    by (smt (verit) state_svr.distinct(41) theI the_wr_tI)
  subgoal for t' by (cases "t' = t"; simp add: svr_unchanged_defs the_wr_tI)
  subgoal for t' by (cases "t' = t"; auto simp add: svr_unchanged_defs the_wr_tI).

\<comment> \<open>kvs_of_gs\<close>
lemma kvs_of_gs_svr_inv:
  assumes "WLockInv s k" and "RLockInv s k"
    and "(\<forall>t. svr_state (svrs s k) t \<noteq> write_lock) \<or> 
              svr_state (svrs s' k) t \<noteq> write_lock"
    and "cl_state (cls s (get_cl t)) \<noteq> cl_committed"
    and "\<And>k. svr_vl (svrs s' k) = svr_vl (svrs s k)"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "kvs_of_gs s' = kvs_of_gs s"
  using assms apply (auto simp add: kvs_of_gs_def del: disjE) apply (rule ext)
  subgoal for k' using eligible_reads_svr_inv[of s k t s'] update_kv_key_writes_svr_inv
  by (cases "k' = k"; simp add: update_kv_all_txn_def update_kv_key_reads_all_txn_def svr_unchanged_defs).

(*TM events*)
\<comment> \<open>eligible reads\<close>
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


\<comment> \<open>write updates\<close>
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
  using assms apply (auto simp add: update_kv_key_writes_all_txn_def cl_unchanged_defs)
  subgoal for t
    apply (cases "get_cl t = cl"; cases "get_sn t = cl_sn (cls s cl)"; simp)
    apply (metis txid0.collapse state_svr.distinct(41))
    by (metis ex_in_conv insertE other_sn_idle state_svr.distinct(41)
              state_svr.distinct(43) state_svr.distinct(5)).

\<comment> \<open>kvs_of_gs\<close>
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

(*All events*)
fun not_cl_commit :: "'a ev \<Rightarrow> bool" where
  "not_cl_commit (Cl_Commit cl sn u'' F) = False" |
  "not_cl_commit _ = True"

lemma not_not_cl_commit [simp]: "\<not>not_cl_commit e \<longleftrightarrow> (\<exists>cl sn u'' F. e = Cl_Commit cl sn u'' F)" 
  by (auto elim: not_cl_commit.elims)


abbreviation invariant_list_kvs where
  "invariant_list_kvs s \<equiv> \<forall>cl k. TIDFutureKm s cl \<and> TIDPastKm s cl \<and> RLockInv s k \<and> WLockInv s k \<and>
                        RLockFpInv s k \<and> NoLockFpInv s k \<and> KVSNonEmp s"

lemma kvs_of_gs_inv:
  assumes "gs_trans s e s'"
    and "invariant_list_kvs s"
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
  case (Commit k t)
  hence u: "kvs_of_gs s' k = kvs_of_gs s k"
    apply (auto simp add: kvs_of_gs_def commit_def)
    subgoal 
      using eligible_reads_read_lock_inv[of s k t s']
            update_kv_key_writes_commit_r_inv[of s k t s']
      apply (auto simp add: update_kv_all_txn_def update_kv_key_reads_all_txn_def Let_def
               RLockFpInv_def KVSNonEmp_def svr_unchanged_defs update_kv_key_ro_set_v_readerset
               dest!: eq_for_all_k[where f=svr_fp])   (* loops if not instantiated *)
      (* 
        previous apply is unable to use the RLockFpInv: 
        there is a problem with the way invariants are used here. 
      *)
      apply (drule spec[where x=undefined], clarsimp)  (* what else? there is no free cl here! *)
      apply (rotate_tac -1)
      apply (drule spec[where x=k], clarsimp)
      apply (rotate_tac -3)
      apply (drule spec[where x=t], clarsimp)
      done

(* loops:
      by (auto simp add: update_kv_all_txn_def update_kv_key_reads_all_txn_def Let_def
               RLockFpInv_def KVSNonEmp_def svr_unchanged_defs update_kv_key_ro_set_v_readerset
               dest!: eq_for_all_k)
*)
    subgoal
        using update_kv_key_reads_commit_w_s_inv[of s k t s']
              update_kv_key_reads_commit_w_s'_inv[of s k t s']
              update_kv_key_writes_commit_w_s_inv[of s k t s']
              update_kv_key_writes_commit_w_s'_inv[of s k t s']
        by (auto simp add: update_kv_all_txn_def update_kv_key_def Let_def
            svr_unchanged_defs dest: eq_for_all_k split: option.split)
    subgoal 
        using eligible_reads_no_lock_inv[of s k t s']
        using update_kv_key_writes_commit_n_inv[of s k t s']
        by (auto simp add: update_kv_all_txn_def update_kv_key_reads_all_txn_def
            NoLockFpInv_def svr_unchanged_defs dest: eq_for_all_k) 
    done
  hence "\<forall>k'. k' \<noteq> k \<longrightarrow> kvs_of_gs s' k' = kvs_of_gs s k'" using Commit
    by (auto simp add: commit_def svr_unchanged_defs kvs_of_gs_def)
  then show ?case using u by auto
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

\<comment> \<open>More specific lemmas about TM commit\<close>
lemma kvs_of_gs_commit_length_increasing:
  assumes "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_cl_cl'_unchanged cl s s'"
  shows "length (kvs_of_gs s k) \<le> length (kvs_of_gs s' k)"
  using assms
  by (force simp add: kvs_of_gs_def cl_unchanged_defs update_kv_all_txn_def
                      update_kv_key_writes_all_txn_def)

lemma kvs_of_gs_length_increasing:
  assumes "gs_trans s e s'"
    and "invariant_list_kvs s"
  shows "length (kvs_of_gs s k) \<le> length (kvs_of_gs s' k)"
proof (cases "not_cl_commit e")
  case True
  then show ?thesis using assms by (simp add: kvs_of_gs_inv)
next
  case False
  then show ?thesis using assms(1) 
    by (auto simp add: cl_commit_def kvs_of_gs_commit_length_increasing)
qed


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

lemma cl_commit_writer_update_kv_all:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "WLockInv s k" and "RLockInv s k"
    and "NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn cl s) \<in> {read_lock, write_lock}"
    and "other_insts_unchanged cl (cls s) (cls s')"
  shows
  "update_kv_all_txn (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s k))
      (svr_fp (svrs s k)) (svr_vl (svrs s k)) = 
   update_kv_all_txn (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s k))
      (svr_fp (svrs s k))
        (update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k))
          (svr_fp (svrs s k)) (svr_vl (svrs s k)))"
  using assms apply auto
  subgoal apply (simp add: read_only_update')
    using cl_commit_updates_kv_reads by blast
  subgoal apply (simp add: writer_update_before)
    by (auto simp add: update_kv_all_txn_def cl_commit_updates_kv_reads[of s s' cl k])
  done

\<comment> \<open>Fingerprint content invariant and Lemmas for proving the fp_property\<close>

(* no longer used:
lemma svr_vl_read_lock_commit_eq_length:
  assumes "RLockFpInv s k"
    and "svr_state (svrs s k) t = read_lock"
    and "svr_vl (svrs s' k) =
          update_kv_key t (svr_fp (svrs s k) t) (full_view (svr_vl (svrs s k))) (svr_vl (svrs s k))"
  shows "length (svr_vl (svrs s' k)) = length (svr_vl (svrs s k))"
  using assms
  by (auto)
*)
lemma svr_vl_read_commit_eq_lv:
  assumes "RLockFpInv s k"
    and "svr_state (svrs s k) t = read_lock"
    and "svr_state (svrs s' k) t = committed"
    and "svr_vl (svrs s' k) =
          update_kv_key t (svr_fp (svrs s k) t) (full_view (svr_vl (svrs s k))) (svr_vl (svrs s k))"
  shows "v_value (last_version (svr_vl (svrs s' k)) (full_view (svr_vl (svrs s' k)))) =
         v_value (last_version (svr_vl (svrs s k)) (full_view (svr_vl (svrs s k))))"
  using assms
  by (metis RLockFpInv_def max_in_full_view full_view_update_kv_key_no_write update_kv_key_v_value_inv)


definition RLockFpContentInv where
  "RLockFpContentInv s k \<longleftrightarrow> (\<forall>t. svr_state (svrs s k) t = read_lock \<longrightarrow>
    svr_fp (svrs s k) t R =
      Some (v_value (last_version (svr_vl (svrs s k)) (full_view (svr_vl (svrs s k))))))"

lemmas RLockFpContentInvI = RLockFpContentInv_def[THEN iffD2, rule_format]
lemmas RLockFpContentInvE[elim] = RLockFpContentInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_rlockfp_content [simp, dest]: "reach tps s \<Longrightarrow> RLockFpContentInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: RLockFpContentInv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockFpContentInv_def)
      by (metis state_svr.distinct(15))+
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockFpContentInv_def)
      by metis+
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockFpContentInv_def)
      by (metis state_svr.distinct(27))+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockFpContentInv_def)
      by (metis state_svr.distinct(29))+
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockFpContentInv_def)
      by (metis state_svr.distinct(31))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans svr_vl_read_commit_eq_lv[of s x81 x82 s']
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockFpContentInv_def del: disjE)
      by (smt (verit, best) NoLockFpInv_def RLockInv_def reach_nolockfp reach_rlock 
              state_svr.distinct(33) update_kv_key_nop)
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockFpContentInv_def)
      by (metis state_svr.distinct(35))+
  qed (auto simp add: tps_trans_defs cl_unchanged_defs RLockFpContentInv_def)
qed

definition WLockFpContentInv where
  "WLockFpContentInv s k \<longleftrightarrow> (\<forall>t. svr_state (svrs s k) t = write_lock \<longrightarrow>
    svr_fp (svrs s k) t R = None \<or>
    svr_fp (svrs s k) t R =
      Some (v_value (last_version (svr_vl (svrs s k)) (full_view (svr_vl (svrs s k))))))"

lemmas WLockFpContentInvI = WLockFpContentInv_def[THEN iffD2, rule_format]
lemmas WLockFpContentInvE[elim] = WLockFpContentInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_wlockfp_content [simp, dest]: "reach tps s \<Longrightarrow> WLockFpContentInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: WLockFpContentInv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockFpContentInv_def)
      by (metis state_svr.distinct(17))
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockFpContentInv_def)
      by (metis state_svr.distinct(27))
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockFpContentInv_def)
      by metis+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockFpContentInv_def)
      by (metis state_svr.distinct(37))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockFpContentInv_def)
      by (metis state_svr.distinct(39))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockFpContentInv_def)
      apply (metis RLockInv_def reach_rlock state_svr.distinct(41))
       apply (smt reach_wlock state_svr.distinct(41) the_wr_tI)
      by (metis NoLockFpInv_def reach_nolockfp update_kv_key_nop)
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs WLockFpContentInv_def)
      by (metis state_svr.distinct(43))+
  qed (auto simp add: tps_trans_defs cl_unchanged_defs WLockFpContentInv_def)
qed

lemma update_kv_all_txn_v_value_inv:
  assumes "i \<in> full_view vl"
  shows "v_value (update_kv_all_txn tStm tSkm tFk vl ! i) = v_value (vl ! i)"
  using assms
  by (auto simp add: update_kv_all_defs update_kv_key_writes_simps nth_append full_view_def
           split: option.split)

lemma svr_vl_kvs_eq_length:
  assumes "WLockInv s k" and "RLockInv s k"
    and "cl_state (cls s cl) = cl_prepared"
    and "svr_state (svrs s k) (get_txn cl s) \<in> {read_lock, write_lock}"
  shows "length (kvs_of_gs s k) = length (svr_vl (svrs s k))"
  using assms
  apply (auto simp add: WLockInv_def RLockInv_def kvs_of_gs_def)
  by (metis assms(1) update_kv_key_reads_all_txn_length writer_update_before)

lemma svr_vl_kvs_eq_lv:
  assumes "WLockInv s k" and "RLockInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "svr_state (svrs s k) (get_txn cl s) \<in> {read_lock, write_lock}"
  shows "v_value (last_version (kvs_of_gs s k) (full_view (kvs_of_gs s k))) =
         v_value (last_version (svr_vl (svrs s k)) (full_view (svr_vl (svrs s k))))"
  using assms svr_vl_kvs_eq_length[of s]
    update_kv_all_txn_v_value_inv[of "Max {..<length (svr_vl (svrs s k))}" "svr_vl (svrs s k)"]
  apply (auto simp add: full_view_def kvs_of_gs_def KVSNonEmp_def)
  apply (metis full_view_def lessThan_iff max_in_full_view)
  by (metis full_view_def lessThan_iff max_in_full_view)

\<comment> \<open>Lemmas for view growth after commit\<close>

lemma committed_kvs_view_grows:
  assumes "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_cl_cl'_unchanged cl s s'"
  shows "(\<lambda>k. full_view (kvs_of_gs s k)) \<sqsubseteq> (\<lambda>k. full_view (kvs_of_gs s' k))"
  using assms
  by (smt (verit) full_view_subset_is_length_leq kvs_of_gs_commit_length_increasing view_order_def)

(* FIX: do not use view_order *)
thm view_order_full_view_increasing kvs_of_gs_commit_length_increasing

  
lemma updated_vl_view_grows:
  assumes "svr_vl (svrs s' k) =
    update_kv_key t (svr_fp (svrs s k) t) (full_view (svr_vl (svrs s k))) (svr_vl (svrs s k))"
    and "other_insts_unchanged k (svrs s) (svrs s')"
  shows "(\<lambda>k. full_view (svr_vl (svrs s k))) \<sqsubseteq> (\<lambda>k. full_view (svr_vl (svrs s' k)))"
  using assms 
  by (auto simp add: view_order_def other_insts_unchanged_def)
     (metis insert_iff full_view_update_kv_key_no_write full_view_update_kv_key_write)

lemma cl_view_inv:
  assumes "gs_trans s e s'"
    and "not_cl_commit e"
  shows "cl_view (cls s' cl) = cl_view (cls s cl)"
  using assms 
  by (induction e) (auto simp add: tps_trans_defs unchanged_defs dest: eq_for_all_cl)

lemma updated_is_kvs_of_gs':
  assumes "cl_state (cls s' cl) = cl_committed"
      and "svr_cl_cl'_unchanged cl s s'"
  shows "(full_view o (updated_kvs s cl)) = (full_view o (kvs_of_gs s'))"
  using assms
  apply (auto simp add: kvs_of_gs_def updated_kvs_def cl_unchanged_defs)
  apply (intro arg_cong[where f="\<lambda>h. full_view o h"] ext) 
  apply (intro arg_cong[where f="\<lambda>tStm. update_kv_all_txn tStm _ _ _"]) 
  by auto

definition TMFullView where
  "TMFullView s cl \<longleftrightarrow> cl_view (cls s cl) \<sqsubseteq> (full_view o (kvs_of_gs s))"

lemmas TMFullViewI = TMFullView_def[THEN iffD2, rule_format]
lemmas TMFullViewE[elim] = TMFullView_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_full_view [simp, dest]:
  assumes "reach tps s"
  shows "TMFullView s cl"
  using assms
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: TMFullView_def tps_defs full_view_def view_order_def
        view_init_def kvs_of_gs_def)
next
  case (reach_trans s e s')
  then show ?case apply (cases "not_cl_commit e") using kvs_of_gs_inv[of s e s']
    apply (auto simp add: TMFullView_def cl_view_inv)
    using committed_kvs_view_grows[of s] updated_is_kvs_of_gs'[of s']
    apply (auto simp add: TMFullView_def tps_trans_defs cl_unchanged_defs o_def)
    by (metis (no_types, lifting) view_order_refl view_order_trans)
qed


(********************************************************************************************)
(********************************************************************************************)
(********************************************************************************************)

\<comment> \<open>Cl_commit updating kv\<close>

lemma kvs_of_gs_cl_commit:    (* TODO: check where used and whether generalizable *)
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "WLockInv s k" and "WLockFpInv s k"
    and "RLockInv s k" and "RLockFpInv s k"
    and "NoLockFpInv s k" and "KVSNonEmp s"
    and "is_locked (svr_state (svrs s k) (get_txn cl s))"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "other_insts_unchanged cl (cls s) (cls s')"
  shows "update_kv_all_txn (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s k))
          (svr_fp (svrs s k)) (svr_vl (svrs s k)) =
    update_kv_key (get_txn cl s) (svr_fp (svrs s k) (get_txn cl s))
      (full_view (update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k))
        (svr_fp (svrs s k)) (svr_vl (svrs s k))))
      (update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k))
        (svr_fp (svrs s k)) (svr_vl (svrs s k)))"
  using assms
  apply (auto simp add: update_kv_key_def)
  subgoal using cl_commit_updates_kv_reads'[of s cl k s']
    by (auto simp add: read_only_update')
  subgoal using cl_commit_updates_kv_reads'[of s cl k s']
    apply (simp add: writer_update_before)
    by (auto simp add: update_kv_all_txn_def update_kv_key_writes_all_txn_def the_wr_tI)
  by (auto simp add: update_kv_all_cl_commit_no_lock_inv)


(********************************************************************************************)
(********************************************************************************************)
(********************************************************************************************)


\<comment> \<open>Lemmas about reader and writer transaction id sets (2PC+2PL)\<close>

text \<open>Readers\<close>

lemma vl_readers_update_kv_key_writes_all_txn [simp]:
  "vl_readers (update_kv_key_writes_all_txn tStm tSkm tFk vl) = vl_readers vl"
  by (auto simp add: update_kv_key_writes_all_txn_def)

lemma vl_readers_update_kv_key_reads_all_txn [simp]:
  assumes "vl \<noteq> []"
  shows "vl_readers (update_kv_key_reads_all_txn tStm tSkm tFk vl) = 
         vl_readers vl \<union> eligible_reads tStm tSkm tFk"
  using assms 
  apply (auto simp add: update_kv_key_reads_all_txn_def vl_readers_def Let_def full_view_def 
                        Max_list_index_set set_update del: equalityI)
  apply (simp add: Un_commute)
  apply (subst Un_assoc) 
  apply (intro arg_cong[where f="(\<union>) (eligible_reads tStm tSkm tFk)"])
  apply auto
  subgoal by (meson diff_Suc_less length_greater_0_conv nth_mem)
  subgoal using nth_mem by blast
  subgoal by (metis in_set_conv_nth)
  done

lemma vl_readers_update_kv_all_txn [simp]:
  assumes "vl \<noteq> []"
  shows "vl_readers (update_kv_all_txn tCls tSvrs tFk vl) = 
         vl_readers vl \<union> eligible_reads tCls tSvrs tFk"
  using assms
  by (auto simp add: update_kv_all_txn_def del: equalityI)


text \<open>Readers' sequence numbers\<close>
(*
lemma vl_readers_sqns_update_key_reads_all_txn [simp]:
  assumes "vl \<noteq> []"
  shows "vl_readers_sqns (update_kv_key_reads_all_txn tCls tSvrs tFk vl) cl = 
         vl_readers_sqns vl cl \<union> {n. Tn_cl n cl \<in> eligible_reads tCls tSvrs tFk}"
  using assms
  by (auto simp add: vl_readers_sqns_def)

lemma vl_readers_sqns_update_kv_key_writes_all_txn [simp]:
  "vl_readers_sqns (update_kv_key_writes_all_txn tStm tSkm tFk vl) = vl_readers_sqns vl"
  by (auto simp add: vl_readers_sqns_def)
*)

lemma vl_readers_sqns_update_kv_all_txn [simp]:
  assumes "vl \<noteq> []"
  shows "vl_readers_sqns (update_kv_all_txn tCls tSvrs tFk vl) cl = 
         vl_readers_sqns vl cl \<union> {n. Tn_cl n cl \<in> eligible_reads tCls tSvrs tFk}"
  using assms
  by (auto simp add: vl_readers_sqns_def)


text \<open>Writers\<close>

lemma vl_writers_update_kv_key_reads_all_txn [simp]:
  assumes "vl \<noteq> []"                     
  shows "vl_writers (update_kv_key_reads_all_txn tCls tSvrs tFk vl) = vl_writers vl"
  using assms
  apply (auto simp add: update_kv_key_reads_all_txn_def vl_writers_def Let_def full_view_def 
                        Max_list_index_set intro!: image_set_equality_iff)
  subgoal for i by (cases "i = length vl - 1") (auto)
  done

lemma vl_writers_update_kv_key_writes_all_txn [simp]:
  assumes "\<And>t. tSvrs t = write_lock \<Longrightarrow> (\<exists>!t. tSvrs t = write_lock)"
  shows "vl_writers (update_kv_key_writes_all_txn tCls tSvrs tFk vl) = 
        (if (\<exists>t. tCls t = cl_committed \<and> tSvrs t = write_lock \<and> tFk t W \<noteq> None) 
         then insert (Tn (the_wr_t tSvrs)) (vl_writers vl) 
         else vl_writers vl)"
proof (cases "\<exists>t. tCls t = cl_committed \<and> tSvrs t = write_lock \<and> tFk t W \<noteq> None")
  case True  
  then obtain t v where 
    **: "tCls t = cl_committed" "tSvrs t = write_lock" "tFk t W = Some v"
    by auto
  moreover have "t = the_wr_t tSvrs" using assms **
    by (auto intro: theI2)
  ultimately show ?thesis 
    by (auto simp add: update_kv_key_writes_all_txn_def del: equalityI)
next
  case False
  then show ?thesis using assms
    apply (auto simp add: update_kv_key_writes_all_txn_def del: equalityI)
    by (metis (mono_tags, lifting) option.distinct(1) the_equality)
qed


text \<open>Writers' sequence numbers\<close>

lemma vl_writers_sqns_update_kv_key_reads_all_txn [simp]:
  assumes "vl \<noteq> []"
  shows "vl_writers_sqns (update_kv_key_reads_all_txn tCls tSvrs tFk vl) cl = vl_writers_sqns vl cl"
  using assms
  by (simp add: vl_writers_sqns_def)

lemma vl_writers_sqns_update_kv_key_writes_all_txn [simp]:
  assumes "\<And>t. tSvrs t = write_lock \<Longrightarrow> (\<exists>!t. tSvrs t = write_lock)"
  shows "vl_writers_sqns (update_kv_key_writes_all_txn tCls tSvrs tFk vl) cl = 
         (if (\<exists>t. tCls t = cl_committed \<and> tSvrs t = write_lock \<and> tFk t W \<noteq> None \<and> get_cl t = cl) 
         then insert (get_sn (the_wr_t tSvrs)) (vl_writers_sqns vl cl) 
         else vl_writers_sqns vl cl)"
proof (cases "\<exists>t. tCls t = cl_committed \<and> tSvrs t = write_lock \<and> tFk t W \<noteq> None \<and> get_cl t = cl")
  case True
  then obtain t v where 
    **: "tCls t = cl_committed" "tSvrs t = write_lock" "tFk t W = Some v" "get_cl t = cl" 
    by auto
  moreover have "t = the_wr_t tSvrs" using assms ** 
    by (auto intro: theI2)
  ultimately show ?thesis using assms
    apply (auto simp add: vl_writers_sqns_def del: equalityI)
    by (cases "the_wr_t tSvrs") (auto)
next
  case False 
  then show ?thesis using assms
    apply (auto simp add: vl_writers_sqns_def)
    by (metis (mono_tags, lifting) option.simps(3) the_equality txid0.sel(2))
qed

lemma vl_writers_sqns_update_kv_all_txn [simp]:
  assumes 
    "vl \<noteq> []"
    "\<And>t. tSvrs t = write_lock \<Longrightarrow> (\<exists>!t. tSvrs t = write_lock)"
  shows "vl_writers_sqns (update_kv_all_txn tCls tSvrs tFk vl) cl = 
         (if \<exists>t. tCls t = cl_committed \<and> tSvrs t = write_lock \<and> tFk t W \<noteq> None \<and> get_cl t = cl
          then insert (get_sn (the_wr_t tSvrs)) (vl_writers_sqns vl cl) 
          else vl_writers_sqns vl cl)"
  using assms
  by (auto simp add: update_kv_all_txn_def del: equalityI)


(********************************************************************************************)
(********************************************************************************************)
(********************************************************************************************)


\<comment> \<open>Lemmas for showing transaction id freshness\<close>


lemma kvs_readers_sqns_other_cl_inv:
  assumes "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<And>k. is_locked (svr_state (svrs s k) (get_txn cl s))"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
    and "cl' \<noteq> cl"
  shows "kvs_readers_sqns (kvs_of_gs s') cl' = kvs_readers_sqns (kvs_of_gs s) cl'"
  using assms
  by (auto simp add: kvs_of_gs_def unchanged_defs eligible_reads_def 
                del: equalityI)

(*
lemma vl_writers_sqns_other_cl_inv:
  assumes "KVSNonEmp s"
    and "\<And>k. WLockInv s k"
    and "\<And>k. WLockFpInv s k"
    and "cl' \<noteq> cl"
  shows "vl_writers_sqns (update_kv_key (get_txn cl s) (svr_fp (svrs s k) (get_txn cl s))
      (full_view vl) vl) cl' = vl_writers_sqns vl cl'"
  using assms
  by (auto simp add: update_kv_key_def vl_writers_sqns_def)
*)

lemma kvs_writers_sqns_other_cl_inv:
  assumes "\<And>k. WLockInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<And>k. is_locked (svr_state (svrs s k) (get_txn cl s))"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
    and "cl' \<noteq> cl"
  shows "kvs_writers_sqns (kvs_of_gs s') cl' = kvs_writers_sqns (kvs_of_gs s) cl'"
  using assms
  apply (auto simp add: kvs_of_gs_def unchanged_defs del: equalityI)
  apply (subst vl_writers_sqns_update_kv_all_txn)
  subgoal by auto
  subgoal by auto
  apply (subst vl_writers_sqns_update_kv_all_txn)
  apply (auto del: equalityI)
  done

(*
  apply (auto simp add: kvs_writers_sqns_def kvs_of_gs_def)
  subgoal for x k using kvs_of_gs_cl_commit[of s cl k s'] apply simp apply (rule exI[where x=k])
    by (smt (verit) other_insts_unchanged_def vl_writers_sqns_other_cl_inv)
  subgoal for x k using kvs_of_gs_cl_commit[of s cl k s'] apply simp apply (rule exI[where x=k])
    by (smt (verit) other_insts_unchanged_def vl_writers_sqns_other_cl_inv)
  done
*)

(******)

lemma get_sqns_other_cl_inv:    (****** used twice in SqnInv proof below ******)
  assumes "\<And>k. WLockInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<And>k. is_locked (svr_state (svrs s k) (get_txn cl s))"
    and "svr_cl_cl'_unchanged cl s s'"
    and "cl' \<noteq> cl"
  shows "get_sqns (kvs_of_gs s') cl' = get_sqns (kvs_of_gs s) cl'"
  using assms 
  apply (auto simp add: get_sqns_def kvs_writers_sqns_other_cl_inv
                        kvs_readers_sqns_other_cl_inv svr_cl_cl'_unchanged_def del: equalityI)
  apply (subst kvs_writers_sqns_other_cl_inv, auto)    (* why not automatic? *)
  done

(**********)

(*
lemma vl_writers_sqns_reads_other_cl_inv:   (* NOTE: does not require vl \<noteq> [] *)
  "vl_writers_sqns (update_kv_key_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) tSkm tFk vl) = 
   vl_writers_sqns vl"
  unfolding vl_writers_sqns_def apply (rule ext)
  apply (auto simp add: vl_writers_def in_set_conv_nth image_iff)
  subgoal for cl x i apply (rule bexI[where x="vl ! i"])
     apply (auto simp add: update_kv_key_reads_all_defs)
    by (metis (lifting) nth_list_update_eq nth_list_update_neq version.select_convs(2)
        version.surjective version.update_convs(3))
  subgoal for cl x i apply (rule bexI[where x="update_kv_key_reads_all_txn
      (\<lambda>t. cl_state (cls s (get_cl t))) tSkm tFk vl ! i"])
     apply (auto simp add: update_kv_key_reads_all_defs)
    by (metis (lifting) nth_list_update_eq nth_list_update_neq version.select_convs(2)
        version.surjective version.update_convs(3))
  done
*)


text \<open>Writer sequence numbers during client commit\<close>

lemma new_t_is_in_writers_write_lock:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn cl s) = write_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "vl_writers_sqns (kvs_of_gs s' k) cl = 
         insert (cl_sn (cls s cl)) (vl_writers_sqns (kvs_of_gs s k) cl)"
  using assms 
  by (auto simp add: vl_writers_sqns_def kvs_of_gs_def update_kv_key_def kvs_of_gs_cl_commit)

lemma new_t_is_in_writers_read_lock:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn cl s) = read_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "vl_writers_sqns (kvs_of_gs s' k) cl = vl_writers_sqns (kvs_of_gs s k) cl"
  using assms 
  by (auto simp add: kvs_of_gs_def vl_writers_sqns_def update_kv_key_def kvs_of_gs_cl_commit
                     RLockFpInv_def)

lemma new_t_is_in_writers_no_lock:  (* chsp added *)  (* USING update_kv_all_cl_commit_no_lock_inv *)
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn cl s) = no_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "vl_writers_sqns (kvs_of_gs s' k) cl = vl_writers_sqns (kvs_of_gs s k) cl"
  using assms 
  by (simp add: kvs_of_gs_def update_kv_all_cl_commit_no_lock_inv)

lemmas new_t_is_in_writers_lemmas = 
   new_t_is_in_writers_write_lock new_t_is_in_writers_read_lock new_t_is_in_writers_no_lock


text \<open>Readers sequence numbers during client commit\<close>

lemma new_t_is_in_readers_read_lock:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn cl s) = read_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "vl_readers_sqns (kvs_of_gs s' k) cl = 
         insert (cl_sn (cls s cl)) (vl_readers_sqns (kvs_of_gs s k) cl)"
  using assms 
(*
  apply (auto simp add: kvs_of_gs_def update_kv_key_def RLockFpInv_def KVSNonEmp_def del: equalityI)
*)
  apply (auto simp add: kvs_of_gs_def update_kv_key_def vl_readers_sqns_def kvs_of_gs_cl_commit
                        RLockFpInv_def KVSNonEmp_def)
  (*
    same problem as above: RLockFpInv is not applied (two quantifiers to instantiate)
    NOTE: using fastforce instead of auto above works here, but should possibly improve the way 
    in which invariants are applied.
  *)
  apply fastforce
  done


(********)

lemma eligible_reads_write_lock_no_read:
  assumes "\<And>k. WLockInv s k" and "\<And>k. RLockInv s k" 
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn cl s) = write_lock"
    and "svr_fp (svrs s k) (get_txn cl s) R \<noteq> None"
    and "other_insts_unchanged cl (cls s) (cls s')"
  shows "eligible_reads (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s k)) (svr_fp (svrs s k))
       = insert (get_txn cl s) 
           (eligible_reads (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k)) (svr_fp (svrs s k)))"
  using assms
  by (auto simp add: eligible_reads_def other_insts_unchanged_def) (blast, blast, metis)


(*******)

lemma new_t_is_in_readers_write_lock:      (* chsp: using kvs_of_gs_cl_commit *)
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"  
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn cl s) = write_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "vl_readers_sqns (kvs_of_gs s' k) cl =
         (if svr_fp (svrs s k) (get_txn cl s) R = None
          then vl_readers_sqns (kvs_of_gs s k) cl
          else insert (cl_sn (cls s cl)) (vl_readers_sqns (kvs_of_gs s k) cl))"
proof (cases "svr_fp (svrs s k) (get_txn cl s) R = None")
  case True
  then show ?thesis using assms 
    by (auto simp add: kvs_of_gs_def update_kv_key_def vl_readers_sqns_def kvs_of_gs_cl_commit)
next
  case False
  then show ?thesis using assms 
    by (auto simp add: kvs_of_gs_def KVSNonEmp_def eligible_reads_write_lock_no_read
             del: equalityI)
       (blast)
qed

lemma new_t_is_in_readers_no_lock:   (* chsp added *)  (* USING update_kv_all_cl_commit_no_lock_inv*)
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn cl s) = no_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "vl_readers_sqns (kvs_of_gs s' k) cl = vl_readers_sqns (kvs_of_gs s k) cl"
  using assms 
  by (auto simp add: kvs_of_gs_def update_kv_all_cl_commit_no_lock_inv)

lemmas new_t_is_in_readers_lemmas = 
  new_t_is_in_readers_read_lock new_t_is_in_readers_write_lock new_t_is_in_readers_no_lock


(***********)

lemma kvs_writers_cl_commit_grows:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<forall>k. is_locked (svr_state (svrs s k) (get_txn cl s))"
    and "svr_state (svrs s k) (get_txn cl s) = write_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "kvs_writers_sqns (kvs_of_gs s') cl = 
         insert (cl_sn (cls s cl)) (kvs_writers_sqns (kvs_of_gs s) cl)"
proof (intro kvs_writers_sqns_eq_insert[where k = k])
  show "vl_writers_sqns (kvs_of_gs s' k) cl = insert (cl_sn (cls s cl)) (vl_writers_sqns (kvs_of_gs s k) cl)"
    using assms
    by (simp add: new_t_is_in_writers_write_lock)
next
  fix k'
  have "svr_state (svrs s k') (get_txn cl s) = read_lock \<or>
        svr_state (svrs s k') (get_txn cl s) = write_lock \<or>
        svr_state (svrs s k') (get_txn cl s) = no_lock " using assms by simp
  then show 
    "vl_writers_sqns (kvs_of_gs s' k') cl = insert (cl_sn (cls s cl)) (vl_writers_sqns (kvs_of_gs s k') cl) \<or> 
     vl_writers_sqns (kvs_of_gs s' k') cl = vl_writers_sqns (kvs_of_gs s k') cl" 
    using assms
    by (elim disjE) (simp_all add: new_t_is_in_writers_lemmas)
qed

lemma kvs_writers_cl_commit_doesnt_grow:   (* TODO: REVIEW PROOF *)
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<forall>k. svr_state (svrs s k) (get_txn cl s) \<in> {read_lock, no_lock}"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "kvs_writers_sqns (kvs_of_gs s') cl = kvs_writers_sqns (kvs_of_gs s) cl"
  using assms 
  apply (auto simp add: kvs_of_gs_def cl_unchanged_defs del: equalityI) 
  apply (subst vl_writers_sqns_update_kv_all_txn)
  subgoal by auto
  subgoal by auto
  apply (subst vl_writers_sqns_update_kv_all_txn)
  subgoal by auto
  subgoal by auto
  apply (auto del: equalityI)
  by (metis RLockInv_def insertE other_sn_idle singletonD state_svr.distinct(5) 
            state_svr.simps(38) state_svr.simps(42) state_svr.simps(44) txid0.collapse)

lemma kvs_readers_sqns_cl_commit_grows:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<forall>k. is_locked (svr_state (svrs s k) (get_txn cl s))"
    and "svr_state (svrs s k) (get_txn cl s) = read_lock \<or>
         (svr_state (svrs s k) (get_txn cl s) = write_lock \<and>
          svr_fp (svrs s k) (get_txn cl s) R \<noteq> None)"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "kvs_readers_sqns (kvs_of_gs s') cl = 
         insert (cl_sn (cls s cl)) (kvs_readers_sqns (kvs_of_gs s) cl)"
proof (intro kvs_readers_sqns_eq_insert[where k=k])
  show "vl_readers_sqns (kvs_of_gs s' k) cl = insert (cl_sn (cls s cl)) (vl_readers_sqns (kvs_of_gs s k) cl)" 
    using assms
    by (auto simp add: new_t_is_in_readers_lemmas del: equalityI)
next 
  fix k'
  have "svr_state (svrs s k') (get_txn cl s) = read_lock \<or>
        svr_state (svrs s k') (get_txn cl s) = write_lock \<or>
        svr_state (svrs s k') (get_txn cl s) = no_lock " using assms by simp
  then show 
    "vl_readers_sqns (kvs_of_gs s' k') cl = insert (cl_sn (cls s cl)) (vl_readers_sqns (kvs_of_gs s k') cl) \<or> 
     vl_readers_sqns (kvs_of_gs s' k') cl = vl_readers_sqns (kvs_of_gs s k') cl "
    using assms(1-11,13,14)
    by (elim disjE) (simp_all add: new_t_is_in_readers_lemmas)
qed

lemma kvs_readers_sqns_cl_commit_doesnt_grow:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<And>k. svr_state (svrs s k) (get_txn cl s) = no_lock \<or>
             (svr_state (svrs s k) (get_txn cl s) = write_lock \<and>
              svr_fp (svrs s k) (get_txn cl s) R = None)"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "kvs_readers_sqns (kvs_of_gs s') cl = kvs_readers_sqns (kvs_of_gs s) cl"
  using assms
proof (intro kvs_readers_sqns_eq)
  fix k
  have "svr_state (svrs s k) (get_txn cl s) = no_lock \<or>
             (svr_state (svrs s k) (get_txn cl s) = write_lock \<and>
              svr_fp (svrs s k) (get_txn cl s) R = None)" using assms by simp
  then show "vl_readers_sqns (kvs_of_gs s' k) cl = vl_readers_sqns (kvs_of_gs s k) cl"
    using assms
    by (elim disjE) (auto simp add: new_t_is_in_readers_lemmas del: equalityI)
qed


(********************************************************************************************)

lemma get_sqns_cl_commit_grows:   (* used in SqnInv proof below *)
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<And>k. is_locked (svr_state (svrs s k) (get_txn cl s))"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "get_sqns (kvs_of_gs s') cl =
         (if \<forall>k. svr_state (svrs s k) (get_txn cl s) = no_lock then
          get_sqns (kvs_of_gs s) cl else
          insert (cl_sn (cls s cl)) (get_sqns (kvs_of_gs s) cl))" 
proof (cases "\<forall>k. svr_state (svrs s k) (get_txn cl s) = no_lock")
  case True
  then show ?thesis using assms
    apply (simp add: get_sqns_def)
    apply (simp add:  kvs_of_gs_def)
    by (simp add: kvs_of_gs_def update_kv_all_cl_commit_no_lock_inv)
next
  case False
  then show ?thesis using assms 
  apply simp apply (rule conjI) apply blast
  apply (clarsimp simp add: get_sqns_def)
  using kvs_readers_sqns_cl_commit_doesnt_grow[of s cl s']
        kvs_readers_sqns_cl_commit_grows[of s cl s']
        kvs_writers_cl_commit_doesnt_grow[of s cl s']
        kvs_writers_cl_commit_grows[of s cl s']
  by (smt (verit) Un_insert_left Un_insert_right insert_absorb2 insert_iff)
qed

(********************************************************************************************)
(********************************************************************************************)
(********************************************************************************************)



definition SqnInv where
  "SqnInv s cl \<longleftrightarrow>
    (cl_state (cls s cl) \<noteq> cl_committed \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_gs s) cl. m < cl_sn (cls s cl))) \<and>
    (cl_state (cls s cl) = cl_committed \<longrightarrow> (\<forall>m \<in> get_sqns (kvs_of_gs s) cl. m \<le> cl_sn (cls s cl)))"

lemmas SqnInvI = SqnInv_def[THEN iffD2, rule_format]
lemmas SqnInvE[elim] = SqnInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_sql_inv [simp, dest]:
  assumes "reach tps s"
  shows "SqnInv s cl"
  using assms
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
    apply (auto simp add: SqnInv_def tps_defs kvs_of_gs_def get_sqns_old_def kvs_txids_def
        update_kv_all_defs full_view_def version_init_def)
    apply (auto simp add: kvs_writers_def vl_writers_def)
    by (auto simp add: kvs_readers_def vl_readers_def eligible_reads_def)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_gs_inv[of s e s']
  proof (induction e)
    case (WLock x1 x2 x3 x4)
    then show ?case
      by (auto simp add: SqnInv_def tps_trans_defs svr_unchanged_defs)
  next
    case (NoLock x1 x2)
    then show ?case
      by (auto simp add: SqnInv_def tps_trans_defs svr_unchanged_defs)
  next
    case (User_Commit x)
    then show ?case
      apply (auto simp add: SqnInv_def tps_trans_defs cl_unchanged_defs)
      apply (metis state_cl.distinct(3))
      by (metis state_cl.distinct(7))
  next
    case (Cl_Commit x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: SqnInv_def tps_trans_defs) 
      subgoal using get_sqns_other_cl_inv
        by (smt (verit) insertCI other_insts_unchanged_def reach_kvs_non_emp reach_wlock 
                 svr_cl_cl'_unchanged_def)
      subgoal 
        apply (cases "cl = x1")
        subgoal using get_sqns_cl_commit_grows[of s cl s']
          by (metis dual_order.eq_iff insert_iff nless_le reach_kvs_non_emp reach_nolockfp 
                    reach_rlock reach_rlockfp reach_tidfuturekm reach_tidpastkm reach_wlock 
                    reach_wlockfp svr_cl_cl'_unchanged_def)
        subgoal using get_sqns_other_cl_inv
          by (smt (verit, ccfv_SIG) insertCI other_insts_unchanged_def reach_kvs_non_emp 
                  reach_wlock svr_cl_cl'_unchanged_def)
        done
      done
  next
    case (Cl_Abort x)
    then show ?case apply (auto simp add: SqnInv_def tps_trans_defs cl_unchanged_defs)
    apply (metis state_cl.distinct(7)) by (metis state_cl.distinct(11))
  next
    case (Cl_ReadyC x)
    then show ?case apply (auto simp add: SqnInv_def tps_trans_defs cl_unchanged_defs)
    apply (metis less_Suc_eq_le) by (metis state_cl.distinct(3))
  next
    case (Cl_ReadyA x)
    then show ?case apply (auto simp add: SqnInv_def tps_trans_defs cl_unchanged_defs)
    apply (metis less_Suc_eq state_cl.distinct(11)) by (metis state_cl.distinct(3))
  qed (auto simp add: SqnInv_def tps_trans_defs svr_unchanged_defs)
qed

\<comment> \<open>Lemmas for proving view wellformedness of cl_view\<close>

lemma helper_lemma:
  assumes "i \<in> full_view (update_kv_key_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl t)))
    (svr_state (svrs s k)) (svr_fp (svrs s k)) (svr_vl (svrs s k)))"
  shows "
  update_kv_key_writes (the_wr_t (svr_state (svrs s k))) (svr_fp (svrs s k) (the_wr_t (svr_state (svrs s k))) W)
    (update_kv_key_reads_all_txn (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s k))
      (svr_fp (svrs s k)) (svr_vl (svrs s k))) ! i =
  update_kv_key_reads_all_txn (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s k))
    (svr_fp (svrs s k)) (svr_vl (svrs s k)) ! i"
  using assms
  by (metis assms full_view_def update_kv_key_reads_all_txn_length update_kv_key_writes_simps)

lemma kvs_of_gs_version_order:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl" and "WLockInv s k" and "RLockInv s k" and "KVSNonEmp s"
    and "i \<in> full_view (kvs_of_gs s k)"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "is_locked (svr_state (svrs s k) (get_txn cl s))"
    and "svr_cl_cl'_unchanged cl s s'"
  shows "kvs_of_gs s k ! i \<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r kvs_of_gs s' k ! i"
  using assms
  apply (auto simp add: kvs_of_gs_def svr_cl_cl'_unchanged_def update_kv_all_cl_commit_no_lock_inv)
   apply (simp_all add: writer_update_before read_only_update')
   apply (auto simp add: update_kv_all_txn_def update_kv_key_writes_all_txn_def helper_lemma)
   apply (auto simp add: version_order_def)
   using cl_commit_updates_kv_reads[of s s' cl k] 
     expanding_feature3'[where vl="update_kv_key_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl t)))
      (svr_state (svrs s k)) (svr_fp (svrs s k)) (svr_vl (svrs s k))"]
   by (auto simp add: update_kv_key_reads_all_defs)    (* very slow: ~30s *)

lemma new_writer:
  assumes "WLockInv s k" and "WLockFpInv s k"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn cl s) = write_lock"
  shows "v_writer (update_kv_all_txn (\<lambda>t. cl_state (cls s' (get_cl t))) (svr_state (svrs s k))
    (svr_fp (svrs s k)) (svr_vl (svrs s k)) ! length (svr_vl (svrs s k))) =
   Tn (the_wr_t (svr_state (svrs s k)))"
  using assms
  apply (auto simp add: update_kv_all_txn_def update_kv_key_writes_all_txn_def the_wr_tI 
              split: option.split)
  by (metis WLockFpInv_def nth_append_length update_kv_key_reads_all_txn_length 
            update_kv_key_writes.elims version.select_convs(2))

lemma update_kv_all_txn_v_writer_inv: 
  assumes "i \<in> full_view vl"
  shows "v_writer (update_kv_all_txn tStm tSkm tFk vl ! i) = v_writer (vl ! i)"
  using assms
  by (auto simp add: update_kv_all_defs update_kv_key_writes_simps)

lemma new_version_index:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "WLockInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn cl s) = write_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "i \<in> full_view (update_kv_all_txn (\<lambda>t. cl_state (cls s' (get_cl t)))
    (svr_state (svrs s k)) (svr_fp (svrs s k)) (svr_vl (svrs s k)))"
    and "i \<notin> full_view (update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl t)))
    (svr_state (svrs s k)) (svr_fp (svrs s k)) (svr_vl (svrs s k)))"
  shows "i = length (svr_vl (svrs s k))"
  using assms
  by (meson full_view_length_increasing index_in_longer_kv update_kv_all_txn_length_increasing)

lemma t_is_fresh:
  assumes "SqnInv s cl"
    and "cl_state (cls s cl) = cl_prepared"
  shows "get_txn cl s \<in> next_txids (kvs_of_gs s) cl"
  using assms by (auto simp add: kvs_of_gs_def next_txids_def SqnInv_def)

lemma kvs_of_gs_view_atomic:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. NoLockFpInv s k"
    and "SqnInv s cl" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<forall>k. is_locked (svr_state (svrs s k) (get_txn cl s))"
    and "svr_cl_cl'_unchanged cl s s'"
  shows "view_atomic (kvs_of_gs s') (\<lambda>k. full_view (kvs_of_gs s k))"
  using assms
  apply (auto simp add: kvs_of_gs_def svr_cl_cl'_unchanged_def view_atomic_def)
  subgoal for k k' i i'
    apply (auto elim!: allE[where x=k'])
    apply (auto simp add: update_kv_all_cl_commit_no_lock_inv read_only_update')
     apply (metis full_view_same_length update_kv_key_reads_all_txn_length)
    apply (cases "i' \<in> full_view (update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl t)))
      (svr_state (svrs s k')) (svr_fp (svrs s k')) (svr_vl (svrs s k')))"; simp)
    using new_version_index[of s cl k' s' i'] apply (auto simp add: writer_update_before)
     apply (simp add: new_writer the_wr_tI)
    using cl_commit_writer_update_kv_all[of s cl k s'] apply simp
    using update_kv_all_txn_v_writer_inv[of i
        "update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl t))) (svr_state (svrs s k))
          (svr_fp (svrs s k)) (svr_vl (svrs s k))"] assms(3, 5, 6, 11)
    apply (auto elim!: allE[where x=k])     (* very slow: ~ 25s *)
    apply (simp_all add: update_kv_all_cl_commit_no_lock_inv)
    by (metis t_is_fresh fresh_txid_v_writer kvs_of_gs_def)+
  done

lemma reach_kvs_expands [simp, dest]:
  assumes "reach tps s" and "gs_trans s e s'"
    and "\<And>cl. TIDFutureKm s cl" and "\<And>cl. TIDPastKm s cl"
    and "\<And>k. RLockInv s k" and "\<And>k. WLockInv s k"
    and "\<And>k. RLockFpInv s k" and "\<And>k. NoLockFpInv s k"
    and "KVSNonEmp s"
  shows "kvs_of_gs s \<sqsubseteq>\<^sub>k\<^sub>v\<^sub>s kvs_of_gs s'"
  using assms kvs_of_gs_inv[of s e s'] apply (cases "not_cl_commit e"; auto)
  using kvs_of_gs_view_atomic[of s]
  apply (auto simp add: tps_trans_defs kvs_expands_def vlist_order_def)
    apply (metis full_view_length_increasing kvs_of_gs_commit_length_increasing)
  apply (simp add: kvs_of_gs_version_order)
  by (smt (verit, ccfv_threshold) o_apply view_atomic_def)


definition KVSView where
  "KVSView s cl \<longleftrightarrow> view_wellformed (kvs_of_gs s) (cl_view (cls s cl))"

lemmas KVSViewI = KVSView_def[THEN iffD2, rule_format]
lemmas KVSViewE[elim] = KVSView_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_view [simp, dest]:
  assumes "reach tps s" 
  and "KVSGSNonEmp s" and "TIDPastKm s cl"
  shows "KVSView s cl"
  using assms
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: KVSView_def tps_defs sim_defs update_kv_all_defs
        view_wellformed_defs full_view_def view_init_def)
next
  case (reach_trans s e s')
  then show ?case using kvs_of_gs_inv[of s e s']
  proof (induction e)
    case (WLock x1 x2 x3 x4)
    then show ?case
      by (auto simp add: KVSView_def tps_trans_defs svr_unchanged_defs)
  next
    case (NoLock x1 x2)
    then show ?case
      by (auto simp add: KVSView_def tps_trans_defs svr_unchanged_defs)
  next
    case (User_Commit x)
    then show ?case
      by (auto simp add: KVSView_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Cl_Commit x1 x2 x3 x4)
    then show ?case using updated_is_kvs_of_gs'[of s' x1 s]
      apply (auto simp add: KVSView_def tps_trans_defs cl_unchanged_defs)
      apply (cases "cl = x1")
       apply (simp add: KVSGSNonEmp_def full_view_wellformed)
      by (smt (verit) kvs_expanded_view_wellformed reach_kvs_expands reach_kvs_non_emp 
          reach_nolockfp reach_rlock reach_rlockfp reach_tidfuturekm reach_tidpastkm
          reach_trans.hyps(1) reach_wlock tps_trans)
  next
    case (Cl_Abort x)
    then show ?case
      by (auto simp add: KVSView_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Cl_ReadyC x)
    then show ?case
      by (auto simp add: KVSView_def tps_trans_defs cl_unchanged_defs, metis)
  next
    case (Cl_ReadyA x)
    then show ?case
      by (auto simp add: KVSView_def tps_trans_defs cl_unchanged_defs, metis)
  qed (auto simp add: KVSView_def tps_trans_defs svr_unchanged_defs)
qed

\<comment> \<open>CanCommit\<close>

lemma all_writers_visible: "visTx K (full_view o K) = kvs_writers K"
  apply (auto simp add: visTx_def kvs_writers_def vl_writers_def in_set_conv_nth)
  using list_nth_in_set apply blast
  subgoal for k i apply (rule exI[where x=i]) apply (rule exI[where x= k])
    by (simp add: full_view_def) 
  done



(************)
(*
  STUFF BELOW NEEDS TO BE MOVED ELSEWHERE
*)

(*  not used, but could be useful?

lemma view_in_range_full_view [simp, intro]:
  "kvs_initialized K \<Longrightarrow> view_in_range K (full_view o K)"
  by (auto simp add: view_in_range_defs kvs_initialized_def zero_in_full_view)

lemmas view_in_range_full_view' [simp, intro] = view_in_range_full_view [unfolded o_def]
*)

lemma in_full_view_writers:    (* To: Key_Value_Stores *)
  "\<lbrakk> i \<in> full_view (K k) \<rbrakk> \<Longrightarrow> v_writer (K k ! i) \<in> kvs_writers K"
  by (auto simp add: kvs_writers_def vl_writers_def intro: exI[where x=k])  (* uses list_nth_in_set *)


lemma WW_relates_writers:      (* To: Execution_Tests *)
  "\<lbrakk> (t1, t2) \<in> WW K k \<rbrakk> \<Longrightarrow> t1 \<in> kvs_writers K \<and> t2 \<in> kvs_writers K"
  by (auto simp add: WW_def in_full_view_writers)

(*************)

(* To: Execution_Tests? *)
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
                all_writers_visible R_SER_closed_simplified)


definition invariant_list where   (* chsp removed: KVSGSNonEmp s (derivable) *)
  "invariant_list s \<equiv> (\<forall>cl k. TIDFutureKm s cl \<and> TIDPastKm s cl \<and> RLockInv s k \<and> WLockInv s k \<and>
    RLockFpInv s k \<and> WLockFpInv s k \<and> NoLockFpInv s k \<and> KVSNonEmp s \<and> 
    RLockFpContentInv s k \<and> WLockFpContentInv s k \<and> TMFullView s cl \<and> KVSView s cl \<and> SqnInv s cl)"

lemma invariant_listE [elim]:   (* chsp removed: KVSGSNonEmp s *)
 "\<lbrakk> invariant_list s; 
    \<lbrakk> \<And>cl. TIDFutureKm s cl; \<And>cl. TIDPastKm s cl; \<And>k. RLockInv s k; \<And>k. WLockInv s k;
      \<And>k. RLockFpInv s k; \<And>k. WLockFpInv s k; \<And>k. NoLockFpInv s k; KVSNonEmp s; 
      \<And>k. RLockFpContentInv s k; \<And>k. WLockFpContentInv s k; 
      \<And>cl. TMFullView s cl; \<And>cl. KVSView s cl; \<And>cl. SqnInv s cl \<rbrakk> \<Longrightarrow> P \<rbrakk> 
  \<Longrightarrow> P"
  by (auto simp add: invariant_list_def)

subsection \<open>Refinement Proof\<close>

lemma tps_refines_et_es: "tps \<sqsubseteq>\<^sub>med ET_SER.ET_ES"
proof (intro simulate_ES_fun_with_invariant[where I="invariant_list"])
  fix gs0 :: "'v global_conf"
  assume p: "init tps gs0"
  then show "init ET_SER.ET_ES (sim gs0)"
    by (auto simp add: ET_SER.ET_ES_defs tps_defs sim_defs update_kv_all_defs full_view_def 
                       kvs_init_def v_list_init_def eligible_reads_def lessThan_Suc)
next
  fix gs a and gs' :: "'v global_conf"
  assume p: "tps: gs\<midarrow>a\<rightarrow> gs'" and inv: "invariant_list gs"
  then show "ET_SER.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  using kvs_of_gs_inv[of gs a gs'] cl_view_inv[of gs a gs'] 
  proof (induction a)
    case (Cl_Commit cl sn u'' F)
    show ?case 
    proof -
      { 
        assume cmt: \<open>cl_commit cl sn u'' F gs gs'\<close> and I: \<open>invariant_list gs\<close>
        have \<open>ET_SER.ET_trans_and_fp 
                (kvs_of_gs gs, views_of_gs gs) (ET cl sn u'' F) (kvs_of_gs gs', views_of_gs gs')\<close>
        proof (rule ET_SER.ET_trans_rule [where u'="full_view o (kvs_of_gs gs')"])
          show \<open>views_of_gs gs cl \<sqsubseteq> u''\<close> using cmt I
            by (auto 4 3 simp add: cl_commit_def views_of_gs_def)
        next 
          show \<open>ET_SER.canCommit (kvs_of_gs gs) u'' F\<close> using cmt I 
            by (auto simp add: cl_commit_def full_view_satisfies_ET_SER_canCommit)
        next 
          show \<open>view_wellformed (kvs_of_gs gs) u''\<close> using cmt I
            by (auto 4 4 simp add: cl_commit_def full_view_wellformed)
        next 
          show \<open>view_wellformed (kvs_of_gs gs') (full_view o (kvs_of_gs gs'))\<close> using cmt I
          proof - 
            have "KVSGSNonEmp gs'" using cmt I
              by (simp add: cl_commit_def KVSGSNonEmp_def KVSNonEmp_def invariant_list_def 
                            sim_defs(2) unchanged_defs(4))
            then show ?thesis 
              by (auto simp add: full_view_wellformed)
          qed
        next 
          show \<open>view_wellformed (kvs_of_gs gs) (views_of_gs gs cl)\<close> using I
            thm KVSViewE
            by (auto 4 3 simp add: views_of_gs_def)
        next 
          show \<open>Tn_cl sn cl \<in> next_txids (kvs_of_gs gs) cl\<close> using cmt I
            by (auto simp add: cl_commit_def t_is_fresh)
        next 
          show \<open>fp_property F (kvs_of_gs gs) u''\<close> using cmt I
            apply (auto simp add: cl_commit_def fp_property_def view_snapshot_def)
            subgoal for k y
              apply (cases "svr_state (svrs gs k) (get_txn cl gs) = no_lock")
              subgoal by (auto simp add: NoLockFpInv_def invariant_list_def)
              subgoal by (smt (verit) RLockFpContentInv_def WLockFpContentInv_def
                                      empty_iff insertCI insertE invariant_listE o_apply 
                                      option.distinct(1) option.inject svr_vl_kvs_eq_lv) 
              done
            done
        next 
          show \<open>kvs_of_gs gs' = update_kv (Tn_cl sn cl) F u'' (kvs_of_gs gs)\<close> using cmt I
            by (auto 4 3 simp add: cl_commit_def kvs_of_gs_def update_kv_def 
                                   kvs_of_gs_cl_commit svr_cl_cl'_unchanged_def)         
        next 
          show \<open>views_of_gs gs' = (views_of_gs gs)(cl := full_view o (kvs_of_gs gs'))\<close> using cmt I
            apply (auto simp add: cl_commit_def views_of_gs_def)
            apply (rule ext)
            by (auto simp add: cl_unchanged_defs intro: updated_is_kvs_of_gs')
        qed simp
      }
      then show ?thesis using Cl_Commit
        by (simp only: ET_SER.trans_ET_ES_eq tps_trans gs_trans.simps sim_def med.simps)
    qed
  qed (auto simp add: sim_defs invariant_list_def)
qed (simp add: invariant_list_def)

end
