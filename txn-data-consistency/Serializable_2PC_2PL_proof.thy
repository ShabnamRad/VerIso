section \<open>Two Phase Commit (2PC) with Two Phase Locking (2PL)\<close>

theory Serializable_2PC_2PL_proof
  imports Serializable_2PC_2PL
begin

subsection \<open>Invariants and lemmas\<close>

(*modified version of expanding_feature3 for all txns read update*)
lemma expanding_feature3':
  assumes "i \<in> full_view vl"
    and "x \<in> v_readerset (vl ! i)"
  shows "x \<in> v_readerset (update_kv_reads_all_txn tStm tSkm tFk vl ! i)"
  using assms
  by (auto simp add: update_kv_reads_all_defs expanding_feature3)

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

lemma update_kv_reads_all_txn_length [simp]:
  "length (update_kv_reads_all_txn tStm tSkm tFk vl) = length vl"
  by (auto simp add: update_kv_reads_all_defs)

lemma update_kv_writes_all_txn_length:
  "length (update_kv_writes_all_txn tStm tSkm tFk vl) = Suc (length vl) \<or>
  length (update_kv_writes_all_txn tStm tSkm tFk vl) = length vl"
  by (auto simp add: update_kv_writes_all_txn_def update_kv_writes_length)

lemma update_kv_writes_all_txn_length_increasing [simp]:
  "length vl \<le> length (update_kv_writes_all_txn tStm tSkm tFk vl)"
  by (metis Suc_n_not_le_n nat_le_linear update_kv_writes_all_txn_length)

lemma update_kv_writes_all_txn_on_diff_len:
  assumes "length vl1 \<le> length vl2"
  shows "length (update_kv_writes_all_txn tStm tSkm tFk vl1) \<le>
         length (update_kv_writes_all_txn tStm tSkm tFk vl2)"
  using assms
  by (auto simp add: update_kv_writes_all_txn_def update_kv_writes_on_diff_len)

lemma update_kv_all_txn_length:
  "length (update_kv_all_txn tStm tSkm tFk vl) = length vl \<or>
  length (update_kv_all_txn tStm tSkm tFk vl) = Suc (length vl)"
  apply (auto simp add: update_kv_all_txn_def)
  by (metis update_kv_reads_all_txn_length update_kv_writes_all_txn_length)
  

lemma update_kv_all_txn_length_increasing [simp]:
  "length vl \<le> length (update_kv_all_txn tStm tSkm tFk vl)"
  by (auto simp add: update_kv_all_defs update_kv_writes_def split: option.split)

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
  assumes "\<And>t. svr_state (svrs s k) t \<noteq> write_lock"
  shows "update_kv_all_txn tStm (svr_state (svrs s k)) tFk vl =
         update_kv_reads_all_txn tStm (svr_state (svrs s k)) tFk vl"
  using assms
  by (auto simp add: update_kv_all_txn_def update_kv_writes_all_txn_def)

lemma read_only_update':
  assumes "RLockInv s k"
    and "svr_state (svrs s k) t = read_lock"
  shows "update_kv_all_txn tStm (svr_state (svrs s k)) tFk vl =
         update_kv_reads_all_txn tStm (svr_state (svrs s k)) tFk vl"
  using assms
  by (meson RLockInv_def read_only_update)

lemma writer_update_before:
  assumes "WLockInv s k"
    and "cl_state (cls s cl) = cl_prepared"
    and "svr_state (svrs s k) (get_txn_cl cl s) = write_lock"
  shows "update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k)) tFk vl =
         update_kv_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k)) tFk vl"
  using assms
  apply (auto simp add: update_kv_all_txn_def update_kv_writes_all_txn_def update_kv_writes_def
      WLockInv_def split: option.split)
  by (metis state_cl.distinct(7) txid0.sel(2))


\<comment> \<open>lemmas for unchanged elements in svrs\<close>

lemma svr_vl_eq_all_k:
  assumes "svr_vl (svrs s' k) = svr_vl (svrs s k)"
    and "other_insts_unchanged k (svrs s) (svrs s')"
  shows "\<forall>k. svr_vl (svrs s' k) = svr_vl (svrs s k)"
  using assms by (auto simp add: other_insts_unchanged_def)

lemma eq_for_all_k: 
  assumes "f (svrs s' k) t = f (svrs s k) t"
    and "\<forall>k'. k' \<noteq> k \<longrightarrow> svrs s' k' = svrs s k'"
    and "\<forall>t'. t' \<noteq> t \<longrightarrow> f (svrs s' k) t' = f (svrs s k) t'"
  shows "\<forall>k. f (svrs s' k) = f (svrs s k)"
  apply (auto simp add: fun_eq_iff) using assms
  subgoal for k' t' by (cases "k' = k"; cases "t' = t"; simp).

lemma eq_for_all_cl:
  assumes "f (cls s' cl) = f (cls s cl)"
    and "\<forall>cl'. cl' \<noteq> cl \<longrightarrow> cls s' cl' = cls s cl'"
  shows "\<forall>cl. f (cls s' cl) = f (cls s cl)"
  apply (auto simp add: fun_eq_iff) using assms
  subgoal for cl' by (cases "cl' = cl"; simp).

lemma other_sn_idle:  
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "get_cl_txn t = cl" and "get_sn_txn t \<noteq> cl_sn (cls s cl)"
  shows "\<And>k. svr_state (svrs s k) t \<in> {working, committed, aborted}"
  using assms
  apply (auto simp add: TIDFutureKm_def TIDPastKm_def)
  apply (cases "get_sn_txn t > cl_sn (cls s cl)")
  apply (metis txid0.collapse)
  by (metis linorder_neqE_nat txid0.collapse)

\<comment> \<open>Invariants for fingerprint, knowing the lock (svrs status)\<close>

definition RLockFpInv where
  "RLockFpInv s k \<longleftrightarrow> (\<forall>t. svr_state (svrs s k) t = read_lock \<longrightarrow>
    svr_key_fp (svrs s k) t W = None \<and>
    svr_key_fp (svrs s k) t R \<noteq> None)"

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
  "WLockFpInv s k \<longleftrightarrow> (\<forall>t. svr_state (svrs s k) t = write_lock \<longrightarrow> svr_key_fp (svrs s k) t W \<noteq> None)"

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
    svr_key_fp (svrs s k) t W = None \<and>
    svr_key_fp (svrs s k) t R = None)"

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
  shows "svr_key_fp (svrs s k) (the_wr_t (svr_state (svrs s k))) W \<noteq> None"
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
      apply (auto simp add: KVSNonEmp_def tps_trans_defs svr_unchanged_defs)
      apply (metis bot_nat_0.not_eq_extremum full_view_def full_view_update_kv_writes
            length_0_conv lessThan_iff update_kv_writes_key_decides_length)
      apply (metis length_greater_0_conv update_kv_writes_key_decides_length
            update_kv_writes_length zero_less_Suc)
      by (metis length_greater_0_conv update_kv_writes_key_decides_length
            update_kv_writes_length zero_less_Suc)
  qed (auto simp add: KVSNonEmp_def tps_trans_defs unchanged_defs dest!: svr_vl_eq_all_k)
qed

definition KVSGSNonEmp where
  "KVSGSNonEmp s \<longleftrightarrow> (\<forall>k. kvs_of_gs s k \<noteq> [])"

lemmas KVSGSNonEmpI = KVSGSNonEmp_def[THEN iffD2, rule_format]
lemmas KVSGSNonEmpE[elim] = KVSGSNonEmp_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_gs_non_emp [simp, dest]:
  assumes "reach tps s"
    and "KVSNonEmp s"
  shows "KVSGSNonEmp s"
  using assms
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: KVSGSNonEmp_def kvs_of_gs_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: KVSGSNonEmp_def tps_trans_defs kvs_of_gs_def unchanged_defs)
qed

subsubsection \<open>Lemmas for kvs_of_gs changing by different events\<close>

(*KM events*)

\<comment> \<open>eligible reads and read updates\<close>
lemma eligible_reads_svr_inv:
  assumes "RLockInv s k"
    and "(svr_state (svrs s k) t \<notin> {write_lock, read_lock} \<and>
          svr_state (svrs s' k) t = svr_state (svrs s k) t) \<or>
          cl_state (cls s (get_cl_txn t)) \<noteq> cl_committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "
  eligible_reads (\<lambda>t. cl_state (cls s' (get_cl_txn t))) (svr_state (svrs s' k)) (svr_key_fp (svrs s' k)) t' =
  eligible_reads (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k)) (svr_key_fp (svrs s k)) t'"
  using assms apply (cases "t' = t"; simp add: svr_unchanged_defs) by metis

lemma none_eligible: "vl[Max (full_view vl) := last_version vl (full_view vl)
  \<lparr>v_readerset := v_readerset (last_version vl (full_view vl)) \<union> {}\<rparr>] = vl"
  by (simp add: last_version_def)

lemma eligible_reads_read_lock_inv:
  assumes "RLockFpInv s k"
    and "svr_state (svrs s k) t = read_lock"
    and "cl_state (cls s (get_cl_txn t)) = cl_committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "{t. eligible_reads (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k))
            (svr_key_fp (svrs s k)) t} =
          insert t {t. eligible_reads (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s' k))
            (svr_key_fp (svrs s k)) t}"
  using assms by (auto simp add: svr_unchanged_defs)

lemma eligible_reads_write_lock_s_the_t:
  assumes "RLockInv s k" and "WLockInv s k"
    and "svr_state (svrs s k) t = write_lock"
    and "cl_state (cls s (get_cl_txn t)) = cl_committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "{t. eligible_reads (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k))
            (svr_key_fp (svrs s k)) t} =
         (case (svr_key_fp (svrs s k) t R) of None \<Rightarrow> {} | Some y \<Rightarrow> {t})"
  using assms
  apply (auto intro: Collect_empty_eq split: option.split)
  subgoal for t' by (cases "t' = t"; auto simp add: RLockInv_def WLockInv_def svr_unchanged_defs).

lemma update_kv_reads_commit_w_s_inv:
  assumes "RLockInv s k" and "WLockInv s k"
    and "svr_state (svrs s k) t = write_lock"
    and "cl_state (cls s (get_cl_txn t)) = cl_committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "update_kv_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t))) 
                (svr_state (svrs s k)) (svr_key_fp (svrs s k)) vl =
        (case (svr_key_fp (svrs s k) t R) of None \<Rightarrow> vl | Some y \<Rightarrow> 
          vl[Max (full_view vl) := last_version vl (full_view vl)
                \<lparr>v_readerset := v_readerset (last_version vl (full_view vl)) \<union> {t}\<rparr>])"
  using assms eligible_reads_write_lock_s_the_t[of s k t s']
  by (auto simp add: update_kv_reads_all_defs split: option.split)

lemma eligible_reads_write_lock_s'_empty:
  assumes "RLockInv s k" and "WLockInv s k"
    and "svr_state (svrs s k) t = write_lock"
    and "svr_state (svrs s' k) t = committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "{t. eligible_reads (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s' k))
            (svr_key_fp (svrs s k)) t} = {}"
  using assms
  apply (auto intro: Collect_empty_eq)
  subgoal for t' by (cases "t' = t"; auto simp add: RLockInv_def WLockInv_def svr_unchanged_defs)
  subgoal for t' by (cases "t' = t"; auto simp add: RLockInv_def WLockInv_def svr_unchanged_defs).

lemma update_kv_reads_commit_w_s'_inv:
  assumes "RLockInv s k" and "WLockInv s k"
    and "svr_state (svrs s k) t = write_lock"
    and "svr_state (svrs s' k) t = committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "update_kv_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s' k))
    (svr_key_fp (svrs s k)) vl = vl"
  using assms eligible_reads_write_lock_s'_empty[of s k t s']
  unfolding update_kv_reads_all_defs
  by (metis (lifting) last_version_def none_eligible version.unfold_congs(3))

lemma eligible_reads_no_lock_inv:
  assumes "svr_state (svrs s k) t = no_lock"
    and "svr_state (svrs s' k) t = committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "
  eligible_reads (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s' k)) (svr_key_fp (svrs s k)) t' =
  eligible_reads (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k)) (svr_key_fp (svrs s k)) t'"
  using assms apply (auto simp add: svr_unchanged_defs)
  apply (metis state_svr.distinct(33))
  apply (metis state_svr.distinct(41))
  apply (metis state_svr.distinct(29))
  by (metis state_svr.distinct(37))

\<comment> \<open>write updates\<close>
lemma update_kv_writes_svr_inv:
  assumes "WLockInv s k"
    and "(\<forall>t. svr_state (svrs s k) t \<noteq> write_lock) \<or> 
              svr_state (svrs s' k) t \<noteq> write_lock"
    and "cl_state (cls s (get_cl_txn t)) \<noteq> cl_committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "update_kv_writes_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t)))
                (svr_state (svrs s' k')) (svr_key_fp (svrs s' k')) vl =
               update_kv_writes_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t)))
                (svr_state (svrs s k')) (svr_key_fp (svrs s k')) vl"
  using assms apply (auto simp add: update_kv_writes_all_txn_def)
  apply (cases "k' = k"; simp add: svr_unchanged_defs)
  subgoal for t' by (cases "k' = k"; cases "t' = t"; simp add: svr_unchanged_defs)
  apply (cases "k' = k"; simp add: svr_unchanged_defs)
  apply (cases "k' = k", simp_all add: svr_unchanged_defs, smt (verit) WLockInv_def theI)
  subgoal for t' by (cases "k' = k"; cases "t' = t"; simp add: svr_unchanged_defs the_wr_tI)
  by (cases "k' = k"; auto simp add: svr_unchanged_defs the_wr_tI)

lemma update_kv_writes_commit_r_inv:
  assumes "RLockInv s k"
    and "svr_state (svrs s k) t = read_lock"
    and "svr_state (svrs s' k) t = committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "update_kv_writes_all_txn tStm (svr_state (svrs s' k)) (svr_key_fp (svrs s k)) vl = 
         update_kv_writes_all_txn tStm (svr_state (svrs s k)) (svr_key_fp (svrs s k)) vl"
  using assms apply (auto simp add: update_kv_writes_all_txn_def svr_unchanged_defs)
  by (metis state_svr.distinct(41))

lemma update_kv_writes_commit_w_s_inv:
  assumes "WLockInv s k"
    and "svr_state (svrs s k) t = write_lock"
    and "cl_state (cls s (get_cl_txn t)) = cl_committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "update_kv_writes_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k))
           (svr_key_fp (svrs s k)) vl = update_kv_writes t (svr_key_fp (svrs s k) t) vl"
  using assms apply (auto simp add: update_kv_writes_all_txn_def)
  using the_wr_tI by blast

lemma update_kv_writes_commit_w_s'_inv:
  assumes "WLockInv s k"
    and "svr_state (svrs s k) t = write_lock"
    and "svr_state (svrs s' k) t = committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "update_kv_writes_all_txn tStm (svr_state (svrs s' k)) (svr_key_fp (svrs s k)) vl = vl"
  using assms apply (auto simp add: update_kv_writes_all_txn_def svr_unchanged_defs)
  by (metis state_svr.distinct(41) the_wr_tI)

lemma update_kv_writes_commit_n_inv:
  assumes "WLockInv s k"
    and "svr_state (svrs s k) t = no_lock"
    and "svr_state (svrs s' k) t = committed"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "update_kv_writes_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s' k))
           (svr_key_fp (svrs s k)) vl =
         update_kv_writes_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k))
           (svr_key_fp (svrs s k)) vl"
  using assms apply (auto simp add: update_kv_writes_all_txn_def)
  subgoal for t' apply (cases "t' = t"; simp add: svr_unchanged_defs)
    by (smt (verit) state_svr.distinct(41) theI the_wr_tI)
  subgoal for t' by (cases "t' = t"; simp add: svr_unchanged_defs the_wr_tI)
  subgoal for t' by (cases "t' = t"; auto simp add: svr_unchanged_defs the_wr_tI).

\<comment> \<open>kvs_of_gs\<close>
lemma kvs_of_gs_svr_inv:
  assumes "WLockInv s k" and "RLockInv s k"
    and "(\<forall>t. svr_state (svrs s k) t \<noteq> write_lock) \<or> 
              svr_state (svrs s' k) t \<noteq> write_lock"
    and "cl_state (cls s (get_cl_txn t)) \<noteq> cl_committed"
    and "\<And>k. svr_vl (svrs s' k) = svr_vl (svrs s k)"
    and "cl_svr_k'_t'_unchanged k s s' t"
  shows "kvs_of_gs s' = kvs_of_gs s"
  using assms apply (auto simp add: kvs_of_gs_def del: disjE) apply (rule ext)
  subgoal for k' using eligible_reads_svr_inv[of s k t s'] update_kv_writes_svr_inv
  by (cases "k' = k"; simp add: update_kv_all_txn_def update_kv_reads_all_txn_def svr_unchanged_defs).

(*TM events*)
\<comment> \<open>eligible reads\<close>
lemma eligible_reads_cl_inv:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "cl_state (cls s cl) \<noteq> cl_committed \<or>
         (\<forall>k. svr_state (svrs s k) (get_txn_cl cl s) = committed)"
    and "cl_state (cls s' cl) \<noteq> cl_committed"
    and "svr_cl_cl'_unchanged cl s s'"
  shows "
  eligible_reads (\<lambda>t. cl_state (cls s' (get_cl_txn t))) (svr_state (svrs s k)) (svr_key_fp (svrs s k)) t =
  eligible_reads (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k)) (svr_key_fp (svrs s k)) t"
  using assms apply (auto simp add: update_kv_writes_all_txn_def cl_unchanged_defs)
  subgoal
    apply (cases "get_cl_txn t = cl"; cases "get_sn_txn t = cl_sn (cls s cl)";
            simp add: cl_unchanged_defs)
    apply (metis txid0.collapse state_svr.distinct(33))
    by (metis empty_iff insert_iff other_sn_idle state_svr.distinct(3)
        state_svr.distinct(33) state_svr.distinct(35))
  subgoal
    apply (cases "get_cl_txn t = cl"; cases "get_sn_txn t = cl_sn (cls s cl)";
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
    and "svr_state (svrs s k) (get_txn_cl cl s) = no_lock"
  shows "
  eligible_reads (\<lambda>t. cl_state (cls s' (get_cl_txn t))) (svr_state (svrs s k)) (svr_key_fp (svrs s k)) t =
  eligible_reads (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k)) (svr_key_fp (svrs s k)) t"
  using assms apply (cases "get_cl_txn t = cl"; simp add: other_insts_unchanged_def)
  by (metis empty_iff txid0.collapse insert_iff other_sn_idle
      state_svr.distinct(29) state_svr.distinct(3) state_svr.distinct(33) state_svr.distinct(35)
      state_svr.distinct(37) state_svr.distinct(41) state_svr.distinct(43) state_svr.distinct(5))

\<comment> \<open>write updates\<close>
lemma update_kv_writes_cl_inv:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "cl_state (cls s cl) \<noteq> cl_committed \<or>
         (\<forall>k. svr_state (svrs s k) (get_txn_cl cl s) = committed)"
    and "cl_state (cls s' cl) \<noteq> cl_committed"
    and "svr_cl_cl'_unchanged cl s s'"
  shows "update_kv_writes_all_txn (\<lambda>t. cl_state (cls s' (get_cl_txn t)))
                (svr_state (svrs s k)) (svr_key_fp (svrs s k)) vl =
               update_kv_writes_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t)))
                (svr_state (svrs s k)) (svr_key_fp (svrs s k)) vl"
  using assms apply (auto simp add: update_kv_writes_all_txn_def cl_unchanged_defs)
  subgoal for t
    apply (cases "get_cl_txn t = cl"; cases "get_sn_txn t = cl_sn (cls s cl)"; simp)
    apply (metis txid0.collapse state_svr.distinct(41))
    by (metis ex_in_conv insertE other_sn_idle state_svr.distinct(41)
        state_svr.distinct(43) state_svr.distinct(5)).

\<comment> \<open>kvs_of_gs\<close>
lemma kvs_of_gs_cl_inv:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "cl_state (cls s cl) \<noteq> cl_committed \<or>
         (\<forall>k. svr_state (svrs s k) (get_txn_cl cl s) = committed)"
    and "cl_state (cls s' cl) \<noteq> cl_committed"
    and "svr_cl_cl'_unchanged cl s s'"
  shows "kvs_of_gs s' = kvs_of_gs s"
  using assms
  apply (simp add: kvs_of_gs_def) apply (rule ext)
  using update_kv_writes_cl_inv[of s] eligible_reads_cl_inv[of s cl s']
  by (auto simp add: update_kv_all_txn_def update_kv_reads_all_txn_def cl_unchanged_defs)

lemma update_kv_all_cl_commit_no_lock_inv:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svr_state (svrs s k) (get_txn_cl cl s) = no_lock"
  shows "update_kv_all_txn (\<lambda>t. cl_state (cls s' (get_cl_txn t))) (svr_state (svrs s k))
          (svr_key_fp (svrs s k)) (svr_vl (svrs s k)) =
         update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k))
          (svr_key_fp (svrs s k)) (svr_vl (svrs s k))"
  using assms eligible_reads_cl_commit_no_lock_inv[of s cl s' k]
  apply (auto simp add: NoLockFpInv_def update_kv_all_defs other_insts_unchanged_def)
  apply (metis (mono_tags, lifting) txid0.collapse insert_compr mem_Collect_eq other_sn_idle singleton_conv2
    state_svr.distinct(37) state_svr.distinct(41) state_svr.distinct(43) state_svr.distinct(5))
  by metis

(*All events*)
abbreviation not_cl_commit where
  "not_cl_commit e \<equiv> \<forall>cl sn u F. e \<noteq> Cl_Commit cl sn u F"

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
    case (Commit x1 x2)
    hence u: "kvs_of_gs s' x1 = kvs_of_gs s x1"
      apply (auto simp add: kvs_of_gs_def commit_def)
      subgoal
        using eligible_reads_read_lock_inv[of s x1 x2 s']
              update_kv_writes_commit_r_inv[of s x1 x2 s']
        by (auto simp add: update_kv_all_txn_def update_kv_reads_all_txn_def Let_def
            RLockFpInv_def KVSNonEmp_def svr_unchanged_defs update_kv_key_ro_set_v_readerset
            dest!: eq_for_all_k)
      subgoal
        using update_kv_reads_commit_w_s_inv[of s x1 x2 s']
              update_kv_reads_commit_w_s'_inv[of s x1 x2 s']
              update_kv_writes_commit_w_s_inv[of s x1 x2 s']
              update_kv_writes_commit_w_s'_inv[of s x1 x2 s']
        by (auto simp add: update_kv_all_txn_def update_kv_key_def update_kv_reads_defs
            svr_unchanged_defs dest!: eq_for_all_k split: option.split)
      subgoal
        using eligible_reads_no_lock_inv[of s x1 x2 s']
        using update_kv_writes_commit_n_inv[of s x1 x2 s']
        by (auto simp add: update_kv_all_txn_def update_kv_reads_all_txn_def
            NoLockFpInv_def svr_unchanged_defs dest!: eq_for_all_k) done
    hence "\<forall>k. k \<noteq> x1 \<longrightarrow> kvs_of_gs s' k = kvs_of_gs s k" using Commit
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
  apply (auto simp add: kvs_of_gs_def cl_unchanged_defs update_kv_all_txn_def
      update_kv_writes_all_txn_def update_kv_writes_on_diff_len)
  by (metis (no_types, lifting) update_kv_reads_all_txn_length update_kv_writes_length_increasing)

lemma kvs_of_gs_length_increasing:
  assumes "gs_trans s e s'"
    and "invariant_list_kvs s"
  shows "\<And>k. length (kvs_of_gs s k) \<le> length (kvs_of_gs s' k)"
  using assms
  apply (cases "not_cl_commit e"; simp add: kvs_of_gs_inv)
  apply auto apply (simp add: cl_commit_def) by (auto dest!: kvs_of_gs_commit_length_increasing)

lemma cl_commit_expands_eligible_reads:
  assumes "cl_state (cls s' cl) = cl_committed"
    and "other_insts_unchanged cl (cls s) (cls s')"
  shows
  "{t. eligible_reads (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k)) (svr_key_fp (svrs s k)) t} \<subseteq>
   {t. eligible_reads (\<lambda>t. cl_state (cls s' (get_cl_txn t))) (svr_state (svrs s k)) (svr_key_fp (svrs s k)) t}"
  using assms by (auto simp add: other_insts_unchanged_def)

lemma cl_commit_expands_eligible_reads':
  assumes "NoLockFpInv s k" and "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "is_locked (svr_state (svrs s k) (get_txn_cl cl s))"
    and "other_insts_unchanged cl (cls s) (cls s')"
  shows "{x. eligible_reads (\<lambda>t. cl_state (cls s' (get_cl_txn t))) (svr_state (svrs s k))
    (svr_key_fp (svrs s k)) x} = (case svr_key_fp (svrs s k) (get_txn_cl cl s) R of
   None \<Rightarrow> {x. eligible_reads (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k))
     (svr_key_fp (svrs s k)) x}|
   Some _ \<Rightarrow> insert (get_txn_cl cl s) {x. eligible_reads (\<lambda>t. cl_state (cls s (get_cl_txn t)))
     (svr_state (svrs s k)) (svr_key_fp (svrs s k)) x})"
  using assms
  apply (auto simp add: other_insts_unchanged_def NoLockFpInv_def split: option.split del: disjE)
  subgoal for t apply (cases "get_cl_txn t = cl"; cases "get_sn_txn t = cl_sn (cls s cl)"; simp)
    apply (metis txid0.collapse option.distinct(1))
    by (metis emptyE insert_iff other_sn_idle state_svr.distinct(3) state_svr.distinct(33)
        state_svr.distinct(35) state_svr.distinct(41) state_svr.distinct(43) state_svr.distinct(5))
  subgoal for v t apply (cases "get_cl_txn t = cl"; cases "get_sn_txn t = cl_sn (cls s cl)"; simp)
    apply (metis txid0.collapse)
    by (metis empty_iff insertE other_sn_idle state_svr.distinct(3) state_svr.distinct(33)
        state_svr.distinct(35) state_svr.distinct(41) state_svr.distinct(43) state_svr.distinct(5))
  by auto
  
lemma cl_commit_updates_kv_reads:
  assumes "KVSNonEmp s"
    and "cl_state (cls s' cl) = cl_committed"
    and "other_insts_unchanged cl (cls s) (cls s')"
  shows
  "update_kv_reads_all_txn (\<lambda>t. cl_state (cls s' (get_cl_txn t))) (svr_state (svrs s k))
      (svr_key_fp (svrs s k)) (svr_vl (svrs s k)) = 
   update_kv_reads_all_txn (\<lambda>t. cl_state (cls s' (get_cl_txn t))) (svr_state (svrs s k))
      (svr_key_fp (svrs s k))
        (update_kv_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k))
          (svr_key_fp (svrs s k)) (svr_vl (svrs s k)))"
  using assms cl_commit_expands_eligible_reads[of s' cl s k]
  by (auto simp add: update_kv_reads_all_defs Un_assoc subset_Un_eq)

lemma cl_commit_updates_kv_reads':
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "KVSNonEmp s" and "NoLockFpInv s k"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "is_locked (svr_state (svrs s k) (get_txn_cl cl s))"
    and "other_insts_unchanged cl (cls s) (cls s')"
  shows
  "update_kv_reads_all_txn (\<lambda>t. cl_state (cls s' (get_cl_txn t))) (svr_state (svrs s k))
      (svr_key_fp (svrs s k)) (svr_vl (svrs s k)) = 
   update_kv_reads (get_txn_cl cl s) (svr_key_fp (svrs s k) (get_txn_cl cl s))
     (full_view (update_kv_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k))
          (svr_key_fp (svrs s k)) (svr_vl (svrs s k))))
        (update_kv_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k))
          (svr_key_fp (svrs s k)) (svr_vl (svrs s k)))"
  using assms cl_commit_expands_eligible_reads'[of s k cl s']
  by (auto simp add: update_kv_reads_all_txn_def update_kv_reads_defs
      del:disjE split: option.split)

lemma cl_commit_writer_update_kv_all:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "WLockInv s k" and "RLockInv s k"
    and "NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn_cl cl s) \<in> {read_lock, write_lock}"
    and "other_insts_unchanged cl (cls s) (cls s')"
  shows
  "update_kv_all_txn (\<lambda>t. cl_state (cls s' (get_cl_txn t))) (svr_state (svrs s k))
      (svr_key_fp (svrs s k)) (svr_vl (svrs s k)) = 
   update_kv_all_txn (\<lambda>t. cl_state (cls s' (get_cl_txn t))) (svr_state (svrs s k))
      (svr_key_fp (svrs s k))
        (update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k))
          (svr_key_fp (svrs s k)) (svr_vl (svrs s k)))"
  using assms apply auto
  subgoal apply (simp add: read_only_update')
    using cl_commit_updates_kv_reads by blast
  subgoal apply (simp add: writer_update_before)
    by (auto simp add: update_kv_all_txn_def cl_commit_updates_kv_reads[of s s' cl k])
  done

\<comment> \<open>Fingerprint content invariant and Lemmas for proving the fp_property\<close>

lemma svr_vl_read_lock_commit_eq_length:
  assumes "RLockFpInv s k"
    and "svr_state (svrs s k) t = read_lock"
    and "svr_vl (svrs s' k) =
          update_kv_key t (svr_key_fp (svrs s k) t) (full_view (svr_vl (svrs s k))) (svr_vl (svrs s k))"
  shows "length (svr_vl (svrs s' k)) = length (svr_vl (svrs s k))"
  using assms
  apply (auto simp add: RLockFpInv_def)
  by (metis update_kv_writes_key_decides_length update_kv_writes_none_length)

lemma svr_vl_read_commit_eq_lv:
  assumes "RLockFpInv s k"
    and "svr_state (svrs s k) t = read_lock"
    and "svr_state (svrs s' k) t = committed"
    and "svr_vl (svrs s' k) =
          update_kv_key t (svr_key_fp (svrs s k) t) (full_view (svr_vl (svrs s k))) (svr_vl (svrs s k))"
  shows "v_value (last_version (svr_vl (svrs s' k)) (full_view (svr_vl (svrs s' k)))) =
         v_value (last_version (svr_vl (svrs s k)) (full_view (svr_vl (svrs s k))))"
  using assms svr_vl_read_lock_commit_eq_length[of s k t s']
  apply (auto simp add: last_version_def)
  by (metis full_view_def max_in_full_view update_kv_key_v_value_inv)

definition RLockFpContentInv where
  "RLockFpContentInv s k \<longleftrightarrow> (\<forall>t. svr_state (svrs s k) t = read_lock \<longrightarrow>
    svr_key_fp (svrs s k) t R =
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
      by (metis NoLockFpInv_def RLockInv_def reach_nolockfp reach_rlock state_svr.distinct(33)
          update_kv_key_empty_fp)
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tps_trans_defs svr_unchanged_defs RLockFpContentInv_def)
      by (metis state_svr.distinct(35))+
  qed (auto simp add: tps_trans_defs cl_unchanged_defs RLockFpContentInv_def)
qed

definition WLockFpContentInv where
  "WLockFpContentInv s k \<longleftrightarrow> (\<forall>t. svr_state (svrs s k) t = write_lock \<longrightarrow>
    svr_key_fp (svrs s k) t R = None \<or>
    svr_key_fp (svrs s k) t R =
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
      by (metis NoLockFpInv_def reach_nolockfp update_kv_key_empty_fp)
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
  using assms update_kv_writes_version_inv
  by (auto simp add: update_kv_all_defs update_kv_writes_def nth_append full_view_def
      split: option.split)

lemma svr_vl_kvs_eq_length:
  assumes "WLockInv s k" and "RLockInv s k"
    and "cl_state (cls s cl) = cl_prepared"
    and "svr_state (svrs s k) (get_txn_cl cl s) \<in> {read_lock, write_lock}"
  shows "length (kvs_of_gs s k) = length (svr_vl (svrs s k))"
  using assms
  apply (auto simp add: WLockInv_def RLockInv_def kvs_of_gs_def)
  by (metis assms(1) update_kv_reads_all_txn_length writer_update_before)

lemma svr_vl_kvs_eq_lv:
  assumes "WLockInv s k" and "RLockInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "svr_state (svrs s k) (get_txn_cl cl s) \<in> {read_lock, write_lock}"
  shows "v_value (last_version (kvs_of_gs s k) (full_view (kvs_of_gs s k))) =
         v_value (last_version (svr_vl (svrs s k)) (full_view (svr_vl (svrs s k))))"
  using assms svr_vl_kvs_eq_length[of s]
    update_kv_all_txn_v_value_inv[of "Max {..<length (svr_vl (svrs s k))}" "svr_vl (svrs s k)"]
  apply (auto simp add: full_view_def last_version_def kvs_of_gs_def KVSNonEmp_def)
  apply (metis full_view_def lessThan_iff max_in_full_view)
  by (metis full_view_def lessThan_iff max_in_full_view)

\<comment> \<open>Lemmas for view growth after commit\<close>

lemma committed_kvs_view_grows:
  assumes "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_cl_cl'_unchanged cl s s'"
  shows "(\<lambda>k. full_view (kvs_of_gs s k)) \<sqsubseteq> (\<lambda>k. full_view (kvs_of_gs s' k))"
  using assms
  by (metis view_order_full_view_increasing kvs_of_gs_commit_length_increasing)
  
lemma updated_vl_view_grows:
  assumes "svr_vl (svrs s' k) =
    update_kv_key t (svr_key_fp (svrs s k) t) (full_view (svr_vl (svrs s k))) (svr_vl (svrs s k))"
    and "other_insts_unchanged k (svrs s) (svrs s')"
  shows "(\<lambda>k. full_view (svr_vl (svrs s k))) \<sqsubseteq> (\<lambda>k. full_view (svr_vl (svrs s' k)))"
  using assms update_kv_key_length_increasing[of "svr_vl (svrs s k)" t "svr_key_fp (svrs s k) t"
      "full_view (svr_vl (svrs s k))"]
  apply (auto simp add: view_order_def other_insts_unchanged_def)
  subgoal for k' x by (cases "k' = k"; auto simp add: full_view_length_increasing).

lemma cl_view_inv:
  assumes "gs_trans s e s'"
    and "not_cl_commit e"
  shows "cl_view (cls s' cl) = cl_view (cls s cl)"
  using assms by (induction e) (auto simp add: tps_trans_defs unchanged_defs dest!:eq_for_all_cl)

lemma updated_is_kvs_of_gs':
  assumes "cl_state (cls s' cl) = cl_committed"
      and "svr_cl_cl'_unchanged cl s s'"
  shows "(\<lambda>k. full_view (updated_kvs s cl k)) = (\<lambda>k. full_view (kvs_of_gs s' k))"
  using assms
  apply (auto simp add: kvs_of_gs_def updated_kvs_def cl_unchanged_defs)
  apply (rule ext, rule arg_cong[where f=full_view])
  apply (rule arg_cong[where f="\<lambda>tStm. update_kv_all_txn tStm _ _ _"]) by auto

definition TMFullView where
  "TMFullView s cl \<longleftrightarrow> cl_view (cls s cl) \<sqsubseteq> (\<lambda>k. full_view (kvs_of_gs s k))"

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
    by (metis (no_types, lifting) view_order_refl view_order_transitive)
qed

\<comment> \<open>Cl_commit updating kv\<close>

lemma or3_not_eq:
  assumes "\<forall>k. P k = a \<or> P k = b \<or> P k = c"
    and "P k \<noteq> c"
  shows "P k = a \<or> P k = b"
  using assms by auto

lemma kvs_of_gs_cl_commit:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "WLockInv s k" and "WLockFpInv s k"
    and "RLockInv s k" and "RLockFpInv s k"
    and "NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "is_locked (svr_state (svrs s k) (get_txn_cl cl s))"
    and "cl_state (cls s' cl) = cl_committed"
    and "other_insts_unchanged cl (cls s) (cls s')"
  shows "update_kv_all_txn (\<lambda>t. cl_state (cls s' (get_cl_txn t))) (svr_state (svrs s k))
          (svr_key_fp (svrs s k)) (svr_vl (svrs s k)) =
    update_kv_key (get_txn_cl cl s) (svr_key_fp (svrs s k) (get_txn_cl cl s))
      (full_view (update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k))
        (svr_key_fp (svrs s k)) (svr_vl (svrs s k))))
      (update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k))
        (svr_key_fp (svrs s k)) (svr_vl (svrs s k)))"
  using assms
  apply (auto simp add: update_kv_key_def)
  subgoal using cl_commit_updates_kv_reads'[of s cl k s']
    by (auto simp add: read_only_update' update_kv_writes_def)
  subgoal using cl_commit_updates_kv_reads'[of s cl k s']
    apply (simp add: writer_update_before)
    by (auto simp add: update_kv_all_txn_def update_kv_writes_all_txn_def the_wr_tI)
  by (auto simp add: update_kv_writes_def update_kv_reads_def update_kv_all_cl_commit_no_lock_inv)

\<comment> \<open>Lemmas about reader and writer transaction sets\<close>
lemma update_kv_writes_all_txn_v_readerset_set:
  "vl_readers (update_kv_writes_all_txn tStm tSkm tFk vl) = vl_readers vl"
  by (auto simp add: update_kv_writes_all_txn_def update_kv_writes_def split: option.split)

\<comment> \<open>Lemmas for showing transaction id freshness\<close>

lemma vl_writers_sqns_reads_other_cl_inv:
  "vl_writers_sqns (update_kv_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t))) tSkm tFk vl) = 
   vl_writers_sqns vl"
  unfolding vl_writers_sqns_def apply (rule ext)
  apply (auto simp add: vl_writers_def in_set_conv_nth image_iff)
  subgoal for cl x i apply (rule bexI[where x="vl ! i"])
     apply (auto simp add: update_kv_reads_all_defs)
    by (metis (lifting) nth_list_update_eq nth_list_update_neq version.select_convs(2)
        version.surjective version.update_convs(3))
  subgoal for cl x i apply (rule bexI[where x="update_kv_reads_all_txn
      (\<lambda>t. cl_state (cls s (get_cl_txn t))) tSkm tFk vl ! i"])
     apply (auto simp add: update_kv_reads_all_defs)
    by (metis (lifting) nth_list_update_eq nth_list_update_neq version.select_convs(2)
        version.surjective version.update_convs(3))
  done

lemma vl_readers_sqns_other_cl_inv:
  assumes "vl \<noteq> []"
    and "\<And>k. WLockInv s k"
    and "\<And>k. WLockFpInv s k"
    and "cl' \<noteq> cl"
  shows "vl_readers_sqns (update_kv_key (get_txn_cl cl s) (svr_key_fp (svrs s k) (get_txn_cl cl s))
      (full_view vl) vl) cl' = vl_readers_sqns vl cl'"
  using assms
  by (auto simp add: update_kv_key_def update_kv_writes_def vl_readers_sqns_def
      update_kv_reads_vl_readers_inv split: option.split)

lemma kvs_readers_sqns_other_cl_inv:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<And>k. is_locked (svr_state (svrs s k) (get_txn_cl cl s))"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
    and "cl' \<noteq> cl"
  shows "kvs_readers_sqns (kvs_of_gs s') cl' = kvs_readers_sqns (kvs_of_gs s) cl'"
  using assms
  apply (auto simp add: kvs_readers_sqns_def kvs_of_gs_def)
  subgoal for x k using kvs_of_gs_cl_commit[of s cl k s'] apply (simp add: KVSNonEmp_def)
  apply (rule exI[where x=k])
  by (smt (verit) other_insts_unchanged_def update_kv_all_txn_non_empty vl_readers_sqns_other_cl_inv)
  subgoal for x k using kvs_of_gs_cl_commit[of s cl k s'] apply (simp add: KVSNonEmp_def)
  apply (rule exI[where x=k])
    by (smt (verit) assms(10, 12, 14) other_insts_unchanged_def update_kv_all_txn_non_empty
        vl_readers_sqns_other_cl_inv)
  done

lemma vl_writers_sqns_other_cl_inv:
  assumes "KVSNonEmp s"
    and "\<And>k. WLockInv s k"
    and "\<And>k. WLockFpInv s k"
    and "cl' \<noteq> cl"
  shows "vl_writers_sqns (update_kv_key (get_txn_cl cl s) (svr_key_fp (svrs s k) (get_txn_cl cl s))
      (full_view vl) vl) cl' = vl_writers_sqns vl cl'"
  using assms
  by (auto simp add: update_kv_key_def update_kv_writes_def vl_writers_sqns_def
      split: option.split)

lemma kvs_writers_sqns_other_cl_inv:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<And>k. is_locked (svr_state (svrs s k) (get_txn_cl cl s))"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
    and "cl' \<noteq> cl"
  shows "kvs_writers_sqns (kvs_of_gs s') cl' = kvs_writers_sqns (kvs_of_gs s) cl'"
  using assms
  apply (auto simp add: kvs_writers_sqns_def kvs_of_gs_def)
  subgoal for x k using kvs_of_gs_cl_commit[of s cl k s'] apply simp apply (rule exI[where x=k])
    by (smt (verit) other_insts_unchanged_def vl_writers_sqns_other_cl_inv)
  subgoal for x k using kvs_of_gs_cl_commit[of s cl k s'] apply simp apply (rule exI[where x=k])
    by (smt (verit) other_insts_unchanged_def vl_writers_sqns_other_cl_inv)
  done

lemma get_sqns_other_cl_inv:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<And>k. svr_state (svrs s k) (get_txn_cl cl s) = read_lock \<or>
             svr_state (svrs s k) (get_txn_cl cl s) = write_lock \<or> 
             svr_state (svrs s k) (get_txn_cl cl s) = no_lock"
    and "svr_cl_cl'_unchanged cl s s'"
    and "cl' \<noteq> cl"
  shows "get_sqns (kvs_of_gs s') cl' = get_sqns (kvs_of_gs s) cl'"
  using assms by (auto simp add: get_sqns_def kvs_writers_sqns_other_cl_inv
      kvs_readers_sqns_other_cl_inv cl_unchanged_defs)

lemma new_t_is_in_writers:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn_cl cl s) = write_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "vl_writers_sqns (kvs_of_gs s' k) cl = vl_writers_sqns (kvs_of_gs s k) cl \<union> {cl_sn (cls s cl)}"
  using assms kvs_of_gs_cl_commit[of s cl k s']
  by (auto simp add: kvs_of_gs_def vl_writers_sqns_def update_kv_key_def
      update_kv_writes_def split: option.split)

lemma new_t_is_in_writers2:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn_cl cl s) = read_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "vl_writers_sqns (kvs_of_gs s' k) cl = vl_writers_sqns (kvs_of_gs s k) cl"
  using assms kvs_of_gs_cl_commit[of s cl k s']
  apply (auto simp add: kvs_of_gs_def vl_writers_sqns_def update_kv_key_def update_kv_writes_def
      split: option.split)
  by (metis RLockFpInv_def option.discI)

lemma new_t_is_in_readers:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn_cl cl s) = read_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "vl_readers_sqns (kvs_of_gs s' k) cl = vl_readers_sqns (kvs_of_gs s k) cl \<union> {cl_sn (cls s cl)}"
  using assms kvs_of_gs_cl_commit[of s cl k s']
  apply (auto simp add: kvs_of_gs_def update_kv_key_def update_kv_writes_def vl_readers_sqns_def
      RLockFpInv_def update_kv_reads_vl_readers_inv KVSNonEmp_def split: option.split)
  by (meson RLockFpInv_def assms(6))

lemma new_t_is_in_readers2:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn_cl cl s) = write_lock"
    and "svr_key_fp (svrs s k) (get_txn_cl cl s) R \<noteq> None"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "vl_readers_sqns (kvs_of_gs s' k) cl = vl_readers_sqns (kvs_of_gs s k) cl \<union> {cl_sn (cls s cl)}"
  using assms kvs_of_gs_cl_commit[of s cl k s']
  by (auto simp add: kvs_of_gs_def update_kv_key_def update_kv_writes_def vl_readers_sqns_def
       update_kv_reads_vl_readers_inv split: option.split)

lemma new_t_is_in_readers3:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn_cl cl s) = write_lock"
    and "svr_key_fp (svrs s k) (get_txn_cl cl s) R = None"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "vl_readers_sqns (kvs_of_gs s' k) cl = vl_readers_sqns (kvs_of_gs s k) cl"
  using assms kvs_of_gs_cl_commit[of s cl k s']
  by (auto simp add: kvs_of_gs_def update_kv_key_def update_kv_writes_def vl_readers_sqns_def
       update_kv_reads_vl_readers_inv split: option.split)

lemma kvs_writers_cl_commit_grows:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<forall>k. is_locked (svr_state (svrs s k) (get_txn_cl cl s))"
    and "svr_state (svrs s k) (get_txn_cl cl s) = write_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "kvs_writers_sqns (kvs_of_gs s') cl = kvs_writers_sqns (kvs_of_gs s) cl \<union> {cl_sn (cls s cl)}"
  using assms new_t_is_in_writers[of s cl s' k]
  apply (auto simp add: kvs_writers_sqns_def)
  subgoal for x k' apply (auto elim!: allE[where x=k']; cases "k' = k", simp_all)
    apply (metis kvs_of_gs_def read_only_update' vl_writers_sqns_reads_other_cl_inv)
    apply (metis Un_empty_right Un_insert_right assms(3-7) insert_iff new_t_is_in_writers)
    by (metis kvs_of_gs_def update_kv_all_cl_commit_no_lock_inv)
  subgoal for x k' apply (rule exI[where x=k'])
    by (smt (verit, ccfv_SIG) UnCI assms(13) kvs_of_gs_def new_t_is_in_writers new_t_is_in_writers2
        update_kv_all_cl_commit_no_lock_inv)
  done

lemma kvs_writers_cl_commit_doesnt_grow:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<forall>k. svr_state (svrs s k) (get_txn_cl cl s) \<in> {read_lock, no_lock}"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "kvs_writers_sqns (kvs_of_gs s') cl = kvs_writers_sqns (kvs_of_gs s) cl"
  using assms apply (auto simp add: kvs_writers_sqns_def)
  subgoal for x k apply (auto elim!: allE[where x=k])
    apply (metis assms(3-7) new_t_is_in_writers2)
    by (metis kvs_of_gs_def update_kv_all_cl_commit_no_lock_inv)
  subgoal for x k  apply (auto elim!: allE[where x=k])
    apply (metis assms(3-7) new_t_is_in_writers2)
    by (metis kvs_of_gs_def update_kv_all_cl_commit_no_lock_inv)
  done

lemma kvs_readers_sqns_cl_commit_grows:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<forall>k. is_locked (svr_state (svrs s k) (get_txn_cl cl s))"
    and "svr_state (svrs s k) (get_txn_cl cl s) = read_lock \<or>
         (svr_state (svrs s k) (get_txn_cl cl s) = write_lock \<and>
          svr_key_fp (svrs s k) (get_txn_cl cl s) R \<noteq> None)"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "kvs_readers_sqns (kvs_of_gs s') cl = kvs_readers_sqns (kvs_of_gs s) cl \<union> {cl_sn (cls s cl)}"
  using assms
  apply (auto simp add: kvs_readers_sqns_def del: disjE)
  subgoal for x k' apply (auto elim!: allE[where x=k'])
    apply (metis (no_types) Un_insert_right assms(3-7) insert_iff new_t_is_in_readers sup_bot_right)
    apply (metis (no_types) Un_insert_right assms(3-7) insert_iff new_t_is_in_readers2
      new_t_is_in_readers3 sup_bot_right)
    apply (metis kvs_of_gs_def update_kv_all_cl_commit_no_lock_inv)
    apply (metis (no_types) Un_insert_right assms(3-7) insert_iff new_t_is_in_readers sup_bot_right)
    apply (metis (no_types) Un_insert_right assms(3-7) insert_iff new_t_is_in_readers2
      new_t_is_in_readers3 sup_bot_right)
    by (metis kvs_of_gs_def update_kv_all_cl_commit_no_lock_inv)
   subgoal apply (rule exI[where x=k])
     by (metis UnI2 assms(12,13) new_t_is_in_readers new_t_is_in_readers2 singletonI)
   subgoal for x k' apply (auto elim!: allE[where x=k'])
     apply (metis Un_iff assms(3-7) new_t_is_in_readers)
     apply (smt (verit) Un_insert_left assms(3-7) insert_iff mk_disjoint_insert
       new_t_is_in_readers2 new_t_is_in_readers3)
     apply (metis kvs_of_gs_def update_kv_all_cl_commit_no_lock_inv)
     apply (metis Un_iff assms(3-7) new_t_is_in_readers)
     apply (smt (verit) Un_insert_left assms(3-7) insert_iff mk_disjoint_insert
       new_t_is_in_readers2 new_t_is_in_readers3)
     by (metis kvs_of_gs_def update_kv_all_cl_commit_no_lock_inv)
   done

lemma kvs_readers_sqns_cl_commit_doesnt_grow:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<forall>k. svr_state (svrs s k) (get_txn_cl cl s) \<in> {write_lock, no_lock}"
    and "\<forall>k. svr_state (svrs s k) (get_txn_cl cl s) \<noteq> write_lock \<or>
             svr_key_fp (svrs s k) (get_txn_cl cl s) R = None"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "kvs_readers_sqns (kvs_of_gs s') cl = kvs_readers_sqns (kvs_of_gs s) cl"
  using assms apply (auto simp add: kvs_readers_sqns_def)
  subgoal for x k apply (auto elim!: allE[where x=k])
    apply (metis assms(1, 3-7) new_t_is_in_readers3)
    by (metis kvs_of_gs_def update_kv_all_cl_commit_no_lock_inv)+
  subgoal for x k  apply (auto elim!: allE[where x=k])
    apply (metis assms(1, 3-7) new_t_is_in_readers3)
    by (metis kvs_of_gs_def update_kv_all_cl_commit_no_lock_inv)+
  done

lemma get_sqns_cl_commit_grows:
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. RLockFpInv s k"
    and "\<And>k. NoLockFpInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<And>k. is_locked (svr_state (svrs s k) (get_txn_cl cl s))"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "svrs s' = svrs s"
  shows "get_sqns (kvs_of_gs s') cl =
         (if \<forall>k. svr_state (svrs s k) (get_txn_cl cl s) = no_lock then
          get_sqns (kvs_of_gs s) cl else
          get_sqns (kvs_of_gs s) cl \<union> {cl_sn (cls s cl)})"
  using assms
  apply (cases "\<forall>k. svr_state (svrs s k) (get_txn_cl cl s) = no_lock")
   apply (simp add: kvs_of_gs_def update_kv_all_cl_commit_no_lock_inv)
  apply simp apply (rule conjI) apply blast
  apply (simp add: get_sqns_def)
  using kvs_readers_sqns_cl_commit_doesnt_grow[of s cl s']
        kvs_readers_sqns_cl_commit_grows[of s cl s']
        kvs_writers_cl_commit_doesnt_grow[of s cl s']
        kvs_writers_cl_commit_grows[of s cl s']
  by (smt (z3) Un_insert_right insertCI sup.right_idem sup_bot_right sup_commute)

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
    by (auto simp add: kvs_readers_def vl_readers_def)
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
      apply (auto simp add: SqnInv_def tps_trans_defs) using get_sqns_other_cl_inv
      apply (smt (verit) cl_unchanged_defs reach_kvs_non_emp reach_nolockfp reach_rlock
          reach_rlockfp reach_tidfuturekm reach_tidpastkm reach_wlock reach_wlockfp)
      apply (cases "cl = x1")
      using get_sqns_cl_commit_grows[of s cl s']
      apply (smt (z3) cl_unchanged_defs UnE insert_absorb insert_iff insert_not_empty order.strict_implies_order
        order_class.order_eq_iff other_insts_unchanged_def reach_kvs_non_emp reach_nolockfp
        reach_rlock reach_rlockfp reach_tidfuturekm reach_tidpastkm reach_wlock reach_wlockfp)
      using get_sqns_other_cl_inv
      by (smt (verit) cl_unchanged_defs reach_kvs_non_emp reach_nolockfp reach_rlock
          reach_rlockfp reach_tidfuturekm reach_tidpastkm reach_wlock reach_wlockfp)
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
  assumes "i \<in> full_view (update_kv_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t)))
    (svr_state (svrs s k)) (svr_key_fp (svrs s k)) (svr_vl (svrs s k)))"
  shows "
  update_kv_writes (the_wr_t (svr_state (svrs s k))) (svr_key_fp (svrs s k) (the_wr_t (svr_state (svrs s k))))
    (update_kv_reads_all_txn (\<lambda>t. cl_state (cls s' (get_cl_txn t))) (svr_state (svrs s k))
      (svr_key_fp (svrs s k)) (svr_vl (svrs s k))) ! i =
  update_kv_reads_all_txn (\<lambda>t. cl_state (cls s' (get_cl_txn t))) (svr_state (svrs s k))
    (svr_key_fp (svrs s k)) (svr_vl (svrs s k)) ! i"
  using assms
  update_kv_writes_version_inv[of i "update_kv_reads_all_txn (\<lambda>t. cl_state (cls s' (get_cl_txn t)))
   (svr_state (svrs s k)) (svr_key_fp (svrs s k)) (svr_vl (svrs s k))" "the_wr_t (svr_state (svrs s k))"
   "svr_key_fp (svrs s k) (the_wr_t (svr_state (svrs s k)))"]
  by (simp add: full_view_def)

lemma kvs_of_gs_version_order:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl" and "WLockInv s k" and "RLockInv s k" and "KVSNonEmp s"
    and "i \<in> full_view (kvs_of_gs s k)"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "is_locked (svr_state (svrs s k) (get_txn_cl cl s))"
    and "svr_cl_cl'_unchanged cl s s'"
  shows "kvs_of_gs s k ! i \<sqsubseteq>\<^sub>v\<^sub>e\<^sub>r kvs_of_gs s' k ! i"
  using assms
  apply (auto simp add: kvs_of_gs_def svr_cl_cl'_unchanged_def update_kv_all_cl_commit_no_lock_inv)
   apply (simp_all add: writer_update_before read_only_update')
   apply (auto simp add: update_kv_all_txn_def update_kv_writes_all_txn_def helper_lemma)
   apply (auto simp add: version_order_def)
   using cl_commit_updates_kv_reads[of s s' cl k] 
     expanding_feature3'[where vl="update_kv_reads_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t)))
      (svr_state (svrs s k)) (svr_key_fp (svrs s k)) (svr_vl (svrs s k))"]
   by (auto simp add: update_kv_reads_all_defs)

lemma new_writer:
  assumes "WLockInv s k" and "WLockFpInv s k"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn_cl cl s) = write_lock"
  shows "v_writer (update_kv_all_txn (\<lambda>t. cl_state (cls s' (get_cl_txn t))) (svr_state (svrs s k))
    (svr_key_fp (svrs s k)) (svr_vl (svrs s k)) ! length (svr_vl (svrs s k))) =
   Tn (the_wr_t (svr_state (svrs s k)))"
  using assms
  apply (auto simp add: update_kv_all_txn_def update_kv_writes_all_txn_def update_kv_writes_def
      the_wr_tI split: option.split)
  by (metis nth_append_length update_kv_reads_all_txn_length version.select_convs(2))

lemma update_kv_all_txn_v_writer_inv: 
  assumes "i \<in> full_view vl"
  shows "v_writer (update_kv_all_txn tStm tSkm tFk vl ! i) = v_writer (vl ! i)"
  using assms
  by (auto simp add: update_kv_all_defs update_kv_writes_def split: option.split)

lemma new_version_index:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "WLockInv s k" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "svr_state (svrs s k) (get_txn_cl cl s) = write_lock"
    and "other_insts_unchanged cl (cls s) (cls s')"
    and "i \<in> full_view (update_kv_all_txn (\<lambda>t. cl_state (cls s' (get_cl_txn t)))
    (svr_state (svrs s k)) (svr_key_fp (svrs s k)) (svr_vl (svrs s k)))"
    and "i \<notin> full_view (update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t)))
    (svr_state (svrs s k)) (svr_key_fp (svrs s k)) (svr_vl (svrs s k)))"
  shows "i = length (svr_vl (svrs s k))"
  using assms
  by (meson full_view_length_increasing index_in_longer_kv update_kv_all_txn_length_increasing)

lemma t_is_fresh:
  assumes "SqnInv s cl"
    and "cl_state (cls s cl) = cl_prepared"
  shows "get_txn_cl cl s \<in> next_txids (kvs_of_gs s) cl"
  using assms by (auto simp add: kvs_of_gs_def next_txids_def SqnInv_def)

lemma kvs_of_gs_view_atomic:
  assumes "TIDPastKm s cl" and "TIDFutureKm s cl"
    and "\<And>k. WLockInv s k" and "\<And>k. WLockFpInv s k"
    and "\<And>k. RLockInv s k" and "\<And>k. NoLockFpInv s k"
    and "SqnInv s cl" and "KVSNonEmp s"
    and "cl_state (cls s cl) = cl_prepared"
    and "cl_state (cls s' cl) = cl_committed"
    and "\<forall>k. is_locked (svr_state (svrs s k) (get_txn_cl cl s))"
    and "svr_cl_cl'_unchanged cl s s'"
  shows "view_atomic (kvs_of_gs s') (\<lambda>k. full_view (kvs_of_gs s k))"
  using assms
  apply (auto simp add: kvs_of_gs_def svr_cl_cl'_unchanged_def view_atomic_def)
  subgoal for k k' i i'
    apply (auto elim!: allE[where x=k'])
    apply (auto simp add: update_kv_all_cl_commit_no_lock_inv read_only_update')
     apply (metis full_view_same_length update_kv_reads_all_txn_length)
    apply (cases "i' \<in> full_view (update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t)))
      (svr_state (svrs s k')) (svr_key_fp (svrs s k')) (svr_vl (svrs s k')))"; simp)
    using new_version_index[of s cl k' s' i'] apply (auto simp add: writer_update_before)
     apply (simp add: new_writer the_wr_tI)
    using cl_commit_writer_update_kv_all[of s cl k s'] apply simp
    using update_kv_all_txn_v_writer_inv[of i
        "update_kv_all_txn (\<lambda>t. cl_state (cls s (get_cl_txn t))) (svr_state (svrs s k))
          (svr_key_fp (svrs s k)) (svr_vl (svrs s k))"] assms(3, 5, 6, 11)
    apply (auto elim!: allE[where x=k])
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
  apply (meson kvs_of_gs_commit_length_increasing)
  by (simp add: kvs_of_gs_version_order)

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
      apply (auto simp add: KVSView_def tps_trans_defs cl_unchanged_defs o_def)
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

lemma writers_visible:
  assumes "u = (\<lambda>k. full_view (K k))"
  shows "visTx K u = kvs_writers K"
  using assms
  apply (auto simp add: visTx_def kvs_writers_def vl_writers_def in_set_conv_nth)
  using list_nth_in_set apply blast
  subgoal for k i apply (rule exI[where x=i]) apply (rule exI[where x= k])
    by (simp add: full_view_def).

lemma WW_writers_id_helper:
  assumes "(x, v_writer x') \<in> {(xa, x). \<exists>xb i.
            i \<in> full_view (K xb) \<and>
            (\<exists>i'. i' \<in> full_view (K xb) \<and>
              x = v_writer (K xb ! i) \<and> xa = v_writer (K xb ! i') \<and> i < i')}\<^sup>* "
    and "x' \<in> set (K k)"
  shows "\<exists>xa. x \<in> v_writer ` set (K xa)"
  using assms
  apply (induction x rule: converse_rtrancl_induct, auto)
  subgoal for xb apply (rule exI[where x=xb])
    using list_nth_in_set by blast.

lemma WW_writers_id:
  "(((\<Union> (range (WW K)))\<inverse>)\<^sup>*)\<inverse> `` kvs_writers K = kvs_writers K"
  apply (auto simp add: converse_def WW_def kvs_writers_def vl_writers_def)
  by (simp add: WW_writers_id_helper)

lemma full_view_satisfies_ET_SER_canCommit:
  "u = (\<lambda>k. full_view (K k)) \<Longrightarrow> ET_SER.canCommit K u F"
   by (simp add: ET_SER.canCommit_def ExecutionTest.canCommit_def closed_def read_only_Txs_def
      R_SER_def R_onK_def writers_visible WW_writers_id Diff_triv)

abbreviation invariant_list where
  "invariant_list s \<equiv> (\<forall>cl k. TIDFutureKm s cl \<and> TIDPastKm s cl \<and> RLockInv s k \<and> WLockInv s k \<and>
    RLockFpInv s k \<and> WLockFpInv s k \<and> NoLockFpInv s k \<and> KVSNonEmp s \<and> KVSGSNonEmp s \<and>
    RLockFpContentInv s k \<and> WLockFpContentInv s k \<and> TMFullView s cl \<and> KVSView s cl \<and> SqnInv s cl)"

subsection \<open>Refinement Proof\<close>

lemma tps_refines_et_es: "tps \<sqsubseteq>\<^sub>med ET_SER.ET_ES"
proof (intro simulate_ES_fun_with_invariant[where I="\<lambda>s. invariant_list s"])
  fix gs0 :: "'v global_conf"
  assume p: "init tps gs0"
  then show "init ET_SER.ET_ES (sim gs0)"
    by (auto simp add: ET_SER.ET_ES_defs tps_defs sim_defs update_kv_all_defs
        full_view_def kvs_init_def v_list_init_def lessThan_Suc)
next
  fix gs a and gs' :: "'v global_conf"
  assume p: "tps: gs\<midarrow>a\<rightarrow> gs'" and inv: "invariant_list gs"
  then show "ET_SER.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  using kvs_of_gs_inv[of gs a gs'] cl_view_inv[of gs a gs']
  proof (induction a)
  case (Cl_Commit cl sn u F)
  then show ?case using p apply simp
    using updated_is_kvs_of_gs'[of gs' cl gs]
    apply (auto simp add: cl_commit_def cl_unchanged_defs sim_def o_def)
    subgoal apply (rule exI [where x="(\<lambda>k. full_view (kvs_of_gs gs' k))"])
      apply (auto simp add: views_of_gs_def)
      apply (auto simp add: ET_SER.ET_cl_txn_def t_is_fresh KVSGSNonEmp_def full_view_wellformed)
      subgoal by (metis kvs_of_gs_length_increasing full_view_wellformed longer_list_not_empty)
      subgoal by (simp add: full_view_satisfies_ET_SER_canCommit)
      subgoal apply (auto simp add: kvs_of_gs_def update_kv_def) apply (rule ext)
        using kvs_of_gs_cl_commit[of gs cl] by (simp add: other_insts_unchanged_def)
      done
    subgoal apply (auto simp add: fp_property_def view_snapshot_def)
      subgoal for k y
        apply (cases "svr_state (svrs gs k) (get_txn_cl cl gs) = no_lock")
        apply (auto simp add: svr_vl_kvs_eq_lv NoLockFpInv_def del: disjE dest!:or3_not_eq)
          by (metis RLockFpContentInv_def WLockFpContentInv_def option.discI option.inject).
      done
  qed (auto simp add: sim_defs)
qed auto

end