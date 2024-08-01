section \<open>2PC-2PL: Invariant Proofs\<close>

theory Serializable_2PC_2PL_Invariant_Proofs
  imports Serializable_2PC_2PL
begin

subsection \<open>Auxiliary definitions and basic lemmas\<close>

fun not_cl_commit :: "'a ev \<Rightarrow> bool" where
  "not_cl_commit (Cl_Commit cl sn u'' F) = False" |
  "not_cl_commit _ = True"

lemma not_not_cl_commit [simp]: "\<not>not_cl_commit e \<longleftrightarrow> (\<exists>cl sn u'' F. e = Cl_Commit cl sn u'' F)" 
  by (auto elim: not_cl_commit.elims)

lemma med_not_cl_commit [simp]: "not_cl_commit e \<Longrightarrow> med e = ETSkip"
  by (cases e) simp_all

subsection \<open>Lemmas for unchanged elements in svrs\<close>

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


subsubsection \<open>Basic invariants about KV store\<close>

definition KVSNonEmp where
  "KVSNonEmp s \<longleftrightarrow> (\<forall>k. svr_vl (svrs s k) \<noteq> [])"

lemmas KVSNonEmpI = KVSNonEmp_def[THEN iffD2, rule_format]
lemmas KVSNonEmpE[elim] = KVSNonEmp_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_non_emp [simp, dest]: "reach tpl s \<Longrightarrow> KVSNonEmp s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: KVSNonEmp_def tpl_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Commit x1 x2)
    then show ?case using reach_trans 
      by (auto simp add: KVSNonEmp_def tpl_trans_defs svr_unchanged_defs)
         (metis length_greater_0_conv list.size(3) nat.distinct(1) length_update_kv_key)+
  qed (auto simp add: KVSNonEmp_def tpl_trans_defs unchanged_defs dest!: svr_vl_eq_all_k)
qed


definition KVS_T0_init where
  "KVS_T0_init s \<longleftrightarrow> (\<forall>k. \<forall>i \<in> full_view (svr_vl (svrs s k)). 
                        v_writer (svr_vl (svrs s k) ! i) = T0 \<longleftrightarrow> i = 0)"

lemmas KVS_T0_initI = KVS_T0_init_def[THEN iffD2, rule_format]
lemmas KVS_T0_initE[elim] = KVS_T0_init_def[THEN iffD1, elim_format, rule_format]

lemma reach_kvs_T0_init [simp, dest]: "reach tpl s \<Longrightarrow> KVS_T0_init s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case 
    by (auto simp add: tpl_defs kvs_init_defs KVS_T0_init_def)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Commit k t)
    then show ?case using reach_trans 
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs intro!: KVS_T0_initI del: iffI)
      subgoal for k' i  \<comment> \<open>read lock\<close>
        by (cases "k' = k")
           (auto 4 3 simp add: full_view_update_kv_key update_kv_key_simps  
                     split: if_split_asm del: iffI)
      subgoal for k' i  \<comment> \<open>write lock\<close>
        by (cases "k' = k")
           (auto 4 3 simp add: full_view_update_kv_key update_kv_key_simps  
                    split: if_split_asm del: iffI)
      subgoal for k' i  \<comment> \<open>no lock\<close>
        thm  svr_vl_eq_all_k
        by (cases "k' = k")
           (auto 4 3 simp add: full_view_update_kv_key update_kv_key_simps  
                     split: if_split_asm del: iffI)
      done
  qed (auto simp add: KVS_T0_init_def tpl_trans_defs unchanged_defs dest!: svr_vl_eq_all_k)
qed


subsection \<open>Invariants about future and past transactions\<close>

definition TIDFutureKm where
  "TIDFutureKm s cl \<longleftrightarrow> (\<forall>n k. n > cl_sn (cls s cl) \<longrightarrow> svr_state (svrs s k) (Tn_cl n cl) = working)"

lemmas TIDFutureKmI = TIDFutureKm_def[THEN iffD2, rule_format]
lemmas TIDFutureKmE[elim] = TIDFutureKm_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidfuturekm [simp, dest]: "reach tpl s \<Longrightarrow> TIDFutureKm s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: TIDFutureKm_def tpl_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs tid_match_def TIDFutureKm_def)
      subgoal for n k apply (cases "(Tn_cl n x) = x32"; cases "k = x31", auto) done.
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs TIDFutureKm_def)
      by (metis state_svr.distinct(1))
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs TIDFutureKm_def)
      by (metis state_svr.distinct(1))+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs TIDFutureKm_def)
      by (metis state_svr.distinct(1))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs TIDFutureKm_def)
      by (metis state_svr.distinct(1))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs TIDFutureKm_def)
      apply (metis state_svr.distinct(3))
      apply (metis state_svr.distinct(5))
      by (metis state_svr.distinct(7))
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs TIDFutureKm_def)
      apply (metis state_svr.distinct(3))
      apply (metis state_svr.distinct(5))
      apply (metis state_svr.distinct(7))
      by (metis state_svr.distinct(9))
  next
    case (User_Commit x10)
    then show ?thesis using reach_trans
      by (auto simp add: tpl_trans_defs cl_unchanged_defs TIDFutureKm_def, metis)
  next
    case (Cl_Commit x111 x112 x113 x114)
    then show ?thesis using reach_trans
      by (auto simp add: tpl_trans_defs cl_unchanged_defs TIDFutureKm_def, metis)
  next
    case (Cl_Abort x12a)
    then show ?thesis using reach_trans
      by (auto simp add: tpl_trans_defs cl_unchanged_defs TIDFutureKm_def, metis)
  next
    case (Cl_ReadyC x13a)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs cl_unchanged_defs TIDFutureKm_def)
      by (metis Suc_lessD)
  next
    case (Cl_ReadyA x14)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs cl_unchanged_defs TIDFutureKm_def)
      by (metis Suc_lessD)
  qed simp
qed

definition TIDPastKm where
  "TIDPastKm s cl \<longleftrightarrow> (\<forall>n k. n < cl_sn (cls s cl) \<longrightarrow> svr_state (svrs s k) (Tn_cl n cl) \<in> {committed, aborted})"

lemmas TIDPastKmI = TIDPastKm_def[THEN iffD2, rule_format]
lemmas TIDPastKmE[elim] = TIDPastKm_def[THEN iffD1, elim_format, rule_format]

lemma reach_tidpastkm [simp, dest]: "reach tpl s \<Longrightarrow> TIDPastKm s cl"
proof(induction s arbitrary: cl rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: TIDPastKm_def tpl_defs tid_match_def)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs TIDPastKm_def)
      by (metis state_svr.distinct(11) state_svr.distinct(13))
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs TIDPastKm_def)
      by (metis state_svr.distinct(23) state_svr.distinct(25))
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs TIDPastKm_def)
      by (metis state_svr.distinct(23) state_svr.distinct(25))+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs TIDPastKm_def)
      by (metis state_svr.distinct(23) state_svr.distinct(25))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs TIDPastKm_def)
      by (metis state_svr.distinct(23) state_svr.distinct(25))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      by (auto simp add: tpl_trans_defs svr_unchanged_defs TIDPastKm_def, fastforce+)
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      by (auto simp add: tpl_trans_defs svr_unchanged_defs TIDPastKm_def, fastforce+)
  next
    case (User_Commit x10)
    then show ?thesis using reach_trans
      by (auto simp add: tpl_trans_defs cl_unchanged_defs TIDPastKm_def, metis)
  next
    case (Cl_Commit x111 x112 x113 x114)
    then show ?thesis using reach_trans
      by (auto simp add: tpl_trans_defs cl_unchanged_defs TIDPastKm_def, metis)
  next
    case (Cl_Abort x12a)
    then show ?thesis using reach_trans
      by (auto simp add: tpl_trans_defs cl_unchanged_defs TIDPastKm_def, metis)
  next
    case (Cl_ReadyC x13a)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs cl_unchanged_defs TIDPastKm_def)
        by (metis less_antisym)
  next
    case (Cl_ReadyA x14)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs cl_unchanged_defs TIDPastKm_def)
        by (metis less_antisym)
  qed auto
qed

lemma other_sn_idle:  
  assumes "TIDFutureKm s cl" and "TIDPastKm s cl"
    and "get_cl t = cl" and "get_sn t \<noteq> cl_sn (cls s cl)"
  shows "\<And>k. svr_state (svrs s k) t \<in> {working, committed, aborted}"
  using assms
  apply (auto simp add: TIDFutureKm_def TIDPastKm_def)
  apply (cases "get_sn t > cl_sn (cls s cl)")
  apply (metis txid0.collapse)
  by (metis linorder_neqE_nat txid0.collapse)


subsection \<open>Locking Invariants\<close>

subsubsection \<open>Read lock invariant\<close>

definition RLockInv where
  "RLockInv s k \<longleftrightarrow> (\<forall>t. svr_state (svrs s k) t = read_lock \<longrightarrow> (\<forall>t. svr_state (svrs s k) t \<noteq> write_lock))"

lemmas RLockInvI = RLockInv_def[THEN iffD2, rule_format]
lemmas RLockInvE[elim] = RLockInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_rlock [simp, dest]: "reach tpl s \<Longrightarrow> RLockInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: RLockInv_def tpl_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (Prepare x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockInv_def)
      by (metis state_svr.distinct(15) state_svr.distinct(17))
  next
    case (RLock x1 x2 x3)
    then show ?case using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockInv_def)
      by (metis state_svr.distinct(27))
  next
    case (WLock x1 x2 x3 x4)
    then show ?case using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockInv_def)
      by (metis state_svr.distinct(27))+
  next
    case (NoLock x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockInv_def)
      by (metis state_svr.distinct(30) state_svr.distinct(38))
  next
    case (NOK x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockInv_def)
      by (metis state_svr.distinct(31) state_svr.distinct(39))
  next
    case (Commit x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockInv_def)
      apply (metis state_svr.distinct(42))
      apply (metis state_svr.distinct(34))
      by (metis state_svr.distinct(34) state_svr.distinct(42))
  next
    case (Abort x1 x2)
    then show ?case using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockInv_def)
      apply (metis state_svr.distinct(44))
      apply (metis state_svr.distinct(36))
      apply (metis state_svr.distinct(36) state_svr.distinct(44))
      by (metis state_svr.distinct(35) state_svr.distinct(44))
  qed (auto simp add: tpl_trans_defs cl_unchanged_defs RLockInv_def)
qed


subsubsection \<open>Write lock invariant\<close>

definition WLockInv where
  "WLockInv s k \<longleftrightarrow> (\<forall>t. svr_state (svrs s k) t \<noteq> write_lock) \<or> (\<exists>!t. svr_state (svrs s k) t = write_lock)"

lemmas WLockInvI = WLockInv_def[THEN iffD2, rule_format]
lemmas WLockInvE[elim] = WLockInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_wlock [simp, dest]: "reach tpl s \<Longrightarrow> WLockInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: WLockInv_def tpl_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockInv_def)
      by (metis state_svr.distinct(17))
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockInv_def)
      by (metis state_svr.distinct(27))
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockInv_def)
      by metis+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockInv_def)
      by (metis state_svr.distinct(37))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockInv_def)
      by (metis state_svr.distinct(39))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockInv_def)
      by (metis state_svr.distinct(41))+
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockInv_def)
      by (metis state_svr.distinct(43))+
  qed (auto simp add: tpl_trans_defs cl_unchanged_defs WLockInv_def)
qed

lemma the_wr_tI:
  assumes "svr_state (svrs s k) t = write_lock"
      and "WLockInv s k"
  shows "the_wr_t (svr_state (svrs s k)) = t"
  using assms
  by blast


subsection \<open>Invariants for fingerprint, knowing the lock (svrs status)\<close>

definition RLockFpInv where
  "RLockFpInv s k \<longleftrightarrow> (\<forall>t. svr_state (svrs s k) t = read_lock \<longrightarrow>
    svr_fp (svrs s k) t W = None \<and>
    svr_fp (svrs s k) t R \<noteq> None)"

lemmas RLockFpInvI = RLockFpInv_def[THEN iffD2, rule_format]
lemmas RLockFpInvE[elim] = RLockFpInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_rlockfp [simp, dest]: "reach tpl s \<Longrightarrow> RLockFpInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: RLockFpInv_def tpl_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockFpInv_def)
      by (metis state_svr.distinct(15))+
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockFpInv_def)
      by metis+
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockFpInv_def)
      by (metis state_svr.distinct(27))+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockFpInv_def)
      by (metis state_svr.distinct(29))+
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockFpInv_def)
      by (metis state_svr.distinct(31))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockFpInv_def)
      by (metis state_svr.distinct(33))+
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockFpInv_def)
      by (metis state_svr.distinct(35))+
  qed (auto simp add: tpl_trans_defs cl_unchanged_defs RLockFpInv_def)
qed

definition WLockFpInv where
  "WLockFpInv s k \<longleftrightarrow> (\<forall>t. svr_state (svrs s k) t = write_lock \<longrightarrow> svr_fp (svrs s k) t W \<noteq> None)"

lemmas WLockFpInvI = WLockFpInv_def[THEN iffD2, rule_format]
lemmas WLockFpInvE[elim] = WLockFpInv_def[THEN iffD1, elim_format, rule_format]

lemma reach_wlockfp [simp, dest]: "reach tpl s \<Longrightarrow> WLockFpInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: WLockFpInv_def tpl_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockFpInv_def)
      by (metis state_svr.distinct(17))
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockFpInv_def)
      by (metis state_svr.distinct(27))
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockFpInv_def)
      by metis+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockFpInv_def)
      by (metis state_svr.distinct(37))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockFpInv_def)
      by (metis state_svr.distinct(39))
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockFpInv_def)
      by (metis state_svr.distinct(41))+
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockFpInv_def)
      by (metis state_svr.distinct(43))+
  qed (auto simp add: tpl_trans_defs cl_unchanged_defs WLockFpInv_def)
qed


definition NoLockFpInv where
  "NoLockFpInv s k \<longleftrightarrow> (\<forall>t. svr_state (svrs s k) t = no_lock \<longrightarrow> svr_fp (svrs s k) t = Map.empty)"

lemmas NoLockFpInvI = NoLockFpInv_def[THEN iffD2, rule_format]
lemmas NoLockFpInvE[elim] = NoLockFpInv_def[THEN iffD1, elim_format, rule_format]
lemmas NoLockFpInvD = NoLockFpInv_def[THEN iffD1, rule_format, rotated 1]

lemma reach_nolockfp [simp, dest]: "reach tpl s \<Longrightarrow> NoLockFpInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: NoLockFpInv_def tpl_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      by (auto simp add: tpl_trans_defs svr_unchanged_defs NoLockFpInv_def)
         (metis state_svr.distinct(19))+
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      by (auto simp add: tpl_trans_defs svr_unchanged_defs NoLockFpInv_def)
         (metis state_svr.distinct(29))+
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      by (auto simp add: tpl_trans_defs svr_unchanged_defs NoLockFpInv_def)
         (metis state_svr.simps(38))+
  next
    case (NoLock k t)
    then show ?thesis using reach_trans
      by (auto simp add: tpl_trans_defs svr_unchanged_defs NoLockFpInv_def) (metis)
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      by (auto simp add: tpl_trans_defs svr_unchanged_defs NoLockFpInv_def)
         (metis state_svr.distinct(45))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      by (auto simp add: tpl_trans_defs svr_unchanged_defs NoLockFpInv_def)
         (metis state_svr.distinct(47))+
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      by (auto simp add: tpl_trans_defs svr_unchanged_defs NoLockFpInv_def)
         (metis state_svr.simps(50))+
  qed (auto simp add: tpl_trans_defs cl_unchanged_defs NoLockFpInv_def)
qed

lemma the_wr_t_fp:
  assumes "\<And>k. WLockInv s k"
    and "\<And>k. WLockFpInv s k"
    and "svr_state (svrs s k) t = write_lock"
  shows "svr_fp (svrs s k) (the_wr_t (svr_state (svrs s k))) W \<noteq> None"
  using assms 
  by (auto simp add: WLockInv_def WLockFpInv_def the_wr_tI)


subsubsection \<open>Fingerprint content invariants\<close>

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
lemmas RLockFpContentInvD = RLockFpContentInv_def[THEN iffD1, rule_format, rotated 1]

lemma reach_rlockfp_content [simp, dest]: "reach tpl s \<Longrightarrow> RLockFpContentInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: RLockFpContentInv_def tpl_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockFpContentInv_def)
      by (metis state_svr.distinct(15))+
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockFpContentInv_def)
      by metis+
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockFpContentInv_def)
      by (metis state_svr.distinct(27))+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockFpContentInv_def)
      by (metis state_svr.distinct(29))+
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockFpContentInv_def)
      by (metis state_svr.distinct(31))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans svr_vl_read_commit_eq_lv[of s x81 x82 s']
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockFpContentInv_def del: disjE)
      by (smt (verit, best) NoLockFpInv_def RLockInv_def reach_nolockfp reach_rlock 
              state_svr.distinct(33) update_kv_key_nop)
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs RLockFpContentInv_def)
      by (metis state_svr.distinct(35))+
  qed (auto simp add: tpl_trans_defs cl_unchanged_defs RLockFpContentInv_def)
qed


definition WLockFpContentInv where
  "WLockFpContentInv s k \<longleftrightarrow> (\<forall>t. svr_state (svrs s k) t = write_lock \<longrightarrow>
    svr_fp (svrs s k) t R = None \<or>
    svr_fp (svrs s k) t R =
      Some (v_value (last_version (svr_vl (svrs s k)) (full_view (svr_vl (svrs s k))))))"

lemmas WLockFpContentInvI = WLockFpContentInv_def[THEN iffD2, rule_format]
lemmas WLockFpContentInvE[elim] = WLockFpContentInv_def[THEN iffD1, elim_format, rule_format]
lemmas WLockFpContentInvD = WLockFpContentInv_def[THEN iffD1, rule_format, rotated 1]

lemma reach_wlockfp_content [simp, dest]: "reach tpl s \<Longrightarrow> WLockFpContentInv s k"
proof(induction s arbitrary: k rule: reach.induct)
  case (reach_init s)
  then show ?case by (auto simp add: WLockFpContentInv_def tpl_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (cases e)
    case (Prepare x31 x32)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockFpContentInv_def)
      by (metis state_svr.distinct(17))
  next
    case (RLock x41 x42 x43)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockFpContentInv_def)
      by (metis state_svr.distinct(27))
  next
    case (WLock x51 x52 x53 x54)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockFpContentInv_def)
      by metis+
  next
    case (NoLock x61 x62)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockFpContentInv_def)
      by (metis state_svr.distinct(37))
  next
    case (NOK x71 x72)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockFpContentInv_def)
      by (metis state_svr.distinct(39))+
  next
    case (Commit x81 x82)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockFpContentInv_def)
      apply (metis RLockInv_def reach_rlock state_svr.distinct(41))
       apply (smt reach_wlock state_svr.distinct(41) the_wr_tI)
      by (metis NoLockFpInv_def reach_nolockfp update_kv_key_nop)
  next
    case (Abort x91 x92)
    then show ?thesis using reach_trans
      apply (auto simp add: tpl_trans_defs svr_unchanged_defs WLockFpContentInv_def)
      by (metis state_svr.distinct(43))+
  qed (auto simp add: tpl_trans_defs cl_unchanged_defs WLockFpContentInv_def)
qed


abbreviation invariant_list_kvs where
  "invariant_list_kvs s \<equiv> KVSNonEmp s \<and> KVS_T0_init s \<and>
                          (\<forall>cl. TIDFutureKm s cl) \<and> (\<forall>cl. TIDPastKm s cl) \<and> 
                          (\<forall>k. RLockInv s k) \<and> (\<forall>k. RLockFpInv s k) \<and> (\<forall>k. RLockFpContentInv s k) \<and>
                          (\<forall>k. WLockInv s k) \<and> (\<forall>k. WLockFpInv s k) \<and> (\<forall>k. WLockFpContentInv s k) \<and>
                          (\<forall>k. NoLockFpInv s k)"


end
