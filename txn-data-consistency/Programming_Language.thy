section \<open>Programming Language\<close>

theory Programming_Language
  imports Key_Value_Stores
begin

subsection \<open>Syntax\<close>

datatype 'a       cmd_p = Assign "'a \<Rightarrow> 'a" | Assume "'a \<Rightarrow> bool"

datatype ('a, 'v) txn_p = TCp "'a cmd_p" | Lookup key "'v \<Rightarrow>'a \<Rightarrow> 'a" | Mutate key "'a \<Rightarrow> 'v"

datatype ('a, 'v) txn   = TSkip| Tp "('a, 'v) txn_p" | TItr "('a, 'v) txn" |
                          TSeq "('a, 'v) txn" "('a, 'v) txn" (infixr "[;]" 60) |
                          TChoice "('a, 'v) txn" "('a, 'v) txn" (infixr "[+]" 65)

datatype ('a, 'v) cmd   = Skip| Cp "'a cmd_p" | Atomic "('a, 'v) txn" | Itr "('a, 'v) cmd" |
                          Seq "('a, 'v) cmd" "('a, 'v) cmd" (infixr ";;" 60) |
                          Choice "('a, 'v) cmd" "('a, 'v) cmd" (infixr "[[+]]" 65)

subsection \<open>Operational Semantics\<close>

\<comment> \<open>primitive commands\<close>

inductive cp_step :: "'a \<Rightarrow> 'a cmd_p \<Rightarrow> 'a \<Rightarrow> bool" where
  "cp_step s (Assign f) (f s)" |
  "t s \<Longrightarrow> cp_step s (Assume t) s"

\<comment> \<open>primitives transactions\<close>

inductive tp_step :: "'a \<Rightarrow> 'v snapshot \<Rightarrow> ('a, 'v) txn_p \<Rightarrow> 'a \<Rightarrow> 'v snapshot \<Rightarrow> bool" where
  "tp_step s \<sigma> (Lookup k f_rd) (f_rd (\<sigma> k) s) \<sigma>" |
  "\<sigma>' = \<sigma>(k := f_wr s) \<Longrightarrow> tp_step s \<sigma> (Mutate k f_wr) s \<sigma>'"|
  "cp_step s cp s' \<Longrightarrow> tp_step s \<sigma> (TCp cp) s' \<sigma>"

\<comment> \<open>transaction semantics\<close>

type_synonym ('a, 'v) t_state = "('a \<times> 'v snapshot \<times> 'v fingerpr) \<times> ('a, 'v) txn"

fun get_op :: "'a \<Rightarrow> 'v snapshot \<Rightarrow> ('a, 'v) txn_p \<Rightarrow> 'v op" where
  "get_op s \<sigma> (Lookup k f_rd)  = Read k (\<sigma> k)" |
  "get_op s \<sigma> (Mutate k f_wr)  = Write k (f_wr s)"|
  "get_op s \<sigma> _ = Eps"

inductive t_step :: "('a, 'v) t_state \<Rightarrow> ('a, 'v) t_state \<Rightarrow> bool"  where
  TPrim: "\<lbrakk>tp_step s \<sigma> tp s' \<sigma>'; F' = update_fp F (get_op s \<sigma> tp)\<rbrakk>
    \<Longrightarrow> t_step ((s, \<sigma>, F), Tp tp) ((s', \<sigma>', F'), TSkip)" |
  "t_step (ts, T1 [+] T2) (ts, T1)" |
  "t_step (ts, T1 [+] T2) (ts, T2)" |
  "t_step (ts, TSkip [;] T) (ts, T)" |
  "t_step (ts, T1) (ts', T1') \<Longrightarrow> t_step (ts, T1[;] T2) (ts', T1'[;] T2)" |
  "t_step (ts, TItr T) (ts, TSkip [+] (T [;] TItr T))"

lemma fp_cond_inv:
  assumes "F' = update_fp F opr" and "opr = (get_op s \<sigma> tp)"
    and "fp_property F K u" and "\<sigma> = view_snapshot K u"
  shows "fp_property F' K u"
  using assms unfolding fp_property_def
  by (induction s \<sigma> tp rule: get_op.induct; simp)

fun snapshot_fp_property :: "'v kv_store \<Rightarrow> view \<Rightarrow> 'v snapshot \<Rightarrow> 'v fingerpr \<Rightarrow> bool" where
  "snapshot_fp_property K u \<sigma> F \<longleftrightarrow>
    (\<forall>k. F(k, R) = None \<and> F(k, W) = None \<longrightarrow> \<sigma> k = view_snapshot K u k) \<and> fp_property F K u"

declare snapshot_fp_property.simps [simp del]
lemmas snapshot_fp_property_def = snapshot_fp_property.simps

lemma tp_step_snapshot_fp_inv:
  assumes "t_step ((s, \<sigma>, F), T) ((s', \<sigma>', F'), T')"
    and "snapshot_fp_property K u \<sigma> F"
  shows "snapshot_fp_property K u \<sigma>' F'"
  using assms
proof (induction "((s, \<sigma>, F), T)" "((s', \<sigma>', F'), T')" arbitrary: T T' rule: t_step.induct)
  case (TPrim tp)
  then show ?case unfolding snapshot_fp_property_def
    by (induction s \<sigma> tp rule: get_op.induct; simp add: tp_step.simps fp_property_def)
qed simp_all

lemma t_mstep_snapshot_fp_inv:
  assumes "t_step\<^sup>*\<^sup>* ((s, \<sigma>, F), T) st'" and "st'=((s', \<sigma>', F'), T')"
    and "snapshot_fp_property K u \<sigma> F"
  shows "snapshot_fp_property K u \<sigma>' F'"
  using assms thm rtranclp_induct
proof (induction st' arbitrary: s' \<sigma>' F' T' rule: rtranclp_induct)
  case (step y z)
  then show ?case
    apply (cases y) subgoal for a T apply (cases a) subgoal for s \<sigma> F
    using tp_step_snapshot_fp_inv
    by (metis). .
      (*[of "fst (fst y)" "fst (snd (fst y))" "snd (snd (fst y))" "snd y" s' \<sigma>' F' T' K u]
    by (metis prod.collapse)*)
qed auto

lemma t_mstep_fp_inv:
  assumes "t_step\<^sup>*\<^sup>* ((s, \<sigma>, Map.empty), T) ((s', \<sigma>', F), T')" and "\<sigma> = view_snapshot K u"
  shows "fp_property F K u"
proof -
  have "snapshot_fp_property K u \<sigma> Map.empty" using assms
    by (simp add: snapshot_fp_property_def fp_property_def)
  hence "snapshot_fp_property K u \<sigma>' F" using assms by (auto dest!: t_mstep_snapshot_fp_inv)
  thus ?thesis by (simp add: snapshot_fp_property_def)
qed


\<comment> \<open>command semantics\<close>
                                      
datatype 'v c_label = CDot cl_id | CL "'v label"

type_synonym ('a, 'v) c_state = "('v kv_store \<times> view \<times> 'a) \<times> ('a, 'v) cmd"

context ExecutionTest
begin

definition c_init :: "('a, 'v) c_state \<Rightarrow> bool" where
  "c_init cs \<equiv> fst cs = (kvs_init, view_init, undefined)"

inductive c_step :: "cl_id \<Rightarrow> ('a, 'v) c_state \<Rightarrow> 'v c_label \<Rightarrow> ('a, 'v) c_state \<Rightarrow> bool" for cl  where
  "cp_step s cp s' \<Longrightarrow> c_step cl ((K, u, s), (Cp cp)) (CDot cl) ((K, u, s'), Skip)" |
  "\<lbrakk> ET_cl_txn cl u'' F (K, u) (K', u');
     \<sigma> = view_snapshot K u'';
     t_step\<^sup>*\<^sup>* ((s, \<sigma>, \<lambda>k. None), T) ((s', _, F), TSkip) \<rbrakk>
    \<Longrightarrow> c_step cl ((K, u, s), Atomic T) (CL  (ET cl u'' F)) ((K', u', s'), Skip)" |
  "c_step cl ((K, u, s), C1 [[+]] C2) (CDot cl) ((K, u, s), C1)" |
  "c_step cl ((K, u, s), C1 [[+]] C2) (CDot cl) ((K, u, s), C2)" |
  "c_step cl ((K, u, s), Skip;; C) (CDot cl) ((K, u, s), C)" |
  "c_step cl ((K, u, s), C1) l ((K', u', s'), C1')
    \<Longrightarrow> c_step cl ((K, u, s), C1;; C2) l ((K', u', s'), C1';; C2)" |
  "c_step cl ((K, u, s), Itr C) (CDot cl) ((K, u, s), Skip [[+]] (C;; Itr C))"

lemmas c_step_induct =
  c_step.induct [consumes 1, case_names CPrim AtomicT Choice1 Choice2 SeqSkip SeqRec ItrC] \<comment>\<open>not working for some reason\<close>

lemma c_step_dot_inv:
  assumes "c_step cl ((K, u, s), C) l ((K', u', s'), C')" and "l = CDot cl"
  shows "K' = K \<and> u' = u"
  using assms
  by (induction "((K, u, s), C)" l "((K', u', s'), C')" arbitrary: C C' rule: c_step_induct) auto

lemma c_step_l_cases:
  assumes "c_step cl ((K, u, s), C) l ((K', u', s'), C')"
  shows "l = CDot cl \<or>
     (\<exists>u'' F \<sigma> T uu. l = CL (ET cl u'' F) \<and> ET_cl_txn cl u'' F (K, u) (K', u') \<and> 
      \<sigma> = view_snapshot K u'' \<and> t_step\<^sup>*\<^sup>* ((s, \<sigma>, \<lambda>k. None), T) ((s', uu, F), TSkip))"
  using assms
  by (induction "((K, u, s), C)" l "((K', u', s'), C')" arbitrary: C C' rule: c_step_induct) auto

end

\<comment> \<open>program semantics\<close>

type_synonym 'a c_env = "cl_id \<Rightarrow> 'a"

definition c_env_init :: "'a c_env" where
  "c_env_init \<equiv> \<lambda>cl. undefined"

type_synonym ('a, 'v) progs = "cl_id \<Rightarrow> ('a, 'v) cmd"

type_synonym ('a, 'v) p_state = "('v config \<times> 'a c_env) \<times> ('a, 'v) progs"

context ExecutionTest
begin

definition PProg_init :: "('a, 'v) p_state \<Rightarrow> bool" where
  "PProg_init ps \<equiv> fst ps = (config_init, c_env_init)"

inductive PProg_trans :: "('a, 'v) p_state \<Rightarrow>'v c_label \<Rightarrow> ('a, 'v) p_state \<Rightarrow> bool" where
  "\<lbrakk> c_step cl ((K, u, s), C) l ((K', u', s'), C');
     u = U cl;
     s = E cl;
     C = P cl \<rbrakk>
    \<Longrightarrow> PProg_trans (((K, U), E), P) l
                    (((K', U(cl := u')), E(cl := s')), P(cl := C'))"

lemmas PProg_trans_induct = PProg_trans.induct [consumes 1, case_names PProg]

definition PProgES :: "('v c_label, ('a, 'v) p_state) ES" where
  "PProgES \<equiv> \<lparr>
    init = PProg_init,
    trans = PProg_trans
  \<rparr>"

lemmas PProgES_defs = PProgES_def PProg_init_def

lemma trans_PProgES_eq [simp]: "(PProgES: s\<midarrow>e\<rightarrow> s') \<longleftrightarrow> PProg_trans s e s'"
  by (auto simp add: PProgES_def)

subsection \<open>Wellformedness of kv_stores in programs\<close>

lemma bla:
  assumes "(\<And>a b env prgms. K = a \<and> U = b \<and> E = env \<and> P = prgms \<longrightarrow> reach ET_ES (a, b))"
  shows "reach ET_ES (K, U)"
  using assms
  by auto


lemma mapping [rule_format]:
  assumes "reach PProgES ps"
  shows "ps = ((conf, env), prgms) \<longrightarrow> reach ET_ES conf"
  using assms
proof (induction ps arbitrary: conf env prgms rule: reach.induct)
  case (reach_init st)
  then show ?case by (auto simp add: PProgES_defs ET_ES_defs)
next
  case (reach_trans st evt st')
  then show ?case apply simp
  proof (induction st evt st' rule: PProg_trans_induct)
    case (PProg cl K u s C l K' u' s' C' U E P)
    then show ?case
  proof (induction "((K, u, s), C)" l "((K', u', s'), C')" 
         arbitrary: C C' E P rule: c_step_induct)
    case (AtomicT u'' F \<sigma> T _)
    hence "fp_property Map.empty K u''" by (simp add: fp_property_def)
    then show ?case using AtomicT
      by (auto intro!: reach.intros(2) [of ET_ES "(K, U)" "ET cl u'' F" "(K', U(cl := u'))"]
               simp add: t_mstep_fp_inv)
  next                            
    case (SeqRec C1 l C1' C2)
    hence "c_step cl ((K, u, s), C1;; C2) l ((K', u', s'), C1';; C2)" by (metis c_step.intros(6))
    then show ?case using SeqRec
      apply (auto dest!: c_step_l_cases)
      subgoal by (metis SeqRec.hyps(1) c_step_dot_inv fun_upd_idem_iff)
      subgoal for T uu u'' F
        by (auto intro!: reach.intros(2) [of ET_ES "(K, U)" "(ET cl u'' F)" "(K', U(cl := u'))"]
                 simp add: t_mstep_fp_inv).
    qed auto
  qed
qed


definition kvs_wellformed_in_prog :: "('a, 'v) p_state \<Rightarrow> bool" where
  "kvs_wellformed_in_prog ps \<longleftrightarrow> kvs_wellformed (fst (fst (kvs ps)))"

lemma reach_kv_wellformed [simp, dest]: "reach PProgES ps \<Longrightarrow> kvs_wellformed_in_prog ps"
  by (auto simp add: kvs_wellformed_in_prog_def intro!: reach_kvs_wellformed 
              elim: mapping [where env="snd (fst ps)" and prgms="snd ps"])

end

end