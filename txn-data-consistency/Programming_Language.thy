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
  "\<lbrakk>tp_step s \<sigma> tp s' \<sigma>'; fp' = update_fp fp (get_op s \<sigma> tp)\<rbrakk>
    \<Longrightarrow> t_step ((s,\<sigma>,fp), Tp tp) ((s',\<sigma>',fp'), TSkip)" |
  "t_step (ts, T1 [+] T2) (ts, T1)" |
  "t_step (ts, T1 [+] T2) (ts, T2)" |
  "t_step (ts, TSkip [;] T) (ts, T)" |
  "t_step (ts, T1) (ts', T1') \<Longrightarrow> t_step (ts, T1[;] T2) (ts', T1'[;] T2)" |
  "t_step (ts, TItr T) (ts, TSkip [+] (T [;] TItr T))"

fun t_multi_step :: "('a, 'v) t_state \<Rightarrow> ('a, 'v) t_state \<Rightarrow> bool" where
  "t_multi_step s s' \<longleftrightarrow> t_step^** s s'"


\<comment> \<open>command semantics\<close>
                                      
datatype 'v c_label = CDot cl_id | CL "'v label"

type_synonym ('a, 'v) c_state = "('v kv_store \<times> view \<times> 'a) \<times> ('a, 'v) cmd"

context ExecutionTest
begin

definition c_init :: "('a, 'v) c_state \<Rightarrow> bool" where
  "c_init cs \<equiv> fst cs = (kvs_init, view_init, undefined)"

inductive c_step :: "cl_id \<Rightarrow> ('a, 'v) c_state \<Rightarrow> 'v c_label \<Rightarrow> ('a, 'v) c_state \<Rightarrow> bool" for cl  where
  "cp_step s cp s' \<Longrightarrow> c_step cl ((K, u, s), (Cp cp)) (CDot cl) ((K, u, s'), Skip)" |
  "\<lbrakk> ET_txn cl u'' F (K, U) (K', U');
     \<sigma> = view_snapshot K u'';
     t_multi_step ((s, \<sigma>, \<lambda>k. None), T) ((s', _, F), TSkip) \<rbrakk>
    \<Longrightarrow> c_step cl ((K, U cl, s), Atomic T) (CL  (ET cl u'' F)) ((K', U' cl, s'), Skip)" |
  "c_step cl ((K, u, s), C1 [[+]] C2) (CDot cl) ((K, u, s), C1)" |
  "c_step cl ((K, u, s), C1 [[+]] C2) (CDot cl) ((K, u, s), C2)" |
  "c_step cl ((K, u, s), Skip;; C) (CDot cl) ((K, u, s), C)" |
  "c_step cl ((K, u, s), C1) l ((K', u', s'), C1')
    \<Longrightarrow> c_step cl ((K, u, s), C1;; C2) l ((K', u', s'), C1';; C2)" |
  "c_step cl ((K, u, s), Itr C) (CDot cl) ((K, u, s), Skip [[+]] (C;; Itr C))"

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

fun PProg_trans :: "('a, 'v) p_state \<Rightarrow>'v c_label \<Rightarrow> ('a, 'v) p_state \<Rightarrow> bool" where
  "PProg_trans (((K, U), E), P) l (((K', U'), E'), P') \<longleftrightarrow> (\<exists>cl u' s' C' x x'.
    c_step cl x l x' \<and> 
    U' = U(cl := u') \<and>
    E' = E(cl := s') \<and>
    P' = P(cl := C') \<and>
    x = ((K, U cl, E cl), P cl) \<and>
    x' = ((K', u', s'), C'))"

declare PProg_trans.simps [simp del]
lemmas PProg_trans_def = PProg_trans.simps

lemmas PProg_trans_induct = PProg_trans.induct [case_names PProg]

definition PProgES :: "('v c_label, ('a, 'v) p_state) ES" where
  "PProgES \<equiv> \<lparr>
    init = PProg_init,
    trans = PProg_trans
  \<rparr>"

lemmas PProgES_defs = PProgES_def PProg_init_def

subsection \<open>Wellformedness of kv_stores in programs\<close>

lemma bla:
  assumes "\<And>a b env prgms. K = a \<and> U = b \<and> E = env \<and> P = prgms
  \<longrightarrow> reach \<lparr>init = (=) (kvs_init, c_views_init), trans = ET_trans_and_fp\<rparr> (a, b)"
  shows "reach \<lparr>init = (=) (kvs_init, c_views_init), trans = ET_trans_and_fp\<rparr> (K, U)"
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
  then show ?case
  proof (induction st evt st' rule: PProg_trans_induct)
    case (PProg K U E P l K' U' E' P')
    then show ?case using reach_trans
      apply (auto simp add: PProgES_defs PProg_trans_def) subgoal for cl u' s' C'
        apply (induction  "((K, U cl, E cl), P cl)" l "((K', u', s'), C')" rule: c_step.induct)
        sorry done
  qed
qed


definition kvs_wellformed_in_prog :: "('a, 'v) p_state \<Rightarrow> bool" where
  "kvs_wellformed_in_prog ps \<longleftrightarrow> kvs_wellformed (fst (fst (kvs ps)))"

lemma reach_kv_wellformed [simp, dest]: "reach PProgES ps \<Longrightarrow> kvs_wellformed_in_prog ps"
  by (auto simp add: kvs_wellformed_in_prog_def intro!: reach_kvs_wellformed 
              elim: mapping [where env="snd (fst ps)" and prgms="snd ps"])
   
(*
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (CDot x1)
    then show ?thesis sorry (*using reach_trans
    apply (auto simp add: KVWellformed_def PProgES_defs wellformed_def)
      subgoal  apply(auto simp add: snapshot_property_def)
        subgoal for k i j x apply(induction rule: PProg_trans.cases) apply (auto)*)
  next
    case (CL x2)
    then show ?thesis sorry (*using reach_trans
      apply (auto simp add: KVWellformed_def PProgES_defs wellformed_def)
      subgoal  apply(auto simp add: snapshot_property_def)
        subgoal for k i j x apply(induction rule: PProg_trans.cases) apply (auto)*)
  qed
qed
*)

end

end