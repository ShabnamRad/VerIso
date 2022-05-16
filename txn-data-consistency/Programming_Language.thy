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

inductive c_step :: "('a, 'v) c_state \<Rightarrow> 'v c_label \<Rightarrow> ('a, 'v) c_state \<Rightarrow> bool" where
  "cp_step s cp s' \<Longrightarrow> c_step ((K, u, s), (Cp cp)) (CDot cl) ((K, u, s'), Skip)" |
  "\<lbrakk> u \<sqsubseteq> u''; view_wellformed K u; view_wellformed K u'';
     \<sigma> = view_snapshot K u'';
     t_multi_step ((s, \<sigma>, \<lambda>k. None), T) ((s', _, F), TSkip);
     t \<in> next_txids K cl;
     K' = update_kv t F u'' K;
     view_wellformed K' u';
     canCommit K u'' F; vShift K u'' K' u' \<rbrakk>
    \<Longrightarrow> c_step ((K, u, s), Atomic T) (CL (cl, u'', F)) ((K', u', s'), Skip)" |
  "c_step ((K, u, s), C1 [[+]] C2) (CDot cl) ((K, u, s), C1)" |
  "c_step ((K, u, s), C1 [[+]] C2) (CDot cl) ((K, u, s), C2)" |
  "c_step ((K, u, s), Skip;; C) (CDot cl) ((K, u, s), C)" |
  "c_step ((K, u, s), C1) l ((K', u', s'), C1')
    \<Longrightarrow> c_step ((K, u, s), C1;; C2) l ((K', u', s'), C1';; C2)" |
  "c_step ((K, u, s), Itr C) (CDot cl) ((K, u, s), Skip [[+]] (C;; Itr C))"

inductive c_multi_step :: "('a, 'v) c_state \<Rightarrow> ('a, 'v) c_state \<Rightarrow> bool" where
  "c_multi_step s s" |
  "\<lbrakk> c_multi_step s s';
     c_multi_step s' s'' \<rbrakk>
    \<Longrightarrow> c_multi_step s s''" |
  "c_step s _ s' \<Longrightarrow> c_multi_step s s'"

definition cES :: "('v c_label, ('a, 'v) c_state) ES" where
  "cES \<equiv> \<lparr>
    init = c_init,
    trans = c_step
  \<rparr>"
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
  "\<lbrakk> u = U cl;
     s = E cl;
     C = P cl;
     c_step ((K, u, s), C) l ((K', u', s'), C') \<rbrakk>
    \<Longrightarrow> PProg_trans (((K, U), E), P) l
                    (((K', U(cl := u')), E(cl := s')), P(cl := C'))"

definition PProgES :: "('v c_label, ('a, 'v) p_state) ES" where
  "PProgES \<equiv> \<lparr>
    init = PProg_init,
    trans = PProg_trans
  \<rparr>"

lemmas PProgES_defs = PProgES_def PProg_init_def


subsection \<open>Wellformedness Invariants\<close>

definition KVWellformed :: "('a, 'v) p_state \<Rightarrow> bool" where
  "KVWellformed s \<longleftrightarrow> wellformed (fst (fst (fst s)))"

lemmas KVWellformedI = KVWellformed_def[THEN iffD2, rule_format]
lemmas KVWellformedE[elim] = KVWellformed_def[THEN iffD1, elim_format, rule_format]

lemma reach_kv_wellformed [simp, dest]: "reach PProgES s \<Longrightarrow> KVWellformed s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: KVWellformed_def PProgES_defs wellformed_defs config_init_def
      kvs_init_def version_init_def)
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
end

end