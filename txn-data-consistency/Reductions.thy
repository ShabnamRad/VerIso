(*
  Title:   Reductions
  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
  Version: Isabelle/HOL 2022
  Date:    July 2023
  ID:      $Id$
*)
section \<open>Reductions\<close>

text \<open>This theory supports reductions using left and right movers.\<close>

theory Reductions
  imports Executions
begin

subsection \<open>Reduction steps and sequences\<close>

text \<open>Per-event state transition relation\<close>

abbreviation strans :: "('e, 's) ES \<Rightarrow> 'e \<Rightarrow> ('s \<times> 's) set" where
  "strans E e \<equiv> {(s, s') | s s'. trans E s e s'}"


text \<open>Condition for commuting a pair of events\<close>

definition left_commute :: "('e, 's) ES \<Rightarrow> 'e \<Rightarrow> 'e \<Rightarrow> bool" where
  "left_commute E e1 e2 \<longleftrightarrow> strans E e2 O strans E e1 \<subseteq> strans E e1 O strans E e2"

abbreviation right_commute where
  "right_commute E e1 e2 \<equiv> left_commute e2 e1"


abbreviation cwit :: "('e, 's) ES \<Rightarrow> 's \<Rightarrow> 'e \<Rightarrow> 'e \<Rightarrow> 's \<Rightarrow> 's" where
  \<open>cwit E s e1 e2 s' \<equiv> (SOME x. (E: s \<midarrow>e1\<rightarrow> x) \<and> (E: x \<midarrow>e2\<rightarrow> s'))\<close>


lemma left_commute_diamond:
  assumes
    \<open>E: s \<midarrow>e2\<rightarrow> t\<close> \<open>E: t \<midarrow>e1\<rightarrow> s'\<close>
    \<open>left_commute E e1 e2\<close>
  shows
    \<open>\<exists>u. E: s \<midarrow>e1\<rightarrow> u \<and> E: u \<midarrow>e2\<rightarrow> s'\<close>
  using assms
  by (auto simp add: left_commute_def)

lemma left_commute_diamond_with_witness:
  assumes
    \<open>E: s \<midarrow>e2\<rightarrow> t\<close> \<open>E: t \<midarrow>e1\<rightarrow> s'\<close>
    \<open>left_commute E e1 e2\<close>
    \<open>w = cwit E s e1 e2 s'\<close>
  shows
    \<open>E: s \<midarrow>e1\<rightarrow> w \<and> E: w \<midarrow>e2\<rightarrow> s'\<close>
  using assms
  by - (drule left_commute_diamond, auto del: conjI intro: someI)


text \<open>Commute transitions in execution fragments\<close>

lemma commuted_exec_frag_valid:
  assumes
    \<open>valid_exec_frag E (Exec_frag s0 (efl @ (s, e2, t) # (t, e1, s') # efl') sf)\<close>
    \<open>left_commute E e1 e2\<close>
    \<open>w = cwit E s e1 e2 s'\<close>
  shows
    \<open>valid_exec_frag E (Exec_frag s0 (efl @ (s, e1, w) # (w, e2, s') # efl') sf)\<close>
proof -
  from assms(1)
  have fr1: \<open>valid_exec_frag E (Exec_frag s0 efl s)\<close> and
       trs: \<open>E: s \<midarrow>e2\<rightarrow> t\<close> \<open>E: t \<midarrow>e1\<rightarrow> s'\<close> and
       fr3: \<open>valid_exec_frag E (Exec_frag s' efl' sf)\<close>
    by (auto simp add: valid_exec_frag_append_cons_eq valid_exec_frag_cons_eq)
  have \<open>E: s \<midarrow>e1\<rightarrow> w\<close> \<open>E: w \<midarrow>e2\<rightarrow> s'\<close> using trs \<open>left_commute E e1 e2\<close> \<open>w = cwit E s e1 e2 s'\<close>
    by (auto dest: left_commute_diamond_with_witness)
  then show ?thesis using fr1 fr3
    by (intro valid_exec_frag_append) auto
qed 

lemma commuted_exec_frag_valid':
  assumes
    \<open>valid_exec_frag E (Exec_frag s0 (efl @ (s, e2, t) # (t, e1, s') # efl') sf)\<close>
    \<open>left_commute E e1 e2\<close>
  shows
    \<open>\<exists>u. valid_exec_frag E (Exec_frag s0 (efl @ (s, e1, u) # (u, e2, s') # efl') sf)\<close>
  using assms
  by (auto intro: commuted_exec_frag_valid)


subsection \<open>Reduction relation on execution fragments\<close>

inductive reduce_frag :: 
  "('e, 's) ES \<Rightarrow> ('e, 's) exec_frag \<Rightarrow> ('e, 's) exec_frag \<Rightarrow> bool" 
  ("(3_: _ \<rhd> _)" [50, 50, 50] 90) for E ef1 ef2
  where
  reduce_fragI: 
    "\<lbrakk> valid_exec_frag E ef1;
       left_commute E e1 e2;
       ef1 = Exec_frag s0 (efl @ (s, e2, t) # (t, e1, s') # efl') sf;
       ef2 = Exec_frag s0 (efl @ (s, e1, w) # (w, e2, s') # efl') sf;
       w = cwit E s e1 e2 s' \<rbrakk> 
  \<Longrightarrow> E: ef1 \<rhd> ef2"

lemma reduce_frag_valid:
  "E: ef1 \<rhd> ef2 \<Longrightarrow> valid_exec_frag E ef1 \<and> valid_exec_frag E ef2"
  by (auto simp add: reduce_frag.simps intro: commuted_exec_frag_valid)

lemma reduce_frag_last_state_equiv: \<open>E: ef1 \<rhd> ef2 \<Longrightarrow> ef1 \<simeq> ef2\<close>
  by (auto simp add: reduce_frag.simps)


text \<open>Transitive closure.\<close>

abbreviation reduce_frag_plus ("(3_: _ \<rhd>\<^sup>+ _)" [50, 50, 50] 90) where
  "E: ef1 \<rhd>\<^sup>+ ef2 \<equiv> (reduce_frag E)\<^sup>+\<^sup>+ ef1 ef2" 

lemma reduce_frag_valid_plus:
  "E: ef1 \<rhd>\<^sup>+ ef2 \<Longrightarrow> valid_exec_frag E ef1 \<and> valid_exec_frag E ef2"
  by (induction ef1 ef2 rule: tranclp.induct) (auto dest: reduce_frag_valid)

lemma reduce_frag_plus_last_state_equiv: \<open>E: ef1 \<rhd>\<^sup>+ ef2 \<Longrightarrow> ef1 \<simeq> ef2\<close>
  by (induction ef1 ef2 rule: tranclp.induct)
     (auto intro: reduce_frag_last_state_equiv efrag_last_equiv_trans)



subsection \<open>Proof rules for reduction\<close>

text \<open>Primitive "proof rule" for showing that every reachable state of an ES is the last state 
of an element of a set of "good" executions provided every valid execution can be reduced
to a "good" one.\<close>

(* not yet clear how useful this is: *)

lemma reach_reduced:
  assumes 
    \<open>reach E s\<close>
    \<open>\<And>ef. \<lbrakk> valid_exec E ef; ef \<notin> Good \<rbrakk> \<Longrightarrow> \<exists>ef' \<in> Good. E: ef \<rhd>\<^sup>+ ef'\<close> 
  shows 
    \<open>s \<in> ef_last`Good\<close>
  using assms
proof -
  from \<open>reach E s\<close> obtain s0 efl where *: \<open>valid_exec E (Exec_frag s0 efl s)\<close> 
    by (auto simp add: reach_last_exec)
  then show ?thesis
  proof (cases "Exec_frag s0 efl s \<in> Good")
    case True
    then show ?thesis by force
  next 
    case False
    with * obtain ef' where \<open>ef' \<in> Good\<close> \<open>E: (Exec_frag s0 efl s) \<rhd>\<^sup>+ ef'\<close> using assms(2) by auto
    from this(2) have \<open>ef_last ef' = s\<close> by (auto dest!: reduce_frag_plus_last_state_equiv)
    then show ?thesis using \<open>ef' \<in> Good\<close> by auto
  qed
qed


lemma reach_reduced_invariants:
  assumes 
    \<open>s \<in> ef_last`Good \<Longrightarrow> I s\<close>
    \<open>\<And>ef. \<lbrakk> valid_exec E ef; ef \<notin> Good \<rbrakk> \<Longrightarrow> \<exists>ef' \<in> Good. E: ef \<rhd>\<^sup>+ ef'\<close> 
  shows 
    \<open>reach E s \<Longrightarrow> I s\<close>
  using assms
  by (metis reach_reduced)




text \<open>More useful rules TBA.\<close>


end

