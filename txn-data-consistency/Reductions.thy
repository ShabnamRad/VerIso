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

abbreviation right_commute :: "('e, 's) ES \<Rightarrow> 'e \<Rightarrow> 'e \<Rightarrow> bool" where
  "right_commute E e1 e2 \<equiv> left_commute E e2 e1"


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
    \<open>E: s \<midarrow>e1\<rightarrow> w\<close>
    \<open>E: w \<midarrow>e2\<rightarrow> s'\<close>
  shows
    \<open>valid_exec_frag E (Exec_frag s0 (efl @ (s, e1, w) # (w, e2, s') # efl') sf)\<close>
proof -
  from assms(1)
  have fr1: \<open>valid_exec_frag E (Exec_frag s0 efl s)\<close> and
       trs: \<open>E: s \<midarrow>e2\<rightarrow> t\<close> \<open>E: t \<midarrow>e1\<rightarrow> s'\<close> and
       fr3: \<open>valid_exec_frag E (Exec_frag s' efl' sf)\<close>
    by (auto simp add: valid_exec_frag_append_cons_eq valid_exec_frag_cons_eq)
  have \<open>E: s \<midarrow>e1\<rightarrow> w\<close> \<open>E: w \<midarrow>e2\<rightarrow> s'\<close> using trs \<open>(E: s \<midarrow>e1\<rightarrow> w)\<close> \<open>(E: w\<midarrow>e2\<rightarrow> s')\<close>
    by (auto dest: left_commute_diamond_with_witness)
  then show ?thesis using fr1 fr3
    by (intro valid_exec_frag_append) auto
qed


subsection \<open>Reduction relation on execution fragments\<close>

inductive reduce_frag :: 
  "('e, 's) ES \<Rightarrow> ('e, 's) exec_frag \<Rightarrow> ('e, 's) exec_frag \<Rightarrow> bool" 
  ("(3_: _ \<rhd> _)" [50, 50, 50] 90) for E ef1 ef2
  where
  reduce_fragI: 
    "\<lbrakk> valid_exec_frag E ef1;
       ef1 = Exec_frag s0 (efl @ (s, e2, t) # (t, e1, s') # efl') sf;
       ef2 = Exec_frag s0 (efl @ (s, e1, w) # (w, e2, s') # efl') sf;
       E: s \<midarrow>e1\<rightarrow> w; E: w \<midarrow>e2\<rightarrow> s'\<rbrakk> 
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

lemma reducable_to_Good_exec_frag:
  assumes
    \<open>wf R\<close>
    \<open>valid_exec_frag E ef\<close>
    \<open>ef \<notin> Good\<close>
    \<open>\<And>ef. \<lbrakk> valid_exec_frag E ef; ef \<notin> Good \<rbrakk> \<Longrightarrow> (\<exists>ef'. E: ef \<rhd> ef' \<and> (ef' \<in> Good \<or> (ef', ef) \<in> R))\<close>
  shows
    \<open>\<exists>ef' \<in> Good. E: ef \<rhd>\<^sup>+ ef'\<close>
  using assms(1-3)
proof (induction ef rule: wf_induct_rule)
  case (less x)
  then obtain ef' where ef': "E: x \<rhd> ef' \<and> (ef' \<in> Good \<or> (ef', x) \<in> R)" using assms(4) by auto
  then show ?case
  proof (cases "ef' \<in> Good")
    case True
    then show ?thesis using ef' by auto
  next
    case False
    then obtain a where "a \<in> Good" and "E: ef' \<rhd>\<^sup>+ a"
      using less ef' reduce_frag_valid by blast
    then show ?thesis by (metis ef' tranclp_into_tranclp2)
  qed
qed


\<comment> \<open>measure 1\<close>

definition inverted_pairs :: "('s \<Rightarrow> 'a :: linorder) \<Rightarrow> ('e, 's) exec_frag \<Rightarrow> nat rel" where
  "inverted_pairs f ef =
    {(i, j) | i j sl. i < j \<and> j < length sl \<and> f (sl ! i) > f (sl ! j) \<and> sl = states_of_efrag ef}"

\<comment> \<open>measure 2\<close>
definition closest_pair_distance :: "nat rel \<Rightarrow> nat" where
  "closest_pair_distance id_pairs \<equiv> Min {j - i | j i. (i, j) \<in> id_pairs}"

abbreviation measure_rel :: "('s \<Rightarrow> 'a :: linorder) \<Rightarrow> ('e, 's) exec_frag rel" where
  "measure_rel f \<equiv> measures [card o (inverted_pairs f), closest_pair_distance o (inverted_pairs f)]"

definition Good_wrt where
  "Good_wrt f \<equiv> {ef | ef. let sl = states_of_efrag ef in
      \<forall>i j. i < j \<and> j < length sl \<longrightarrow> f (sl ! i) \<le> f (sl ! j)}"

lemma reducable_exec_frag:
  assumes
    \<open>valid_exec_frag E ef\<close>
    \<open>ef \<notin> Good_wrt f\<close>
  shows
    \<open>\<exists>ef'. E: ef \<rhd> ef' \<and> (ef' \<in> Good_wrt f \<or> (ef', ef) \<in> measure_rel f)\<close>
  using assms
  sorry
  

lemma reducable_to_Good_wrt_f_exec_frag:
  fixes f :: "'s \<Rightarrow> 'a :: linorder"
  assumes
    \<open>valid_exec_frag E ef\<close>
    \<open>ef \<notin> Good_wrt f\<close>
  shows
    \<open>\<exists>ef' \<in> Good_wrt f. E: ef \<rhd>\<^sup>+ ef'\<close>
  using reducable_to_Good_exec_frag[OF _ assms(1) assms(2) reducable_exec_frag]
  by auto


end

