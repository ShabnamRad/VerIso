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

subsection \<open>Reduction relation on execution fragments\<close>

inductive reduce_frag :: 
  "('e, 's) ES \<Rightarrow> ('e, 's) exec_frag \<Rightarrow> ('e, 's) exec_frag \<Rightarrow> bool" 
  ("(3_: _ \<rhd> _)" [50, 50, 50] 90) for E ef1 ef2
  where
  reduce_fragI: 
    "\<lbrakk> valid_exec_frag E ef1;
       ef1 = Exec_frag s0 (efl @ (s, e2, u) # (u, e1, s') # efl') sf;
       ef2 = Exec_frag s0 (efl @ (s, e1, w) # (w, e2, s') # efl') sf;
       E: s \<midarrow>e1\<rightarrow> w; E: w \<midarrow>e2\<rightarrow> s'\<rbrakk> 
  \<Longrightarrow> E: ef1 \<rhd> ef2"

lemma reduce_frag_orig_valid:
  assumes \<open>E: ef1 \<rhd> ef2\<close> shows \<open>valid_exec_frag E ef1\<close> using assms
  by (auto simp add: reduce_frag.simps)

lemma reduce_frag_reduced_valid:
  assumes \<open>E: ef1 \<rhd> ef2\<close> shows \<open>valid_exec_frag E ef2\<close>
proof -
  from \<open>E: ef1 \<rhd> ef2\<close> obtain s0 efl s e2 u e1 s' efl' sf w where
    val: \<open>valid_exec_frag E ef1\<close> and
    ef1: \<open>ef1 = Exec_frag s0 (efl @ (s, e2, u) # (u, e1, s') # efl') sf\<close> and
    ef2: \<open>ef2 = Exec_frag s0 (efl @ (s, e1, w) # (w, e2, s') # efl') sf\<close> and
    trs: \<open>E: s \<midarrow>e1\<rightarrow> w\<close> \<open>E: w \<midarrow>e2\<rightarrow> s'\<close>
    by (auto simp add: reduce_frag.simps)
  from val ef1 have 
    fr1: \<open>valid_exec_frag E (Exec_frag s0 efl s)\<close> and
    fr3: \<open>valid_exec_frag E (Exec_frag s' efl' sf)\<close>
    by (auto simp add: valid_exec_frag_append_cons_eq valid_exec_frag_cons_eq)
  then show ?thesis using ef2 \<open>E: s \<midarrow>e1\<rightarrow> w\<close> \<open>E: w \<midarrow>e2\<rightarrow> s'\<close>
    by (auto intro: valid_exec_frag_append)
qed

lemmas reduce_frag_valid = reduce_frag_orig_valid reduce_frag_reduced_valid

lemma reduce_frag_last_state_equiv: \<open>E: ef1 \<rhd> ef2 \<Longrightarrow> ef1 \<simeq> ef2\<close>
  by (auto simp add: reduce_frag.simps)


subsection \<open>Transitive closure and reducibility\<close>

abbreviation reduce_frag_plus ("(3_: _ \<rhd>\<^sup>+ _)" [50, 50, 50] 90) where
  "E: ef1 \<rhd>\<^sup>+ ef2 \<equiv> (reduce_frag E)\<^sup>+\<^sup>+ ef1 ef2" 

lemma reduce_frag_valid_plus:
  "E: ef1 \<rhd>\<^sup>+ ef2 \<Longrightarrow> valid_exec_frag E ef1 \<and> valid_exec_frag E ef2"
  by (induction ef1 ef2 rule: tranclp.induct) (auto dest: reduce_frag_valid)

lemma reduce_frag_plus_last_state_equiv: \<open>E: ef1 \<rhd>\<^sup>+ ef2 \<Longrightarrow> ef1 \<simeq> ef2\<close>
  by (induction ef1 ef2 rule: tranclp.induct)
     (auto intro: reduce_frag_last_state_equiv efrag_last_equiv_trans)

inductive reducible :: "('e, 's) ES \<Rightarrow> ('e, 's) exec_frag set \<Rightarrow> bool" for E Good where
  reducibleI: 
    "\<lbrakk> \<And>ef. \<lbrakk> valid_exec_frag E ef; ef \<notin> Good \<rbrakk> \<Longrightarrow> \<exists>ef' \<in> Good. E: ef \<rhd>\<^sup>+ ef' \<rbrakk> 
     \<Longrightarrow> reducible E Good"


subsection \<open>Reduction proof rules\<close>

lemma reducible_to_Good_exec_frag:
  assumes
    \<open>wf R\<close>
    \<open>\<And>ef. \<lbrakk> valid_exec_frag E ef; ef \<notin> Good \<rbrakk> \<Longrightarrow> (\<exists>ef'. E: ef \<rhd> ef' \<and> (ef' \<in> Good \<or> (ef', ef) \<in> R))\<close>
  shows
    \<open>reducible E Good\<close>
proof 
  fix ef
  assume \<open>valid_exec_frag E ef\<close> \<open>ef \<notin> Good\<close>
  with \<open>wf R\<close> show \<open>\<exists>ef' \<in> Good. E: ef \<rhd>\<^sup>+ ef'\<close> 
  proof (induction ef rule: wf_induct_rule)
    case (less x)
    then obtain ef' where ef': "E: x \<rhd> ef'" "(ef' \<in> Good \<or> (ef', x) \<in> R)" using assms(2) by auto
    show ?case
    proof (cases "ef' \<in> Good")
      case True
      then show ?thesis using ef' by auto
    next
      case False
      then obtain a where "a \<in> Good" and "E: ef' \<rhd>\<^sup>+ a"
        using less ef' by (blast dest: reduce_frag_valid)
      then show ?thesis using \<open>E: x \<rhd> ef'\<close> by (blast intro: tranclp_into_tranclp2)
    qed
  qed
qed


text \<open>Every reachable state of an ES is the last state of a "good" execution provided every 
valid execution is reducible to a "good" one.\<close>

lemma reach_reduced:
  assumes 
    \<open>reach E s\<close>
    \<open>reducible E Good\<close> 
  shows 
    \<open>s \<in> ef_last`Good\<close>
  using assms
proof -
  from \<open>reach E s\<close> obtain s0 efl where *: \<open>valid_exec_frag E (Exec_frag s0 efl s)\<close> 
    by (auto simp add: reach_last_exec)
  then show ?thesis
  proof (cases "Exec_frag s0 efl s \<in> Good")
    case True
    then show ?thesis by force
  next 
    case False
    then show ?thesis using * \<open>reducible E Good\<close>
      by (auto simp add: efrag_last_equiv_def reducible.simps 
               dest!: reduce_frag_plus_last_state_equiv)
  qed
qed

lemma reach_reduced_invariants:
  assumes 
    \<open>s \<in> ef_last`Good \<Longrightarrow> I s\<close>
    \<open>reducible E Good\<close> 
  shows 
    \<open>reach E s \<Longrightarrow> I s\<close>
  using assms
  by (metis reach_reduced)


subsection \<open>Commuting events\<close>

text \<open>Per-event state transition relation\<close>

abbreviation strans :: "('e, 's) ES \<Rightarrow> 'e \<Rightarrow> 's rel" where
  "strans E e \<equiv> {(s, s') | s s'. trans E s e s'}"


text \<open>Condition for commuting a pair of events\<close>

definition left_commute :: "('e, 's) ES \<Rightarrow> 'e \<Rightarrow> 'e \<Rightarrow> bool" where
  "left_commute E e1 e2 \<longleftrightarrow> strans E e2 O strans E e1 \<subseteq> strans E e1 O strans E e2"

definition right_commute :: "('e, 's) ES \<Rightarrow> 'e \<Rightarrow> 'e \<Rightarrow> bool" where
  "right_commute E e1 e2 \<equiv> left_commute E e2 e1"

lemma left_commute':
  "left_commute E e1 e2 \<longleftrightarrow>
     (\<forall>x y z. E: x \<midarrow>e2\<rightarrow> y \<and>  E: y \<midarrow>e1\<rightarrow> z \<longrightarrow> (\<exists>u. E: x \<midarrow>e1\<rightarrow> u \<and> E: u \<midarrow>e2\<rightarrow> z))"
  apply (auto simp add: left_commute_def)
  apply (erule allE)+
  by auto

lemma left_commute_diamond:
  assumes
    \<open>left_commute E e1 e2\<close>
    \<open>E: s \<midarrow>e2\<rightarrow> t\<close> \<open>E: t \<midarrow>e1\<rightarrow> s'\<close>
  shows
    \<open>\<exists>u. E: s \<midarrow>e1\<rightarrow> u \<and> E: u \<midarrow>e2\<rightarrow> s'\<close>
  using assms
  by (auto simp add: left_commute_def)

text \<open>Commute transitions in execution fragments. This lemma might be useful for establishing
the main premise of the rule @{thm reducible_to_Good_exec_frag} given that we know that
two events left-commute.\<close>

lemma reduce_frag_left_commute:
  assumes 
    \<open>valid_exec_frag E ef1\<close> 
    \<open>ef1 = Exec_frag s0 (efl @ (s, e2, u) # (u, e1, s') # efl') sf\<close>
    \<open>left_commute E e1 e2\<close>
  shows \<open>\<exists>w. E: ef1 \<rhd> (Exec_frag s0 (efl @ (s, e1, w) # (w, e2, s') # efl') sf)\<close> 
proof - 
  from assms(1-2) have trs: \<open>E: s \<midarrow>e2\<rightarrow> u\<close> \<open>E: u \<midarrow>e1\<rightarrow> s'\<close> 
    by (auto simp add: valid_exec_frag_append_cons_eq valid_exec_frag_cons_eq)
  with assms(3) obtain w where \<open>E: s \<midarrow>e1\<rightarrow> w\<close> \<open>E: w \<midarrow>e2\<rightarrow> s'\<close> 
    by (auto dest: left_commute_diamond) 
  with assms(1-2) show ?thesis by (auto intro: reduce_frag.intros)
qed

datatype mover_type = Lm | Rm

\<comment> \<open>Can be called on a trace with E and None, to get the currently possible moves for all events\<close>
fun ev_mover_type :: "('e, 's) ES \<Rightarrow> 'e option \<Rightarrow> 'e list \<Rightarrow> mover_type set list" where
  "ev_mover_type E _ [] = []" |
  "ev_mover_type E None [e] = [{}]" |
  "ev_mover_type E (Some el) [e] = (if left_commute E e el then [{Lm}] else [{}])" |
  "ev_mover_type E None (e # er # rest) =
    (if right_commute E er e then {Rm} else {}) # ev_mover_type E (Some e) (er # rest)" |
  "ev_mover_type E (Some el) (e # er # rest) =
    ((if left_commute  E e el then {Lm} else {}) \<union>
     (if right_commute E e er then {Rm} else {})) # ev_mover_type E (Some e) (er # rest)"


subsection \<open>More specific proof rules\<close>


\<comment> \<open>measure 1\<close>

definition inverted_pairs :: "('s \<Rightarrow> 'a :: linorder) \<Rightarrow> ('e, 's) exec_frag \<Rightarrow> nat rel" where
  "inverted_pairs f ef =
    {(i, j) | i j sl. i < j \<and> j < length sl \<and> f (sl ! i) > f (sl ! j) \<and> sl = states_of_efrag ef}"

\<comment> \<open>measure 2\<close>
definition pair_distance_sum :: "nat rel \<Rightarrow> nat" where
  "pair_distance_sum id_pairs \<equiv> Sum {j - i | j i. (i, j) \<in> id_pairs}"

abbreviation measure_rel :: "('s \<Rightarrow> 'a :: linorder) \<Rightarrow> ('e, 's) exec_frag rel" where
  "measure_rel f \<equiv> measures [card o (inverted_pairs f), pair_distance_sum o (inverted_pairs f)]"

definition Good_wrt where
  "Good_wrt f \<equiv> {ef | ef. let sl = states_of_efrag ef in
      \<forall>i j. i < j \<and> j < length sl \<longrightarrow> f (sl ! i) \<le> f (sl ! j)}"


lemma reducible_exec_frag:
  assumes
    \<open>valid_exec_frag E ef\<close>
    \<open>ef \<notin> Good_wrt f\<close>
  shows
    \<open>\<exists>ef'. E: ef \<rhd> ef' \<and> (ef' \<in> Good_wrt f \<or> (ef', ef) \<in> measure_rel f)\<close>
  using assms
  sorry
  

lemma reducible_to_Good_wrt_f_exec_frag: 
  fixes f :: \<open>'s \<Rightarrow> 'a :: linorder\<close>
  shows \<open>reducible E (Good_wrt f)\<close>
  by (auto intro: reducible_to_Good_exec_frag [OF _ reducible_exec_frag])


end
