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

definition left_commute where
  "left_commute E e1 e2 \<longleftrightarrow> 
     (\<forall>x y z. reach E x \<longrightarrow> E: x \<midarrow>e2\<rightarrow> y \<longrightarrow>  E: y \<midarrow>e1\<rightarrow> z \<longrightarrow> (\<exists>u. E: x \<midarrow>e1\<rightarrow> u \<and> E: u \<midarrow>e2\<rightarrow> z))"

definition right_commute :: "('e, 's) ES \<Rightarrow> 'e \<Rightarrow> 'e \<Rightarrow> bool" where
  "right_commute E e1 e2 \<equiv> left_commute E e2 e1"

lemma left_commute_diamond:
  assumes
    \<open>left_commute E e1 e2\<close> \<open>reach E s\<close>
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
    \<open>left_commute E e1 e2\<close> \<open>reach E s\<close>
  shows \<open>\<exists>w. E: ef1 \<rhd> (Exec_frag s0 (efl @ (s, e1, w) # (w, e2, s') # efl') sf)\<close> 
proof - 
  from assms(1-2) have trs: \<open>E: s \<midarrow>e2\<rightarrow> u\<close> \<open>E: u \<midarrow>e1\<rightarrow> s'\<close> 
    by (auto simp add: valid_exec_frag_append_cons_eq valid_exec_frag_cons_eq)
  with assms(3-4) obtain w where \<open>E: s \<midarrow>e1\<rightarrow> w\<close> \<open>E: w \<midarrow>e2\<rightarrow> s'\<close> 
    by (auto dest: left_commute_diamond) 
  with assms(1-2) show ?thesis by (auto intro: reduce_frag.intros)
qed


subsection \<open>More specific proof rules\<close>

definition inverted_pairs :: "('e \<Rightarrow> 'a :: linorder option) \<Rightarrow> 'e list \<Rightarrow> nat rel" where
  "inverted_pairs f tr = 
    {(i, j) | i j c1 c2. i < j \<and> j < length tr \<and> f(tr ! i) = Some c2 \<and> f(tr ! j) = Some c1 \<and> c2 > c1}"

definition Good_wrt where
  "Good_wrt f \<equiv> {ef | ef. inverted_pairs f (trace_of_efrag ef) = {}}"

definition reach_good_state :: "('e, 's) ES \<Rightarrow> ('e \<Rightarrow> 'a :: linorder option) \<Rightarrow> 's \<Rightarrow> bool" where
  "reach_good_state E f s \<equiv> \<exists>s0 efl. valid_exec E (Exec_frag s0 efl s) \<and> (Exec_frag s0 efl s) \<in> Good_wrt f"

lemma efrag_snoc_good:
  "\<lbrakk> Exec_frag s0 efl s \<in> Good_wrt f; f e = None \<rbrakk>
    \<Longrightarrow> Exec_frag s0 (efl @ [(s, e, s')]) s' \<in> Good_wrt f"
  apply (auto simp add: Good_wrt_def inverted_pairs_def trace_of_efrag_append)
  by (smt (verit) Suc_less_eq less_Suc_eq less_trans_Suc nth_append nth_append_length option.discI)

lemma efrag_trim_good:
  "Exec_frag s0 (efl @ [(s, e, s')]) s' \<in> Good_wrt f
    \<Longrightarrow> Exec_frag s0 efl s \<in> Good_wrt f"
  apply (simp add: Good_wrt_def inverted_pairs_def trace_of_efrag_append)
  by (smt (verit) butlast_snoc less_SucI nth_butlast order.strict_trans)

lemma exec_frag_good_ects:
  assumes "Exec_frag s0 (efl @ [(s, e, s')]) s' \<in> Good_wrt f"
    "e' \<in> set (trace_of_efrag (Exec_frag s0 efl s))"
    "f e = Some c"
    "f e' = Some c'"
  shows "c \<ge> c'"
  using assms
  apply (auto simp add: Good_wrt_def inverted_pairs_def trace_of_efrag_append trace_of_efrag_length
      in_set_conv_nth)
    by (smt (verit) append_eq_conv_conj lessI nth_take nth_append_length trace_of_efrag_length leI)

lemma reducible_exec_frag:
  assumes
    \<open>valid_exec_frag E ef\<close>
    \<open>ef \<notin> Good_wrt f\<close>
    \<open>wf (measure_rel f)\<close>
  shows
    \<open>\<exists>ef'. E: ef \<rhd> ef' \<and> (ef' \<in> Good_wrt f \<or> (ef', ef) \<in> measure_rel f)\<close>
  using assms
  sorry
  

lemma reducible_to_Good_wrt_f_exec_frag: 
  fixes f :: \<open>'e \<Rightarrow> 'a :: linorder option\<close>
  shows \<open>reducible E (Good_wrt f)\<close>
  by (auto intro: reducible_to_Good_exec_frag [OF _ reducible_exec_frag])


end

