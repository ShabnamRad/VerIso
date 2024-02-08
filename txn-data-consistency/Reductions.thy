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

lemma reduce_frag_ef_first:
  assumes \<open>E: ef1 \<rhd> ef2\<close> shows \<open>ef_first ef1 = ef_first ef2\<close> using assms
  by (auto simp add: reduce_frag.simps)
  
lemma reduce_exec_reduced_valid:
  assumes \<open>E: ef1 \<rhd> ef2\<close> \<open>valid_exec E ef1\<close> shows \<open>valid_exec E ef2\<close> using assms
  by (auto simp add: valid_exec_def reduce_frag_reduced_valid reduce_frag_ef_first)

lemma reduce_frag_last_state_equiv: \<open>E: ef1 \<rhd> ef2 \<Longrightarrow> ef1 \<simeq> ef2\<close>
  by (auto simp add: reduce_frag.simps)

lemma reduce_exec_reduced_reachable:
  assumes \<open>E: ef1 \<rhd> ef2\<close> \<open>reach E (ef_first ef1)\<close>
  shows \<open>valid_exec_frag E ef2\<close> \<open>reach E (ef_first ef2)\<close>
  using assms
  by (auto simp add: reduce_frag_reduced_valid reduce_frag_ef_first)


subsection \<open>Transitive closure and reducibility\<close>

abbreviation reduce_frag_plus ("(3_: _ \<rhd>\<^sup>+ _)" [50, 50, 50] 90) where
  "E: ef1 \<rhd>\<^sup>+ ef2 \<equiv> (reduce_frag E)\<^sup>+\<^sup>+ ef1 ef2" 

lemma reduce_frag_valid_plus:
  "E: ef1 \<rhd>\<^sup>+ ef2 \<Longrightarrow> valid_exec_frag E ef1 \<and> valid_exec_frag E ef2"
  by (induction ef1 ef2 rule: tranclp.induct) (auto dest: reduce_frag_valid)

lemma reduce_frag_ef_first_plus:
  assumes \<open>E: ef1 \<rhd>\<^sup>+  ef2\<close> shows \<open>ef_first ef1 = ef_first ef2\<close> using assms
  by (induction ef1 ef2 rule: tranclp.induct) (auto dest: reduce_frag_ef_first)

lemma reduce_exec_valid_plus:
  "E: ef1 \<rhd>\<^sup>+ ef2 \<Longrightarrow> valid_exec E ef1 \<Longrightarrow> valid_exec E ef2"
  by (auto simp add: valid_exec_def reduce_frag_valid_plus reduce_frag_ef_first_plus)

lemma reduce_frag_plus_last_state_equiv: \<open>E: ef1 \<rhd>\<^sup>+ ef2 \<Longrightarrow> ef1 \<simeq> ef2\<close>
  by (induction ef1 ef2 rule: tranclp.induct)
     (auto intro: reduce_frag_last_state_equiv efrag_last_equiv_trans)

inductive reducible :: "('e, 's) ES \<Rightarrow> ('e, 's) exec_frag set \<Rightarrow> bool" for E Good where
  reducibleI: 
    "\<lbrakk> \<And>ef. \<lbrakk> valid_exec_frag E ef; reach E (ef_first ef); ef \<notin> Good \<rbrakk> \<Longrightarrow> \<exists>ef' \<in> Good. E: ef \<rhd>\<^sup>+ ef' \<rbrakk> 
     \<Longrightarrow> reducible E Good"

inductive reducible_frag :: "('e, 's) ES \<Rightarrow> ('e, 's) exec_frag set \<Rightarrow> bool" for E Good where
  reducible_fragI: 
    "\<lbrakk> \<And>ef. \<lbrakk> valid_exec_frag E ef; ef \<notin> Good \<rbrakk> \<Longrightarrow> \<exists>ef' \<in> Good. E: ef \<rhd>\<^sup>+ ef' \<rbrakk> 
     \<Longrightarrow> reducible_frag E Good"


subsection \<open>Reduction proof rules\<close>

lemma reducible_to_Good_exec:
  assumes
    \<open>wf R\<close>
    \<open>\<And>ef. \<lbrakk> valid_exec_frag E ef; reach E (ef_first ef); ef \<notin> Good \<rbrakk>
      \<Longrightarrow> (\<exists>ef'. E: ef \<rhd> ef' \<and> (ef' \<in> Good \<or> (ef', ef) \<in> R))\<close> (* TODO: can we remove ef' \<in> Good? *)
  shows
    \<open>reducible E Good\<close>
proof 
  fix ef
  assume \<open>valid_exec_frag E ef\<close> \<open>reach E (ef_first ef)\<close> \<open>ef \<notin> Good\<close>
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
        using less ef' by (blast dest: reduce_exec_reduced_reachable)
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
  from \<open>reach E s\<close> obtain s0 efl where *: \<open>valid_exec_frag E (Exec_frag s0 efl s)\<close> \<open>reach E s0\<close>
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

lemma reach_reduced_valid:
  assumes 
    \<open>reach E s\<close>
    \<open>reducible E Good\<close> 
  shows 
    \<open>s \<in> ef_last`(Exec E \<inter> Good)\<close>
  using assms
proof -
  from \<open>reach E s\<close> obtain s0 efl where *: \<open>valid_exec E (Exec_frag s0 efl s)\<close> 
    by (auto simp add: reach_last_exec)
  then show ?thesis
  proof (cases "Exec_frag s0 efl s \<in> Good")
    case True
    then show ?thesis using * by force
  next 
    case False
    then obtain ef where \<open>ef \<in> Good\<close> \<open>E: Exec_frag s0 efl s \<rhd>\<^sup>+ ef\<close>
      using * \<open>reducible E Good\<close> by (auto simp add: reducible.simps valid_exec_def)
    then show ?thesis using *
      apply (auto dest!: reduce_frag_plus_last_state_equiv)
      using \<open>E: Exec_frag s0 efl s \<rhd>\<^sup>+ ef\<close> reduce_exec_valid_plus by fastforce
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
the main premise of the rule @{thm reducible_to_Good_exec} given that we know that
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
    {(i, j) | i j c1 c2. i < j \<and> j < length tr \<and> 
              f (tr ! i) = Some c2 \<and> f (tr ! j) = Some c1 \<and> c2 > c1}"

definition adj_inv_pair where
  "adj_inv_pair f tr i j \<equiv> (i, j) \<in> inverted_pairs f tr \<and>
    (\<forall>l. i < l \<and> l < j \<longrightarrow>
      (i, l) \<notin> inverted_pairs f tr \<and>
      (l, j) \<notin> inverted_pairs f tr)"

definition left_most_adj_pair :: "('e \<Rightarrow> 'a :: linorder option) \<Rightarrow> 'e list \<Rightarrow> (nat \<times> nat)" where
  "left_most_adj_pair f tr \<equiv> (ARG_MIN (fst) (i, j). adj_inv_pair f tr i j)"

definition Good_wrt :: "('e \<Rightarrow> 'a :: linorder option) \<Rightarrow> ('e, 's) exec_frag set" where
  "Good_wrt f \<equiv> {ef | ef. inverted_pairs f (trace_of_efrag ef) = {}}"

abbreviation Good_execs :: "('e, 's) ES \<Rightarrow> ('e \<Rightarrow> 'a :: linorder option) \<Rightarrow> ('e, 's) exec_frag set" where
  "Good_execs E f \<equiv> Exec E \<inter> Good_wrt f"

definition reach_good_state :: "('e, 's) ES \<Rightarrow> ('e \<Rightarrow> 'a :: linorder option) \<Rightarrow> 's \<Rightarrow> bool" where
  "reach_good_state E f s \<equiv> \<exists>s0 efl. valid_exec E (Exec_frag s0 efl s) \<and> (Exec_frag s0 efl s) \<in> Good_wrt f"

lemma finite_inverted_pairs: 
  "finite (inverted_pairs f tr)"
  by (auto simp add: inverted_pairs_def 
           intro: rev_finite_subset[of "{(i, j). i < length tr \<and> j < length tr}"])

lemma inverted_pairs_i_lt_j:
  "(i, j) \<in> inverted_pairs f tr \<Longrightarrow> i < j"
  by (simp add: inverted_pairs_def)

lemma inverted_pairs_prefix: 
  "inverted_pairs f tr \<subseteq> inverted_pairs f (tr @ tr')"
  by (auto simp add: inverted_pairs_def nth_append)

lemma inverted_pairs_suffix: 
  "(\<lambda>(i, j). (i + length tr, j + length tr)) ` inverted_pairs f tr' \<subseteq> inverted_pairs f (tr @ tr')"
  by (auto simp add: inverted_pairs_def nth_append)

lemma inverted_pairs_append_None: 
  assumes "\<And>e. e \<in> set tr' \<Longrightarrow> f e = None"
  shows "inverted_pairs f (tr @ tr') = inverted_pairs f tr" (is  "?A = ?B")
proof 
  show "inverted_pairs f (tr @ tr') \<subseteq> inverted_pairs f tr" using assms
  apply (auto simp add: inverted_pairs_def)
  apply (metis add_diff_inverse_nat add_less_imp_less_left in_set_conv_nth nth_append option.discI)
  by (smt (verit) add.commute in_set_conv_nth le_less_linear less_diff_conv2 nth_append option.discI order_le_less_trans order_less_imp_le)
qed (simp add: inverted_pairs_prefix)

lemma inverted_pairs_snoc_None: 
  assumes "f e = None"
  shows "inverted_pairs f (tr @ [e]) = inverted_pairs f tr" 
  using assms
  \<comment> \<open>special case: simplifier needs some help here\<close>
  by (simp add: inverted_pairs_append_None[where tr'="[e]", simplified])



lemma adj_inv_eq_all_none:   \<comment> \<open>alternative definition of @{term adj_inv_pair}\<close>
  "adj_inv_pair f tr i j \<longleftrightarrow> (i, j) \<in> inverted_pairs f tr \<and> (\<forall>l. i < l \<and> l < j \<longrightarrow> f (tr ! l) = None)"
  apply (auto simp add: adj_inv_pair_def inverted_pairs_def)
  by (meson dual_order.strict_trans1 linorder_le_less_linear option.exhaust)

lemma inverted_pair_within:
  assumes "\<not>adj_inv_pair f tr i j" "(i, j) \<in> inverted_pairs f tr" 
  shows "\<exists>l. ((i, l) \<in> inverted_pairs f tr \<or> (l, j) \<in> inverted_pairs f tr) \<and> i < l \<and> l < j"
  using assms adj_inv_pair_def
  by blast 

lemma adj_inv_pair_within_inverted_pair: 
  assumes \<open>(i, j) \<in> inverted_pairs f tr\<close> \<open>n = j - i\<close> 
  shows "\<exists>i' j'. adj_inv_pair f tr i' j' \<and> i \<le> i' \<and> j' \<le> j"
  using assms
proof (induction n arbitrary: i j rule: nat_less_induct)
  case (1 n)
  then show ?case 
  proof (cases "adj_inv_pair f tr i j")
    case False
    then show ?thesis using 1
      by (smt (verit, del_insts) adj_inv_pair_def diff_less_mono diff_less_mono2 
              inverted_pairs_i_lt_j le_trans order_less_imp_le)
  qed auto
qed

lemma adj_inv_exists_not_Good_ex:
  "ef \<notin> Good_wrt f \<Longrightarrow> \<exists>i j. adj_inv_pair f (trace_of_efrag ef) i j"
  by (auto simp add: Good_wrt_def dest: adj_inv_pair_within_inverted_pair)

lemma inverted_pairs_append: "inverted_pairs f (tr @ [e]) =  inverted_pairs f tr \<union>
  {(i, length tr) | i j c1 c2. i < length tr \<and> f (tr ! i) = Some c2 \<and> f e = Some c1 \<and> c2 > c1}"
  apply (auto simp add: inverted_pairs_def)
  apply (metis append_eq_conv_conj less_SucE nth_append_length nth_take)
  apply (simp add: nth_append)
  apply (metis (mono_tags, lifting) Suc_less_eq less_Suc_eq less_trans_Suc nth_append nth_append_length)
  apply (metis (mono_tags, lifting) nth_append order.strict_trans)
  by (simp add: nth_append) 

lemma efrag_snoc_good:
  "\<lbrakk> Exec_frag s0 efl s \<in> Good_wrt f; f e = None \<rbrakk>
    \<Longrightarrow> Exec_frag s0 (efl @ [(s, e, s')]) s' \<in> Good_wrt f"
  by (auto simp add: Good_wrt_def trace_of_efrag_snoc inverted_pairs_snoc_None)

lemma efrag_snoc_good_def:
  "Exec_frag s0 (efl @ [(s, e, s')]) s' \<in> Good_wrt f \<longleftrightarrow>
    (\<forall>j i. j < Suc (length (trace_of_efrag (Exec_frag s0 efl s))) \<longrightarrow> i < j \<longrightarrow>
     (\<forall>c. f ((trace_of_efrag (Exec_frag s0 efl s) @ [e]) ! j) = Some c \<longrightarrow>
     (\<forall>c'. f (trace_of_efrag (Exec_frag s0 efl s) ! i) = Some c' \<longrightarrow>
           \<not> c < c')))"
  by (auto simp add: Good_wrt_def inverted_pairs_def nth_append trace_of_efrag_snoc)

lemma new_wrc_no_conflict:
  "\<lbrakk> Exec_frag s0 (efl @ [(s, e, s')]) s' \<in> Good_wrt f;
     f e = Some c;
     i < length efl;
     f (trace_of_efrag (Exec_frag s0 efl s) ! i) = Some c' \<rbrakk>
     \<Longrightarrow> c \<ge> c'"
  unfolding efrag_snoc_good_def
  by (metis lessI linorder_le_less_linear nth_append_length trace_of_efrag_length)

lemma efrag_trim_good:
  "Exec_frag s0 (efl @ [(s, e, s')]) s' \<in> Good_wrt f
    \<Longrightarrow> Exec_frag s0 efl s \<in> Good_wrt f"
  using inverted_pairs_prefix
  by (fastforce simp add: Good_wrt_def trace_of_efrag_snoc)

lemma reach_good_state_f_Some:
  assumes "Exec_frag s0 efl s \<in> Good_wrt f"
    "f e = Some (ects cts cl)"
    "\<forall>i < length efl. (i, length efl) \<notin> inverted_pairs f (trace_of_efrag (Exec_frag s0 (efl @ [(s, e, s')]) s'))"
  shows "Exec_frag s0 (efl @ [(s, e, s')]) s' \<in> Good_wrt f"
  using assms inverted_pairs_append[of f "trace_of_efrag (Exec_frag s0 efl s)"]
  by (auto simp add: Good_wrt_def trace_of_efrag_snoc nth_append)

lemma exec_frag_good_ects:
  assumes "Exec_frag s0 (efl @ [(s, e, s')]) s' \<in> Good_wrt f"
    "e' \<in> set (trace_of_efrag (Exec_frag s0 efl s))"
    "f e = Some c"
    "f e' = Some c'"
  shows "c \<ge> c'"
  using assms
  apply (auto simp add: Good_wrt_def inverted_pairs_def trace_of_efrag_snoc in_set_conv_nth)
    by (smt (verit) append_eq_conv_conj lessI nth_take nth_append_length trace_of_efrag_length leI)

end

