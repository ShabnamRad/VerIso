section \<open>The swap stategy and WF of the measure relation\<close>

theory "EP+_Measure"
  imports "EP+_Trace"
begin

datatype movt = Lm | Rm | Out

definition mover_type :: "'v ev list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> movt" where
  "mover_type tr i j k \<equiv> (if j \<le> i \<and> i \<le> k then
   (if EVI tr i \<le> EVI tr k then Lm else Rm)
    else Out)"

definition left_movers :: "'v ev list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "left_movers tr j k \<equiv> {i. mover_type tr i j k = Lm}"

abbreviation left_most_Lm where
  "left_most_Lm tr j k \<equiv> Min (left_movers tr j k)"

definition lmp_left_movers :: "'v ev list \<Rightarrow> nat set" where
  "lmp_left_movers tr \<equiv> let (j, k) = left_most_adj_pair ev_ects tr in
    left_movers tr j k"

definition lmp_Lm_dist_left :: "'v ev list \<Rightarrow> nat" where
  "lmp_Lm_dist_left tr \<equiv> let (j, k) = left_most_adj_pair ev_ects tr in
    left_most_Lm tr j k - j"

definition measure_R :: "('v ev, ('v, 'm) global_conf_scheme) exec_frag rel" where
  "measure_R \<equiv> measures [card o inverted_pairs ev_ects o trace_of_efrag,
                           card o lmp_left_movers o trace_of_efrag,
                           lmp_Lm_dist_left o trace_of_efrag]"

lemma wf_measure_R: "wf measure_R"
  by (auto simp add: measure_R_def)

lemma mover_type_left_end:
  "j < k \<Longrightarrow> \<not>EVI tr j < EVI tr k \<Longrightarrow> mover_type tr j j k = Rm"
  by (simp add: mover_type_def)

lemma mover_type_right_end:
  "j < k  \<Longrightarrow> mover_type tr k j k = Lm"
  by (simp add: mover_type_def)

lemma mover_type_in:
  "j \<le> i \<and> i \<le> k \<longleftrightarrow> mover_type tr i j k \<in> {Lm, Rm}"
  by (auto simp add: mover_type_def Let_def)

lemma mover_type_out:
  "\<not>(j \<le> i \<and> i \<le> k) \<longleftrightarrow> mover_type tr i j k = Out"
  by (auto simp add: mover_type_def)

lemma left_most_Lm_is_Lm:
  assumes
    \<open>left_movers tr j k \<noteq> {}\<close>
    \<open>finite (left_movers tr j k)\<close>
    \<open>i = left_most_Lm tr j k\<close>
  shows "mover_type tr i j k = Lm"
  using assms Min_in left_movers_def by fastforce 

lemma left_most_Lm_in_range:
  assumes
    \<open>left_movers tr j k \<noteq> {}\<close>
    \<open>finite (left_movers tr j k)\<close>
    \<open>i = left_most_Lm tr j k\<close>
  shows "j \<le> i""i \<le> k"
  using assms mover_type_in
  apply (auto simp add: left_movers_def)
  using Min_in by blast

lemma left_most_Lm_gt_j:
  assumes
    \<open>left_movers tr j k \<noteq> {}\<close>
    \<open>finite (left_movers tr j k)\<close>
    \<open>i = left_most_Lm tr j k\<close>
    \<open>j < k\<close>
    \<open>\<not>EVI tr j < EVI tr k\<close>
  shows "j < i"
proof -
  have j_Rm: "mover_type tr j j k \<noteq> Lm" using mover_type_left_end[OF assms(4,5)] by simp
  have i_Lm: "mover_type tr i j k = Lm" using assms left_most_Lm_is_Lm by blast
  then have "j \<le> left_most_Lm tr j k" using assms(3) mover_type_in[of j i k tr] by simp
  then show ?thesis using assms(3) j_Rm i_Lm
    by (metis le_neq_implies_less)
qed

lemma Rm_up_to_left_most_Lm:
  assumes
    \<open>left_movers tr j k \<noteq> {}\<close>
    \<open>finite (left_movers tr j k)\<close>
    \<open>i = left_most_Lm tr j k\<close>
    \<open>j < k\<close>
    \<open>\<not>EVI tr j < EVI tr k\<close>
    \<open>i' < i\<close>
    \<open>j \<le> i'\<close>
  shows "mover_type tr i' j k = Rm"
  using assms mover_type_in[of j i' k tr]
    left_most_Lm_in_range[OF assms(1-3)]
  apply (auto simp add: left_movers_def)
  using assms(6) by linarith
  

lemma inverted_pair_not_causal_dep:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>(j, k) \<in> inverted_pairs ev_ects \<tau>\<close>
  shows \<open>\<not>EVI \<tau> j < EVI \<tau> k\<close>
  using assms
  by (auto simp add: inverted_pairs_def dest!: ev_ects_Some WCommit_cts_causal_dep_gt_past)

lemma Rm_Lm_not_causal_dep:
  assumes
    \<open>mover_type \<tau> i j k = Rm\<close>
    \<open>mover_type \<tau> i' j k = Lm\<close>
  shows "\<not> EVI \<tau> i < EVI \<tau> i'"
  using assms
  apply (auto simp add: mover_type_def)
  by (metis dual_order.trans movt.distinct(1) movt.distinct(3) movt.distinct(5) order_less_imp_le)

lemma trace_of_decomposed_frag:
  "trace_of_efrag (Exec_frag s0 (efl @ (s, e2, m) # (m, e1, s') # efl') sf) =
   map (fst o snd) efl @ e2 # e1 # map (fst o snd) efl'"
  by (simp add: trace_of_efrag_def)

lemma nth_append_Suc_length [simp]:
  "(l @ e1 # e2 # l') ! Suc (length l) = e2"
  by (metis append.left_neutral append_Cons append_assoc length_append_singleton nth_append_length)

lemma nth_larger_Suc_length:
  "a > Suc (length l) \<Longrightarrow> (l @ e2 # e1 # l') ! a = (l @ e1 # e2 # l') ! a"
proof -
  assume a: "a > Suc (length l)"
  then have "((l @ e2 # [e1]) @ l') ! a = ((l @ e1 # [e2]) @ l') ! a"
    by (smt (verit, ccfv_threshold) One_nat_def Suc_eq_plus1 add_Suc_right length_Cons length_append
        list.size(3) not_less_eq nth_append)
  then show ?thesis by force
qed


subsection \<open>Measure function lemmas\<close>

lemma i_Suci1:
  assumes
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>j \<le> i \<and> Suc i \<le> k\<close>
    \<open>length l = i\<close>
    \<open>(i, Suc i) \<noteq> (j, k)\<close>
  shows "(i, Suc i) \<notin> inverted_pairs f (l @ e2 # e1 # l')"
  using assms
  apply (simp add: adj_inv_eq_all_none)
  apply (simp add: inverted_pairs_def)
  by (metis Suc_le_lessD le_antisym linorder_le_less_linear option.distinct(1))

lemma i_Suci2:
  assumes
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>j \<le> i \<and> Suc i \<le> k\<close>
    \<open>length l = i\<close>
  shows "(i, Suc i) \<notin> inverted_pairs f (l @ e1 # e2 # l')"
  using assms
  apply (simp add: adj_inv_eq_all_none)
  apply (simp add: inverted_pairs_def)
  by (metis Suc_le_lessD leD le_imp_less_Suc le_neq_implies_less nth_append_Suc_length
      nth_append_length option.discI option.inject order_less_imp_le)

lemma gt_i:
  assumes
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>length l = i\<close>
  shows "\<forall>a > Suc i. (i, a) \<in> inverted_pairs f (l @ e2 # e1 # l') \<longleftrightarrow>
                 (Suc i, a) \<in> inverted_pairs f (l @ e1 # e2 # l')"
  using assms
  apply (auto simp add: inverted_pairs_def)
  by (metis nth_larger_Suc_length)+

lemma gt_Suci:
  assumes
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>length l = i\<close>
  shows "\<forall>a > Suc i. (Suc i, a) \<in> inverted_pairs f (l @ e2 # e1 # l') \<longleftrightarrow>
                 (i, a) \<in> inverted_pairs f (l @ e1 # e2 # l')"
  using assms
  apply (auto simp add: inverted_pairs_def)
  by (metis nth_larger_Suc_length)+

lemma lt_i:
  assumes
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>length l = i\<close>
  shows "\<forall>a < i. (a, i) \<in> inverted_pairs f (l @ e2 # e1 # l') \<longleftrightarrow>
             (a, Suc i) \<in> inverted_pairs f (l @ e1 # e2 # l')"
  using assms
  apply (auto simp add: inverted_pairs_def)
  by (metis nth_append)+

lemma lt_Suci:
  assumes
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>length l = i\<close>
  shows "\<forall>a < i. (a, Suc i) \<in> inverted_pairs f (l @ e2 # e1 # l') \<longleftrightarrow>
             (a, i) \<in> inverted_pairs f (l @ e1 # e2 # l')"
  using assms
  apply (auto simp add: inverted_pairs_def)
  by (metis nth_append)+

lemma other:
  assumes
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>length l = i\<close>
  shows "\<forall>a b. (a < i \<or> a > Suc i) \<and> (b < i \<or> b > Suc i) \<longrightarrow>
      (a, b) \<in> inverted_pairs f (l @ e2 # e1 # l') \<longleftrightarrow>
      (a, b) \<in> inverted_pairs f (l @ e1 # e2 # l')"
  using assms
  apply (auto simp add: inverted_pairs_def)
  by (intro exI, auto simp add: nth_append)

definition swap_i_Suci where
  "swap_i_Suci i a \<equiv> if a = i then Suc i else (if a = Suc i then i else a)"

definition pair_after_swap where
  "pair_after_swap i \<equiv> (\<lambda>(a, b). (swap_i_Suci i a, swap_i_Suci i b))"

lemma inj_on_swap_i_Suci:
  "inj_on (swap_i_Suci i) A"
  by (auto simp add: swap_i_Suci_def inj_on_def)

lemma inj_on_pair_after_swap:
  "inj_on (pair_after_swap i) A"
  apply (auto simp add: pair_after_swap_def swap_i_Suci_def inj_on_def)
  by metis+

lemma pair_after_swap_involution:
  "A = (pair_after_swap i) ` B \<Longrightarrow> B = (pair_after_swap i) ` A"
  apply (auto simp add: pair_after_swap_def swap_i_Suci_def image_iff)
  by (rule bexI, auto)

lemma pair_after_swap_notjk:
  assumes
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>j \<le> i \<and> Suc i \<le> k\<close>
    \<open>length l = i\<close>
    \<open>(i, Suc i) \<noteq> (j, k)\<close>
  shows "(pair_after_swap i) ` inverted_pairs f (l @ e1 # e2 # l') =
         inverted_pairs f (l @ e2 # e1 # l')"
proof -
  show ?thesis using assms(1-3)
  apply (auto simp add: image_def pair_after_swap_def swap_i_Suci_def)
  apply (auto dest: inverted_pairs_i_lt_j)
  apply (metis gt_i inverted_pairs_i_lt_j)
  apply (metis i_Suci2)
  apply (metis Suc_lessI gt_Suci inverted_pairs_i_lt_j)
  apply (metis inverted_pairs_i_lt_j le_less_Suc_eq linorder_le_less_linear lt_i)
  apply (metis inverted_pairs_i_lt_j lt_Suci)
  subgoal for a b
    apply (cases "a = i"; cases "a = Suc i", auto)
    apply (cases "b = i"; cases "b = Suc i", auto)
    by (smt (verit, del_insts) Suc_lessI case_prod_conv linorder_neqE_nat other)
  subgoal for a b
    apply (cases "a = i")
    subgoal apply (cases "b = Suc i")
      apply (metis (no_types, lifting) assms(4) i_Suci1)
      by (smt (verit, del_insts) Suc_lessI case_prod_conv gt_i inverted_pairs_i_lt_j leD le_refl)
    subgoal apply (cases "a = Suc i")
      apply (smt (verit, del_insts) gt_Suci inverted_pairs_i_lt_j old.prod.case verit_comp_simplify1(1))
      apply (cases "b = i"; cases "b = Suc i", auto)
      apply (smt (verit, del_insts) case_prod_conv inverted_pairs_i_lt_j less_le_not_le lt_i)
       apply (smt (verit, del_insts) assms(4) Suc_lessI case_prod_conv inverted_pairs_i_lt_j
          less_Suc_eq_le less_or_eq_imp_le lt_Suci nat.inject not_less_eq adj_inv_pair_def)
      by (smt (verit, del_insts) Suc_lessI case_prod_conv linorder_neqE_nat other)
    done
  done
qed

lemma swap_preserves_card_inverted_pairs:
  assumes
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>j \<le> i \<and> Suc i \<le> k\<close>
    \<open>k < length (l @ e2 # e1 # l')\<close>
    \<open>length l = i\<close>
    \<open>(i, Suc i) \<noteq> (j, k)\<close>
  shows "card (inverted_pairs f (l @ e1 # e2 # l')) = card (inverted_pairs f (l @ e2 # e1 # l'))"
  using assms
  apply (intro bij_betw_same_card[of "pair_after_swap i"])
  by (simp add: bij_betw_def pair_after_swap_notjk inj_on_pair_after_swap)

lemma pair_after_swap_jk:
  assumes
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>length l = i\<close>
    \<open>(i, Suc i) = (j, k)\<close>
  shows "(pair_after_swap i) ` inverted_pairs f (l @ e1 # e2 # l') =
         inverted_pairs f (l @ e2 # e1 # l') - {(j, k)}"
proof -
  have "(j, k) \<notin> inverted_pairs f (l @ e1 # e2 # l')"
    using i_Suci2 by (metis Pair_inject assms nat_le_linear)
  then show ?thesis using assms
  apply (auto simp add: image_def pair_after_swap_def swap_i_Suci_def)
  apply (auto dest: inverted_pairs_i_lt_j)
  apply (metis gt_i inverted_pairs_i_lt_j)
  apply (meson gt_Suci inverted_pairs_i_lt_j linorder_neqE_nat not_less_eq)
  apply (metis inverted_pairs_i_lt_j less_antisym lt_i)
  apply (simp add: inverted_pairs_i_lt_j lt_Suci)
  apply (metis not_less_eq not_less_less_Suc_eq other)
  apply (metis inverted_pairs_i_lt_j less_Suc_eq adj_inv_pair_def)
  subgoal for a b
    apply (cases "a = i"; cases "a = Suc i", auto)
    apply (smt (verit) case_prod_conv gt_Suci inverted_pairs_i_lt_j adj_inv_pair_def)
    apply (cases "b = i"; cases "b = Suc i", auto)
    apply (smt (verit) case_prod_conv inverted_pairs_i_lt_j less_le_not_le lt_i)
    apply (smt (verit) Suc_lessI case_prod_conv inverted_pairs_i_lt_j less_Suc_eq_le
        less_or_eq_imp_le lt_Suci nat.inject not_less_eq)
    by (smt (verit, del_insts) Suc_lessI case_prod_conv linorder_neqE_nat other)
  subgoal for a b
    apply (cases "a = i")
    subgoal apply (cases "b = Suc i", auto)
      by (smt (verit, del_insts) Suc_lessI case_prod_conv gt_i inverted_pairs_i_lt_j leD le_refl)
    subgoal apply (cases "a = Suc i")
      apply (smt (verit, del_insts) gt_Suci inverted_pairs_i_lt_j old.prod.case verit_comp_simplify1(1))
      apply (cases "b = i"; cases "b = Suc i", auto)
      apply (smt (verit, del_insts) case_prod_conv inverted_pairs_i_lt_j less_le_not_le lt_i)
      by (smt (verit, del_insts) Suc_lessI case_prod_conv linorder_neqE_nat other)
    done
  done
qed

lemma swap_reduces_card_inverted_pairs:
  assumes
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>length l = i\<close>
    \<open>(i, Suc i) = (j, k)\<close>
  shows "card (inverted_pairs f (l @ e2 # e1 # l')) = Suc (card (inverted_pairs f (l @ e1 # e2 # l')))"
proof -
  have *: "card (inverted_pairs f (l @ e1 # e2 # l')) = card (inverted_pairs f (l @ e2 # e1 # l') - {(j, k)})"
    apply (intro bij_betw_same_card[of "pair_after_swap i"])
    using pair_after_swap_jk[OF assms] inj_on_pair_after_swap[of i]
    by (simp add: bij_betw_def)
  have **: "finite (inverted_pairs f (l @ e2 # e1 # l'))"
    by (simp add: finite_inverted_pairs)
  then have "card (inverted_pairs f (l @ e2 # e1 # l')) \<noteq> 0"
    using assms card_0_eq by (auto simp add: adj_inv_pair_def)
  then show ?thesis using assms apply (auto simp add: adj_inv_pair_def)
    by (metis * ** card_Suc_Diff1)
qed

lemma "(ARG_MIN f x. P x) = y \<Longrightarrow> {x. P x} \<noteq> {} \<Longrightarrow> finite {x. P x} \<Longrightarrow> f y = Min (f ` {x. P x})"
  apply (auto simp add: arg_min_def image_def is_arg_min_linorder) oops

lemma nth_append_le_len:
  "i \<le> length l \<Longrightarrow> (l @ e1 # e2 # l') ! i = (l @ [e1]) ! i"
  by (metis nth_append nth_append_length order_le_less)

lemma nth_append_gt_len:
  "i \<ge> Suc (length l) \<Longrightarrow> (l @ e1 # e2 # l') ! i = (e2 # l') ! (i - Suc (length l))"
  by (simp add: nth_append)

lemma nth_append_gt_Suc_len:
  "i > Suc (length l) \<Longrightarrow> (l @ e1 # e2 # l') ! i = l' ! (i - Suc (Suc (length l)))"
  by (simp add: nth_append)

lemma adj_inv_pairs_non_overlapping:
  assumes
    "adj_inv_pair f \<tau> j k"
    "adj_inv_pair f \<tau> j' k'"
    "j < j'"
  shows "k \<le> j'"
  using assms
  by (auto simp add: adj_inv_pair_def inverted_pairs_def)

lemma adj_inv_pairs_non_overlapping':
  assumes
    "adj_inv_pair f \<tau> j k"
    "adj_inv_pair f \<tau> j k'"
  shows "k = k'"
  using assms
  apply (auto simp add: adj_inv_pair_def inverted_pairs_def)
  by (metis linorder_neqE_nat)

lemma adj_inv_pair_i_lt_j:
  "adj_inv_pair f \<tau> i j \<Longrightarrow> i < j"
  by (auto simp add: adj_inv_pair_def inverted_pairs_i_lt_j)

lemma collect_arg_min_eq:
  "{(x, y). P x y} = {(x, y). Q x y} \<Longrightarrow> (ARG_MIN f (x, y). P x y) = (ARG_MIN f (x, y). Q x y)"
  by (smt (verit) case_prod_eta cond_case_prod_eta mem_Collect_eq)


lemma focused_pair_after_swap:
  assumes 
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>j \<le> i \<and> Suc i \<le> k\<close>
    \<open>length l = i\<close>
    \<open>(i, Suc i) \<noteq> (j, k)\<close>
  shows "adj_inv_pair f (l @ e1 # e2 # l') (swap_i_Suci i j) (swap_i_Suci i k)" 
proof -
  have "inverted_pairs f (l @ e1 # e2 # l') = pair_after_swap i ` inverted_pairs f (l @ e2 # e1 # l')"
    using pair_after_swap_notjk[OF assms(1-3), symmetric] assms(4)
      pair_after_swap_involution[of "inverted_pairs f (l @ e2 # e1 # l')"]
    by simp
  then show ?thesis using assms(1-3)
  apply (auto simp add: adj_inv_eq_all_none image_def)
  subgoal by (rule bexI[where x="(j, k)"]; simp add: pair_after_swap_def)
  subgoal
    apply (thin_tac "inverted_pairs f _ = _")
    apply (cases "j = i"; cases "k = Suc i", auto simp add: swap_i_Suci_def)
    apply (smt (verit) Suc_lessD nth_larger_Suc_length order_less_imp_not_less)
    apply (metis (full_types, opaque_lifting) less_Suc_eq nth_append)
    by (smt (verit) Suc_le_lessD less_Suc_eq not_less_iff_gr_or_eq nth_append
        nth_append_Suc_length nth_append_length nth_larger_Suc_length)
  done
qed

lemma unfocused_pair_after_swap:
  assumes
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>j \<le> i \<and> Suc i \<le> k\<close>
    \<open>length l = i\<close>
    \<open>(i, Suc i) \<noteq> (j, k)\<close>
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j' k'\<close>
    \<open>k \<le> j'\<close>
  shows "adj_inv_pair f (l @ e1 # e2 # l') (swap_i_Suci i j') k'"
  using assms
proof -
  have "inverted_pairs f (l @ e1 # e2 # l') = pair_after_swap i ` inverted_pairs f (l @ e2 # e1 # l')"
    using pair_after_swap_notjk[OF assms(1-3), symmetric] assms(4)
      pair_after_swap_involution[of "inverted_pairs f (l @ e2 # e1 # l')"]
    by simp
  then show ?thesis using assms(1-3,5-)
  apply (auto simp add: adj_inv_eq_all_none image_def)
  subgoal apply (rule bexI[where x="(j', k')"]; simp add: pair_after_swap_def)
    by (metis inverted_pairs_i_lt_j leD le_trans less_or_eq_imp_le not_less_eq_eq swap_i_Suci_def)
  subgoal
    apply (thin_tac "inverted_pairs f _ = _")
    apply (auto simp add: swap_i_Suci_def)
    by (smt (verit, best) assms(4) le_neq_implies_less le_trans less_eq_Suc_le
        less_trans_Suc nth_append_Suc_length nth_append_length nth_larger_Suc_length)
  done
qed


lemma unfocused_pair_after_swap':
  assumes
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>j \<le> i \<and> Suc i \<le> k\<close>
    \<open>length l = i\<close>
    \<open>(i, Suc i) \<noteq> (j, k)\<close>
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j' k'\<close>
    \<open>k \<le> j'\<close>
  shows "adj_inv_pair f (l @ e1 # e2 # l') (swap_i_Suci i j') (swap_i_Suci i k')"
  using assms
proof -
  have "inverted_pairs f (l @ e1 # e2 # l') = pair_after_swap i ` inverted_pairs f (l @ e2 # e1 # l')"
    using pair_after_swap_notjk[OF assms(1-3), symmetric] assms(4)
      pair_after_swap_involution[of "inverted_pairs f (l @ e2 # e1 # l')"]
    by simp
  then show ?thesis using assms(1-3,5-)
  apply (auto simp add: adj_inv_eq_all_none image_def)
  subgoal by (rule bexI[where x="(j', k')"]; simp add: pair_after_swap_def)
  subgoal
    apply (thin_tac "inverted_pairs f _ = _")
    apply (auto simp add: swap_i_Suci_def)
    by (smt (verit) assms(4) le_neq_implies_less le_trans less_Suc_eq less_or_eq_imp_le
        not_less_eq nth_append_Suc_length nth_append_length nth_larger_Suc_length)
  done
qed

lemma blaaaa:
  assumes
    \<open>left_most_adj_pair f (l @ e2 # e1 # l') = (j, k)\<close>
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>j \<le> i \<and> Suc i \<le> k\<close>
    \<open>length l = i\<close>
    \<open>(i, Suc i) \<noteq> (j, k)\<close>
    \<open>adj_inv_pair f (l @ e1 # e2 # l') j' k'\<close>
  shows "k' > i"
proof (rule ccontr)
  assume a: "\<not> i < k'"
  have "(j', k') \<in> inverted_pairs f (l @ e1 # e2 # l')"
    using assms(6) by (simp add: adj_inv_pair_def)
  then obtain i' where "j' \<le> i' \<and> Suc i' \<le> k'"
    using inverted_pairs_i_lt_j Suc_leI by blast
  then have "(pair_after_swap i (j', k')) \<in> inverted_pairs f (l @ e2 # e1 # l')"
    using a unfocused_pair_after_swap[of f l e1 e2 l' j' k' i' i] apply auto sorry
  show False sorry
qed
    

lemma adj_pair_after_swap_notjk:
  assumes
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>j \<le> i \<and> Suc i \<le> k\<close>
    \<open>length l = i\<close>
    \<open>(i, Suc i) \<noteq> (j, k)\<close>
    \<open>\<forall>j' k'. adj_inv_pair f (l @ e2 # e1 # l') j' k' \<and> j' \<noteq> j \<longrightarrow> k \<le> j'\<close>
  shows "(pair_after_swap i) ` {(j, k). adj_inv_pair f (l @ e1 # e2 # l') j k} =
         {(j, k). adj_inv_pair f (l @ e2 # e1 # l') j k}"
proof -
  show ?thesis using assms(1)
    apply (auto simp add: image_def pair_after_swap_def)
    subgoal for j' k'
      apply (auto simp add: adj_inv_eq_all_none)
       apply (smt (verit) Suc_lessI adj_inv_eq_all_none assms(2) assms(3) gt_Suci i_Suci2
          inverted_pairs_i_lt_j less_SucE lt_Suci nat_neq_iff other swap_i_Suci_def)
      apply (auto simp add: swap_i_Suci_def split: if_split_asm)
          apply (metis Suc_lessD assms(3) nth_larger_Suc_length)
      using assms(2,5)
      sorry
    subgoal for j' k'
      apply (rule exI[where x="swap_i_Suci i j'"])
      apply (rule exI[where x="swap_i_Suci i k'"])
      apply auto
      subgoal apply (cases "j' = j")
        subgoal using adj_inv_pairs_non_overlapping'[OF assms(1), of k']
            focused_pair_after_swap[OF assms(1-4)] by auto
        subgoal using unfocused_pair_after_swap'[OF assms(1-4), of j' k']
            assms(5) by auto
        done
      by (simp_all add: swap_i_Suci_def)
    done
qed


lemma is_arg_min_unique: "is_arg_min f P x \<Longrightarrow> \<forall>x'. x' \<noteq> x \<longrightarrow> \<not>is_arg_min f P x' \<Longrightarrow> arg_min f P = x"
  by (metis arg_min_def someI)

lemma arg_min_unique:
  fixes f :: "'a \<Rightarrow> 'b::order"
  assumes
    "P x"
    "\<forall>x'. x' \<noteq> x \<and> P x' \<longrightarrow> f x < f x'"
  shows "arg_min f P = x"
  using assms
  by (intro is_arg_min_unique, auto simp add: is_arg_min_def)

(*To chsp: I have successfully proven that given an adj_inv_pair (j, k) in the original trace,
  there is an adj_inv_pair (j', k') with i and Suc i swapped. (lemmas on lines 343 to 420)
  The missing part is proving the other direction: given a adjacent pair in the "after-swap" trace,
  there has been an adjacent pair in the original trace. In all the different ways I tried to prove 
  this (for example also see line 462 of the lemma adj_pair_after_swap_notjk) there has always been
  a problem matching the indices with existing established lemmas. *)
lemma swap_preserves_lmp:
  assumes
    \<open>left_most_adj_pair f (l @ e2 # e1 # l') = (j, k)\<close>
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>j \<le> i \<and> Suc i \<le> k\<close>
    \<open>length l = i\<close>
    \<open>(i, Suc i) \<noteq> (j, k)\<close>
  shows "left_most_adj_pair f (l @ e1 # e2 # l') = pair_after_swap i (j, k)"

proof -
  have assms236': "adj_inv_pair f (l @ e1 # e2 # l') (swap_i_Suci i j) (swap_i_Suci i k)"
    "swap_i_Suci i j \<le> Suc i \<and> i \<le> swap_i_Suci i k"
    "(Suc i, i) \<noteq> (swap_i_Suci i j, swap_i_Suci i k)"
    using focused_pair_after_swap[OF assms(2-5)] assms(2,3,5)
    by (auto simp add: swap_i_Suci_def)
  have swap_j'_le_k:
    "\<forall>j' \<ge> k. swap_i_Suci i k \<le> swap_i_Suci i j'"
    using assms(3) by (auto simp add: swap_i_Suci_def)
  have swap_j_lt_k:
    "swap_i_Suci i j < swap_i_Suci i k"
    using assms(3, 5)
    by (auto simp add: swap_i_Suci_def)
  hence swap_j'_lt_j:
    "\<forall>j' \<ge> k. swap_i_Suci i j < swap_i_Suci i j'"
    using assms(3) by (auto simp add: swap_i_Suci_def)
  have "\<forall>j' k'. adj_inv_pair f (l @ e2 # e1 # l') j' k' \<and> j' \<noteq> j \<longrightarrow> k \<le> j'"
    using assms(1-2) apply (auto simp add: left_most_adj_pair_def)
    by (metis adj_inv_pairs_non_overlapping arg_min_nat_le case_prod_conv fst_def le_neq_implies_less)
  then have "\<forall>j' k'. adj_inv_pair f (l @ e2 # e1 # l') j' k' \<and> j' \<noteq> j \<longrightarrow>
    adj_inv_pair f (l @ e1 # e2 # l') (swap_i_Suci i j') k' \<and> swap_i_Suci i j' \<noteq> swap_i_Suci i j"
    using unfocused_pair_after_swap[OF assms(2-5)]
    apply auto by (metis less_imp_neq swap_j'_lt_j)
  then have "\<forall>j' k'. adj_inv_pair f (l @ e1 # e2 # l') j' k' \<and> j' \<noteq> swap_i_Suci i j \<longrightarrow> swap_i_Suci i k \<le> j'"
    using assms(3,5) apply (auto simp add: swap_i_Suci_def) sorry
  then have "\<forall>j' k'. adj_inv_pair f (l @ e1 # e2 # l') j' k' \<and> j' \<noteq> swap_i_Suci i j \<longrightarrow> swap_i_Suci i j < j'"
    using swap_j_lt_k by auto
  then show ?thesis using assms236'(1)
    using arg_min_unique[of "\<lambda>(x, y). adj_inv_pair f (l @ e1 # e2 # l') x y" _ fst]
    apply (auto simp add: left_most_adj_pair_def pair_after_swap_def)
    using adj_inv_pairs_non_overlapping' by blast
qed

(*
then have "{(j, k). adj_inv_pair f (l @ e1 # e2 # l') j k} =
      pair_after_swap i ` {(j, k). adj_inv_pair f (l @ e2 # e1 # l') j k}"
    apply (auto simp add: adj_inv_pair_def)

    apply (auto simp add: adj_inv_pair_def swap_i_Suci_def)
    apply (metis inverted_pairs_i_lt_j less_irrefl_nat)
    apply (metis Suc_lessD inverted_pairs_i_lt_j less_irrefl_nat)
    subgoal for i' apply (auto simp add: image_iff)
      apply (rule exI[where x=i'], auto) sorry
    apply (smt (verit) assms(2) assms(3) assms(5) assms(6) i_Suci1)
    apply (metis inverted_pairs_i_lt_j less_irrefl_nat)
    subgoal for i' apply (auto simp add: image_iff)
      apply (rule exI[where x=i], auto)
      apply (rule exI[where x=i'], auto) sorry
    subgoal for i' apply (auto simp add: image_iff)
      apply (rule exI[where x=i'], auto) sorry
    subgoal for i' apply (auto simp add: image_iff)
      apply (rule exI[where x=i'], auto)
      apply (rule exI[where x=i], auto) sorry
    subgoal for i' j' apply (auto simp add: image_iff)
      apply (rule exI[where x=i'], auto)
      apply (rule exI[where x=j'], auto) sorry
    subgoal for i' j' i'' j''
    apply (auto split: if_split_asm)
      apply (metis inverted_pairs_i_lt_j lessI order.asym)

lemma bla: "Suc (length l) \<le> k \<Longrightarrow>
  EVI (l @ e1 # e2 # l') (Suc (length l)) \<le> EVI (l @ e1 # e2 # l') k \<Longrightarrow>
  EVI (l @ e2 # e1 # l') (length l) \<le> EVI (l @ e2 # e1 # l') k"
  apply (cases "Suc (length l) = k", auto simp add: less_eq_ev_i_def)
  apply (induction "EVI (l @ e1 # e2 # l') i" "EVI (l @ e1 # e2 # l') k" arbitrary: k rule: trancl.induct)
  subgoal for k
    apply simp
    using causal_dep0_pres[of "l @ e1 # e2 # l'" i k "l @ e2 # e1 # l'" i k]
       nth_append_gt_len[of l k e2 e1 l']
    apply (auto dest:)
    subgoal using assms sorry sorry
  subgoal for b k apply (cases b)
    using causal_dep0_tr_eq[of b "EVI \<tau> k"]
      causal_dep0_ind_lt[of b "EVI \<tau> k"] apply auto
      using causal_dep0_pres[of \<tau> _ k \<tau>'] sorry
  done

lemma bla': 
  assumes
    \<open>EVI (l @ e1 # e2 # l') i \<le> EVI (l @ e1 # e2 # l') k\<close>
    \<open>i \<noteq> length l\<close>
    \<open>i \<noteq> Suc (length l)\<close>
    \<open>Suc (length l) \<le> k\<close>
    \<open>\<not> EVI (l @ e2 # e1 # l') (length l) \<le> EVI (l @ e2 # e1 # l') k\<close>
    \<open>EVI (l @ e2 # e1 # l') (Suc (length l)) \<le> EVI (l @ e2 # e1 # l') k\<close>
  shows "EVI (l @ e2 # e1 # l') i \<le> EVI (l @ e2 # e1 # l') k"
  using assms(1-4)
  apply (cases "i = k", auto simp add: less_eq_ev_i_def)
  apply (induction "EVI (l @ e1 # e2 # l') i" "EVI (l @ e1 # e2 # l') k" arbitrary: k rule: trancl.induct)
  subgoal for k
    apply simp
    using causal_dep0_pres[of "l @ e1 # e2 # l'" i k "l @ e2 # e1 # l'" i k]
       nth_append_gt_len[of l k e2 e1 l']
    apply (auto dest:)
    subgoal using assms sorry sorry
  subgoal for b k apply (cases b)
    using causal_dep0_tr_eq[of b "EVI \<tau> k"]
      causal_dep0_ind_lt[of b "EVI \<tau> k"] apply auto
      using causal_dep0_pres[of \<tau> _ k \<tau>'] sorry
  done*)

lemma swap_mover_type:
  "j \<le> length l \<and> Suc (length l) \<le> k \<Longrightarrow>
   mover_type (l @ e2 # e1 # l') (length l) j k = Rm \<Longrightarrow>
   mover_type (l @ e2 # e1 # l') (Suc (length l)) j k = Lm \<Longrightarrow>
   {i. mover_type (l @ e1 # e2 # l') i j k = Lm} =
   (swap_i_Suci (length l)) ` {i. mover_type (l @ e2 # e1 # l') i j k = Lm}"
  apply auto
  subgoal for i
    apply (cases "i = length l"; cases "i = Suc (length l)",
        auto simp add: image_iff swap_i_Suci_def mover_type_def
        split: if_split_asm) sorry
  subgoal for i
    apply (cases "i = length l"; cases "i = Suc (length l)",
        auto simp add: swap_i_Suci_def mover_type_def
        split: if_split_asm) sorry
  done



lemma swap_decreases_measure: 
  assumes
    \<open>left_most_adj_pair ev_ects (trace_of_efrag ef) = (j, k)\<close>
    \<open>\<exists>j k. adj_inv_pair ev_ects (trace_of_efrag ef) j k\<close>
    \<open>j \<le> i\<close> \<open>Suc i \<le> k\<close>
    \<open>k < length (ef_list ef)\<close>
    \<open>Suc i = left_most_Lm (trace_of_efrag ef) j k\<close>
    \<open>length efl = i\<close>
    \<open>valid_exec_frag tps ef\<close>
    \<open>ef = Exec_frag s0 (efl @ (s, e2, m) # (m, e1, s') # efl') sf\<close>
    \<open>ef' = Exec_frag s0 (efl @ (s, e1, w) # (w, e2, s') # efl') sf\<close>
  shows \<open>(ef', ef) \<in> measure_R\<close>
  using assms
proof (cases "j = i")
  case True
  then show ?thesis 
  proof (cases "Suc i = k")
    case True
    then have 
      "card (inverted_pairs ev_ects (trace_of_efrag ef')) <
       card (inverted_pairs ev_ects (trace_of_efrag ef))"
    using \<open>j = i\<close> assms(5-) lmp_is_adj[OF assms(1-2)]
    by (auto simp add: trace_of_efrag_append_cons2 dest: swap_reduces_card_inverted_pairs)
    then show ?thesis by (simp add: measure_R_def)
  next
    case False
    then have \<open>Suc i < k\<close> using \<open>Suc i \<le> k\<close> by simp
    then have inv_pair_card:
      "card (inverted_pairs ev_ects (trace_of_efrag ef')) =
       card (inverted_pairs ev_ects (trace_of_efrag ef))"
    using \<open>j = i\<close> assms(5-) lmp_is_adj[OF assms(1-2)]
    by (auto simp add: trace_of_efrag_append_cons2 dest: swap_preserves_card_inverted_pairs)
  then have
      "card (lmp_left_movers (trace_of_efrag ef')) <
       card (lmp_left_movers (trace_of_efrag ef))"
    using \<open>j = i\<close> assms(1,5-) lmp_is_adj[OF assms(1-2)] sorry
    then show ?thesis using inv_pair_card
      by (simp add: measure_R_def)
  qed
next
  case False
    then have \<open>j < i\<close> using \<open>j \<le> i\<close> by simp
    then have inv_pair_card:
      "card (inverted_pairs ev_ects (trace_of_efrag ef')) =
       card (inverted_pairs ev_ects (trace_of_efrag ef))"
      using assms(4-) lmp_is_adj[OF assms(1-2)]
      by (auto simp add: trace_of_efrag_append_cons2 dest: swap_preserves_card_inverted_pairs[where i=i])
    then have Lms_card:
      "card (lmp_left_movers (trace_of_efrag ef')) =
       card (lmp_left_movers (trace_of_efrag ef))"
      using assms(1,4-) lmp_is_adj[OF assms(1-2)] sorry
    then have 
      "lmp_Lm_dist_left (trace_of_efrag ef') <
       lmp_Lm_dist_left (trace_of_efrag ef)"
      using assms(1,4-) lmp_is_adj[OF assms(1-2)] sorry
  then show ?thesis using inv_pair_card Lms_card
    by (simp add: measure_R_def)
qed


(*
\<comment> \<open>i \<noteq> j \<and> Suc i \<noteq> k\<close>
  using swap_preserves_lmp[of ev_ects _ e2]
  apply (simp add: lmp_left_movers_def pair_after_swap_def swap_i_Suci_def)
  using swap_mover_type[of j _ k e2] card_image[OF inj_on_swap_i_Suci]
  by auto
*)


end