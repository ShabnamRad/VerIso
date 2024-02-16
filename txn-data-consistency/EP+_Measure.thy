section \<open>The swap stategy and WF of the measure relation\<close>

theory "EP+_Measure"
  imports "EP+_Trace"
begin

datatype movt = Lm | Rm | Out

definition mover_type :: "'v ev list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> movt" where
  "mover_type tr i j k \<equiv> (if j \<le> i \<and> i \<le> k then
   (if i = k \<or> tr: i \<lesssim> k then Lm else Rm)
    else Out)"

abbreviation left_movers_interval :: "'v ev list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "left_movers_interval tr j k from to \<equiv> {i. from \<le> i \<and> i \<le> to \<and> mover_type tr i j k = Lm}"

definition left_movers :: "'v ev list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "left_movers tr j k \<equiv> left_movers_interval tr j k j k"

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

\<comment> \<open>mover_type lemmas\<close>
lemma mover_type_left_end:
  "j < k \<Longrightarrow> \<not>tr: j \<lesssim> k \<Longrightarrow> mover_type tr j j k = Rm"
  by (simp add: mover_type_def)

lemma mover_type_right_end:
  "j \<le> k \<Longrightarrow> mover_type tr k j k = Lm"
  by (simp add: mover_type_def)

lemma mover_type_in:
  "mover_type tr i j k \<in> {Lm, Rm} \<longleftrightarrow> j \<le> i \<and> i \<le> k"
  by (auto simp add: mover_type_def Let_def)

lemma mover_type_out:
  "mover_type tr i j k = Out \<longleftrightarrow> \<not>(j \<le> i \<and> i \<le> k)"
  by (auto simp add: mover_type_def)

lemma mover_type_trim_L:
  assumes
    \<open>mover_type (\<tau> @ \<tau>') i j k = Lm\<close>
    \<open>k < length \<tau>\<close>
  shows \<open>mover_type \<tau> i j k = Lm\<close>
  using assms mover_type_in
  apply (auto simp add: mover_type_def)
  by (metis causal_dep_tr_trim movt.distinct(1))

lemma mover_type_trimprefix_L:
  assumes 
    \<open>mover_type (\<tau> @ \<tau>') i j k = Lm\<close>
    \<open>j \<ge> length \<tau>\<close>
  shows \<open>mover_type \<tau>' (i - length \<tau>) (j - length \<tau>) (k - length \<tau>) = Lm\<close>
  using assms mover_type_in[of "\<tau> @ \<tau>'" i j k]
  apply (auto simp add: mover_type_def)
  by (smt (verit) causal_dep_tr_trimprefix le_trans less_or_eq_imp_le movt.distinct(1))

lemma mover_type_append_L:
  assumes
    \<open>mover_type \<tau> i j k = Lm\<close>
    \<open>k < length \<tau>\<close>
  shows \<open>mover_type (\<tau> @ \<tau>') i j k = Lm\<close>
  using assms mover_type_in
  apply (auto simp add: mover_type_def)
  by (metis causal_dep_tr_append movt.distinct(1))

lemma mover_type_prepend_L:
  assumes
    \<open>mover_type \<tau>' i j k = Lm\<close>
  shows "mover_type (\<tau> @ \<tau>') (i + length \<tau>) (j + length \<tau>) (k + length \<tau>) = Lm"
  using assms mover_type_in
  apply (auto simp add: mover_type_def)
  by (metis causal_dep_tr_prepend movt.distinct(1))

lemma mover_type_trim_R:
  assumes
    \<open>mover_type (\<tau> @ \<tau>') i j k = Rm\<close>
    \<open>k < length \<tau>\<close>
  shows \<open>mover_type \<tau> i j k = Rm\<close>
  using assms mover_type_in
  apply (auto simp add: mover_type_def)
  apply (metis movt.distinct(1))
  by (simp add: causal_dep_tr_append)

lemma mover_type_trimprefix_R:
  assumes 
    \<open>mover_type (\<tau> @ \<tau>') i j k = Rm\<close>
    \<open>j \<ge> length \<tau>\<close>
  shows \<open>mover_type \<tau>' (i - length \<tau>) (j - length \<tau>) (k - length \<tau>) = Rm\<close>
  using assms mover_type_in[of "\<tau> @ \<tau>'" i j k]
  apply (auto simp add: mover_type_def)
   apply (meson dual_order.trans eq_diff_iff movt.distinct(1))
  by (smt (verit, ccfv_SIG) causal_dep_tr_prepend diff_add dual_order.trans movt.distinct(1))

lemma mover_type_append_R:
  assumes
    \<open>mover_type \<tau> i j k = Rm\<close>
    \<open>k < length \<tau>\<close>
  shows \<open>mover_type (\<tau> @ \<tau>') i j k = Rm\<close>
  using assms mover_type_in
  apply (auto simp add: mover_type_def)
  apply (metis movt.distinct(1))
  by (metis causal_dep_tr_trim movt.distinct(1))

lemma mover_type_prepend_R:
  assumes
    \<open>mover_type \<tau>' i j k = Rm\<close>
  shows "mover_type (\<tau> @ \<tau>') (i + length \<tau>) (j + length \<tau>) (k + length \<tau>) = Rm"
  using assms mover_type_in
  apply (auto simp add: mover_type_def)
  apply (metis movt.distinct(1))
  by (metis add_diff_cancel_right' causal_dep_tr_trimprefix le_add2 movt.distinct(1))

lemma mover_type_swap_k_pres_Lms:
  assumes
    \<open>mover_type (l @ e2 # e1 # l') (length l) j k = Rm\<close>
    \<open>k = Suc (length l)\<close>
    \<open>x < length l\<close>
  shows \<open>mover_type (l @ e2 # e1 # l') x j k = Lm \<longleftrightarrow>
         mover_type (l @ e1 # e2 # l') x j (length l) = Lm\<close>
  using assms mover_type_in[of "l @ e2 # e1 # l'"]
  apply (auto simp add: mover_type_def)
  apply (metis add_diff_cancel_left' causal_dep_swap_left_Suc_len movt.distinct(1) plus_1_eq_Suc)
  by (metis causal_dep_swap_left_len)

lemma mover_type_swap_k_pres_Rms:
  assumes
    \<open>mover_type (l @ e2 # e1 # l') (length l) j k = Rm\<close>
    \<open>k = Suc (length l)\<close>
    \<open>x < length l\<close>
  shows \<open>mover_type (l @ e2 # e1 # l') x j k = Rm \<longleftrightarrow>
         mover_type (l @ e1 # e2 # l') x j (length l) = Rm\<close>
  using assms mover_type_in[of "l @ e2 # e1 # l'"]
  apply (auto simp add: mover_type_def)
  apply (metis add_diff_cancel_left' causal_dep_swap_left_Suc_len movt.distinct(1) plus_1_eq_Suc)
  by (metis causal_dep_swap_left_len)

lemma mover_type_swap_k_with_Lm:
  assumes
    \<open>mover_type (l @ e2 # e1 # l') (length l) j k = Rm\<close>
    \<open>k = Suc (length l)\<close>
  shows \<open>mover_type (l @ e2 # e1 # l') (Suc (length l)) j k = Lm \<longleftrightarrow>
         mover_type (l @ e1 # e2 # l') (length l) j (length l) = Lm\<close>
  using assms mover_type_in[of "l @ e2 # e1 # l'"]
  apply (auto simp add: mover_type_def)
  by metis

lemma mover_type_swap_within: 
  assumes
    \<open>mover_type (l @ e2 # e1 # l') (length l) j k = Rm\<close>
    \<open>mover_type (l @ e2 # e1 # l') (Suc (length l)) j k = Lm\<close>
    \<open>k > Suc (length l)\<close>
  shows \<open>mover_type (l @ e1 # e2 # l') (length l) j k = Lm\<close>
        \<open>mover_type (l @ e1 # e2 # l') (Suc (length l)) j k = Rm\<close>
  using assms mover_type_in[of "l @ e2 # e1 # l'"]
  apply (auto simp add: mover_type_def split: if_split_asm)
  by (metis causal_dep_swap_Suc_len_right Suc_leI diff_Suc_1)+

lemma mover_type_swap_within_pres_Lms:
  assumes
    \<open>mover_type (l @ e2 # e1 # l') (length l) j k = Rm\<close>
    \<open>mover_type (l @ e2 # e1 # l') (Suc (length l)) j k = Lm\<close>
    \<open>mover_type (l @ e2 # e1 # l') x j k = Lm\<close>
    \<open>k > Suc (length l)\<close>
    \<open>x < length l\<close>
  shows \<open>mover_type (l @ e1 # e2 # l') x j k = Lm\<close>
  using assms mover_type_in[of "l @ e2 # e1 # l'"]
  apply (auto simp add: mover_type_def split: if_split_asm)
  by (metis causal_dep_swap_within Suc_leI trancl_trans)

lemma mover_type_swap_within_pres_Rms:
  assumes
    \<open>mover_type (l @ e2 # e1 # l') (length l) j k = Rm\<close>
    \<open>mover_type (l @ e2 # e1 # l') (Suc (length l)) j k = Lm\<close>
    \<open>mover_type (l @ e2 # e1 # l') x j k = Rm\<close>
    \<open>j < length l\<close>
    \<open>k > Suc (length l)\<close>
    \<open>j \<le> x\<close>\<open>x < length l\<close>
  shows \<open>mover_type (l @ e1 # e2 # l') x j k = Rm\<close>
  using assms mover_type_in[of "l @ e2 # e1 # l'"]
  apply (auto simp add: mover_type_def split: if_split_asm)
  using causal_dep_swap_Suc_len_right[of "Suc (length l)" k l e2 e1 l']
  apply auto oops (*Continue here: how do we know we don't introduce a new dependency after swapping*)


\<comment> \<open>left_movers lemmas\<close>
lemma left_movers_split_first:
  "left_movers \<tau> j k =
    (if mover_type \<tau> j j k = Lm then {j} else {}) \<union> left_movers \<tau> (Suc j) k"
  apply (auto simp add: left_movers_def mover_type_def)
  by (metis Suc_leI le_neq_implies_less)+

lemma left_movers_int_split_first:
  "j' \<le> k' \<Longrightarrow> k' \<le> k \<Longrightarrow>
    left_movers_interval \<tau> j k j' k' =
    (if mover_type \<tau> j' j k = Lm then {j'} else {}) \<union> left_movers_interval \<tau> j k (Suc j') k'"
  apply (auto simp add: mover_type_def)
  by (metis Suc_leI le_neq_implies_less)+

lemma left_movers_int_split_last:
  "j' \<le> Suc k' \<Longrightarrow> Suc k' \<le> k \<Longrightarrow>
    left_movers_interval \<tau> j k j' (Suc k') =
    (if mover_type \<tau> (Suc k') j k = Lm then {Suc k'} else {})
      \<union> left_movers_interval \<tau> j k j' k'"
  apply (auto simp add: mover_type_def)
  using le_SucE by blast

lemma left_movers_split:
  "j' \<le> i \<Longrightarrow> Suc i \<le> k' \<Longrightarrow>
   left_movers_interval \<tau> j k j' k' =
   left_movers_interval \<tau> j k j' i \<union> left_movers_interval \<tau> j k (Suc i) k'"
  by (auto simp add: mover_type_def)

lemma left_movers_swap_split:
  "i > 0 \<Longrightarrow> j < i \<Longrightarrow> Suc i \<le> k \<Longrightarrow>
   left_movers_interval \<tau> j k j k =
   left_movers_interval \<tau> j k j (i - 1) \<union>
    (if mover_type \<tau> i j k = Lm then {i} else {}) \<union> 
    (if mover_type \<tau> (Suc i) j k = Lm then {Suc i} else {}) \<union> 
    left_movers_interval \<tau> j k (Suc (Suc i)) k"
  using left_movers_split[of j "i - 1" k \<tau> j k]
        left_movers_int_split_first[of i k k \<tau> j]
        left_movers_int_split_first[of "Suc i" k k \<tau> j]
  by auto

lemma left_movers_trimprefix:
  "j \<ge> length \<tau> \<Longrightarrow> j \<le> k \<Longrightarrow>
    left_movers (\<tau> @ \<tau>') j k = (\<lambda>i. i + length \<tau>) ` (left_movers \<tau>' (j - length \<tau>) (k - length \<tau>))"
  apply (auto simp add: image_iff)
  subgoal for i
    apply (intro bexI[where x="i - length \<tau>"], auto simp add: left_movers_def)
    using mover_type_trimprefix_L by blast
  subgoal for i
    apply (auto simp add: left_movers_def)
    by (smt (verit, ccfv_SIG) le_add_diff_inverse2 le_trans mover_type_prepend_L)
  done

lemma left_movers_finite:
  "finite (left_movers \<tau> j k)"
  by (auto simp add: left_movers_def mover_type_def)


\<comment> \<open>left_most_Lm lemmas\<close>
lemma left_most_Lm_is_Lm:
  assumes
    \<open>left_movers tr j k \<noteq> {}\<close>
    \<open>i = left_most_Lm tr j k\<close>
  shows "mover_type tr i j k = Lm"
  using assms Min_in left_movers_def
    left_movers_finite[of tr j k]
  by fastforce

lemma left_most_Lm_in_range:
  assumes
    \<open>left_movers tr j k \<noteq> {}\<close>
    \<open>i = left_most_Lm tr j k\<close>
  shows "j \<le> i""i \<le> k"
  using assms mover_type_in
  apply (auto simp add: left_movers_def)
  using dual_order.trans by fastforce

lemma left_most_Lm_gt_j:
  assumes
    \<open>left_movers tr j k \<noteq> {}\<close>
    \<open>i = left_most_Lm tr j k\<close>
    \<open>j < k\<close>
    \<open>\<not>tr: j \<lesssim> k\<close>
  shows "j < i"
proof -
  have j_Rm: "mover_type tr j j k \<noteq> Lm" using mover_type_left_end[OF assms(3,4)] by simp
  have i_Lm: "mover_type tr i j k = Lm" using assms left_most_Lm_is_Lm by blast
  then have "j \<le> left_most_Lm tr j k" using assms(2) mover_type_in[of tr i j k] by simp
  then show ?thesis using assms(2) j_Rm i_Lm
    by (metis le_neq_implies_less)
qed

lemma left_most_Lm_prefix_Rms:
  assumes
    \<open>left_movers tr j k \<noteq> {}\<close>
    \<open>i = left_most_Lm tr j k\<close>
    \<open>i' < i\<close>
    \<open>j \<le> i'\<close>
  shows "mover_type tr i' j k = Rm"
  using assms mover_type_in[of tr i' j k]
    left_most_Lm_in_range[OF assms(1,2)]
  by (auto simp add: left_movers_def)

lemma Rms_prefix_left_most_Lm:
  assumes
    \<open>left_movers tr j k \<noteq> {}\<close>
    \<open>mover_type tr i j k = Lm\<close>
    \<open>\<forall>i' < i. j \<le> i' \<longrightarrow> mover_type tr i' j k = Rm\<close>
  shows "i = left_most_Lm tr j k"
  using assms mover_type_in[of tr i j k] left_movers_finite[of tr j k]
  apply (auto simp add: left_movers_def)
  by (metis assms(1) left_most_Lm_in_range(1) left_most_Lm_is_Lm
      left_most_Lm_prefix_Rms left_movers_def movt.distinct(1) nat_neq_iff)


\<comment> \<open>causal_dependency lemmas\<close>
lemma inverted_pair_not_causal_dep:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>(j, k) \<in> inverted_pairs ev_ects \<tau>\<close>
  shows \<open>\<not> \<tau>: j \<lesssim> k\<close>
  using assms
  by (auto simp add: inverted_pairs_def dest!: ev_ects_Some WCommit_cts_causal_dep_gt_past)

lemma Rm_Lm_not_causal_dep:
  assumes
    \<open>mover_type \<tau> i j k = Rm\<close>
    \<open>mover_type \<tau> i' j k = Lm\<close>
  shows "\<not> \<tau>: i \<lesssim> i'"
  using assms
  apply (auto simp add: mover_type_def)
  by (metis movt.distinct(1) movt.distinct(3) movt.distinct(5) trancl_trans)

lemma i_Suci_not_causal_dep:
  assumes 
    \<open>left_movers tr j k \<noteq> {}\<close>
    \<open>Suc i = left_most_Lm tr j k\<close>
    \<open>j < k\<close>
    \<open>\<not> tr: j \<lesssim> k\<close>
  shows "\<not> tr: i \<lesssim> Suc i"
  using left_most_Lm_prefix_Rms[OF assms(1,2)]
    left_most_Lm_is_Lm[OF assms(1,2)]
    left_most_Lm_gt_j[OF assms]
    Rm_Lm_not_causal_dep[of tr i j k "Suc i"]
  by auto


subsection \<open>Cardinality of inverted Pairs\<close>

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

lemma is_arg_min_unique:
  "is_arg_min f P x \<Longrightarrow> \<forall>x'. x' \<noteq> x \<longrightarrow> \<not>is_arg_min f P x' \<Longrightarrow> arg_min f P = x"
  by (metis arg_min_def someI)

lemma arg_min_unique:
  fixes f :: "'a \<Rightarrow> 'b::order"
  assumes
    "P x"
    "\<And>x'. x' \<noteq> x \<Longrightarrow> P x' \<Longrightarrow> f x < f x'"
  shows "arg_min f P = x"
  using assms
  apply (intro is_arg_min_unique, auto simp add: is_arg_min_def)
  by fastforce

lemma no_adj_on_left_is_lmp:
  assumes
    \<open>adj_inv_pair f \<tau> j k\<close>
    \<open>\<forall>j' k'. k' \<le> j \<longrightarrow> \<not> adj_inv_pair f \<tau> j' k'\<close>
  shows "left_most_adj_pair f \<tau> = (j, k)"
  unfolding left_most_adj_pair_def
proof (intro arg_min_unique)
  show "case (j, k) of (i, j) \<Rightarrow> adj_inv_pair f \<tau> i j" using assms(1) by auto
next
  fix p
  assume a: "p \<noteq> (j, k)" "(case p of (i, j) \<Rightarrow> adj_inv_pair f \<tau> i j)"
  show "fst (j, k) < fst p"
  proof (rule ccontr)
    assume b: "\<not> fst (j, k) < fst p"
    then show "False"
    proof (cases p)
      case (Pair j' k')
      then have a: "(j', k') \<noteq> (j, k)" "adj_inv_pair f \<tau> j' k'" using a by auto
      then show ?thesis using Pair b assms
        by (metis adj_inv_pairs_non_overlapping adj_inv_pairs_non_overlapping'
            fstI linorder_neqE_nat)
    qed
  qed
qed

lemma lmp_no_adj_on_left:
  assumes
    \<open>left_most_adj_pair f \<tau> = (j, k)\<close>
    \<open>k' \<le> j\<close>
  shows "\<not> adj_inv_pair f \<tau> j' k'"
  using assms(1)
proof (rule contrapos_pn)
  assume "adj_inv_pair f \<tau> j' k'"
  then show "left_most_adj_pair f \<tau> \<noteq> (j, k)" using assms(2)
    apply (auto simp add: left_most_adj_pair_def)
    by (metis adj_inv_pair_i_lt_j arg_min_nat_lemma case_prodI fst_conv
        linorder_not_less order_less_le_trans)
qed


subsection \<open>Cardinality of Lms: Case j = i, Suc i < k\<close>

lemma lmp_swap_on_left:
  assumes
    \<open>left_most_adj_pair f (l @ e2 # e1 # l') = (j, k)\<close>
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>length l = j\<close>
    \<open>Suc j < k\<close>
  shows "left_most_adj_pair f (l @ e1 # e2 # l') = (Suc j, k)"
  using assms
proof -
  have adj: "adj_inv_pair f (l @ e1 # e2 # l') (Suc j) k" using assms(2-)
    apply (auto simp add: adj_inv_eq_all_none)
    apply (meson assms(2) gt_i)
    by (metis Suc_lessD nth_larger_Suc_length)
  have e1_None: "f e1 = None" using assms(2-)
    by (auto simp add: adj_inv_eq_all_none)
  have "\<And>j' k'. k' \<le> Suc j \<Longrightarrow> \<not> adj_inv_pair f (l @ e1 # e2 # l') j' k'"
  proof -
    fix j' k'
    assume "k' \<le> Suc j"
    show "\<not> adj_inv_pair f (l @ e1 # e2 # l') j' k'"
    proof (cases "k' = Suc j")
      case True
      show ?thesis using assms(1)
      proof (rule contrapos_pn)
        assume a: "adj_inv_pair f (l @ e1 # e2 # l') j' k'"
        then have "j' < length l"
          using \<open>k' = Suc j\<close> e1_None assms(3)
          apply (auto simp add: adj_inv_eq_all_none inverted_pairs_def)
          by (metis less_antisym nth_append_length option.discI)
        then have "adj_inv_pair f (l @ e2 # e1 # l') j' j"
          using \<open>k' = Suc j\<close> a e1_None assms(3)
          by (auto simp add: adj_inv_eq_all_none inverted_pairs_def nth_append)
        then show "left_most_adj_pair f (l @ e2 # e1 # l') \<noteq> (j, k)"
          using lmp_no_adj_on_left by blast
      qed
    next
      case False
      then have \<open>k' \<le> j\<close> using \<open>k' \<le> Suc j\<close> by auto
      then show ?thesis
      proof (cases "k' = j")
        case True
        then show ?thesis using e1_None assms(3)
          by (auto simp add: adj_inv_eq_all_none inverted_pairs_def)
      next
        case False
        then have \<open>k' < j\<close> using \<open>k' \<le> j\<close> by auto 
        then show ?thesis
          using lmp_no_adj_on_left[OF assms(1)] assms(3)
          by (meson adj_inv_pair_append less_imp_le_nat)
      qed
    qed
  qed
  then show ?thesis by (simp add: adj no_adj_on_left_is_lmp)
qed


lemma swap_reduces_card_left_movers:
  assumes
    \<open>left_most_adj_pair f (l @ e2 # e1 # l') = (j, k)\<close>
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>length l = j\<close>
    \<open>Suc j < k\<close>
    \<open>\<not> (l @ e2 # e1 # l'): j \<lesssim> k\<close>
    \<open>mover_type (l @ e2 # e1 # l') (Suc j) j k = Lm\<close>
  shows "card (left_movers (l @ e2 # e1 # l') j k) =
         Suc (card (left_movers (l @ e1 # e2 # l') (Suc j) k))"
  using assms
proof -
  have j_Rm: "mover_type (l @ e2 # e1 # l') j j k = Rm"
    using assms(4,5) mover_type_left_end[of j k]
    by auto
  then have j_Rm': "mover_type (l @ e1 # e2 # l') (Suc j) (Suc j) k = Rm"
    using assms(3,4)
    apply (auto simp add: mover_type_def split: if_split_asm)
    using causal_dep_swap_Suc_len_right[of "Suc j" k l e1 e2 l']
    by auto
  have
    "left_movers (l @ e2 # e1 # l') j k =
     left_movers (l @ e2 # e1 # l') (Suc j) k"
    using j_Rm left_movers_split_first[of _ j k] by auto
  moreover have
    "left_movers (l @ e2 # e1 # l') (Suc j) k =
     {Suc j} \<union> left_movers (l @ e2 # e1 # l') (Suc (Suc j)) k"
    using assms(6) left_movers_split_first[of _ "Suc j" k]
    by (auto simp add: mover_type_def)
  moreover have
    "left_movers (l @ e2 # e1 # l') (Suc (Suc j)) k =
     left_movers (l @ e1 # e2 # l') (Suc (Suc j)) k"
    using assms(3,4)
      left_movers_trimprefix[of "l @ [e2, e1]"]
      left_movers_trimprefix[of "l @ [e1, e2]"]
    by auto
  moreover have
    "left_movers (l @ e1 # e2 # l') (Suc (Suc j)) k =
     left_movers (l @ e1 # e2 # l') (Suc j) k"
    using j_Rm' left_movers_split_first[of _ "Suc j" k]
    by (auto simp add: mover_type_def)
  moreover have "Suc j \<notin> left_movers (l @ e1 # e2 # l') (Suc j) k"
    using j_Rm' by (auto simp add: left_movers_def)
  ultimately show ?thesis by (auto simp add: left_movers_finite)
qed


subsection \<open>Cardinality of Lms: Case j < i, Suc i \<le> k\<close>

lemma lmp_swap_on_right:
  assumes
    \<open>left_most_adj_pair f (l @ e2 # e1 # l') = (j, k)\<close>
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>length l = i\<close>
    \<open>j < i\<close>
    \<open>Suc i \<le> k\<close>
  shows "left_most_adj_pair f (l @ e1 # e2 # l') = (j, swap_i_Suci i k)"
  using assms
proof -
  have adj: "adj_inv_pair f (l @ e1 # e2 # l') j (swap_i_Suci i k)" using assms(2-)
    apply (auto simp add: adj_inv_eq_all_none swap_i_Suci_def nth_append)
    apply (metis assms(2) lt_Suci)
    apply (metis assms(2) le_neq_implies_less other)
    by (smt (verit) linorder_neqE_nat not_less_eq nth_append nth_append_Suc_length
        nth_append_length nth_larger_Suc_length order.strict_trans)
  have e2_None: "f e2 = None" using assms(2-)
    by (auto simp add: adj_inv_eq_all_none)
  have "\<And>j' k'. k' \<le> j \<Longrightarrow> \<not> adj_inv_pair f (l @ e1 # e2 # l') j' k'"
    using lmp_no_adj_on_left[OF assms(1)] assms(3,4)
    by (simp add: adj_inv_pair_append)
  then show ?thesis by (simp add: adj no_adj_on_left_is_lmp)
qed


lemma swap_preserves_card_left_movers:
  assumes
    \<open>left_most_adj_pair f (l @ e2 # e1 # l') = (j, k)\<close>
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>length l = i\<close>
    \<open>j < i\<close>
    \<open>Suc i \<le> k\<close>
    \<open>\<not> (l @ e2 # e1 # l'): j \<lesssim> k\<close>
    \<open>mover_type (l @ e2 # e1 # l') i j k = Rm\<close>
    \<open>mover_type (l @ e2 # e1 # l') (Suc i) j k = Lm\<close>
  shows "card (left_movers (l @ e2 # e1 # l') j k) =
         card (left_movers (l @ e1 # e2 # l') j (swap_i_Suci i k))"
  using assms
proof -
  have k_Lm: "mover_type (l @ e2 # e1 # l') k j k = Lm"
    using assms(4,5) mover_type_right_end[of j k]
    by auto
  then show ?thesis
  proof (cases "Suc i = k")
    case True
    then have k_Lm': "mover_type (l @ e1 # e2 # l') i j i = Lm"
    using assms(4) by (auto simp add: mover_type_def)
  have
    "left_movers_interval (l @ e2 # e1 # l') j k j k =
     {Suc i} \<union> left_movers_interval (l @ e2 # e1 # l') j k j i"
    using \<open>Suc i = k\<close> k_Lm assms(4)
    by auto
  moreover have
    "left_movers_interval (l @ e2 # e1 # l') j k j i =
     left_movers_interval (l @ e2 # e1 # l') j k j (i - 1)"
    using assms(4,7)
    by (metis Suc_le_D diff_Suc_1 le_neq_implies_less less_eq_Suc_le
        less_or_eq_imp_le movt.distinct(1) not_less_eq_eq)
  moreover have
    "left_movers_interval (l @ e2 # e1 # l') j k j (i - 1) =
     left_movers_interval (l @ e1 # e2 # l') j i j (i - 1)"
    using \<open>Suc i = k\<close> assms(3,4,7) mover_type_swap_k_pres_Lms
    by fastforce
  moreover have
    "left_movers_interval (l @ e1 # e2 # l') j i j i =
     {i} \<union> left_movers_interval (l @ e1 # e2 # l') j i j (i - 1)"
    using assms(4) k_Lm'
    by auto
  moreover have "i \<notin> left_movers_interval (l @ e1 # e2 # l') j i j (i - 1)"
    using assms(4) by auto
  moreover have "Suc i \<notin> left_movers_interval (l @ e2 # e1 # l') j k j i"
    by auto
  ultimately show ?thesis using \<open>Suc i = k\<close> by (auto simp add: swap_i_Suci_def left_movers_def)
  next
    case False
    then have \<open>Suc i < k\<close> using \<open>Suc i \<le> k\<close> by auto
    have i_not: "i \<notin> left_movers (l @ e2 # e1 # l') j k"
      using assms(7) by (auto simp add: left_movers_def)
    have Suci_not: "Suc i \<notin> left_movers (l @ e1 # e2 # l') j k"
      using \<open>Suc i < k\<close> assms(3,4,7)
      apply (auto simp add: left_movers_def mover_type_def)
      by (metis Suc_leI causal_dep_swap_Suc_len_right diff_Suc_1 movt.distinct(1))
    then have 
      "left_movers (l @ e2 # e1 # l') j k \<union> {i} =
       left_movers (l @ e1 # e2 # l') j k \<union> {Suc i}"
      apply (simp add: left_movers_def)
      using left_movers_split
       sorry
    then have "card (left_movers (l @ e2 # e1 # l') j k \<union> {i}) =
       card (left_movers (l @ e1 # e2 # l') j k \<union> {Suc i})" by simp
    then show ?thesis using \<open>Suc i < k\<close> i_not Suci_not
      by (auto simp add: swap_i_Suci_def left_movers_finite)
  qed
qed


subsection \<open>Decreasing distance of left_most_Lm\<close>

lemma swap_reduces_left_most_Lm:
  assumes
    \<open>left_most_adj_pair f (l @ e1 # e2 # l') = (j, swap_i_Suci i k)\<close>
    \<open>length l = i\<close>
    \<open>j < i\<close>
    \<open>Suc i \<le> k\<close>
    \<open>\<not> (l @ e2 # e1 # l'): j \<lesssim> k\<close>
    \<open>mover_type (l @ e2 # e1 # l') i j k = Rm\<close>
    \<open>mover_type (l @ e2 # e1 # l') (Suc i) j k = Lm\<close>
    \<open>left_movers (l @ e2 # e1 # l') j k \<noteq> {}\<close>
    \<open>Suc i = left_most_Lm (l @ e2 # e1 # l') j k\<close>
  shows "i = left_most_Lm (l @ e1 # e2 # l') j (swap_i_Suci i k)"
  using assms
proof -
  have "\<forall>i' < i. j \<le> i' \<longrightarrow> mover_type (l @ e2 # e1 # l') i' j k = Rm"
    using assms(8, 9) left_most_Lm_prefix_Rms less_Suc_eq by metis
  then show ?thesis
  proof (cases "Suc i = k")
    case True
    then show ?thesis sorry
  next
    case False
    then have \<open>Suc i < k\<close> using \<open>Suc i \<le> k\<close> by auto
    then have "mover_type (l @ e1 # e2 # l') i j k = Lm"
      using assms (2,3,6,7) mover_type_swap_within by blast
    then have "\<forall>i' < i. j \<le> i' \<longrightarrow> mover_type (l @ e1 # e2 # l') i' j k = Rm"
      using mover_type_swap_k_pres_Rms
      apply auto using mover_type_trim_R mover_type_append_R sorry
    then show ?thesis
      using \<open>j < i\<close> \<open>Suc i < k\<close> assms
        left_movers_swap_split[of i j k "l @ e1 # e2 # l'"]
      unfolding left_movers_def swap_i_Suci_def
    apply (simp add: left_movers_def swap_i_Suci_def) sorry
  qed
qed

subsection \<open>Lemma: The measure decreases\<close>

lemma swap_decreases_measure: 
  assumes
    \<open>tps: ef_first ef \<midarrow>\<langle>trace_of_efrag ef\<rangle>\<rightarrow> ef_last ef\<close>
    \<open>reach tps (ef_first ef)\<close>
    \<open>ef = Exec_frag s0 (efl @ (s, e2, m) # (m, e1, s') # efl') sf\<close>
    \<open>ef' = Exec_frag s0 (efl @ (s, e1, w) # (w, e2, s') # efl') sf\<close>
    \<open>length efl = i\<close>
    \<open>j \<le> i\<close> \<open>Suc i \<le> k\<close>
    \<open>k < length (ef_list ef)\<close>
    \<open>left_most_adj_pair ev_ects (trace_of_efrag ef) = (j, k)\<close>
    \<open>\<exists>j k. adj_inv_pair ev_ects (trace_of_efrag ef) j k\<close>
    \<open>left_movers (trace_of_efrag ef) j k \<noteq> {}\<close>
    \<open>Suc i = left_most_Lm (trace_of_efrag ef) j k\<close>
  shows \<open>(ef', ef) \<in> measure_R\<close>
  using assms
proof -
  have jltk: "j < k" using assms(6,7) by simp
  have adj: "adj_inv_pair ev_ects (trace_of_efrag ef) j k"
    using lmp_is_adj[OF assms(9,10)] by simp
  then have j_k_not_dep: "\<not> (trace_of_efrag ef): j \<lesssim> k"
    using inverted_pair_not_causal_dep[OF assms(1,2)]
    by (metis adj_inv_pair_def)
  then have i_Suci_not_dep: "\<not> (trace_of_efrag ef): i \<lesssim> Suc i"
    using i_Suci_not_causal_dep[OF assms(11,12)] jltk by simp
  have i_Rm: "mover_type (trace_of_efrag ef) i j k = Rm"
    using assms(6, 11-) left_movers_finite left_most_Lm_prefix_Rms j_k_not_dep jltk
    by blast
  have Suci_Lm: "mover_type (trace_of_efrag ef) (Suc i) j k = Lm"
    using assms(11-) left_most_Lm_is_Lm by metis
  then show ?thesis using assms
  proof (cases "j = i")
    case True
    then show ?thesis 
    proof (cases "Suc i = k")
      case True
      then have 
        "card (inverted_pairs ev_ects (trace_of_efrag ef')) <
         card (inverted_pairs ev_ects (trace_of_efrag ef))"
        using \<open>j = i\<close> assms(3-5) adj
        by (auto simp add: trace_of_efrag_append_cons2 dest: swap_reduces_card_inverted_pairs)
      then show ?thesis
        by (simp add: measure_R_def)
    next
      case False
      then have \<open>Suc i < k\<close> using \<open>Suc i \<le> k\<close> by simp
      then have inv_pair_card:
        "card (inverted_pairs ev_ects (trace_of_efrag ef')) =
         card (inverted_pairs ev_ects (trace_of_efrag ef))"
        using \<open>j = i\<close> assms(3-8) adj
        by (auto simp add: trace_of_efrag_append_cons2 dest: swap_preserves_card_inverted_pairs)
      then have
        "card (lmp_left_movers (trace_of_efrag ef')) <
         card (lmp_left_movers (trace_of_efrag ef))"
        unfolding lmp_left_movers_def
        using \<open>j = i\<close> \<open>Suc i < k\<close> assms(3-5,9) adj j_k_not_dep Suci_Lm
          lmp_swap_on_left[of ev_ects _ e2]
        by (auto simp add: trace_of_efrag_append_cons2 dest: swap_reduces_card_left_movers)
      then show ?thesis using inv_pair_card
        by (simp add: measure_R_def)
    qed
  next
    case False
      then have \<open>j < i\<close> using \<open>j \<le> i\<close> by simp
      then have inv_pair_card:
        "card (inverted_pairs ev_ects (trace_of_efrag ef')) =
         card (inverted_pairs ev_ects (trace_of_efrag ef))"
        using \<open>j \<noteq> i\<close> assms(3-8) adj
        by (auto simp add: trace_of_efrag_append_cons2 dest: swap_preserves_card_inverted_pairs)
      then have lmp':
        "left_most_adj_pair ev_ects (trace_of_efrag ef') = (j, swap_i_Suci i k)"
        using \<open>j < i\<close> assms(3-5,7,9) adj
        by (auto simp add: trace_of_efrag_append_cons2 dest: lmp_swap_on_right)
      then have Lms_card:
        "card (lmp_left_movers (trace_of_efrag ef')) =
         card (lmp_left_movers (trace_of_efrag ef))"
        unfolding lmp_left_movers_def
        using \<open>j < i\<close> assms(3-5,7,9) adj j_k_not_dep i_Rm Suci_Lm
        by (auto simp add: trace_of_efrag_append_cons2 dest: swap_preserves_card_left_movers)
      then have "i = left_most_Lm (trace_of_efrag ef') j (swap_i_Suci i k)"
        using \<open>j < i\<close> assms(3-5,7,9,11-) lmp' j_k_not_dep i_Rm Suci_Lm
          by (auto simp add: trace_of_efrag_append_cons2 dest: swap_reduces_left_most_Lm)
      then have 
        "lmp_Lm_dist_left (trace_of_efrag ef') <
         lmp_Lm_dist_left (trace_of_efrag ef)"
        using \<open>j < i\<close> assms(9,12) lmp'
        by (auto simp add: lmp_Lm_dist_left_def)
    then show ?thesis using inv_pair_card Lms_card
      by (simp add: measure_R_def)
  qed
qed

end