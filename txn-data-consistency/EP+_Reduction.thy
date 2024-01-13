section \<open>Reductions for EP+\<close>

theory "EP+_Reduction"
  imports "EP+" "EP+_Trace" Reductions
begin

datatype movt = Lm | Rm | Out

definition mover_type :: "'v ev list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> movt" where
  "mover_type tr i j k \<equiv> (if j \<le> i \<and> i \<le> k then
   (if EVI tr i \<le> EVI tr k then Lm else Rm)
    else Out)"

definition lmp_Lm_dist_left where
  "lmp_Lm_dist_left tr \<equiv> let (j, k) = left_most_adj_pair ev_ects tr in
    Sum {i - j | i. mover_type tr i j k = Lm}"

definition lmp_left_movers :: "'v ev list \<Rightarrow> nat set" where
  "lmp_left_movers tr \<equiv> let (j, k) = left_most_adj_pair ev_ects tr in
    {i. mover_type tr i j k = Lm}"

abbreviation left_most_Lm where
  "left_most_Lm tr i j k \<equiv> j \<le> i \<and> Suc i \<le> k
     \<and> (\<forall>i'. j \<le> i' \<and> i' \<le> i \<longrightarrow> mover_type tr i' j k = Rm)
     \<and> mover_type tr (Suc i) j k = Lm"

definition left_most_Lm_dist_left :: "'v ev list \<Rightarrow> nat" where
  "left_most_Lm_dist_left tr \<equiv> let (j, k) = left_most_adj_pair ev_ects tr in
    (THE i. left_most_Lm tr i j k) - j"

definition measure_R :: "('v ev, ('v, 'm) global_conf_scheme) exec_frag rel" where
  "measure_R \<equiv> measures [card o inverted_pairs ev_ects o trace_of_efrag, lmp_Lm_dist_left o trace_of_efrag]"

definition measure_R' :: "('v ev, ('v, 'm) global_conf_scheme) exec_frag rel" where
  "measure_R' \<equiv> measures [card o inverted_pairs ev_ects o trace_of_efrag,
                           card o lmp_left_movers o trace_of_efrag,
                           left_most_Lm_dist_left o trace_of_efrag]" \<comment> \<open>Is this better?\<close>

lemma wf_measure_R: "wf measure_R"
  by (auto simp add: measure_R_def)

lemma mover_type_left_end:
  "j < k \<Longrightarrow> \<not>EVI tr j < EVI tr k \<Longrightarrow> mover_type tr j j k = Rm"
  by (simp add: mover_type_def)

lemma mover_type_right_end:
  "j < k  \<Longrightarrow> mover_type tr k j k = Lm"
  by (simp add: mover_type_def)

lemma mover_type_in:
  "j \<le> i \<and> i \<le> k \<Longrightarrow> mover_type tr i j k \<in> {Lm, Rm}"
  by (auto simp add: mover_type_def Let_def)

lemma mover_type_out:
  "\<not>(j \<le> i \<and> i \<le> k) \<Longrightarrow> mover_type tr i j k = Out"
  by (auto simp add: mover_type_def)

lemma cts_lt:
  "cts' > cts \<Longrightarrow> (cts', Suc cl) > (cts, Suc cl)"
  by (simp add: less_prod_def)

lemma causal_dep0_implies_clk_order:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>EVI \<tau> j \<lesssim>\<^sup>0 EVI \<tau> k\<close>
    \<open>k < length \<tau>\<close>
  shows \<open>ev_clk (\<tau> ! j) < ev_clk (\<tau> ! k)\<close>
  using assms
  thm trace.induct
proof (induction \<tau> s' arbitrary: j k rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (cases "k = length \<tau>")
    case True
    then show ?thesis using trace_snoc
        causal_dep0_nth_append[of \<tau>]
        causal_dep0_ind_lt[of "EVI (\<tau> @ [e]) j" "EVI (\<tau> @ [e]) k"]
    proof (induction e)
      case (RInvoke x1 x2 x3 x4)
      then show ?case sorry
    next
      case (Read x1 x2 x3 x4 x5 x6 x7 x8)
      then show ?case sorry
    next
      case (RDone x1 x2 x3 x4 x5)
      then show ?case sorry
    next
      case (WInvoke x1 x2 x3 x4)
      then show ?case sorry
    next
      case (WCommit x1 x2 x3 x4 x5 x6)
      then show ?case sorry
    next
      case (WDone x1 x2 x3 x4)
      then show ?case sorry
    next
      case (RegR x1 x2 x3 x4 x5)
      then show ?case sorry
    next
      case (PrepW x1 x2 x3 x4)
      then show ?case sorry
    next
      case (CommitW x1 x2 x3 x4 x5)
      then show ?case sorry
    qed
  next
    case False
    then show ?thesis using trace_snoc
        causal_dep0_nth_append[of \<tau>]
        causal_dep0_ind_lt[of "EVI (\<tau> @ [e]) j" "EVI (\<tau> @ [e]) k"]
      by (simp add: nth_append)
    qed
qed simp


lemma causal_dep_implies_clk_order:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>EVI \<tau> j < EVI \<tau> k\<close>
    \<open>k < length \<tau>\<close>
  shows \<open>ev_clk (\<tau> ! j) < ev_clk (\<tau> ! k)\<close>
  using assms(3-)
  apply (simp add: less_ev_i_def)
  apply (induction "EVI \<tau> j" "EVI \<tau> k" arbitrary: k rule: trancl.induct)
  subgoal using assms(1,2) causal_dep0_implies_clk_order by blast
  subgoal for b k apply (cases b)
    using assms(1,2) causal_dep0_tr_eq[of b "EVI \<tau> k"]
      causal_dep0_ind_lt[of b "EVI \<tau> k"] apply auto
    by (smt (verit, best) add_diff_inverse_nat causal_dep0_implies_clk_order less_SucI
        not_less_eq trans_less_add1)
  done


lemma WCommit_clk_Suc_cts:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>i < length \<tau>\<close>
    \<open>\<tau> ! i = WCommit cl kv_map cts sn u'' clk\<close>
  shows \<open>clk = Suc cts\<close>
  using assms
proof (induction \<tau> s' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6)
    then show ?case
      apply (cases "i = length \<tau>", simp add: tps_trans_defs)
      by (simp add: length_append_singleton not_less_less_Suc_eq nth_append)
  qed (simp_all, (smt ev.distinct less_SucE nth_append nth_append_length)+)
qed simp

lemma WCommit_cts_causal_dep_gt_past:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>k < length \<tau>\<close>
    \<open>\<tau> ! j = WCommit cl kv_map cts sn u'' clk\<close>
    \<open>\<tau> ! k = WCommit cl' kv_map' cts' sn' u''' clk'\<close>
    \<open>EVI \<tau> j < EVI \<tau> k\<close>
  shows \<open>(cts, Suc cl) < (cts', Suc cl')\<close>
  using assms
proof (induction \<tau> s' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6)
    then show ?case apply (simp add: less_prod_def) using WCommit_clk_Suc_cts
    by (smt (verit) add_less_imp_less_left assms causal_dep_implies_clk_order causal_dep_ind_lt
        ev_clk.simps(5) ev_i.sel(2) less_ev_i_def less_trans_Suc nth_append plus_1_eq_Suc)
  qed (simp_all, (smt (verit) Suc_less_SucD causal_dep_ind_lt causal_dep_nth_append ev.distinct
          ev_i.sel(2) less_ev_i_def less_trans_Suc not_less_less_Suc_eq nth_append nth_append_length')+)
qed simp

lemma inverted_pair_not_causal_dep:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>(j, k) \<in> inverted_pairs ev_ects \<tau>\<close>
  shows \<open>\<not>EVI \<tau> j < EVI \<tau> k\<close>
  using assms
  by (auto simp add: inverted_pairs_def dest!: ev_ects_Some WCommit_cts_causal_dep_gt_past)

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

abbreviation swap_i_Suci where
  "swap_i_Suci a i \<equiv> if a = i then Suc i else (if a = Suc i then i else a)"

lemma swap_preserve_reduce_card:
  assumes
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>j \<le> i \<and> Suc i \<le> k\<close>
    \<open>k < length (l @ e2 # e1 # l')\<close>
    \<open>length l = i\<close>
  shows "if (i, Suc i) = (j, k)
    then card (inverted_pairs f (l @ e2 # e1 # l')) = Suc (card (inverted_pairs f (l @ e1 # e2 # l')))
    else card (inverted_pairs f (l @ e2 # e1 # l')) = card (inverted_pairs f (l @ e1 # e2 # l'))"
proof -
  have i_Suci1: "(i, Suc i) \<noteq> (j, k) \<Longrightarrow> (i, Suc i) \<notin> inverted_pairs f (l @ e2 # e1 # l')" using assms
    apply (simp add: adj_inv_eq_all_none)
    apply (simp add: inverted_pairs_def)
    by (metis Suc_le_lessD le_antisym linorder_le_less_linear option.distinct(1))
  have i_Suci2: "(i, Suc i) \<notin> inverted_pairs f (l @ e1 # e2 # l')" using assms
    apply (simp add: adj_inv_eq_all_none)
    apply (simp add: inverted_pairs_def)
    by (metis Suc_le_lessD leD le_imp_less_Suc le_neq_implies_less nth_append_Suc_length
        nth_append_length option.discI option.inject order_less_imp_le)
  have gt_i:
    "\<forall>a > Suc i. (i, a) \<in> inverted_pairs f (l @ e2 # e1 # l') \<longleftrightarrow>
                 (Suc i, a) \<in> inverted_pairs f (l @ e1 # e2 # l')" using assms
    apply (auto simp add: inverted_pairs_def)
    by (metis nth_larger_Suc_length)+
  have gt_Suci:
    "\<forall>a > Suc i. (Suc i, a) \<in> inverted_pairs f (l @ e2 # e1 # l') \<longleftrightarrow>
                 (i, a) \<in> inverted_pairs f (l @ e1 # e2 # l')" using assms
    apply (auto simp add: inverted_pairs_def)
    by (metis nth_larger_Suc_length)+
  have lt_i:
    "\<forall>a < i. (a, i) \<in> inverted_pairs f (l @ e2 # e1 # l') \<longleftrightarrow>
             (a, Suc i) \<in> inverted_pairs f (l @ e1 # e2 # l')" using assms
    apply (auto simp add: inverted_pairs_def)
    by (metis nth_append)+
  have lt_Suci:
    "\<forall>a < i. (a, Suc i) \<in> inverted_pairs f (l @ e2 # e1 # l') \<longleftrightarrow>
             (a, i) \<in> inverted_pairs f (l @ e1 # e2 # l')" using assms
    apply (auto simp add: inverted_pairs_def)
    by (metis nth_append)+
  have other:
    "\<forall>a b. (a < i \<or> a > Suc i) \<and> (b < i \<or> b > Suc i) \<longrightarrow>
      (a, b) \<in> inverted_pairs f (l @ e2 # e1 # l') \<longleftrightarrow>
      (a, b) \<in> inverted_pairs f (l @ e1 # e2 # l')" using assms
    apply (auto simp add: inverted_pairs_def)
    by (intro exI, auto simp add: nth_append)
  have inj: "inj_on (\<lambda>(a, b). (swap_i_Suci a i, swap_i_Suci b i)) (inverted_pairs f (l @ e1 # e2 # l'))"
    apply (auto simp add: inj_on_def)
    by metis+
  have "(i, Suc i) \<noteq> (j, k) \<Longrightarrow>
  (\<lambda>x. case x of (a, b) \<Rightarrow> (swap_i_Suci a i, swap_i_Suci b i)) ` inverted_pairs f (l @ e1 # e2 # l') =
         inverted_pairs f (l @ e2 # e1 # l')"
    apply (auto simp add: image_def; (auto dest: inverted_pairs_i_lt_j)?)
    apply (metis gt_i inverted_pairs_i_lt_j)
    apply (metis i_Suci2)
    apply (metis Suc_lessI gt_Suci inverted_pairs_i_lt_j)
    apply (metis inverted_pairs_i_lt_j le_less_Suc_eq linorder_le_less_linear lt_i)
    apply (metis inverted_pairs_i_lt_j lt_Suci)
    apply (metis Suc_lessI linorder_neqE_nat other)
    apply (metis gt_i inverted_pairs_i_lt_j)
    apply (metis i_Suci2)
    apply (metis Suc_lessI gt_Suci inverted_pairs_i_lt_j)
    apply (metis inverted_pairs_i_lt_j le_less_Suc_eq linorder_le_less_linear lt_i)
    apply (metis inverted_pairs_i_lt_j lt_Suci)
    apply (metis Suc_lessI nat_neq_iff other)
    subgoal for a b apply (cases "a = i")
      subgoal apply (cases "b = Suc i")
        apply (metis i_Suci1 old.prod.inject)
        by (smt (verit) Suc_lessI case_prod_conv gt_i inverted_pairs_i_lt_j leD le_refl)
      subgoal apply (cases "a = Suc i")
        apply (smt (verit) gt_Suci inverted_pairs_i_lt_j old.prod.case verit_comp_simplify1(1))
        apply (cases "b = i"; cases "b = Suc i")
        apply (metis n_not_Suc_n)
        apply (smt (verit) case_prod_conv inverted_pairs_i_lt_j less_le_not_le lt_i)
        apply (smt (verit) Suc_lessI case_prod_conv inverted_pairs_i_lt_j less_Suc_eq_le
            less_or_eq_imp_le lt_Suci nat.inject not_less_eq)
        by (smt (verit) Suc_lessI case_prod_conv linorder_neqE_nat other)
      done
    subgoal for a b apply (cases "a = i")
      subgoal apply (cases "b = Suc i")
        apply (metis i_Suci1 old.prod.inject)
        by (smt (verit) Suc_lessI case_prod_conv gt_i inverted_pairs_i_lt_j leD le_refl)
      subgoal apply (cases "a = Suc i")
        apply (smt (verit) gt_Suci inverted_pairs_i_lt_j old.prod.case verit_comp_simplify1(1))
        apply (cases "b = i"; cases "b = Suc i")
        apply (metis n_not_Suc_n)
        apply (smt (verit) case_prod_conv inverted_pairs_i_lt_j less_le_not_le lt_i)
        apply (smt (verit) Suc_lessI case_prod_conv inverted_pairs_i_lt_j less_Suc_eq_le
            less_or_eq_imp_le lt_Suci nat.inject not_less_eq)
        by (smt (verit) Suc_lessI case_prod_conv linorder_neqE_nat other)
      done
    done
  then have card_eq: "(i, Suc i) \<noteq> (j, k) \<Longrightarrow>
    card (inverted_pairs f (l @ e1 # e2 # l')) = card (inverted_pairs f (l @ e2 # e1 # l'))" using assms
    apply (intro bij_betw_same_card[of "\<lambda>(a, b). (swap_i_Suci a i, swap_i_Suci b i)"
        "inverted_pairs f (l @ e1 # e2 # l')" "inverted_pairs f (l @ e2 # e1 # l')"])
    apply (simp add: bij_betw_def)
    by (metis inj)
  have "j = i \<and> Suc i = k \<Longrightarrow> (j, k) \<notin> inverted_pairs f (l @ e1 # e2 # l')"
    using i_Suci2 by auto
  then have "j = i \<and> Suc i = k \<Longrightarrow>
    card (inverted_pairs f (l @ e2 # e1 # l')) = Suc (card (inverted_pairs f (l @ e1 # e2 # l')))" sorry
  then show ?thesis using card_eq
    by (metis old.prod.inject)
qed

lemma "(ARG_MIN f x. P x) = y \<Longrightarrow> {x. P x} \<noteq> {} \<Longrightarrow> finite {x. P x} \<Longrightarrow> f y = Min (f ` {x. P x})"
  apply (auto simp add: arg_min_def image_def is_arg_min_linorder) oops

lemma nth_append_le_len:
  "i \<le> length l \<Longrightarrow> (l @ e1 # e2 # l') ! i = (l @ [e1]) ! i"
  by (metis nth_append nth_append_length order_le_less)

lemma nth_append_gt_len:
  "i \<ge> Suc (length l) \<Longrightarrow> (l @ e1 # e2 # l') ! i = (e2 # l') ! (i - Suc (length l))"
  by (simp add: nth_append)

lemma swap_preserves_lmp:
  assumes
    \<open>(j, k) = left_most_adj_pair f (l @ e2 # e1 # l')\<close>
    \<open>adj_inv_pair f (l @ e2 # e1 # l') j k\<close>
    \<open>j \<le> i \<and> Suc i \<le> k\<close>
    \<open>k < length (l @ e2 # e1 # l')\<close>
    \<open>length l = i\<close>
    \<open>(i, Suc i) \<noteq> (j, k)\<close>
  shows "left_most_adj_pair f (l @ e1 # e2 # l') = (j, k)"
proof -
  have "adj_inv_pair f (l @ e1 # e2 # l') j k" using assms
    apply (auto simp add: inverted_pairs_def nth_append_le_len nth_append_gt_len)
    subgoal for c1 c2
      apply (rule exI[where x=c1])
      apply (rule exI[where x=c2]) sorry sorry
  then have e: "\<exists>j k. is_arg_min (fst) (\<lambda>(i, j). adj_inv_pair f (l @ e1 # e2 # l') i j) (j, k)"
    by (smt (verit, del_insts) arg_min_natI case_prodE case_prodI is_arg_min_arg_min_nat)
  then obtain j k where *: "(j, k) = left_most_adj_pair f (l @ e1 # e2 # l')"
    by (metis nat_gcd.cases)
  then show ?thesis using e oops

lemma swap_decreases_measure: 
  assumes
    \<open>(j, k) = left_most_adj_pair ev_ects (trace_of_efrag ef)\<close>
    \<open>adj_inv_pair ev_ects (trace_of_efrag ef) j k\<close>
    \<open>j \<le> i \<and> Suc i \<le> k\<close>
    \<open>k < length (ef_list ef)\<close>
    \<open>\<forall>i'. j \<le> i' \<and> i' \<le> i \<longrightarrow> mover_type (trace_of_efrag ef) i' j k = Rm\<close>
    \<open>mover_type (trace_of_efrag ef) (Suc i) j k = Lm\<close>
    \<open>length efl = i\<close>
    \<open>valid_exec_frag tps ef\<close>
    \<open>ef = Exec_frag s0 (efl @ (s, e2, m) # (m, e1, s') # efl') sf\<close>
  shows \<open>(Exec_frag s0 (efl @ (s, e1, w) # (w, e2, s') # efl') sf, ef) \<in> measure_R\<close>
  using assms
  apply (auto simp add: measure_R_def cons_form_to_index trace_of_decomposed_frag)
  apply (smt (verit) assms(4) exec_frag.sel(2) length_map lessI swap_preserve_reduce_card
      trace_of_decomposed_frag trace_of_efrag_length)
  apply (cases "(i, Suc i) = (j, k)")
  apply (smt (verit) assms(4) exec_frag.sel(2) length_map lessI swap_preserve_reduce_card
      trace_of_decomposed_frag trace_of_efrag_length)

  
  using trace_of_decomposed_frag [of s0 efl s e2 m e1 s' efl' sf]
  apply (auto simp add: lmp_Lm_dist_left_def trace_of_decomposed_frag split:)
  sorry

lemma reducible_exec_frag:
  assumes
    \<open>valid_exec_frag tps ef\<close>
    \<open>reach tps (ef_first ef)\<close>
    \<open>ef \<notin> Good_wrt ev_ects\<close>
  shows
    \<open>\<exists>ef'. tps: ef \<rhd> ef' \<and> (ef' \<in> Good_wrt ev_ects \<or> (ef', ef) \<in> measure_R)\<close>
proof - 
  have "\<exists>j k. adj_inv_pair ev_ects (trace_of_efrag ef) j k" using assms(3)
    by (simp add: adj_inv_exists_not_Good_ex)
  then have e: "\<exists>j k. is_arg_min (fst) (\<lambda>(i, j). adj_inv_pair ev_ects (trace_of_efrag ef) i j) (j, k)"
    by (smt (verit, del_insts) arg_min_natI case_prodE case_prodI is_arg_min_arg_min_nat)
  then obtain j k where *: "(j, k) = left_most_adj_pair ev_ects (trace_of_efrag ef)"
    by (metis nat_gcd.cases)
  then have **: "adj_inv_pair ev_ects (trace_of_efrag ef) j k"
    using e unfolding left_most_adj_pair_def
    by (smt (verit, best) arg_min_natI case_prodD is_arg_min_def)
  then have kLen: "k < length (ef_list ef)"
    by (cases ef, simp add: inverted_pairs_def trace_of_efrag_length)
  then have jltk: "j < k" using **
    by (auto simp add: inverted_pairs_i_lt_j)
  then have tps_trace: "tps: ef_first ef \<midarrow>\<langle>trace_of_efrag ef\<rangle>\<rightarrow> ef_last ef"
    by (metis assms(1) exec_frag.collapse valid_exec_frag_is_trace)
  then have exMin: "\<exists>i. j \<le> i \<and> mover_type (trace_of_efrag ef) (Suc i) j k = Lm"
    using jltk ** assms(2)
    by (metis le_add1 less_natE mover_type_right_end)
  then have finMin: "finite  {i. j \<le> i \<and> mover_type (trace_of_efrag ef) (Suc i) j k = Lm}"
    apply (auto simp add: mover_type_def)
    by (metis (lifting) finite_nat_set_iff_bounded linorder_not_less mem_Collect_eq not_less_eq_eq)
  then have "\<exists>i. left_most_Lm (trace_of_efrag ef) i j k"
    apply (intro exI[where x="Min {i. j \<le> i \<and> mover_type (trace_of_efrag ef) (Suc i) j k = Lm}"])
    using mover_type_left_end [of j k "trace_of_efrag ef"]
          mover_type_right_end [of j k "trace_of_efrag ef"]
          assms(2) jltk ** exMin
    apply auto
    subgoal by (smt (verit, del_insts) Min_le dual_order.trans mem_Collect_eq mover_type_out
          movt.distinct(3) not_less_eq_eq)
    subgoal for i i' apply (cases "mover_type (trace_of_efrag ef) i' j k"; simp)
       apply (metis (no_types, opaque_lifting) Nat.lessE Suc_n_not_le_n tps_trace
          inverted_pair_not_causal_dep le_neq_implies_less less_or_eq_imp_le movt.distinct(1))
      by (smt (verit) Suc_leD dual_order.trans mover_type_def movt.distinct(3) movt.distinct(5))
    subgoal using Min_in by blast
    done
  then obtain i where i_: "left_most_Lm (trace_of_efrag ef) i j k" by blast
  have lc: "left_commute tps (trace_of_efrag ef ! Suc i) (trace_of_efrag ef ! i)" sorry
  then have reach_si: "reach tps (states_of_efrag ef ! i)"
    by (meson Suc_le_lessD assms(1-2) i_(1) kLen order_less_trans valid_exec_reachable_states)
  then obtain w where
    "tps: ef \<rhd> Exec_frag (ef_first ef)
     (take i (ef_list ef) @
       (states_of_efrag ef ! i, trace_of_efrag ef ! Suc i, w) #
       (w, trace_of_efrag ef ! i, states_of_efrag ef ! Suc (Suc i)) #
       drop (Suc (Suc i)) (ef_list ef))
     (ef_last ef)"
    using assms(1) i_(1) kLen valid_exec_decompose lc reach_si reduce_frag_left_commute
    by (smt (verit) order.strict_trans1)
  then show ?thesis using assms * ** i_ kLen
      valid_exec_decompose[of tps ef i]
      swap_decreases_measure[of j k ef i "take i (ef_list ef)"]
  by (auto simp add: Good_wrt_def)
qed

lemma reducible_to_Good_wrt_f_exec_frag: 
  "reducible tps (Good_wrt ev_ects)"
  by (auto intro: reducible_to_Good_exec [OF _ reducible_exec_frag] wf_measure_R)

lemma "ef_last ` Good_execs tps ev_ects = {s. reach tps s}"
proof (rule equalityI)
  show "ef_last ` Good_execs tps ev_ects \<subseteq> {s. reach tps s}"
    by (auto, metis exec_frag.collapse reach_last_exec)
next
  show "{s. reach tps s} \<subseteq> ef_last ` Good_execs tps ev_ects"
    thm reach_reduced[of tps _ "Good_execs tps ev_ects"]
    by (auto intro!: reach_reduced_valid reducible_to_Good_wrt_f_exec_frag)
qed

end