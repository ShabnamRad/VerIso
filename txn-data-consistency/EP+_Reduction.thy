section \<open>Reductions for EP+\<close>

theory "EP+_Reduction"
  imports "EP+" "EP+_Trace" Reductions
begin

definition cl_ord :: "('e ev \<times> nat) rel" where
  "cl_ord \<equiv> {((e\<^sub>1, i), (e\<^sub>2, j)). ev_cl e\<^sub>1 = ev_cl e\<^sub>2 \<and> i < j}"

definition svr_ord :: "('e ev \<times> nat) rel" where
  "svr_ord \<equiv> {((e\<^sub>1, i), (e\<^sub>2, j)). ev_key e\<^sub>1 \<noteq> None \<and> ev_key e\<^sub>1 = ev_key e\<^sub>2 \<and> i < j}"

definition txn_ord :: "('e ev \<times> nat) rel" where
  "txn_ord \<equiv> {((e\<^sub>1, i), (e\<^sub>2, j)). ev_txn e\<^sub>1 = ev_txn e\<^sub>2 \<and> i < j}"

definition causal_dep0 :: "('e::type ev \<times> nat) rel" where
  "causal_dep0 \<equiv> (cl_ord \<union> svr_ord \<union> txn_ord)\<^sup>+"

datatype 'v ev_i = EVI (evi_ev: "'v ev") (evi_i: nat)

lemma ev_i_eq_iff: "evi\<^sub>1 = evi\<^sub>2 \<Longrightarrow> evi_ev evi\<^sub>1 = evi_ev evi\<^sub>2 \<and> evi_i evi\<^sub>1 = evi_i evi\<^sub>2"
  by metis

declare [[show_sorts]]
\<comment> \<open>For events causal dependencies: (ev, index in trace)\<close>
instantiation ev_i :: (type) order
begin

definition
  less_ev_i_def : "evi\<^sub>1 < evi\<^sub>2 = (((evi_ev evi\<^sub>1, evi_i evi\<^sub>1), (evi_ev evi\<^sub>2, evi_i evi\<^sub>2)) \<in> causal_dep0)" 

definition
  less_eq_ev_i_def : "evi\<^sub>1 \<le> evi\<^sub>2 = (((evi_ev evi\<^sub>1, evi_i evi\<^sub>1), (evi_ev evi\<^sub>2, evi_i evi\<^sub>2)) \<in> causal_dep0\<^sup>=)" 

instance proof
  fix x y z :: "'v::type ev_i"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    apply (auto simp add: less_ev_i_def less_eq_ev_i_def) sorry
  show "x \<le> x"
    (*apply (auto simp add: less_eq_ev_i_def)*) sorry
  show "\<lbrakk>x \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> x \<le> z"
    (*by (auto simp add: less_eq_ev_i_def)*) sorry
  show "\<lbrakk>x \<le> y; y \<le> x\<rbrakk> \<Longrightarrow> x = y"
    (*by (auto simp add: less_eq_ev_i_def ev_i_eq_iff)*) sorry
qed

end

datatype movt = Lm | Rm | Out

definition mover_type :: "'v ev list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> movt" where
  "mover_type tr i j k \<equiv> (if j \<le> i \<and> i \<le> k then
   (let e = tr ! i in
    (if ev_cl e = ev_cl (tr ! j) then Rm else
     (if ev_cl e = ev_cl (tr ! k) then Lm else
      (if (\<exists>l m. j < l \<and> l < m \<and> m \<le> i \<and>
            ev_cl (tr ! m) = ev_cl (tr ! i) \<and>
            ev_cl (tr ! l) = ev_cl (tr ! j) \<and>
            ev_key (tr ! l) = ev_key (tr ! m) \<and> ev_key (tr ! m) \<noteq> None) then Rm else Lm)))
    ) else Out)"

definition Lm_dist_left where
  "Lm_dist_left tr j k \<equiv>
    Sum {i - j | i. mover_type tr i j k = Lm}"

definition lmp_dist_left :: "('v ev, ('v, 'm) global_conf_scheme) exec_frag \<Rightarrow> nat" where
  "lmp_dist_left ef \<equiv>
    let (j, k) = left_most_adj_pair ev_ects (trace_of_efrag ef) in
      Lm_dist_left (trace_of_efrag ef) j k"

definition measure_R :: "('v ev, ('v, 'm) global_conf_scheme) exec_frag rel" where
  "measure_R \<equiv> measures [card o inverted_pairs ev_ects o trace_of_efrag, lmp_dist_left]"

lemma wf_measure_R: "wf measure_R"
  by (auto simp add: measure_R_def)

lemma mover_type_left_end:
  "j < k \<Longrightarrow> mover_type tr j j k = Rm"
  by (simp add: mover_type_def)

lemma mover_type_right_end:
  "j < k \<Longrightarrow> ev_cl (tr ! j) \<noteq> ev_cl (tr ! k) \<Longrightarrow> mover_type tr k j k = Lm"
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

lemma WCommit_cts_cl_lt_past:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>write_commit cl kv_map' cts' sn' u''' s' s''\<close>
    \<open>WCommit cl kv_map cts sn u'' \<in> set \<tau>\<close>
  shows \<open>(cts', Suc cl) > (cts, Suc cl)\<close>
  using assms WC_in_\<tau>_wtxn_cts Cl_Cts_lt_Wtxn_Cts_def
  apply (auto simp add: tps_trans_defs)
  using reach_trace_extend[of _ s \<tau> s'] cts_lt by blast

lemma cl_cts_monotonic_in_trace:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>j < k\<close> \<open>k < length \<tau>\<close>
    \<open>\<tau> ! j = WCommit cl kv_map cts sn u''\<close>
    \<open>\<tau> ! k = WCommit cl kv_map' cts' sn' u'''\<close>
  shows \<open>(cts', Suc cl) > (cts, Suc cl)\<close>
  using assms
proof (induction \<tau> s' arbitrary: j k cl cts kv_map sn u'' cts' kv_map' sn' u''' 
                      rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (cases "k = length \<tau>")
      subgoal apply auto
        by (metis WCommit_cts_cl_lt_past append_eq_conv_conj nth_mem nth_take)
      apply (auto simp add: "EP+.tps_trans_defs")
      by (smt Suc_less_SucD append_eq_conv_conj less_antisym less_trans_Suc nth_take)
  qed (auto simp add: "EP+.tps_trans_defs",
      (smt Suc_lessD append1_eq_conv ev.distinct less_SucE less_trans_Suc list_update_append1
        list_update_id list_update_same_conv nth_append_length)+)
qed simp

lemma inverted_pair_not_same_cl:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>(j, k) \<in> inverted_pairs ev_ects \<tau>\<close>
  shows \<open>ev_cl (\<tau> ! j) \<noteq> ev_cl (\<tau> ! k)\<close>
  using assms
  by (auto simp add: inverted_pairs_def dest!: ev_ects_Some cl_cts_monotonic_in_trace)

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
  apply (auto simp add: arg_min_def image_def is_arg_min_linorder)

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
  have "adj_inv_pair f (l @ e1 # e2 # l') j k" sorry
  then have e: "\<exists>j k. is_arg_min (fst) (\<lambda>(i, j). adj_inv_pair f (l @ e1 # e2 # l') i j) (j, k)"
    by (smt (verit, del_insts) arg_min_natI case_prodE case_prodI is_arg_min_arg_min_nat)
  then obtain j k where *: "(j, k) = left_most_adj_pair f (l @ e1 # e2 # l')"
    by (metis nat_gcd.cases)
  then show ?thesis using e

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
  apply (auto simp add: lmp_dist_left_def trace_of_efrag_def)
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
  then have "tps: ef_first ef \<midarrow>\<langle>trace_of_efrag ef\<rangle>\<rightarrow> ef_last ef"
    by (metis assms(1) exec_frag.collapse valid_exec_frag_is_trace)
  then have exMin: "\<exists>i. j \<le> i \<and> mover_type (trace_of_efrag ef) (Suc i) j k = Lm"
    using jltk ** assms(2)
    by (metis inverted_pair_not_same_cl le_add1 less_natE mover_type_right_end)
  then have finMin: "finite  {i. j \<le> i \<and> mover_type (trace_of_efrag ef) (Suc i) j k = Lm}"
    by (smt (z3) finite_nat_set_iff_bounded linorder_not_less mem_Collect_eq mover_type_out
        movt.distinct(3) not_less_eq_eq)
  then have "\<exists>i. j \<le> i \<and> Suc i \<le> k
     \<and> (\<forall>i'. j \<le> i' \<and> i' \<le> i \<longrightarrow> mover_type (trace_of_efrag ef) i' j k = Rm)
     \<and> mover_type (trace_of_efrag ef) (Suc i) j k = Lm"
    apply (intro exI[where x="Min {i. j \<le> i \<and> mover_type (trace_of_efrag ef) (Suc i) j k = Lm}"])
    using mover_type_left_end [of j k "trace_of_efrag ef"]
          assms(2) jltk ** exMin
    apply auto
    subgoal by (smt Min_le le_trans mem_Collect_eq mover_type_out movt.distinct(3) not_less_eq_eq)
    subgoal for i i' apply (cases "mover_type (trace_of_efrag ef) i' j k"; simp)
      apply(metis (no_types, lifting) inc_induct le_SucE le_antisym movt.distinct(1))
      by (smt (verit) Suc_leD linorder_not_le mover_type_def movt.distinct order.strict_trans1)
    subgoal using Min_in by blast
    done
  then obtain i where
    i_: "j \<le> i \<and> Suc i \<le> k"
        "\<forall>i' \<le> i. j \<le> i' \<longrightarrow> mover_type (trace_of_efrag ef) i' j k = Rm"
        "mover_type (trace_of_efrag ef) (Suc i) j k = Lm"
    by blast
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