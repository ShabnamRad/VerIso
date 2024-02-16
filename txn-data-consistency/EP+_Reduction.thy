section \<open>Reductions for EP+\<close>

theory "EP+_Reduction"
  imports "EP+_Measure" "EP+_Commutes"
begin

lemma reducible_exec_frag:
  assumes
    \<open>valid_exec_frag tps ef\<close>
    \<open>reach tps (ef_first ef)\<close>
    \<open>ef \<notin> Good_wrt ev_ects\<close>
  shows
    \<open>\<exists>ef'. tps: ef \<rhd> ef' \<and> (ef' \<in> Good_wrt ev_ects \<or> (ef', ef) \<in> measure_R)\<close>
proof - 
  have ex_adj: "\<exists>j k. adj_inv_pair ev_ects (trace_of_efrag ef) j k" using assms(3)
    by (auto simp add: Good_wrt_def dest: adj_inv_pair_within_inverted_pair)
  then obtain j k where lmp: "left_most_adj_pair ev_ects (trace_of_efrag ef) = (j, k)"
    by (metis nat_gcd.cases)
  then have adj: "adj_inv_pair ev_ects (trace_of_efrag ef) j k"
    using ex_adj lmp_is_adj by metis
  then have kLen: "k < length (ef_list ef)"
    by (cases ef, simp add: adj_inv_pair_def inverted_pairs_def)
  then have jltk: "j < k" using adj
    by (auto simp add: adj_inv_pair_def inverted_pairs_i_lt_j)
  then have tps_trace: "tps: ef_first ef \<midarrow>\<langle>trace_of_efrag ef\<rangle>\<rightarrow> ef_last ef"
    by (metis assms(1) exec_frag.collapse valid_exec_frag_is_trace)
  then have jk_not_dep: "\<not> (trace_of_efrag ef): j \<lesssim> k"
    using adj adj_inv_pair_def inverted_pair_not_causal_dep[OF _ assms(2)] by blast
  have LmsNEmp: "left_movers (trace_of_efrag ef) j k \<noteq> {}"
    using jltk mover_type_right_end nat_less_le
    by (auto simp add: left_movers_def)
  then obtain Suci where
    Suci_: "Suci = left_most_Lm (trace_of_efrag ef) j k" "j < Suci"
    using left_most_Lm_gt_j[OF LmsNEmp _ jltk jk_not_dep] by auto
  then obtain i where
    i_: "Suc i = left_most_Lm (trace_of_efrag ef) j k" and
    i_range: "j \<le> i" "Suc i \<le> k"
    by (metis LmsNEmp Nat.lessE left_most_Lm_in_range(2) less_or_eq_imp_le)
  then have
    indep: "\<not> (trace_of_efrag ef): i \<lesssim> Suc i" "Suc i < length (trace_of_efrag ef)"
    using i_Suci_not_causal_dep[OF LmsNEmp i_ jltk jk_not_dep]
      left_most_Lm_in_range(2)[OF LmsNEmp i_] apply auto
    by (metis kLen i_ exec_frag.exhaust exec_frag.sel(2) order.strict_trans1 trace_of_efrag_length)
  then have
    lc: "left_commute tps (trace_of_efrag ef ! Suc i) (trace_of_efrag ef ! i)"
    using indep_evs_commute tps_trace assms(2) by blast
  then have reach_si: "reach tps (states_of_efrag ef ! i)"
    by (metis (no_types, lifting) LmsNEmp Suc_lessD assms(1-2) i_ kLen
        left_most_Lm_in_range(2) order.strict_trans1 valid_exec_reachable_states)
  then obtain w where
    "tps: ef \<rhd> Exec_frag (ef_first ef)
     (take i (ef_list ef) @
       (states_of_efrag ef ! i, trace_of_efrag ef ! Suc i, w) #
       (w, trace_of_efrag ef ! i, states_of_efrag ef ! Suc (Suc i)) #
       drop (Suc (Suc i)) (ef_list ef))
     (ef_last ef)"
    using assms(1) i_(1) kLen valid_exec_decompose lc reach_si reduce_frag_left_commute
    by (smt (verit) LmsNEmp left_most_Lm_in_range(2) order.strict_trans1)
  then show ?thesis using assms lmp adj i_ kLen
      valid_exec_decompose[OF assms(1), of i]
      swap_decreases_measure[OF tps_trace assms(2) _ _ _ i_range kLen lmp ex_adj LmsNEmp i_]
  apply (auto simp add: Good_wrt_def)
    by (smt cons_form_to_index i_range(2) order.strict_trans1)
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