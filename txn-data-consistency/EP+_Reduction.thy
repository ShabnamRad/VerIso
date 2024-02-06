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
    by (cases ef, simp add: adj_inv_pair_def inverted_pairs_def trace_of_efrag_length)
  then have jltk: "j < k" using **
    by (auto simp add: adj_inv_pair_def inverted_pairs_i_lt_j)
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
       apply (metis (no_types, opaque_lifting) Nat.lessE Suc_n_not_le_n tps_trace adj_inv_pair_def
          inverted_pair_not_causal_dep le_neq_implies_less less_or_eq_imp_le movt.distinct(1))
      by (smt (verit) Suc_leD dual_order.trans mover_type_def movt.distinct(3) movt.distinct(5))
    subgoal using Min_in by blast
    done
  then obtain i where i_: "left_most_Lm (trace_of_efrag ef) i j k" by blast
  then have "\<not>EVI (trace_of_efrag ef) i < EVI (trace_of_efrag ef) (Suc i)"
    "tps: ef_first ef \<midarrow>\<langle>trace_of_efrag ef\<rangle>\<rightarrow> ef_last ef"
    "reach tps (ef_first ef)"
    "Suc i < length (trace_of_efrag ef)"
    using Rm_Lm_not_causal_dep apply blast
    apply (simp add: tps_trace)
     apply (simp add: assms(2))
    by (metis kLen i_ exec_frag.exhaust exec_frag.sel(2) order.strict_trans1 trace_of_efrag_length)
  then have lc: "left_commute tps (trace_of_efrag ef ! Suc i) (trace_of_efrag ef ! i)"
    using indep_evs_commute by blast
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
      swap_decreases_measure[of ef j k i "take i (ef_list ef)"]
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