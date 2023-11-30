section \<open>Reductions for EP+\<close>

theory "EP+_Reduction"
  imports "EP+" "EP+_Trace" Reductions
begin

datatype movt = Lm | Rm | Out

definition mover_type :: "'v ev list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> movt" where
  "mover_type tr i j k \<equiv> (if j \<le> i \<and> i \<le> k then
   (let e = tr ! i in
    (if ev_cl e = ev_cl (tr ! j) then Rm else
     (if ev_cl e = ev_cl (tr ! k) then Lm else
      (if (\<exists>l m. l < m \<and> m \<le> i \<and>
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

lemma WCommit_cts_cl_lt_past:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>write_commit cl kv_map' cts' sn' u''' s' s''\<close>
    \<open>WCommit cl kv_map cts sn u'' \<in> set \<tau>\<close>
  shows \<open>(cts', Suc cl) > (cts, Suc cl)\<close>
  using assms
  apply (auto simp add: write_commit_def write_commit_G_def write_commit_U_def) sorry

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

lemma swap_decreases_measure: 
  assumes
    \<open>(j, k) = left_most_adj_pair ev_ects (trace_of_efrag ef)\<close>
    \<open>adj_inv_pair ev_ects (trace_of_efrag ef) j k\<close>
    \<open>j \<le> i \<and> Suc i \<le> k\<close>
    \<open>k < length (ef_list ef)\<close>
    \<open>\<forall>i' \<le> i. j \<le> i' \<longrightarrow> mover_type (trace_of_efrag ef) i' j k = Rm\<close>
    \<open>mover_type (trace_of_efrag ef) (Suc i) j k = Lm\<close>
    \<open>length efl = i\<close>
    \<open>ef = Exec_frag s0 (efl @ (s, e2, m) # (m, e1, s') # efl') sf\<close>
  shows \<open>(Exec_frag s0 (efl @ (s, e1, w) # (w, e2, s') # efl') sf, ef) \<in> measure_R\<close>
  using assms
  apply (auto simp add: measure_R_def)
  subgoal apply (auto simp add: inverted_pairs_def trace_of_efrag_def o_def)
    sorry
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
    by (simp add: inverted_pairs_def)
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