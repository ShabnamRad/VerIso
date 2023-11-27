section \<open>Reductions for EP+\<close>

theory "EP+_Reduction"
  imports "EP+" Reductions
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
  by (auto simp add: mover_type_def)

lemma mover_type_right_end:
  "j < k \<Longrightarrow> ev_cl (tr ! j) \<noteq> ev_cl (tr ! k) \<Longrightarrow> mover_type tr k j k = Lm"
  by (auto simp add: mover_type_def)

lemma ev_ects_Some:
  "ev_ects e = Some (cts, Suc_cl)
  \<Longrightarrow> \<exists>cl kv_map sn u''. e = WCommit cl kv_map cts sn u'' \<and> Suc_cl = Suc cl"
  by (induction e, auto simp add: ects_def)

lemma inverted_pair_not_same_cl:
  assumes \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
          \<open>init tps s\<close>
          \<open>(j, k) \<in> inverted_pairs ev_ects \<tau>\<close>
        shows "ev_cl (\<tau> ! j) \<noteq> ev_cl (\<tau> ! k)"
  using assms
  apply (auto simp add: inverted_pairs_def ects_def dest!: ev_ects_Some)
  apply (induction rule: ev_ects.induct)
  oops

lemma valid_exec_reachable_states:
  "valid_exec_frag E ef \<Longrightarrow> i < length (ef_list ef) \<Longrightarrow> reach E (states_of_efrag ef ! i)"
  apply (simp add: reach_last_exec)
  apply (intro exI[where x="ef_first ef"])
  apply (intro exI[where x="take i (ef_list ef)"]) oops

lemma swap_decreases_measure: 
  assumes
    "(j, k) = left_most_adj_pair ev_ects (trace_of_efrag ef)"
    "adj_inv_pair ev_ects (trace_of_efrag ef) j k"
    "j \<le> i \<and> Suc i \<le> k"
    "k < length (ef_list ef)"
    "mover_type (trace_of_efrag ef) i j k = Rm"
    "mover_type (trace_of_efrag ef) (Suc i) j k = Lm"
    "ef = Exec_frag s0 (take i (ef_list ef) @ (s, e2, m) # (m, e1, s') # efl') sf"
  shows "(Exec_frag s0 (take i (ef_list ef) @ (s, e1, w) # (w, e2, s') # efl') sf,
          Exec_frag s0 (take i (ef_list ef) @ (s, e2, m) # (m, e1, s') # efl') sf) \<in> measure_R"
  using assms
  apply (auto simp add: measure_R_def)
  subgoal apply (auto simp add: inverted_pairs_def trace_of_efrag_def o_def)
    sorry
  sorry

lemma reducible_exec_frag:
  assumes
    \<open>valid_exec tps ef\<close>
    \<open>ef \<notin> Good_wrt ev_ects\<close>
  shows
    \<open>\<exists>ef'. tps: ef \<rhd> ef' \<and> (ef' \<in> Good_wrt ev_ects \<or> (ef', ef) \<in> measure_R)\<close>
proof - 
  have "\<exists>j k. adj_inv_pair ev_ects (trace_of_efrag ef) j k" using assms(2)
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
  then obtain i where
    i_: "j \<le> i \<and> Suc i \<le> k"
        "mover_type (trace_of_efrag ef) i j k = Rm"
        "mover_type (trace_of_efrag ef) (Suc i) j k = Lm" sorry (* needs showing j, k don't have the same cl *)
  then have lc: "left_commute tps (trace_of_efrag ef ! Suc i) (trace_of_efrag ef ! i)" sorry
  then have reach_si: "reach tps (states_of_efrag ef ! i)" sorry
  then obtain w where
    "tps: ef \<rhd> Exec_frag (ef_first ef)
     (take i (ef_list ef) @
       (states_of_efrag ef ! i, trace_of_efrag ef ! Suc i, w) #
       (w, trace_of_efrag ef ! i, states_of_efrag ef ! Suc (Suc i)) #
       drop (Suc (Suc i)) (ef_list ef))
     (ef_last ef)"
    using assms(1) i_(1) kLen valid_exec_decompose lc reach_si reduce_frag_left_commute
    unfolding valid_exec_def
    by (smt (verit) order.strict_trans1)
  then show ?thesis using assms * ** i_ kLen
      valid_exec_decompose[of tps ef i]
      swap_decreases_measure[of j k ef]
  by (auto simp add: Good_wrt_def valid_exec_def)
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