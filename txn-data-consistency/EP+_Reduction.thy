section \<open>Reductions for EP+\<close>

theory "EP+_Reduction"
  imports "EP+" Reductions
begin

datatype movt = Lm | Rm

definition mover_type :: "'v ev list \<Rightarrow> nat \<Rightarrow> movt" where
  "mover_type tr i \<equiv> (let e = tr ! i in
    (if ev_cl e = ev_cl (hd tr) then Rm else
     (if ev_cl e = ev_cl (last tr) then Lm else
      (if (\<exists>j l. l < j \<and> j \<le> i \<and>
            ev_cl (tr ! j) = ev_cl (tr ! i) \<and>
            ev_cl (tr ! l) = ev_cl (hd tr) \<and>
            ev_key (tr ! l) = ev_key (tr ! j) \<and> ev_key (tr ! j) \<noteq> None) then Rm else Lm)))
  )"

definition Lm_dist_left where
  "Lm_dist_left i j tr \<equiv>
    Sum {d | d. mover_type (take (Suc (j - i)) (drop i tr)) d = Lm}"

definition left_most_pair :: "'v ev list \<Rightarrow> (nat \<times> nat)" where
  "left_most_pair tr \<equiv> (ARG_MIN (fst) (i, j). (i, j) \<in> inverted_pairs ev_ects tr \<and>
    (\<forall>l. i < l \<and> l < j \<longrightarrow>
      (i, l) \<notin> inverted_pairs ev_ects tr \<and>
      (l, j) \<notin> inverted_pairs ev_ects tr))"

definition lmp_dist_left :: "('v ev, ('v, 'm) global_conf_scheme) exec_frag \<Rightarrow> nat" where
  "lmp_dist_left ef \<equiv>
    let (i, j) = left_most_pair (trace_of_efrag ef) in
      Lm_dist_left i j (trace_of_efrag ef)"

definition measure_R :: "('v ev, ('v, 'm) global_conf_scheme) exec_frag rel" where
  "measure_R \<equiv> measures [card o inverted_pairs ev_ects o trace_of_efrag, lmp_dist_left]"

lemma wf_measure_R: "wf measure_R"
  by (auto simp add: measure_R_def)

lemma reducible_exec_frag:
  assumes
    \<open>valid_exec_frag tps ef\<close>
    \<open>ef \<notin> Good_wrt ev_ects\<close>
  shows
    \<open>\<exists>ef'. tps: ef \<rhd> ef' \<and> (ef' \<in> Good_wrt ev_ects \<or> (ef', ef) \<in> measure_R)\<close>
  using assms reduce_frag_left_commute
  apply (auto simp add: Good_wrt_def)
  sorry

lemma reducible_to_Good_wrt_f_exec_frag: 
  "reducible tps (Good_wrt ev_ects)"
  by (auto intro: reducible_to_Good_exec_frag [OF _ reducible_exec_frag] wf_measure_R)

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