section \<open>General Correctness Proof of Eiger-PORT+ (Theorem 4 + lemmas 5 and 6 of the paper (Section 5.5))\<close>

theory "EP+_Proof"
  imports "EP+_Reduction" "EP+_Sorted_eq_E" "EP+_Refinement_Proof"
begin


subsection \<open>Correctness Proof\<close>

lemma lemma_5: "reach tps = reach tps_s"
proof
  fix s :: "'v global_conf"
  show "reach tps s = reach tps_s s"
  proof
    assume "reach tps s"
    then show "reach tps_s s"
      using
        reacheable_set_tps_s_good_eq
        reacheable_set_tps_good_eq
      by (metis mem_Collect_eq)
  next
    assume "reach tps_s s"
    then show "reach tps s"
      using reach_tps by simp
  qed
qed


lemmas lemma_6 = simulation_fun_reach_soundness[OF tps_refines_et_es]

\<comment> \<open>Theorem 4\<close>
theorem Correctness_of_EPP: "sim ` {s. reach tps s} \<subseteq> {s. reach ET_CC.ET_ES s}"
  by (simp add: lemma_5 lemma_6)

end

