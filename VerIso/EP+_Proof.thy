section \<open>EP+: General Correctness Proof (Theorem 4 + lemmas 5 and 6 of the paper (Section 5.5))\<close>

theory "EP+_Proof"
  imports "EP+_Reduction" "EP+_Sorted_eq_E" "EP+_Refinement_Proof"
begin


subsection \<open>Correctness Proof\<close>

lemma lemma_5: "reach epp = reach epp_s"
proof
  fix s :: "'v global_conf"
  show "reach epp s = reach epp_s s"
  proof
    assume "reach epp s"
    then show "reach epp_s s"
      using
        reacheable_set_epp_s_good_eq
        reacheable_set_epp_good_eq
      by (metis mem_Collect_eq)
  next
    assume "reach epp_s s"
    then show "reach epp s"
      using reach_epp by simp
  qed
qed


lemmas lemma_6 = simulation_fun_reach_soundness[OF epp_refines_tccv]

\<comment> \<open>Theorem 4\<close>
theorem Correctness_of_EPP: "sim ` {s. reach epp s} \<subseteq> {s. reach ET_CC.ET_ES s}"
  by (simp add: lemma_5 lemma_6)

end

