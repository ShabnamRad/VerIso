theory Run
  \<comment> \<open>Check the "Theories" panel to see the progress on loading theories\<close>
  imports
    Serializable_2PC_2PL_Proof \<comment> \<open>1.5 min\<close>
    "EP+_Proof" \<comment> \<open>12 min\<close>
    Tapir_Falsification \<comment> \<open>1.5 min\<close>
    Programming_Language \<comment> \<open>5 sec\<close>
begin


text \<open>Section 4.2.1 - Theorem 3\<close>

thm tpl_refines_sser


text \<open>Section 5.5.2\<close>

thm lemma_5
thm lemma_6

thm Correctness_of_EPP \<comment> \<open>Theorem 4\<close>


text \<open>Section 6.2\<close>

thm tapir_refines_sser \<comment> \<open>fails: checkout the states with "sorry"\<close>


text \<open>Programming Language\<close>

thm ExecutionTest.reach_prog_conf


end