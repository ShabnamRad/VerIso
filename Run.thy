theory Run
  \<comment> \<open>Check Isabelle's "Theories" panel to see the progress on loading theories\<close>
  imports
    "VerIso/refinement-example/Simple_DB"
    "VerIso/S2PL_Proof" \<comment> \<open>1.5 min\<close>
    "VerIso/Tapir_Falsification" \<comment> \<open>1.5 min\<close>
begin

text \<open>Please make sure "Proof state" is checked in Isabelle's "Output" tab.
  - To see the lemmas or theorems listed below, place the cursor on them .
  - To see the lemma statement in the original theory where it is proven, Ctrl + Click on its name. (Cmd + Click for mac users) \<close>


text \<open>Section 3.2\<close>

thm cdb_refines_adb \<comment> \<open>Example 3\<close>


text \<open>Section 5.2\<close>

thm tpl_refines_sser \<comment> \<open>Theorem 4\<close>


text \<open>Section 6.3\<close>

thm tapir_refines_sser
  \<comment> \<open>fails: checkout the proof state at line 486 (in Isabelle's "Output" tab)\<close>


end