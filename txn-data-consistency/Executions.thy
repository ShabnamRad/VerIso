(*
  Title:   Event system executions
  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
  Version: Isabelle/HOL 2022
  Date:    July 2023
  ID:      $Id$
*)
section \<open>Event System Executions\<close>

text \<open>This theory defines a new type for event system executions and relates executions to event
system reachability and traces.\<close>
                                                                            
theory Executions
  imports Event_Systems 
begin


subsection \<open>Execution fragments and executions\<close>

datatype ('e, 's) exec_frag = 
  Exec_frag (ef_first: 's) (ef_list: "('s \<times> 'e \<times> 's) list") (ef_last: 's)

print_theorems

definition trace_of_efrag :: "('e, 's) exec_frag \<Rightarrow> 'e list" where
  "trace_of_efrag = map (fst o snd) o ef_list" 

definition states_of_efrag :: "('e, 's) exec_frag \<Rightarrow> 's list" where
  "states_of_efrag ef = map fst (ef_list ef) @ [ef_last ef]"

lemma "length (states_of_efrag ef) = Suc (length (trace_of_efrag ef))"
  by (simp add: trace_of_efrag_def states_of_efrag_def)

(* needed? *)
abbreviation cut_efrag :: "('e, 's) exec_frag \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('e, 's) exec_frag" where
  "cut_efrag ef i j \<equiv> Exec_frag (states_of_efrag ef ! i) (take (Suc (j - i)) (drop i (ef_list ef))) (states_of_efrag ef ! Suc j)"

(*
fun ef_tail :: "('e, 's) exec_frag \<Rightarrow> ('e, 's) exec_frag" where       (* not needed? *)
  "ef_tail (Exec_frag _ ((_, _, s) # efl) s') = Exec_frag s efl s'"
*)

inductive valid_exec_frag :: "('e, 's) ES \<Rightarrow> ('e, 's) exec_frag \<Rightarrow> bool" for E where
  vef_empty [simp, intro!]: "valid_exec_frag E (Exec_frag s0 [] s0)" |
  vef_snoc [intro]: 
    "\<lbrakk> valid_exec_frag E (Exec_frag s0 efl s); E: s\<midarrow>e\<rightarrow> s' \<rbrakk> 
   \<Longrightarrow> valid_exec_frag E (Exec_frag s0 (efl @ [(s, e, s')]) s')"

inductive_cases vef_empty_invert [elim!]: "valid_exec_frag E (Exec_frag s [] s')"
inductive_cases vef_single_trans_invert [elim!]: "valid_exec_frag E (Exec_frag s [tr] s')"
inductive_cases vef_snoc_invert: "valid_exec_frag E (Exec_frag s (efl @ [tr]) s')"

definition valid_exec :: "('e, 's) ES \<Rightarrow> ('e, 's) exec_frag \<Rightarrow> bool" where
  "valid_exec E ef \<longleftrightarrow> valid_exec_frag E ef \<and> init E (ef_first ef)"


lemma valid_exec_frag_single [intro]: 
  assumes \<open>E: s \<midarrow>e\<rightarrow> s'\<close>
  shows \<open>valid_exec_frag E (Exec_frag s [(s, e, s')] s')\<close>
  using assms
proof -
  have "valid_exec_frag E (Exec_frag s ([] @ [(s, e, s')]) s')" using assms
    by (intro vef_snoc) auto
  then show ?thesis by simp
qed

lemma valid_exec_frag_single_eq [simp]:
  \<open>valid_exec_frag E (Exec_frag s [(s, e, s')] s') \<longleftrightarrow> E: s \<midarrow>e\<rightarrow> s'\<close> (is "?A \<longleftrightarrow> ?B")
  by (auto)

lemma valid_exec_frag_cons [intro]: 
  assumes \<open>valid_exec_frag E (Exec_frag s efl s')\<close> \<open>E: s0 \<midarrow>e\<rightarrow> s\<close>
  shows \<open>valid_exec_frag E (Exec_frag s0 ((s0, e, s) # efl) s')\<close>
  using assms 
  by (induction "Exec_frag s efl s'" arbitrary: efl s' rule: valid_exec_frag.induct)
     (auto simp flip: append.simps(2))


lemma valid_exec_frag_first_last: 
  assumes \<open>valid_exec_frag E (Exec_frag s efl s')\<close>
  shows \<open>efl = [] \<and> s = s' \<or> efl \<noteq> [] \<and> s = fst (hd efl) \<and> s' = snd (snd (last efl))\<close>
  using assms
  by (induction "Exec_frag s efl s'" arbitrary: efl s' rule: valid_exec_frag.induct) (auto)

lemma valid_exec_frag_cons_align_first [dest]: 
  assumes \<open>valid_exec_frag E (Exec_frag s ((s1, e, s2) # efl) s')\<close> 
  shows \<open>valid_exec_frag E (Exec_frag s ((s, e, s2) # efl) s') \<and> s1 = s\<close>
proof - 
  from assms have \<open>s1 = s\<close> by (auto dest: valid_exec_frag_first_last)
  then show ?thesis using assms by auto
qed


text \<open>Lemmas about appending and splitting execution fragments\<close>

lemma valid_exec_frag_append: 
  assumes 
    \<open>valid_exec_frag E (Exec_frag s0 efl1 s1)\<close> 
    \<open>valid_exec_frag E (Exec_frag s1 efl2 s2)\<close> 
  shows
    \<open>valid_exec_frag E (Exec_frag s0 (efl1 @ efl2) s2)\<close>
  using assms(2)
proof (induction "(Exec_frag s1 efl2 s2)" arbitrary: efl2 s2 rule: valid_exec_frag.induct)
  case vef_empty
  then show ?case using assms(1) by simp 
next
  case (vef_snoc efl s e s')
  then show ?case by (auto simp flip: append_assoc)
qed

lemma valid_exec_frag_split: 
  assumes 
    \<open>valid_exec_frag E (Exec_frag s0 (efl1 @ efl2) s2)\<close>
  shows
    \<open>\<exists>s1. valid_exec_frag E (Exec_frag s0 efl1 s1) \<and> valid_exec_frag E (Exec_frag s1 efl2 s2)\<close>
  using assms
proof (induction efl2 arbitrary: s2 rule: List.rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc a efl2)
  then show ?case 
    by (auto simp flip: append_assoc elim!: vef_snoc_invert)
qed

lemma valid_exec_frag_append_eq: 
  \<open>valid_exec_frag E (Exec_frag s0 (efl1 @ efl2) s2) \<longleftrightarrow> 
   (\<exists>s1. valid_exec_frag E (Exec_frag s0 efl1 s1) \<and> 
         valid_exec_frag E (Exec_frag s1 efl2 s2))\<close> 
  by (auto simp add: valid_exec_frag_append valid_exec_frag_split)  


text \<open>Some useful special cases.\<close>

lemma valid_exec_frag_append_cons_eq: 
  \<open>valid_exec_frag E (Exec_frag s0 (efl1 @ (s, e, s') # efl2) s2) \<longleftrightarrow> 
   (valid_exec_frag E (Exec_frag s0 efl1 s) \<and> 
    valid_exec_frag E (Exec_frag s ((s, e, s') # efl2) s2))\<close> 
  by (auto simp add: valid_exec_frag_append_eq)

lemma valid_exec_frag_cons_eq:
  \<open>valid_exec_frag E (Exec_frag s ((s, e, s') # efl) sf) \<longleftrightarrow> 
   E: s \<midarrow>e\<rightarrow> s' \<and> valid_exec_frag E (Exec_frag s' efl sf)\<close> (is "?A \<longleftrightarrow> ?B \<and> ?C")
proof (intro iffI; (elim conjE)?)
  assume \<open>?A\<close> 
  then have \<open>valid_exec_frag E (Exec_frag s ([(s, e, s')] @ efl) sf)\<close> by simp
  then show \<open>?B \<and> ?C\<close> 
    by (auto simp add: valid_exec_frag_append_eq simp del: append.simps)
qed auto


subsection \<open>Relating executions to reachability and traces\<close>

lemma reach_last_exec: "reach E s \<longleftrightarrow> (\<exists>s0 efl. valid_exec E (Exec_frag s0 efl s))"
  unfolding valid_exec_def
proof (intro iffI; clarsimp simp only: exec_frag.sel)
  assume \<open>reach E s\<close>
  then show \<open>\<exists>s0 efl. valid_exec_frag E (Exec_frag s0 efl s) \<and> init E s0\<close>
    by (induction rule: reach.induct) (auto)
next
  fix s0 efl
  assume \<open>valid_exec_frag E (Exec_frag s0 efl s)\<close> \<open>init E s0\<close>
  then show \<open>reach E s\<close>
    by (induction "(Exec_frag s0 efl s)" arbitrary: efl s rule: valid_exec_frag.induct) (auto)
qed

lemma trace_is_trace_of_exec_frag: 
  "(E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s') \<longleftrightarrow> 
   (\<exists>efl. valid_exec_frag E (Exec_frag s efl s') \<and> trace_of_efrag (Exec_frag s efl s') = \<tau>)"
proof (intro iffI; (elim exE conjE)?)
  assume \<open>E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
  then show \<open>\<exists>efl. valid_exec_frag E (Exec_frag s efl s') \<and> trace_of_efrag (Exec_frag s efl s') = \<tau>\<close>
  by (induction rule: trace.induct) (auto simp add: trace_of_efrag_def)
next
  fix efl
  assume \<open>valid_exec_frag E (Exec_frag s efl s')\<close> \<open>trace_of_efrag (Exec_frag s efl s') = \<tau>\<close> 
  then show \<open>E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    by (induction "Exec_frag s efl s'" arbitrary: \<tau> efl s' rule: valid_exec_frag.induct) 
       (auto simp add: trace_of_efrag_def)
qed

lemma traces_is_trace_of_exec:
  "\<tau> \<in> traces E \<longleftrightarrow> 
   (\<exists>s efl s'. valid_exec E (Exec_frag s efl s') \<and> trace_of_efrag (Exec_frag s efl s') = \<tau>)"
  by (auto simp add: traces_def valid_exec_def trace_is_trace_of_exec_frag)


subsection \<open>Equivalent execution fragments\<close>

definition efrag_last_equiv :: "('e, 's) exec_frag \<Rightarrow> ('e, 's) exec_frag \<Rightarrow> bool" (infix \<open>\<simeq>\<close> 65) where
  "efrag_last_equiv ef1 ef2 \<longleftrightarrow> ef_last ef1 = ef_last ef2"

lemmas efrag_last_equivI [intro] = efrag_last_equiv_def[THEN iffD2]
lemmas efrag_last_equivE [elim] = efrag_last_equiv_def[THEN iffD1, elim_format]

lemma efrag_last_equiv_refl: \<open>ef \<simeq> ef\<close>
  by (simp add: efrag_last_equiv_def)

lemma efrag_last_equiv_sym: \<open>ef1 \<simeq> ef2 \<Longrightarrow> ef2 \<simeq> ef1\<close>
  by (simp add: efrag_last_equiv_def)

lemma efrag_last_equiv_trans: \<open>\<lbrakk> ef1 \<simeq> ef2; ef2 \<simeq> ef3 \<rbrakk> \<Longrightarrow> ef1 \<simeq> ef3\<close>
  by (simp  add: efrag_last_equiv_def)


end 
