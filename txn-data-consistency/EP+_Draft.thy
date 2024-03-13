theory "EP+_Draft"
  imports "EP+_Refinement_Proof"
begin


inductive ver_step :: "'v ver_state \<Rightarrow> 'v ver_state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>v" 60) where
  "ver_step v v" |
  "ver_step No_Ver (Prep pdts pts v)" |
  "ver_step (Prep pdts pts v) (Commit cts sts lst v rs_emp)" |
  "rs' = rs (t \<mapsto> (x, y)) \<Longrightarrow> ver_step (Commit cts sts lst v rs) (Commit cts sts lst v rs')"

lemma ver_step_inv:
  assumes "state_trans s e s'"
  shows "\<forall>t. svr_state (svrs s k) t \<rightarrow>\<^sub>v svr_state (svrs s' k) t"
  using assms
proof (induction e)
  case (RegR x1 x2 x3 x4 x5 x6 x7)
  then show ?case by (auto simp add: tps_trans_defs add_to_readerset_def
   intro: ver_step.intros split: ver_state.split)
next
  case (CommitW x1 x2 x3 x4 x5 x6 x7)
  then show ?case by (auto simp add: tps_trans_defs intro: ver_step.intros)
qed (auto simp add: tps_trans_defs intro: ver_step.intros)

end