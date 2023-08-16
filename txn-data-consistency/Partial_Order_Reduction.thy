section \<open>Partial order reduction\<close>

theory Partial_Order_Reduction
  imports "EP+_TCCv" Reductions
begin

\<comment> \<open>read_invoke (all except write_done independent)\<close>
lemma read_invoke_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (RInvoke cl' keys')"
  apply (auto simp add: left_commute_def tps_trans_defs del: equalityI)
  apply (rule relcompI, auto)
  by (simp add: fun_upd_twist)

lemma read_invoke_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (Read cl' k' v' t')"
  apply (auto simp add: left_commute_def tps_trans_defs del: equalityI)
  apply (rule relcompI, auto)
  by (simp add: fun_upd_twist)

lemma read_invoke_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_defs get_ctx_defs del: equalityI)
  apply (rule relcompI, auto)
  by (simp add: fun_upd_twist)

lemma read_invoke_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (WInvoke cl' kv_map')"
  apply (auto simp add: left_commute_def tps_trans_defs del: equalityI)
  apply (rule relcompI, auto)
  by (simp add: fun_upd_twist)

lemma read_invoke_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_defs del: equalityI)
  apply (rule relcompI, auto)
  apply (simp add: fun_upd_twist)
  by (metis domI option.inject)

lemma read_invoke_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (RInvoke cl keys) (RegR k' t' i' rts')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma read_invoke_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (RInvoke cl keys) (PrepW k' t' v')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma read_invoke_commit_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (RInvoke cl keys) (CommitW k' t' v' cts')"
  apply (auto simp add: left_commute_def tps_trans_defs del: equalityI; (rule relcompI)?, auto) sorry


\<comment> \<open>read (all client events independent)\<close>
lemma read_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t) (Read cl' k' v' t')"
  apply (auto simp add: left_commute_def tps_trans_defs del: equalityI)
  apply (rule relcompI, auto)
  by (simp add: fun_upd_twist)

lemma read_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t) (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_defs get_ctx_defs del: equalityI)
  apply (rule relcompI, auto)
  by (simp add: fun_upd_twist)

lemma read_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t) (WInvoke cl' kv_map')"
  apply (auto simp add: left_commute_def tps_trans_defs del: equalityI)
  apply (rule relcompI, auto)
  by (simp add: fun_upd_twist)

lemma read_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t) (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_defs del: equalityI)
  apply (rule relcompI, auto)
  apply (simp add: fun_upd_twist)
  by (metis domI option.inject)

lemma read_write_done_indep:
  assumes "cl \<noteq> cl'"
  shows "left_commute tps (Read cl k v t) (WDone cl' kv_map')"
  using assms
  apply (auto simp add: left_commute_def tps_trans_defs)
  apply (rule relcompI, auto)
  subgoal for s _ _ keys _ kv_map
    proof -
      have "let s' = s\<lparr>cls := (cls s)
              (cl := cls s cl
                 \<lparr>cl_state := RtxnInProg keys (kv_map(k \<mapsto> v)),
                    cl_clock := Suc (max (cl_clock (cls s cl)) (svr_clock (svrs s k))),
                    lst_map := (lst_map (cls s cl))(k := lst (svrs s k))\<rparr>)\<rparr>
            in (\<lambda>ka. if kv_map' ka = None then lst_map (cls s' cl') ka
                                else lst (svrs s' ka)) = 
            (\<lambda>k. if kv_map' k = None then lst_map (cls s cl') k else lst (svrs s k))"
        using assms by (auto simp add: Let_def)
      then show ?thesis using assms by (auto simp add: Let_def fun_upd_twist)
    qed
    done

lemma read_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (Read cl k v t_wr) (RegR k' t' t_wr' rts')" oops

lemma read_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> t \<noteq> t' \<Longrightarrow> left_commute tps (Read cl k v t) (PrepW k' t' v')" oops

lemma read_commit_write_indep:
  "cl \<noteq> get_cl_w t \<Longrightarrow> left_commute tps (Read cl k v t) (CommitW k' t' v' cts')" oops


\<comment> \<open>read_done\<close>

lemma read_done_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_defs get_ctx_defs del: equalityI)
  apply (rule relcompI, auto)
  by (simp add: fun_upd_twist)

lemma read_done_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (WInvoke cl' kv_map')"
  apply (auto simp add: left_commute_def tps_trans_defs get_ctx_defs del: equalityI)
  apply (rule relcompI, auto)
  by (simp add: fun_upd_twist)

lemma read_done_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_defs get_ctx_defs ext_corder_def del: equalityI)
  apply (rule relcompI, auto) oops

lemma read_done_write_done_indep:
  assumes "cl \<noteq> cl'"
  shows "left_commute tps (RDone cl kv_map sn u'') (WDone cl' kv_map')"
  apply (auto simp add: left_commute_def tps_trans_defs get_ctx_defs del: equalityI)
  apply (rule relcompI, auto) oops

lemma read_done_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (RegR k' t' t_wr' rts')" oops

lemma read_done_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (PrepW k' t' v')" oops

lemma read_done_commit_write_indep:
  "cl \<noteq> get_cl_w t \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (CommitW k' t' v' cts')" oops


\<comment> \<open>write_invoke\<close>

lemma write_invoke_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (WInvoke cl' kv_map')"
  apply (auto simp add: left_commute_def tps_trans_defs del: equalityI)
  apply (rule relcompI, auto)
  by (simp add: fun_upd_twist)

lemma write_invoke_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_defs del: equalityI)
  apply (rule relcompI, auto)
  apply (simp add: fun_upd_twist)
  by (metis domI option.inject)

lemma write_invoke_write_done_indep:
  assumes "cl \<noteq> cl'"
  shows "left_commute tps (WInvoke cl kv_map) (WDone cl' kv_map')"
  apply (auto simp add: left_commute_def tps_trans_defs del: equalityI)
  apply (rule relcompI, auto)
  using assms apply fastforce oops

lemma write_invoke_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (RegR k' t' t_wr' rts')" oops

lemma write_invoke_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (PrepW k' t' v')" oops

lemma write_invoke_commit_write_indep:
  "cl \<noteq> get_cl_w t \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (CommitW k' t' v' cts')" oops


\<comment> \<open>write_commit\<close>

lemma write_commit_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_defs del: equalityI)
  apply (rule relcompI, auto) oops

lemma write_commit_write_done_indep:
  assumes "cl \<noteq> cl'"
  shows "left_commute tps (WCommit cl kv_map cts sn u'') (WDone cl' kv_map')"
  apply (auto simp add: left_commute_def tps_trans_defs get_ctx_defs del: equalityI)
  apply (rule relcompI, auto) oops

lemma write_commit_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (RegR k' t' t_wr' rts')" oops

lemma write_commit_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (PrepW k' t' v')" oops

lemma write_commit_commit_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (CommitW k' t' v' cts')" oops


end