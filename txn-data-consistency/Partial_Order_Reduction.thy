section \<open>Partial order reduction\<close>

theory Partial_Order_Reduction
  imports "EP+_TCCv" Reductions
begin

\<comment> \<open>read_invoke\<close>
lemma read_invoke_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (RInvoke cl' keys')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma read_invoke_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (Read cl' k' v' t')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma read_invoke_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (RDone cl' kv_map' sn' u''')"
  by (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist)

lemma read_invoke_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (WInvoke cl' kv_map')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma read_invoke_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (WCommit cl' kv_map' cts' sn' u''')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma read_invoke_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (WDone cl' kv_map')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> cl'" "write_done cl' kv_map' s w" "read_invoke cl keys w s'"
    hence "(\<lambda>ka. if kv_map' ka = None then lst_map (cls (read_invoke_U cl keys s) cl') ka
                              else lst (svrs (read_invoke_U cl keys s) ka)) = 
           (\<lambda>k. if kv_map' k = None then lst_map (cls s cl') k else lst (svrs s k))" by auto
    then show ?thesis using a by (auto simp add: tps_trans_defs fun_upd_twist)
  qed
  done

lemma read_invoke_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (RInvoke cl keys) (RegR k' t' i' rts')"
  by (auto simp add: left_commute' tps_trans_defs)

lemma read_invoke_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (RInvoke cl keys) (PrepW k' t' v')"
  by (auto simp add: left_commute' tps_trans_defs)

lemma read_invoke_commit_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (RInvoke cl keys) (CommitW k' t' v' cts')"
  by (auto simp add: left_commute' tps_trans_defs)


\<comment> \<open>read\<close>

lemma read_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t) (RInvoke cl' keys')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma read_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t) (Read cl' k' v' t')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma read_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t) (RDone cl' kv_map' sn' u''')"
  by (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist)

lemma read_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t) (WInvoke cl' kv_map')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma read_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t) (WCommit cl' kv_map' cts' sn' u''')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma read_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t) (WDone cl' kv_map')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> cl'" "write_done cl' kv_map' s w" "read cl k v t w s'"
    hence "(\<lambda>ka. if kv_map' ka = None then lst_map (cls (read_U cl k v s) cl') ka
                              else lst (svrs (read_U cl k v s) ka)) = 
           (\<lambda>k. if kv_map' k = None then lst_map (cls s cl') k else lst (svrs s k))" by auto
    then show ?thesis using a by (auto simp add: tps_trans_defs fun_upd_twist)
  qed
  done

lemma read_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (Read cl k v t_wr) (RegR k' t' t_wr' rts')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops

lemma read_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> t \<noteq> t' \<Longrightarrow> left_commute tps (Read cl k v t) (PrepW k' t' v')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops

lemma read_commit_write_indep:
  "cl \<noteq> get_cl_w t \<Longrightarrow> left_commute tps (Read cl k v t) (CommitW k' t' v' cts')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops


\<comment> \<open>read_done\<close>

lemma read_done_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (RInvoke cl' keys')"
  by (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist)

lemma read_done_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (Read cl' k' v' t')"
  by (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist)

lemma read_done_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (RDone cl' kv_map' sn' u''')"
  by (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist)

lemma read_done_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (WInvoke cl' kv_map')"
  by (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist)

lemma read_done_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute' tps_trans_defs get_ctx_defs ext_corder_def fun_upd_twist) oops

lemma read_done_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (WDone cl' kv_map')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> cl'" "write_done cl' kv_map' s w" "read_done cl kv_map sn w s'"
    hence "(\<lambda>ka. if kv_map' ka = None then lst_map (cls (read_done_U cl kv_map s) cl') ka
                              else lst (svrs (read_done_U cl kv_map s) ka)) = 
           (\<lambda>k. if kv_map' k = None then lst_map (cls s cl') k else lst (svrs s k))" by auto
    then show ?thesis using a apply (auto simp add: tps_trans_defs fun_upd_twist) oops

lemma read_done_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (RegR k' t' t_wr' rts')"
  apply (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist) oops

lemma read_done_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (PrepW k' t' v')"
  apply (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist) oops

lemma read_done_commit_write_indep:
  "cl \<noteq> get_cl_w t \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (CommitW k' t' v' cts')"
  apply (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist) oops


\<comment> \<open>write_invoke\<close>

lemma write_invoke_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (RInvoke cl' keys')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma write_invoke_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (Read cl' k' v' t')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma write_invoke_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (RDone cl' kv_map' sn' u''')"
  by (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist)

lemma write_invoke_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (WInvoke cl' kv_map')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma write_invoke_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (WCommit cl' kv_map' cts' sn' u''')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma write_invoke_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (WDone cl' kv_map')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> cl'" "write_done cl' kv_map' s w" "write_invoke cl kv_map w s'"
    hence "(\<lambda>ka. if kv_map' ka = None then lst_map (cls (write_invoke_U cl kv_map s) cl') ka
                              else lst (svrs (write_invoke_U cl kv_map s) ka)) = 
           (\<lambda>k. if kv_map' k = None then lst_map (cls s cl') k else lst (svrs s k))" by auto
    then show ?thesis using a by (auto simp add: tps_trans_defs fun_upd_twist)
  qed
  done

lemma write_invoke_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (RegR k' t' t_wr' rts')"
  by (auto simp add: left_commute' tps_trans_defs)

lemma write_invoke_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (PrepW k' t' v')"
  by (auto simp add: left_commute' tps_trans_defs)

lemma write_invoke_commit_write_indep:
  "cl \<noteq> get_cl_w t \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (CommitW k' t' v' cts')"
  by (auto simp add: left_commute' tps_trans_defs)


\<comment> \<open>write_commit\<close>

lemma write_commit_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (RInvoke cl' keys')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma write_commit_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (Read cl' k' v' t')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma write_commit_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops

lemma write_commit_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (WInvoke cl' kv_map')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma write_commit_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (WCommit cl' kv_map' cts' sn' u''')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma write_commit_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (WDone cl' kv_map')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> cl'" "write_done cl' kv_map' s w" "write_commit cl kv_map cts sn w s'"
    hence "(\<lambda>ka. if kv_map' ka = None then lst_map (cls (write_commit_U cl kv_map cts s) cl') ka
                              else lst (svrs (write_commit_U cl kv_map cts s) ka)) = 
           (\<lambda>k. if kv_map' k = None then lst_map (cls s cl') k else lst (svrs s k))" by auto
    then show ?thesis using a by (auto simp add: tps_trans_defs fun_upd_twist)
  qed
  done

lemma write_commit_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (RegR k' t' t_wr' rts')" oops

lemma write_commit_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (PrepW k' t' v')" oops

lemma write_commit_commit_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (CommitW k' t' v' cts')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> get_cl_w t'" "commit_write k' t' v' cts' s w" "write_commit cl kv_map cts sn w s'"
    then show ?thesis using a (*apply (auto simp add: tps_trans_defs fun_upd_twist)*)
      oops


\<comment> \<open>write_done\<close>

lemma write_done_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map) (RInvoke cl' keys')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> cl'" "read_invoke cl' keys' s w" "write_done cl kv_map w s'"
    hence "(\<lambda>ka. if kv_map ka = None then lst_map (cls (read_invoke_U cl' keys' s) cl) ka
                              else lst (svrs (read_invoke_U cl' keys' s) ka)) = 
           (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k else lst (svrs s k))" by auto
    then show ?thesis using a by (auto simp add: tps_trans_defs fun_upd_twist)
  qed
  done

lemma write_done_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map) (Read cl' k' v' t')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> cl'" "read cl' k' v' t' s w" "write_done cl kv_map w s'"
    hence "(\<lambda>ka. if kv_map ka = None then lst_map (cls (read_U cl' k' v' s) cl) ka
                              else lst (svrs (read_U cl' k' v' s) ka)) = 
           (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k else lst (svrs s k))" by auto
    then show ?thesis using a by (auto simp add: tps_trans_defs fun_upd_twist)
  qed
  done

lemma write_done_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map) (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> cl'" "read_done cl' kv_map' sn' s w" "write_done cl kv_map w s'"
    hence "(\<lambda>ka. if kv_map ka = None then lst_map (cls (read_done_U cl' kv_map' s) cl) ka
                              else lst (svrs (read_done_U cl' kv_map' s) ka)) = 
           (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k else lst (svrs s k))" by auto
    then show ?thesis using a apply (auto simp add: tps_trans_defs get_ctx_defs fun_upd_twist) oops

lemma write_done_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map) (WInvoke cl' kv_map')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> cl'" "write_invoke cl' kv_map' s w" "write_done cl kv_map w s'"
    hence "(\<lambda>ka. if kv_map ka = None then lst_map (cls (write_invoke_U cl' kv_map' s) cl) ka
                              else lst (svrs (write_invoke_U cl' kv_map' s) ka)) = 
           (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k else lst (svrs s k))" by auto
    then show ?thesis using a by (auto simp add: tps_trans_defs fun_upd_twist)
  qed
  done

lemma write_done_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map) (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> cl'" "write_commit cl' kv_map' cts' sn' s w" "write_done cl kv_map w s'"
    hence "(\<lambda>ka. if kv_map ka = None then lst_map (cls (write_commit_U cl' kv_map' cts' s) cl) ka
                              else lst (svrs (write_commit_U cl' kv_map' cts' s) ka)) = 
           (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k else lst (svrs s k))" by auto
    then show ?thesis using a by (auto simp add: tps_trans_defs fun_upd_twist)
  qed
  done

lemma write_done_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map) (WDone cl' kv_map')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> cl'" "write_done cl' kv_map' s w" "write_done cl kv_map w s'"
    hence wd1: "(\<lambda>ka. if kv_map ka = None then lst_map (cls (write_done_U cl' kv_map' s) cl) ka
                              else lst (svrs (write_done_U cl' kv_map' s) ka)) = 
           (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k else lst (svrs s k))" by auto
    have "(\<lambda>ka. if kv_map' ka = None then lst_map (cls (write_done_U cl kv_map s) cl') ka
                              else lst (svrs (write_done_U cl kv_map s) ka)) = 
           (\<lambda>k. if kv_map' k = None then lst_map (cls s cl') k else lst (svrs s k))" using a by auto
    then show ?thesis using a wd1 by (auto simp add: tps_trans_defs fun_upd_twist)
  qed
  done

lemma write_done_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WDone cl kv_map) (RegR k' t' t_wr' rts')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> get_cl t'" "register_read k' t' t_wr' rts' s w" "write_done cl kv_map w s'"
    hence "(\<lambda>ka. if kv_map ka = None then lst_map (cls (register_read_U k' t' t_wr' s) cl) ka
                              else lst (svrs (register_read_U k' t' t_wr' s) ka)) = 
           (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k else lst (svrs s k))" by auto
    then show ?thesis using a (*apply (auto simp add: tps_trans_defs fun_upd_twist)*) oops

lemma write_done_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (WDone cl kv_map) (PrepW k' t' v')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> get_cl_w t'" "prepare_write k' t' v' s w" "write_done cl kv_map w s'"
    hence "(\<lambda>ka. if kv_map ka = None then lst_map (cls (prepare_write_U k' t' v' s) cl) ka
                              else lst (svrs (prepare_write_U k' t' v' s) ka)) = 
           (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k else lst (svrs s k))" by auto
    then show ?thesis using a (*apply (auto simp add: tps_trans_defs fun_upd_twist)*) oops

lemma write_done_commit_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> kv_map k' = None \<Longrightarrow> left_commute tps (WDone cl kv_map) (CommitW k' t' v' cts')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> get_cl_w t'" "commit_write k' t' v' cts' s w" "write_done cl kv_map w s'"
    and k'_notin_kv_map: "kv_map k' = None"
    have "(\<lambda>ka. if kv_map ka = None then lst_map (cls (commit_write_U k' t' v' cts' s) cl) ka
                              else lst (svrs (commit_write_U k' t' v' cts' s) ka)) = 
           (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k else lst (svrs s k))"
      apply (rule ext) using k'_notin_kv_map by auto
    then show ?thesis using a (*k'_notin_kv_map apply (auto simp add: tps_trans_defs)
         apply (smt (verit) domI domIff option.inject)
      subgoal sorry
      apply (smt (verit) domI domIff option.inject)*) oops


\<comment> \<open>register_read\<close>

lemma register_read_read_invoke_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (RInvoke cl' keys')"
  by (auto simp add: left_commute' tps_trans_defs)

lemma register_read_read_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (Read cl' k' v' t')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops

lemma register_read_read_done_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops

lemma register_read_write_invoke_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (WInvoke cl' kv_map')"
  by (auto simp add: left_commute' tps_trans_defs)

lemma register_read_write_commit_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops

lemma register_read_write_done_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (WDone cl' kv_map')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops

lemma register_read_register_read_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (RegR k' t' t_wr' rts')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma register_read_prepare_write_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (PrepW k' t' v')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma register_read_commit_write_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (CommitW k' t' v' cts')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)


\<comment> \<open>prepare_write\<close>

lemma prepare_write_read_invoke_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (RInvoke cl' keys')"
  by (auto simp add: left_commute' tps_trans_defs)

lemma prepare_write_read_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (Read cl' k' v' t')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops

lemma prepare_write_read_done_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops

lemma prepare_write_write_invoke_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (WInvoke cl' kv_map')"
  by (auto simp add: left_commute' tps_trans_defs)

lemma prepare_write_write_commit_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops

lemma prepare_write_write_done_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (WDone cl' kv_map')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops

lemma prepare_write_register_read_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (PrepW k t v) (RegR k' t' t_wr' rts')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma prepare_write_prepare_write_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (PrepW k t v) (PrepW k' t' v')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma prepare_write_commit_write_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (PrepW k t v) (CommitW k' t' v' cts')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

\<comment> \<open>commit_write\<close>

lemma commit_write_read_invoke_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (RInvoke cl' keys')"
  by (auto simp add: left_commute' tps_trans_defs)

lemma commit_write_read_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (Read cl' k' v' t')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops

lemma commit_write_read_done_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops

lemma commit_write_write_invoke_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (WInvoke cl' kv_map')"
  by (auto simp add: left_commute' tps_trans_defs)

lemma commit_write_write_commit_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops

lemma commit_write_write_done_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (WDone cl' kv_map')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops

lemma commit_write_register_read_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (CommitW k t v cts) (RegR k' t' t_wr' rts')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma commit_write_prepare_write_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (CommitW k t v cts) (PrepW k' t' v')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma commit_write_commit_write_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (CommitW k t v cts) (CommitW k' t' v' cts')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

end