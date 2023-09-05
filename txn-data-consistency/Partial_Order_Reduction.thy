section \<open>Partial order reduction\<close>

theory Partial_Order_Reduction
  imports "EP+_TCCv" Reductions
begin

\<comment> \<open>read_invoke\<close>
lemma read_invoke_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (RInvoke cl' keys')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma read_invoke_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (Read cl' k' v' t' rts' rlst')"
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
              else get_lst (svr_state (svrs (read_invoke_U cl keys s) ka)
                     (get_wtxn (read_invoke_U cl keys s) cl'))) = 
           (\<lambda>k. if kv_map' k = None then lst_map (cls s cl') k
              else get_lst (svr_state (svrs s k) (get_wtxn s cl')))" by auto
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
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst) (RInvoke cl' keys')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma read_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst) (Read cl' k' v' t' rts' rlst')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma read_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst) (RDone cl' kv_map' sn' u''')"
  by (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist)

lemma read_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst) (WInvoke cl' kv_map')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma read_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst) (WCommit cl' kv_map' cts' sn' u''')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma read_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst) (WDone cl' kv_map')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> cl'" "write_done cl' kv_map' s w" "read cl k v t rts rlst w s'"
    hence "(\<lambda>ka. if kv_map' ka = None then lst_map (cls (read_U cl k v rts rlst s) cl') ka
              else get_lst (svr_state (svrs (read_U cl k v rts rlst s) ka)
                     (get_wtxn (read_U cl k v rts rlst s) cl'))) = 
           (\<lambda>k. if kv_map' k = None then lst_map (cls s cl') k
              else get_lst (svr_state (svrs s k) (get_wtxn s cl')))" by auto
    then show ?thesis using a by (auto simp add: tps_trans_defs fun_upd_twist)
  qed
  done

lemma read_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (Read cl k v t_wr rts rlst) (RegR k' t' t_wr' rts')"
  by (auto simp add: left_commute' tps_trans_defs add_to_readerset_def split: ver_state.split)

lemma read_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> t \<noteq> t' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst) (PrepW k' t' v')"
  by (auto simp add: left_commute' tps_trans_defs)

lemma read_commit_write_indep:
  "cl \<noteq> get_cl_w t \<Longrightarrow> left_commute tps (Read cl k v t rts rlst) (CommitW k' t' v' cts')"
  by (auto simp add: left_commute' tps_trans_defs)


\<comment> \<open>read_done\<close>

lemma read_done_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (RInvoke cl' keys')"
  by (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist)

lemma read_done_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (Read cl' k' v' t' rts' rlst')"
  by (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist)

lemma read_done_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (RDone cl' kv_map' sn' u''')"
  by (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist)

lemma read_done_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (WInvoke cl' kv_map')"
  by (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist)

(*
  TODO:
*)
term Union

lemma read_done_write_commit_indep_L1:   (*  *)
  "cl \<noteq> cl' \<Longrightarrow> 
  get_ctx (s\<lparr>cls := (cls s)(cl' := X), 
             wtxn_deps := (wtxn_deps s)(get_wtxn s cl' := cl_ctx (cls s cl'))\<rparr>) cl keys = 
  get_ctx s cl keys"
  apply (auto simp add: get_ctx_defs del: equalityI)
  apply (intro arg_cong[where f="Union"] arg_cong[where f="\<lambda>g. image g _"] ext)
  (* DOES NOT SEEM TO HOLD, requires removal of history variable wtxn_deps? *)
  sorry

lemma read_done_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute' read_done_def write_commit_def)
  subgoal for s
    by (auto simp add: tps_trans_defs)

  subgoal for s
    by (auto simp add: tps_trans_defs)

  subgoal for s
    by (auto simp add: tps_trans_defs read_done_write_commit_indep_L1 fun_upd_twist)

  done



term fun_upd

lemma fun_upd1_cong: 
  "\<lbrakk> a = b \<rbrakk> \<Longrightarrow> f(x := a) = f(x := b)"
  by auto

lemma fun_upd2_cong: 
  "\<lbrakk> a = c; b = d \<rbrakk> \<Longrightarrow> f(x := a, y := b) = f(x := c, y := d)"
  by auto


lemma read_done_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (WDone cl' kv_map')"
  apply (auto simp add: left_commute' read_done_def write_done_def)
  subgoal for s
    by (auto simp add: tps_trans_defs)

  subgoal for s
    by (auto simp add: tps_trans_defs)

  subgoal for s
    apply (auto simp add: tps_trans_defs)
    apply (intro global_conf.unfold_congs, simp_all)
    apply (subst fun_upd_twist, simp)
    apply (intro fun_upd2_cong cl_conf.fold_congs arg_cong[where f="(\<union>) _"], auto  del: equalityI)
    (* SHOULD HOLD? (does not change gst on client) *)
    sorry
  done 

thm cl_conf.unfold_congs
thm global_conf.unfold_congs

(*
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> cl'" "write_done cl' kv_map' s w" "read_done cl kv_map sn w s'"
    hence "(\<lambda>ka. if kv_map' ka = None then lst_map (cls (read_done_U cl kv_map s) cl') ka
              else get_lst (svr_state (svrs (read_done_U cl kv_map s) ka)
                     (get_wtxn (read_done_U cl kv_map s) cl'))) = 
           (\<lambda>k. if kv_map' k = None then lst_map (cls s cl') k
              else get_lst (svr_state (svrs s k) (get_wtxn s cl')))" by auto
    then show ?thesis using a apply (auto simp add: tps_trans_defs fun_upd_twist) oops
*)

lemma global_conf_svrs_cls_twisted_update_cong:
  "\<lbrakk> X = X'; Y = Y' \<rbrakk> \<Longrightarrow> s\<lparr>svrs := X, cls := Y\<rparr> = s\<lparr>cls := Y', svrs := X'\<rparr>" 
  by auto

lemma read_done_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (RegR k' t' t_wr' rts')"
  apply (auto simp add: left_commute' read_done_def register_read_def)
  subgoal for s
    by (auto simp add: tps_trans_defs)

  subgoal for s
    by (auto simp add: tps_trans_defs)

  subgoal for s
    apply (auto simp add: tps_trans_defs)
    apply (intro global_conf_svrs_cls_twisted_update_cong, simp)
    apply (intro fun_upd1_cong cl_conf.fold_congs arg_cong[where f="(\<union>) _"], simp_all)
    (* SHOULD HOLD (does not change get_ts on server). *)
    sorry

  done 
(*
  apply (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist) oops
*)

lemma read_done_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (PrepW k' t' v')"
  apply (auto simp add: left_commute' read_done_def prepare_write_def)
  subgoal for s
    by (auto simp add: tps_trans_defs)

  subgoal for s
    by (auto simp add: tps_trans_defs)

  subgoal for s
    apply (auto simp add: tps_trans_defs)
    apply (intro global_conf_svrs_cls_twisted_update_cong, simp)
    apply (intro fun_upd1_cong cl_conf.unfold_congs arg_cong[where f="(\<union>) _"], simp_all)
    (* DOES NOT HOLD? (changes get_ts on server k') *)
    sorry

  done 
(*  
  apply (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist) oops
*)

lemma read_done_commit_write_indep:
  "cl \<noteq> get_cl_w t \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (CommitW k' t' v' cts')"
  apply (auto simp add: left_commute' read_done_def commit_write_def)
  subgoal for s
    by (auto simp add: tps_trans_defs)

  subgoal for s
    by (auto simp add: tps_trans_defs)

  subgoal for s
    apply (auto simp add: tps_trans_defs)
    subgoal for kv_map' ts y 
      apply (intro global_conf_svrs_cls_twisted_update_cong, simp)
      apply (intro fun_upd1_cong cl_conf.unfold_congs arg_cong[where f="(\<union>) _"], simp_all)
      (* DOES NOT HOLD? (changes get_ts on server side) *)
      sorry

    subgoal for kv_map' ts y x
      thm contrapos_np
      apply (erule contrapos_np[where Q="(_ :: 'v global_conf)= _"])
      apply (intro global_conf_svrs_cls_twisted_update_cong, simp)
      apply (intro fun_upd1_cong cl_conf.unfold_congs arg_cong[where f="(\<union>) _"], simp_all)
      (* DOES NOT HOLD? (changes get_ts on server side) *)
      sorry      
    done
  done 
(*
  apply (auto simp add: left_commute' tps_trans_defs get_ctx_defs fun_upd_twist) oops
*)


\<comment> \<open>write_invoke\<close>

lemma write_invoke_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (RInvoke cl' keys')"
  by (auto simp add: left_commute' tps_trans_defs fun_upd_twist)

lemma write_invoke_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (Read cl' k' v' t' rts' rlst')"
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
              else get_lst (svr_state (svrs (write_invoke_U cl kv_map s) ka)
                     (get_wtxn (write_invoke_U cl kv_map s) cl'))) = 
           (\<lambda>k. if kv_map' k = None then lst_map (cls s cl') k
              else get_lst (svr_state (svrs s k) (get_wtxn s cl')))" by auto
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
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (Read cl' k' v' t' rts' rlst')"
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
             else get_lst (svr_state (svrs (write_commit_U cl kv_map cts s) ka)
                     (get_wtxn (write_commit_U cl kv_map cts s) cl'))) = 
           (\<lambda>k. if kv_map' k = None then lst_map (cls s cl') k
             else get_lst (svr_state (svrs s k) (get_wtxn s cl')))" 
      by (auto simp add: write_commit_U_def)
    then show ?thesis using a unfolding write_commit_U_def
      by (auto simp add: tps_trans_defs fun_upd_twist)
  qed
  done

lemma write_commit_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (RegR k' t' t_wr' rts')"
  apply (auto simp add: left_commute' write_commit_def register_read_def)
  subgoal for s
    apply (simp add: write_commit_G_def register_read_U_def add_to_readerset_def
        split: if_split_asm ver_state.split)
    by (smt Collect_cong fun_upd_other fun_upd_same ver_state.distinct(5) ver_state.simps(10)
        ver_state.simps(11) ver_state.simps(9))
  by (simp_all add: register_read_G_def register_read_U_def write_commit_U_def)

lemma write_commit_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (PrepW k' t' v')"
  apply (auto simp add: left_commute' write_commit_def prepare_write_def)
  subgoal for s
    apply (auto simp add: write_commit_G_def prepare_write_U_def)
    subgoal
      by (smt (verit, best) domI fun_upd_apply option.simps(1) svr_conf.select_convs(1) 
                svr_conf.simps(5) svr_conf.simps(6) svr_conf.simps(7) svr_conf.surjective)
    subgoal
      by metis
    done
  by (simp_all add: prepare_write_G_def prepare_write_U_def write_commit_U_def)

lemma write_commit_commit_write_indep:   
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (CommitW k' t' v' cts')"
  apply (auto simp add: left_commute' write_commit_def commit_write_def)
  subgoal for s
    apply (auto simp add: write_commit_G_def commit_write_U_def)
    subgoal
      by (smt (verit, best) domI fun_upd_apply option.simps(1) svr_conf.select_convs(1) 
                svr_conf.simps(5) svr_conf.simps(6) svr_conf.simps(7) svr_conf.surjective)
    subgoal
      by metis
    done
  by (simp_all add: commit_write_G_def commit_write_U_def write_commit_U_def)


\<comment> \<open>write_done\<close>

lemma write_done_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map) (RInvoke cl' keys')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> cl'" "read_invoke cl' keys' s w" "write_done cl kv_map w s'"
    hence "(\<lambda>ka. if kv_map ka = None then lst_map (cls (read_invoke_U cl' keys' s) cl) ka
             else get_lst (svr_state (svrs (read_invoke_U cl' keys' s) ka)
                     (get_wtxn (read_invoke_U cl' keys' s) cl))) = 
           (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k
             else get_lst (svr_state (svrs s k) (get_wtxn s cl)))" by auto
    then show ?thesis using a by (auto simp add: tps_trans_defs fun_upd_twist)
  qed
  done

lemma write_done_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map) (Read cl' k' v' t' rts' rlst')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> cl'" "read cl' k' v' t' rts' rlst' s w" "write_done cl kv_map w s'"
    hence "(\<lambda>ka. if kv_map ka = None then lst_map (cls (read_U cl' k' v' rts' rlst' s) cl) ka
             else get_lst (svr_state (svrs (read_U cl' k' v' rts' rlst' s) ka)
                    (get_wtxn (read_U cl' k' v' rts' rlst' s) cl))) = 
           (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k
             else get_lst (svr_state (svrs s k) (get_wtxn s cl)))" by auto
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
                              else svr_lst (svrs (read_done_U cl' kv_map' s) ka)) = 
           (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k else svr_lst (svrs s k))"
    by (auto simp add: read_done_U_def)
    then show ?thesis using a apply (auto simp add: tps_trans_defs get_ctx_defs fun_upd_twist) oops

lemma write_done_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map) (WInvoke cl' kv_map')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> cl'" "write_invoke cl' kv_map' s w" "write_done cl kv_map w s'"
    hence "(\<lambda>ka. if kv_map ka = None then lst_map (cls (write_invoke_U cl' kv_map' s) cl) ka
             else get_lst (svr_state (svrs (write_invoke_U cl' kv_map' s) ka)
                    (get_wtxn (write_invoke_U cl' kv_map' s) cl))) = 
           (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k
             else get_lst (svr_state (svrs s k) (get_wtxn s cl)))" by auto
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
             else get_lst (svr_state (svrs (write_commit_U cl' kv_map' cts' s) ka)
                    (get_wtxn (write_commit_U cl' kv_map' cts' s) cl))) = 
           (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k
             else get_lst (svr_state (svrs s k) (get_wtxn s cl)))" 
      by (auto simp add: write_commit_U_def)
    then show ?thesis using a unfolding write_commit_U_def
      by (auto simp add: tps_trans_defs fun_upd_twist)
  qed
  done

lemma write_done_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map) (WDone cl' kv_map')"
  apply (auto simp add: left_commute')
  subgoal for s w s'
  proof -
    assume a: "cl \<noteq> cl'" "write_done cl' kv_map' s w" "write_done cl kv_map w s'"
    hence wd1: "(\<lambda>ka. if kv_map ka = None then lst_map (cls (write_done_U cl' kv_map' s) cl) ka
             else get_lst (svr_state (svrs (write_done_U cl' kv_map' s) ka)
                    (get_wtxn (write_done_U cl' kv_map' s) cl))) = 
           (\<lambda>k. if kv_map k = None then lst_map (cls s cl) k
             else get_lst (svr_state (svrs s k) (get_wtxn s cl)))" 
      by (auto simp add: write_done_U_def)
    have "(\<lambda>ka. if kv_map' ka = None then lst_map (cls (write_done_U cl kv_map s) cl') ka
             else get_lst (svr_state (svrs (write_done_U cl kv_map s) ka)
                    (get_wtxn (write_done_U cl kv_map s) cl'))) = 
           (\<lambda>k. if kv_map' k = None then lst_map (cls s cl') k
             else get_lst (svr_state (svrs s k) (get_wtxn s cl')))" using a 
      by (auto simp add: write_done_U_def)
    then show ?thesis using a wd1 unfolding write_done_U_def
      by (auto simp add: tps_trans_defs fun_upd_twist)
  qed
  done

lemma write_done_server_ev_indep_L: 
  "{u.
      \<exists>k. (k = k' \<longrightarrow> u = get_sclk (svr_state (svrs s k') (get_wtxn s cl)) \<and> 
                      k' \<in> dom kv_map) \<and>
          (k \<noteq> k' \<longrightarrow> u = get_sclk (svr_state (svrs s k) (get_wtxn s cl)) \<and> k \<in> dom kv_map)} = 
   {get_sclk (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map}"
  by (auto)

lemma write_done_register_read_indep_L1:
  "svr_state (svrs s k') t_wr = Commit cts sclk lst v rs \<Longrightarrow>
   {u.
      \<exists>k. (k = k' \<longrightarrow> u = sclk \<and> k' \<in> dom kv_map) \<and>
          (k \<noteq> k' \<longrightarrow> u = get_sclk (svr_state (svrs s k) t_wr) \<and> k \<in> dom kv_map)} = 
   {get_sclk (svr_state (svrs s k) t_wr) | k. k \<in> dom kv_map}"
  apply (auto simp add: domIff)
  by (metis ver_state.sel(5))

lemma write_done_register_read_indep_L2:
   "(if kv_map k = None
     then lst_map (cls (s\<lparr>svrs := Z\<rparr>) cl) k
     else get_lst (svr_state (svrs (s\<lparr>svrs := (svrs s)(k' := svrs s k'\<lparr>
                     svr_state := svr_state (svrs s k'),
                     svr_clock := B\<rparr>)\<rparr>) k)
                  (get_wtxn (s\<lparr>svrs := (svrs s)(k' := X)\<rparr>) cl))) = 
    (if kv_map k = None 
     then lst_map (cls s cl) k 
     else get_lst (svr_state (svrs s k) (get_wtxn s cl)))"
  by auto

lemma write_done_register_read_indep_L3:
   "svr_state (svrs s k') t_wr = Commit cts sts lst v rs
   \<Longrightarrow>
    (if kv_map k = None
     then lst_map (cls (s\<lparr>svrs := Z\<rparr>) cl) k
     else get_lst (svr_state (svrs (s\<lparr>svrs := (svrs s)(k' := svrs s k'\<lparr>
                     svr_state := (svr_state (svrs s k')) (t_wr := Commit cts sts lst v (insert Y rs)),
                     svr_clock := B\<rparr>)\<rparr>) k)
                  (get_wtxn (s\<lparr>svrs := (svrs s)(k' := X)\<rparr>) cl))) = 
    (if kv_map k = None 
     then lst_map (cls s cl) k 
     else get_lst (svr_state (svrs s k) (get_wtxn s cl)))"
  by auto

lemmas write_done_register_read_indep_lemmas = 
  write_done_server_ev_indep_L write_done_register_read_indep_L1
  write_done_register_read_indep_L2 write_done_register_read_indep_L3

lemma write_done_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WDone cl kv_map) (RegR k' t' t_wr' rts')"
  apply (auto simp add: left_commute' write_done_def register_read_def)
  subgoal for s
    apply (auto simp add: register_read_U_def write_done_G_def add_to_readerset_def
                split: if_split_asm ver_state.split)
    by (smt  domI fun_upd_other fun_upd_same option.inject ver_state.case_eq_if ver_state.exhaust_sel
        ver_state.sel(2) ver_state.sel(4) ver_state.simps(10))

  subgoal for s
    by (auto simp add: register_read_G_def write_done_U_def)

  subgoal for s
    apply (auto simp add: register_read_U_def write_done_U_def add_to_readerset_def
        write_done_register_read_indep_lemmas split: if_split_asm ver_state.split)
    done
  done

lemma write_done_prepare_write_indep_L2:
   "get_wtxn s cl \<noteq> t'
   \<Longrightarrow>
    (if kv_map k = None
     then lst_map (cls (s\<lparr>svrs := Z\<rparr>) cl) k
     else get_lst (svr_state (svrs (s\<lparr>svrs := (svrs s)(k' := svrs s k'\<lparr>
                     svr_state := (svr_state (svrs s k'))(t' := A),
                     svr_clock := B\<rparr>)\<rparr>) k)
                  (get_wtxn (s\<lparr>svrs := (svrs s)(k' := X)\<rparr>) cl))) = 
    (if kv_map k = None 
     then lst_map (cls s cl) k 
     else get_lst (svr_state (svrs s k) (get_wtxn s cl)))"
  by auto

lemmas write_done_prepare_write_indep_lemmas = 
  write_done_server_ev_indep_L write_done_prepare_write_indep_L2

lemma write_done_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (WDone cl kv_map) (PrepW k' t' v')"
  apply (auto simp add: left_commute' write_done_def prepare_write_def)
  subgoal for s
    apply (auto simp add: prepare_write_U_def write_done_G_def)
    by (smt (verit) domI fun_upd_apply get_cl_w.simps(2) option.sel svr_conf.select_convs(1) 
            svr_conf.simps(5) svr_conf.simps(6) svr_conf.simps(7) svr_conf.surjective)

  subgoal for s
    by (auto simp add: prepare_write_G_def write_done_U_def)

  subgoal for s
    apply (auto simp add: prepare_write_U_def write_done_U_def write_done_prepare_write_indep_lemmas)
    done
  done

lemma write_done_commit_write_indep_L2:
   "get_wtxn s cl \<noteq> t'
   \<Longrightarrow>
    (if kv_map k = None
     then lst_map (cls (s\<lparr>svrs := Z\<rparr>) cl) k
     else get_lst (svr_state (svrs (s\<lparr>svrs := (svrs s)(k' := svrs s k'\<lparr>
                     svr_state := (svr_state (svrs s k'))(t' := A),
                     svr_clock := B, 
                     svr_lst := C\<rparr>)\<rparr>) k)
                  (get_wtxn (s\<lparr>svrs := (svrs s)(k' := X)\<rparr>) cl))) = 
    (if kv_map k = None 
     then lst_map (cls s cl) k 
     else get_lst (svr_state (svrs s k) (get_wtxn s cl)))"
  by auto

lemmas write_done_commit_write_indep_lemmas = 
  write_done_server_ev_indep_L write_done_commit_write_indep_L2

lemma write_done_commit_write_indep:  
  "\<lbrakk> cl \<noteq> get_cl_w t' \<rbrakk>
  \<Longrightarrow> left_commute tps (WDone cl kv_map) (CommitW k' t' v' cts')"
  apply (auto simp add: left_commute' write_done_def commit_write_def)
  subgoal for s
    apply (auto simp add: commit_write_U_def write_done_G_def)
    by (smt (verit) domI fun_upd_apply get_cl_w.simps(2) option.sel svr_conf.select_convs(1) 
            svr_conf.simps(5) svr_conf.simps(6) svr_conf.simps(7) svr_conf.surjective)

  subgoal for s
    by (auto simp add: commit_write_G_def write_done_U_def)

  subgoal for s
    apply (auto simp add: commit_write_U_def write_done_U_def write_done_commit_write_indep_lemmas)
    done
  done


\<comment> \<open>register_read\<close>

lemma register_read_read_invoke_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (RInvoke cl' keys')"
  by (auto simp add: left_commute' tps_trans_defs)

lemma register_read_read_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (Read cl' k' v' t' rts' rlst')"
  by (auto simp add: left_commute' tps_trans_defs add_to_readerset_def split: ver_state.split)

lemma register_read_read_done_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops

lemma register_read_write_invoke_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (WInvoke cl' kv_map')"
  by (auto simp add: left_commute' tps_trans_defs)

lemma register_read_write_commit_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute' register_read_def write_commit_def)
  apply (simp_all add: register_read_U_def register_read_G_def write_commit_G_def write_commit_U_def
         add_to_readerset_def split: if_split_asm ver_state.split)
  by (smt (verit) Collect_cong ver_state.distinct(5))

lemma register_read_write_done_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (WDone cl' kv_map')"
  apply (auto simp add: left_commute' write_done_def register_read_def)
  subgoal for s
    by (auto simp add: register_read_G_def write_done_U_def)

  subgoal for s
    apply (auto simp add: register_read_U_def write_done_G_def add_to_readerset_def
                split: if_split_asm ver_state.split)
    apply (metis domI ver_state.sel(2))
    by (metis domIff option.discI option.sel ver_state.sel(4))

  subgoal for s
    apply (auto simp add: register_read_U_def write_done_U_def add_to_readerset_def
        write_done_register_read_indep_lemmas split: if_split_asm ver_state.split)
    done
  done

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
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (Read cl' k' v' t' rts' rlst')"
  by (auto simp add: left_commute' tps_trans_defs)

lemma prepare_write_read_done_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute' tps_trans_defs fun_upd_twist) oops

lemma prepare_write_write_invoke_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (WInvoke cl' kv_map')"
  by (auto simp add: left_commute' tps_trans_defs)

lemma prepare_write_write_commit_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute' prepare_write_def write_commit_def)
  subgoal for s
    by (auto simp add: prepare_write_G_def write_commit_U_def)

  apply (simp_all add: write_commit_G_def write_commit_U_def prepare_write_U_def)
  by (smt (verit) Collect_cong get_cl_w.simps(2))

lemma prepare_write_write_done_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (WDone cl' kv_map')"
  apply (auto simp add: left_commute' prepare_write_def write_done_def)
  by (auto simp add: write_done_G_def write_done_U_def prepare_write_G_def prepare_write_U_def
                     write_done_prepare_write_indep_lemmas)

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
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (Read cl' k' v' t' rts' rlst')"
  by (auto simp add: left_commute' tps_trans_defs) 

lemma commit_write_read_done_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute' tps_trans_defs) 
  oops

lemma commit_write_write_invoke_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (WInvoke cl' kv_map')"
  by (auto simp add: left_commute' tps_trans_defs)

lemma commit_write_write_commit_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (WCommit cl' kv_map' cts' sn' u''')"
  by (auto simp add: left_commute' tps_trans_defs) (metis)

lemma commit_write_write_done_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (WDone cl' kv_map')"
  apply (auto simp add: left_commute' write_done_def commit_write_def)
  subgoal for s
    by (auto simp add: commit_write_G_def write_done_U_def)

  subgoal for s
    by (auto simp add: commit_write_U_def write_done_G_def)

  subgoal for s 
    apply (auto simp add: commit_write_U_def write_done_U_def write_done_commit_write_indep_lemmas)
    done
  done

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