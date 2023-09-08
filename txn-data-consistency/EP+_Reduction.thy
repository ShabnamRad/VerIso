section \<open>Reductions for EP+\<close>

theory "EP+_Reduction"
  imports "EP+_TCCv" Reductions
begin


subsection \<open>Auxiliary lemmas\<close>

text \<open>Some congruence lemmas for explorative proofs\<close>

lemma fun_upd1_cong: 
  "\<lbrakk> a = b \<rbrakk> \<Longrightarrow> f(x := a) = f(x := b)"
  by auto

lemma fun_upd2_cong: 
  "\<lbrakk> a = c; b = d \<rbrakk> \<Longrightarrow> f(x := a, y := b) = f(x := c, y := d)"
  by auto

lemma global_conf_rtxn_cls_twisted_update_cong:
  "s\<lparr>rtxn_rts := b, cls := a\<rparr> = s\<lparr> cls := a, rtxn_rts := b\<rparr>"
  by auto

thm cl_conf.unfold_congs
thm global_conf.unfold_congs

lemma global_conf_svrs_cls_twisted_update_cong:
  "\<lbrakk> X = X'; Y = Y'; Z = Z' \<rbrakk> \<Longrightarrow> s\<lparr>svrs := X, cls := Y, rtxn_rts := Z\<rparr> = s\<lparr>cls := Y', rtxn_rts := Z', svrs := X'\<rparr>" 
  by auto


(***********************)

lemma wtxns_dom_add_to_readerset [simp]:
  "wtxns_dom (add_to_readerset (svr_state (svrs s k')) t rts rlst t_wr) 
 = wtxns_dom (svr_state (svrs s k'))"
  by (auto simp add: wtxns_dom_def add_to_readerset_def split: ver_state.split)

lemma wtxns_dom_svr_state_update_other_txn:
  "cl \<noteq> get_cl_w t' \<Longrightarrow>
   wtxns_dom ((svr_state (svrs s k'))(t' := X)) = wtxns_dom (svr_state (svrs s k'))"
  apply (auto simp add: wtxns_dom_def split: ver_state.split)
  oops

(****)


text \<open>Possible invariants (TBC)\<close>

definition wtxn_cts_gt_gst_INV :: "'v global_conf \<Rightarrow> bool" where
  "wtxn_cts_gt_gst_INV s \<longleftrightarrow> (\<forall>t cts cl. wtxn_cts s t = Some cts \<longrightarrow> gst (cls s cl) < cts)"

lemmas wtxn_cts_gt_gst_INV_I = wtxn_cts_gt_gst_INV_def [THEN iffD2, rule_format]
lemmas wtxn_cts_gt_gst_INV_E[elim] = wtxn_cts_gt_gst_INV_def [THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_cts_gt_gst_INV: "reach tps s \<Longrightarrow> wtxn_cts_gt_gst_INV s"
  sorry


text \<open>View update lemmas\<close>

lemma get_view_update_cls:
  "cl' \<noteq> cl \<Longrightarrow>
   get_view (s\<lparr>cls := (cls s)(cl := X) \<rparr>) cl' = get_view s cl'"
  by (auto simp add: get_view_def)

lemma get_view_update_cls_rtxn_rts:
  "cl' \<noteq> cl \<Longrightarrow>
   get_view (s\<lparr>cls := (cls s)(cl := X), rtxn_rts := Y \<rparr>) cl' = get_view s cl'"
  by (auto simp add: get_view_def)

lemma get_view_update_svr_wtxns_dom:
   "wtxns_dom new_svr_state = wtxns_dom (svr_state (svrs s k)) \<Longrightarrow> 
    get_view (s\<lparr>svrs := (svrs s)
                   (k := svrs s k
                      \<lparr>svr_state := new_svr_state,
                       svr_clock := clk \<rparr>)\<rparr>) cl 
 = get_view s cl"
  by (auto simp add: get_view_def ext)


lemma get_view_update_svr_prep:  
   "\<lbrakk> cl \<noteq> get_cl_w t'; wtxn_cts_gt_gst_INV s \<rbrakk> \<Longrightarrow>
     get_view (s\<lparr>svrs := (svrs s)
                   (k := svrs s k
                      \<lparr>svr_state := (svr_state (svrs s k))(t' := Prep clk v'),
                       svr_clock := clk' \<rparr>)\<rparr>) cl 
   = get_view s cl"
(* possible additional premises (if needed for invariant application):
     svr_state (svrs s k) t' = No_Ver; 
     cl_state (cls s (get_cl_w t')) = WtxnPrep kvmap; 
     kvmap k = Some v
*)
  apply (auto simp add: get_view_def wtxns_dom_def)
  apply (intro ext arg_cong[where f=Collect], auto)
  apply (thin_tac "_ \<noteq> _")
  apply (thin_tac "svr_state (svrs s k) t' = No_Ver")
  subgoal for cts
    apply (elim wtxn_cts_gt_gst_INV_E)       (* why is this so painful? *)
    apply (atomize)
    apply (drule spec[where x=t'])
    apply (drule spec[where x=cts])
    apply auto
    apply (thin_tac "_ = Some _")
    apply (drule spec[where x=cl])
    apply auto
    done
  done


lemmas get_view_update_lemmas = 
  get_view_update_cls get_view_update_cls_rtxn_rts 
  get_view_update_svr_wtxns_dom get_view_update_svr_prep


(***********************)


subsection \<open>Commutativity proofs\<close>

\<comment> \<open>read_invoke\<close>
lemma read_invoke_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (RInvoke cl' keys')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_invoke_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (Read cl' k' v' t' rts' rlst')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_invoke_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (RDone cl' kv_map' sn' u''')"
  by (auto simp add: left_commute_def tps_trans_defs get_view_def fun_upd_twist)

lemma read_invoke_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (WInvoke cl' kv_map')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_invoke_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (WCommit cl' kv_map' cts' sn' u''')"
  by (auto simp add: left_commute_def tps_trans_defs get_view_def fun_upd_twist)

lemma read_invoke_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys) (WDone cl' kv_map')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist ext)

lemma read_invoke_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (RInvoke cl keys) (RegR k' t' i' rts')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma read_invoke_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (RInvoke cl keys) (PrepW k' t' v')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma read_invoke_commit_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (RInvoke cl keys) (CommitW k' t' v' cts')"
  by (auto simp add: left_commute_def tps_trans_defs)


\<comment> \<open>read\<close>

lemma read_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst) (RInvoke cl' keys')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst) (Read cl' k' v' t' rts' rlst')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst) (RDone cl' kv_map' sn' u''')"
  by (auto simp add: left_commute_def tps_trans_defs get_view_def fun_upd_twist)

lemma read_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst) (WInvoke cl' kv_map')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst) (WCommit cl' kv_map' cts' sn' u''')"
  by (auto simp add: left_commute_def tps_trans_defs get_view_def fun_upd_twist)

lemma read_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst) (WDone cl' kv_map')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist ext)

lemma read_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (Read cl k v t_wr rts rlst) (RegR k' t' t_wr' rts')"
  by (auto simp add: left_commute_def tps_trans_defs add_to_readerset_def split: ver_state.split)

lemma read_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> t \<noteq> t' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst) (PrepW k' t' v')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma read_commit_write_indep:
  "cl \<noteq> get_cl_w t \<Longrightarrow> left_commute tps (Read cl k v t rts rlst) (CommitW k' t' v' cts')"
  by (auto simp add: left_commute_def tps_trans_defs)


\<comment> \<open>read_done\<close>

lemma read_done_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (RInvoke cl' keys')"
  by (auto simp add: left_commute_def tps_trans_defs get_view_def fun_upd_twist)

lemma read_done_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (Read cl' k' v' t' rts' rlst')"
  by (auto simp add: left_commute_def tps_trans_defs get_view_def fun_upd_twist)

lemma read_done_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (RDone cl' kv_map' sn' u''')"
  by (auto simp add: left_commute_def tps_trans_defs get_view_def fun_upd_twist)

lemma read_done_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (WInvoke cl' kv_map')"
  by (auto simp add: left_commute_def tps_trans_defs get_view_def fun_upd_twist)




lemma read_done_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute_def read_done_def write_commit_def)
  subgoal for s
    apply (auto simp add: tps_trans_defs get_view_update_lemmas)
    sorry

  subgoal for s
    by (auto simp add: tps_trans_defs get_view_update_lemmas)

  subgoal for s
    by (auto simp add: tps_trans_defs fun_upd_twist)
  done


term fun_upd


lemma read_done_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (WDone cl' kv_map')"
  apply (auto simp add: left_commute_def read_done_def write_done_def)
  subgoal for s
    by (auto simp add: tps_trans_defs get_view_update_lemmas)

  subgoal for s
    by (auto simp add: tps_trans_defs get_view_update_lemmas)

  subgoal for s
    apply (auto simp add: tps_trans_defs get_view_def global_conf_rtxn_cls_twisted_update_cong)
    apply (intro global_conf.unfold_congs, simp_all)
    apply (subst fun_upd_twist, simp)
    by (intro fun_upd2_cong cl_conf.fold_congs arg_cong[where f="(\<union>) _"], auto del: equalityI)
  done 


\<comment> \<open>taken from the EP+_TCCv_proof.thy\<close>

lemma add_to_readerset_no_ver_inv:
  "add_to_readerset wtxns t rts rlst t' t'' = No_Ver \<longleftrightarrow> wtxns t'' = No_Ver"
  by (simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_prep_inv:
  "add_to_readerset wtxns t rts rlst t' t'' = Prep ts v \<longleftrightarrow> wtxns t'' = Prep ts v"
  by (simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_commit:
  "add_to_readerset wtxns t rts rlst t' t'' = Commit cts sts lst v rs \<Longrightarrow>
    \<exists>rs'. wtxns t'' = Commit cts sts lst v rs'"
  apply (simp add: add_to_readerset_def)
  by (cases "wtxns t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_pres_get_ts:
  "get_ts (add_to_readerset wtxns t rts rlst t_wr t') = get_ts (wtxns t')"
  by (smt (verit, ccfv_SIG) add_to_readerset_commit add_to_readerset_no_ver_inv
      add_to_readerset_prep_inv ver_state.exhaust_sel ver_state.sel(2))

lemma add_to_readerset_pres_is_committed:
  "is_committed (add_to_readerset wtxns t rts rlst t_wr t') = is_committed (wtxns t')"
  by (smt (verit, best) add_to_readerset_no_ver_inv add_to_readerset_prep_inv is_committed.elims(1))

lemma add_to_readerset_pres_at:
  "at (add_to_readerset wtxns t rts rlst t_wr) ts = at wtxns ts"
  by (simp add: at_def ver_committed_before_def add_to_readerset_pres_get_ts o_def
      add_to_readerset_pres_is_committed)

lemma add_to_readerset_pres_newest_own_write:
  "newest_own_write (add_to_readerset wtxns t rts rlst t_wr) ts cl = newest_own_write wtxns ts cl"
  by (auto simp add: newest_own_write_def ver_committed_after_def add_to_readerset_pres_get_ts o_def
      add_to_readerset_pres_is_committed)

lemma add_to_readerset_pres_read_at:
  "read_at (add_to_readerset wtxns t rts rlst t_wr) ts cl = read_at wtxns ts cl"
  by (simp add: read_at_def add_to_readerset_pres_at add_to_readerset_pres_get_ts
      add_to_readerset_pres_newest_own_write)

lemma read_done_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (RegR k' t' t_wr' rts')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: tps_trans_GU_defs get_view_update_lemmas)

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)
  done 


(**HERE**)

lemma read_done_prepare_write_indep:
  "\<lbrakk> cl \<noteq> get_cl_w t' \<rbrakk> 
 \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (PrepW k' t' v')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: tps_trans_GU_defs get_view_update_lemmas reach_wtxn_cts_gt_gst_INV) 

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)
  done 

lemma read_done_commit_write_indep:
  "cl \<noteq> get_cl_w t \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (CommitW k' t' v' cts')"
  apply (auto simp add: left_commute_def read_done_def commit_write_def)
  subgoal for s
    apply (auto simp add: tps_trans_defs get_view_update_lemmas )
    sorry

  subgoal for s
    by (auto simp add: tps_trans_defs)

  subgoal for s
    by (auto simp add: tps_trans_defs)
  done 

\<comment> \<open>write_invoke\<close>

lemma write_invoke_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (RInvoke cl' keys')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma write_invoke_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (Read cl' k' v' t' rts' rlst')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma write_invoke_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (RDone cl' kv_map' sn' u''')"
  by (auto simp add: left_commute_def tps_trans_defs get_view_def fun_upd_twist)

lemma write_invoke_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (WInvoke cl' kv_map')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma write_invoke_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (WCommit cl' kv_map' cts' sn' u''')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist get_view_update_lemmas)

lemma write_invoke_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (WDone cl' kv_map')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist ext)

lemma write_invoke_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (RegR k' t' t_wr' rts')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma write_invoke_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (PrepW k' t' v')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma write_invoke_commit_write_indep:
  "cl \<noteq> get_cl_w t \<Longrightarrow> left_commute tps (WInvoke cl kv_map) (CommitW k' t' v' cts')"
  by (auto simp add: left_commute_def tps_trans_defs)


\<comment> \<open>write_commit\<close>

lemma write_commit_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (RInvoke cl' keys')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist get_view_update_lemmas)

lemma write_commit_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (Read cl' k' v' t' rts' rlst')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist get_view_update_lemmas)

lemma write_commit_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: tps_trans_GU_defs get_view_update_lemmas)

  subgoal for s
    apply (simp_all add: tps_trans_GU_defs get_view_update_lemmas)
    sorry

  subgoal for s
    by (auto simp add: tps_trans_GU_defs fun_upd_twist)
  done

lemma write_commit_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (WInvoke cl' kv_map')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist get_view_update_lemmas)


(* TRICKY?! *)

lemma write_commit_write_commit_indep:    
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: tps_trans_GU_defs)
    
    sorry

  subgoal for s
    apply (simp add: tps_trans_GU_defs)
    sorry

  subgoal for s
    apply (auto simp add: tps_trans_GU_defs fun_upd_twist)
    apply (intro global_conf.unfold_congs, simp_all)
    apply auto
    sorry
  done

lemma write_commit_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (WDone cl' kv_map')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist get_view_update_lemmas ext)

lemma write_commit_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (RegR k' t' t_wr' rts')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: tps_trans_GU_defs get_view_update_lemmas)
    subgoal
      by (smt (verit, ccfv_SIG) add_to_readerset_prep_inv domI option.sel svr_conf.select_convs(1) 
              svr_conf.surjective svr_conf.update_convs(1) svr_conf.update_convs(2)) 
    subgoal
      by (metis add_to_readerset_pres_get_ts) 
    done
  by (simp_all add: tps_trans_GU_defs)

lemma write_commit_prepare_write_indep:
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (PrepW k' t' v')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: tps_trans_GU_defs get_view_update_lemmas reach_wtxn_cts_gt_gst_INV)
    subgoal
      by (smt (verit, ccfv_SIG) domI fun_upd_apply option.sel svr_conf.select_convs(1) 
              svr_conf.surjective svr_conf.update_convs(1) svr_conf.update_convs(2))
    subgoal 
      by metis
    done
  by (simp_all add: tps_trans_GU_defs)

lemma write_commit_commit_write_indep:   
  "cl \<noteq> get_cl_w t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (CommitW k' t' v' cts')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: tps_trans_GU_defs )
    subgoal 
      (* TBD *)
      sorry
    subgoal 
      by (smt (verit, ccfv_SIG) domI fun_upd_other option.sel svr_conf.select_convs(1) 
              svr_conf.simps(7) svr_conf.surjective svr_conf.update_convs(1-2)) 
    subgoal
      by metis 
    subgoal 
      (* TBD *)
      sorry
    subgoal 
      by (smt (verit, ccfv_SIG) domI fun_upd_other option.sel svr_conf.select_convs(1) 
              svr_conf.simps(7) svr_conf.surjective svr_conf.update_convs(1-2)) 
    subgoal 
      by metis 
    done

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    apply (subst (1) tps_trans_GU_defs)
    apply (subst (1) tps_trans_GU_defs)
    apply (subst (10) commit_write_U_def)
    apply (subst (10) commit_write_U_def)
    (* apply (simp add: tps_trans_GU_defs) *)      (* PROBLEM: LOOPS? *)
    (* TBD *)
    sorry
  done

\<comment> \<open>write_done\<close>

lemma write_done_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map) (RInvoke cl' keys')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist ext)

lemma write_done_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map) (Read cl' k' v' t' rts' rlst')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist ext)

lemma write_done_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map) (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    by (auto simp add: tps_trans_GU_defs get_view_def)

  subgoal for s
    apply (auto simp add: tps_trans_defs get_view_def global_conf_rtxn_cls_twisted_update_cong)
    apply (intro global_conf.unfold_congs, simp_all)
    apply (subst fun_upd_twist, simp)
    by (intro fun_upd2_cong cl_conf.fold_congs arg_cong[where f="(\<union>) _"], auto  del: equalityI)
  done 

lemma write_done_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map) (WInvoke cl' kv_map')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist ext)

lemma write_done_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map) (WCommit cl' kv_map' cts' sn' u''')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist get_view_def ext)

lemma write_done_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map) (WDone cl' kv_map')"
  by (auto simp add: left_commute_def  tps_trans_defs fun_upd_twist ext)

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
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: tps_trans_GU_defs add_to_readerset_def
                split: if_split_asm ver_state.split)
    by (smt  domI fun_upd_other fun_upd_same option.inject ver_state.case_eq_if ver_state.exhaust_sel
        ver_state.sel(2) ver_state.sel(4) ver_state.simps(10))

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    apply (auto simp add: tps_trans_GU_defs add_to_readerset_def
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
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: tps_trans_GU_defs)
    by (smt (verit) domI fun_upd_apply get_cl_w.simps(2) option.sel svr_conf.select_convs(1) 
            svr_conf.simps(5) svr_conf.simps(6) svr_conf.simps(7) svr_conf.surjective)

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    apply (auto simp add: tps_trans_GU_defs write_done_prepare_write_indep_lemmas)
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
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: tps_trans_GU_defs)
    by (smt (verit) domI fun_upd_apply get_cl_w.simps(2) option.sel svr_conf.select_convs(1) 
            svr_conf.simps(5) svr_conf.simps(6) svr_conf.simps(7) svr_conf.surjective)

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    by (auto simp add: tps_trans_GU_defs write_done_commit_write_indep_lemmas)  (* SLOW *)
  done


\<comment> \<open>register_read\<close>

lemma register_read_read_invoke_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (RInvoke cl' keys')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma register_read_read_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (Read cl' k' v' t' rts' rlst')"
  by (auto simp add: left_commute_def tps_trans_defs add_to_readerset_def split: ver_state.split)

lemma register_read_read_done_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_top_defs )
  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    by (auto simp add: tps_trans_GU_defs get_view_update_lemmas)

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)
  done 

lemma register_read_write_invoke_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (WInvoke cl' kv_map')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma register_read_write_commit_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (simp_all add: tps_trans_GU_defs)

  subgoal for s
    apply (auto simp add: tps_trans_GU_defs get_view_update_lemmas)

    subgoal for keys kv_map v
      by (metis add_to_readerset_prep_inv domIff option.inject option.simps(3))

    subgoal for keys kv_map
      by (metis add_to_readerset_pres_get_ts)
    done

  subgoal for s
    by (simp_all add: tps_trans_GU_defs)
  done


lemma register_read_write_done_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (WDone cl' kv_map')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    apply (auto simp add: tps_trans_GU_defs add_to_readerset_def split: if_split_asm ver_state.split)
    subgoal by (metis domI ver_state.sel(2))
    subgoal by (metis domIff option.discI option.sel ver_state.sel(4))
    done

  subgoal for s
    by (auto simp add: tps_trans_GU_defs add_to_readerset_def write_done_register_read_indep_lemmas 
             split: if_split_asm ver_state.split)
  done

lemma register_read_register_read_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (RegR k' t' t_wr' rts')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma register_read_prepare_write_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (PrepW k' t' v')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma register_read_commit_write_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (CommitW k' t' v' cts')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)


\<comment> \<open>prepare_write\<close>

lemma prepare_write_read_invoke_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (RInvoke cl' keys')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma prepare_write_read_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (Read cl' k' v' t' rts' rlst')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma prepare_write_read_done_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_top_defs) 
  subgoal for s
    by (auto simp add: tps_trans_GU_defs)
  
  subgoal for s
    by (auto simp add: tps_trans_GU_defs get_view_update_lemmas reach_wtxn_cts_gt_gst_INV)

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)
  done

lemma prepare_write_write_invoke_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (WInvoke cl' kv_map')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma prepare_write_write_commit_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: tps_trans_GU_defs)
  
  subgoal for s
    apply (auto simp add: tps_trans_GU_defs  get_view_update_lemmas reach_wtxn_cts_gt_gst_INV)
    subgoal for kv_map
      by metis
    done

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)
  done

lemma prepare_write_write_done_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (WDone cl' kv_map')"
  apply (auto simp add: left_commute_def prepare_write_def write_done_def)
  by (auto simp add: write_done_G_def write_done_U_def prepare_write_G_def prepare_write_U_def
                     write_done_prepare_write_indep_lemmas)

lemma prepare_write_register_read_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (PrepW k t v) (RegR k' t' t_wr' rts')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma prepare_write_prepare_write_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (PrepW k t v) (PrepW k' t' v')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma prepare_write_commit_write_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (PrepW k t v) (CommitW k' t' v' cts')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

\<comment> \<open>commit_write\<close>

lemma commit_write_read_invoke_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (RInvoke cl' keys')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma commit_write_read_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (Read cl' k' v' t' rts' rlst')"
  by (auto simp add: left_commute_def tps_trans_defs) 

lemma commit_write_read_done_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_top_defs) 
  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    apply (auto simp add: tps_trans_GU_defs)
    subgoal for kv_map ts v

      sorry
    subgoal for kv_map ts v pts
      (* ? *)
      sorry
    done

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)
  done

lemma commit_write_write_invoke_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (WInvoke cl' kv_map')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma commit_write_write_commit_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_top_defs) 
  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    apply (auto simp add: tps_trans_GU_defs)
    (* TBD, 2 remaining subgoals *)
    subgoal
      apply (intro arg_cong[where f="view_of _"])
      sorry

    subgoal 
      by metis

    subgoal 
      apply (intro arg_cong[where f="view_of _"])
      sorry

    subgoal
      by metis
    done

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)
  done

lemma commit_write_write_done_indep:
  "get_cl_w t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (WDone cl' kv_map')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s 
    by (auto simp add: tps_trans_GU_defs write_done_commit_write_indep_lemmas)  (* SLOW, ~15s *)
  done                                                                                                               

lemma commit_write_register_read_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (CommitW k t v cts) (RegR k' t' t_wr' rts')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma commit_write_prepare_write_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (CommitW k t v cts) (PrepW k' t' v')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma commit_write_commit_write_indep:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (CommitW k t v cts) (CommitW k' t' v' cts')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

end