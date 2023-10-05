section \<open>Reductions for EP+\<close>

theory "EP+_Reduction"
  imports "EP+" Reductions
begin


subsection \<open>Auxiliary lemmas\<close>

text \<open>Some congruence lemmas for explorative proofs\<close>

lemma fun_upd1_cong: 
  "\<lbrakk> a = b \<rbrakk> \<Longrightarrow> f(x := a) = f(x := b)"
  by auto

lemma fun_upd2_cong: 
  "\<lbrakk> a = c; b = d \<rbrakk> \<Longrightarrow> f(x := a, y := b) = f(x := c, y := d)"
  by auto

lemma insort_key_arg_cong: "f = g \<Longrightarrow> insort_key f t l = insort_key g t l"
  by simp

lemma global_conf_rtxn_cls_twisted_update_cong:
  "s\<lparr>rtxn_rts := b, cls := a\<rparr> = s\<lparr> cls := a, rtxn_rts := b\<rparr>"
  by auto

thm cl_conf.unfold_congs
thm global_conf.unfold_congs

lemma global_conf_svrs_cls_twisted_update_cong:
  "\<lbrakk> X = X'; Y = Y'; Z = Z' \<rbrakk> \<Longrightarrow> s\<lparr>svrs := X, cls := Y, rtxn_rts := Z\<rparr> = s\<lparr>cls := Y', rtxn_rts := Z', svrs := X'\<rparr>" 
  by auto

lemma global_conf_wtxn_cts_cls_twisted_update_cong:
  "\<lbrakk> X = X'; Y = Y'; Z = Z' \<rbrakk> \<Longrightarrow> s\<lparr>wtxn_cts := X, cts_order := Y, cls := Z\<rparr> = s\<lparr>cls := Z', wtxn_cts := X', cts_order := Y'\<rparr>"
  by auto

lemma global_conf_wtxn_cts_cls_rtxn_twisted_update_cong:
  "\<lbrakk> V = V'; X = X'; Y = Y'; Z = Z' \<rbrakk> \<Longrightarrow>
    s\<lparr>wtxn_cts := V, cts_order := X, cls := Y, rtxn_rts := Z\<rparr> =
    s\<lparr>rtxn_rts := Z', cls := Y', wtxn_cts := V', cts_order := X'\<rparr>"
  by auto


(***********************)

lemma wtxns_dom_add_to_readerset [simp]:
  "wtxns_dom (add_to_readerset (svr_state (svrs s k')) t rts rlst t_wr) 
 = wtxns_dom (svr_state (svrs s k'))"
  by (auto simp add: wtxns_dom_def add_to_readerset_def split: ver_state.split)

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


text \<open>Invariants\<close>

definition Wtxn_Cts_Tn_None where
  "Wtxn_Cts_Tn_None s \<longleftrightarrow> (\<forall>cts kv_map keys n cl. 
    (cl_state (cls s cl) \<in> {Idle, WtxnPrep kv_map} \<and> n \<ge> cl_sn (cls s cl)) \<or>
    (cl_state (cls s cl) \<in> {RtxnInProg keys kv_map, WtxnCommit cts kv_map} \<and> n > cl_sn (cls s cl))
     \<longrightarrow> wtxn_cts s (Tn (Tn_cl n cl)) = None)"

lemmas Wtxn_Cts_Tn_NoneI = Wtxn_Cts_Tn_None_def[THEN iffD2, rule_format]
lemmas Wtxn_Cts_Tn_NoneE[elim] = Wtxn_Cts_Tn_None_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_cts_tn_none [simp, intro]: "reach tps s \<Longrightarrow> Wtxn_Cts_Tn_None s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: Wtxn_Cts_Tn_None_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
    by (induction e) (auto simp add: Wtxn_Cts_Tn_None_def tps_trans_defs)
qed

definition Wtxn_Cts_None where
  "Wtxn_Cts_None s \<longleftrightarrow> (\<forall>cts kv_map keys t. t \<noteq> T0 \<and> (
    (cl_state (cls s (get_cl_w t)) \<in> {Idle, WtxnPrep kv_map} \<and>
        get_sn_w t \<ge> cl_sn (cls s (get_cl_w t))) \<or>
    (cl_state (cls s (get_cl_w t)) \<in> {RtxnInProg keys kv_map, WtxnCommit cts kv_map} \<and>
        get_sn_w t > cl_sn (cls s (get_cl_w t))))
     \<longrightarrow> wtxn_cts s t = None)"

lemmas Wtxn_Cts_NoneI = Wtxn_Cts_None_def[THEN iffD2, rule_format]
lemmas Wtxn_Cts_NoneE[elim] = Wtxn_Cts_None_def[THEN iffD1, elim_format, rule_format]

lemma reach_wtxn_cts_none [simp, intro]: "reach tps s \<Longrightarrow> Wtxn_Cts_None s"
  apply (simp add: Wtxn_Cts_None_def)
  apply rule+ subgoal for cts kv_map keys t apply (cases t)
    apply metis
    by (smt Wtxn_Cts_Tn_None_def get_cl_w.simps(2) get_sn_w.simps(2) insert_iff
        reach_wtxn_cts_tn_none txid0.exhaust). (* SLOW *)

definition CO_Tid where
  "CO_Tid s cl \<longleftrightarrow> (case cl_state (cls s cl) of
    WtxnCommit cts kv_map \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow> n \<le> cl_sn (cls s cl))
  | _ \<Rightarrow> (\<forall>k n. Tn (Tn_cl n cl) \<in> set (cts_order s k) \<longrightarrow> n < cl_sn (cls s cl)))"

lemmas CO_TidI = CO_Tid_def[THEN iffD2, rule_format]
lemmas CO_TidE[elim] = CO_Tid_def[THEN iffD1, elim_format, rule_format]

lemma reach_co_tid[simp]: "reach tps s \<Longrightarrow> CO_Tid s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: CO_Tid_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case
  proof (induction e)
    case (RDone x1 x2 x3 x4)
    then show ?case apply (simp add: CO_Tid_def tps_trans_defs split: txn_state.split_asm)
      using less_SucI less_Suc_eq_le by blast+
  next
    case (WCommit x1 x2 x3 x4 x5)
    then show ?case apply (simp add: CO_Tid_def tps_trans_all_defs set_insort_key split: txn_state.split_asm)
      apply (metis txn_state.distinct(3))
      apply (metis txn_state.distinct(7))
      apply (meson less_or_eq_imp_le)
      by blast
  next
    case (WDone x1 x2)
    then show ?case apply (simp add: CO_Tid_def tps_trans_defs split: txn_state.split_asm)
      apply (meson less_SucI)+
      by (meson linorder_le_less_linear not_less_eq_eq)
  qed (auto simp add: CO_Tid_def tps_trans_defs split: txn_state.split_asm)
qed


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


lemma get_view_update_cls_wtxn_cts_cts_order:
  "\<lbrakk> cl' \<noteq> cl; wtxn_cts s (get_wtxn s cl) = None; Y > gst (cls s cl') \<rbrakk> \<Longrightarrow>
   get_view (s\<lparr> cls := (cls s)(cl := X),
                wtxn_cts := (wtxn_cts s) (get_wtxn s cl \<mapsto> Y),
                cts_order := Z \<rparr>) cl'
  = get_view s cl'"
  by (auto simp add: get_view_def)

lemma get_view_update_svr_prep:
  assumes "cl \<noteq> get_cl_w t"
    "t \<noteq> T0"
    "cl_state (cls s (get_cl_w t)) = WtxnPrep kv_map'"
    "cl_sn (cls s (get_cl_w t)) = get_sn_w t"
    "Wtxn_Cts_None s"
  shows "get_view (s\<lparr>svrs := (svrs s)
                   (k := svrs s k
                      \<lparr>svr_state := (svr_state (svrs s k))(t := Prep ts v),
                       svr_clock := clk \<rparr>)\<rparr>) cl 
       = get_view s cl"
  using assms
  apply (auto simp add: get_view_def wtxns_dom_def)
  apply (intro ext)
  by auto

lemma get_view_update_svr_commit:
   "cl \<noteq> get_cl_w t \<Longrightarrow>
    svr_state (svrs s k) t = Prep ts v \<Longrightarrow>
    get_view (s\<lparr>svrs := (svrs s)
                   (k := svrs s k
                      \<lparr>svr_state := (svr_state (svrs s k))(t := Commit cts sts lst v rs),
                       svr_clock := clk,
                       svr_lst := sclk \<rparr>)\<rparr>) cl
 = get_view s cl"
  apply (auto simp add: get_view_def wtxns_dom_def)
  apply (intro ext)
  by auto


lemmas get_view_update_lemmas = 
  get_view_update_cls get_view_update_cls_rtxn_rts get_view_update_cls_wtxn_cts_cts_order
  get_view_update_svr_wtxns_dom get_view_update_svr_prep get_view_update_svr_commit


(***********************)

subsection \<open>Commutativity proofs\<close>

\<comment> \<open>read_invoke\<close>
lemma read_invoke_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys sn) (RInvoke cl' keys' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_invoke_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys sn) (Read cl' k' v' t' rts' rlst' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_invoke_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys sn) (RDone cl' kv_map' sn' u''')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_invoke_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys sn) (WInvoke cl' kv_map' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_invoke_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys sn) (WCommit cl' kv_map' cts' sn' u''')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_invoke_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys sn) (WDone cl' kv_map' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist ext)

lemma read_invoke_register_read_indep:
  "left_commute tps (RInvoke cl keys sn) (RegR k' t' i' rts')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma read_invoke_prepare_write_indep:
  "left_commute tps (RInvoke cl keys sn) (PrepW k' t' v')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma read_invoke_commit_write_indep:
  "left_commute tps (RInvoke cl keys sn) (CommitW k' t' v' cts')"
  by (auto simp add: left_commute_def tps_trans_defs)


\<comment> \<open>read\<close>

lemma read_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst sn) (RInvoke cl' keys' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst sn) (Read cl' k' v' t' rts' rlst' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst sn) (RDone cl' kv_map' sn' u''')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst sn) (WInvoke cl' kv_map' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst sn) (WCommit cl' kv_map' cts' sn' u''')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t rts rlst sn) (WDone cl' kv_map' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist ext)

lemma read_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (Read cl k v t_wr rts rlst sn) (RegR k' t' t_wr' rts')"
  by (auto simp add: left_commute_def tps_trans_defs add_to_readerset_def split: ver_state.split)

lemma read_prepare_write_indep:
  "left_commute tps (Read cl k v t rts rlst sn) (PrepW k' t' v')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma read_commit_write_indep:
  "left_commute tps (Read cl k v t rts rlst sn) (CommitW k' t' v' cts')"
  by (auto simp add: left_commute_def tps_trans_defs)


\<comment> \<open>read_done\<close>

lemma read_done_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (RInvoke cl' keys' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_done_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (Read cl' k' v' t' rts' rlst' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_done_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (RDone cl' kv_map' sn' u''')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_done_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (WInvoke cl' kv_map' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_done_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (WCommit cl' kv_map' cts' sn' u''')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_done_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'') (WDone cl' kv_map' sn')"
  apply (auto simp add: left_commute_def tps_trans_defs fun_upd_twist global_conf_rtxn_cls_twisted_update_cong)
  apply (intro global_conf.unfold_congs, simp_all)
  by (intro fun_upd2_cong cl_conf.fold_congs, auto)

lemma read_done_register_read_indep:
  "left_commute tps (RDone cl kv_map sn u'') (RegR k' t' t_wr' rts')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma read_done_prepare_write_indep:
  "left_commute tps (RDone cl kv_map sn u'') (PrepW k' t' v')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma read_done_commit_write_indep:
  "left_commute tps (RDone cl kv_map sn u'') (CommitW k' t' v' cts')"
  by (auto simp add: left_commute_def tps_trans_defs)


\<comment> \<open>write_invoke\<close>

lemma write_invoke_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map sn) (RInvoke cl' keys' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma write_invoke_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map sn) (Read cl' k' v' t' rts' rlst' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma write_invoke_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map sn) (RDone cl' kv_map' sn' u''')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma write_invoke_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map sn) (WInvoke cl' kv_map' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma write_invoke_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map sn) (WCommit cl' kv_map' cts' sn' u''')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)
  

lemma write_invoke_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map sn) (WDone cl' kv_map' sn')"
  by (auto simp add: left_commute_def tps_trans_defs ext)

lemma write_invoke_register_read_indep:
  "left_commute tps (WInvoke cl kv_map sn) (RegR k' t' t_wr' rts')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma write_invoke_prepare_write_indep:
  "left_commute tps (WInvoke cl kv_map sn) (PrepW k' t' v')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma write_invoke_commit_write_indep:
  "left_commute tps (WInvoke cl kv_map sn) (CommitW k' t' v' cts')"
  by (auto simp add: left_commute_def tps_trans_defs)


\<comment> \<open>write_commit\<close>

lemma write_commit_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (RInvoke cl' keys' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma write_commit_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (Read cl' k' v' t' rts' rlst' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma write_commit_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (RDone cl' kv_map' sn' u''')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma write_commit_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (WInvoke cl' kv_map' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma insort_key_same_f:
  "\<forall>t. t \<noteq> new_t \<longrightarrow> f' t = f t \<Longrightarrow> new_t \<notin> set corder \<Longrightarrow> t \<noteq> new_t \<Longrightarrow>
    insort_key f' t corder = insort_key f t corder"
  by (induction corder, auto)

lemma insort_key_comm':
  "t1 \<notin> set corder \<Longrightarrow> t1 \<noteq> t2 \<Longrightarrow> f t2 \<noteq> X \<Longrightarrow>
   insort_key (f (t1 := X)) t1 (insort_key f t2 corder) =
   insort_key (f (t1 := X)) t2 (insort_key (f (t1 := X)) t1 corder)"
  apply (induction corder, auto)
  by (metis fun_upd_def insort_key_left_comm remove1_insort_key)+

lemma timestamp_update:
  "t1 \<noteq> t2 \<Longrightarrow>
   (\<lambda>t. (the (if t = t2 then Some Y else wtxn_cts s t), Z t))(t1 := (X, Z t1)) =
   (\<lambda>t. (the (if t = t2 then Some Y else (wtxn_cts s(t1 \<mapsto> X)) t), Z t))"
  by auto

lemma insort_key_twist:
  "t1 \<noteq> t2 \<Longrightarrow> t1 \<notin> set corder \<Longrightarrow> t2 \<notin> set corder \<Longrightarrow> (Y, Z t2) \<noteq> (X, Z t1) \<Longrightarrow>
    insort_key (\<lambda>t. (the (if t = t2 then Some Y else (wtxn_cts s(t1 \<mapsto> X)) t), Z t)) t1
      (insort_key (\<lambda>t. (the (if t = t2 then Some Y else wtxn_cts s t), Z t)) t2 corder) =
    insort_key (\<lambda>t. (the (if t = t2 then Some Y else (wtxn_cts s(t1 \<mapsto> X)) t), Z t)) t2
      (insort_key (\<lambda>t. (the (if t = t1 then Some X else wtxn_cts s t), Z t)) t1 corder)"
  using insort_key_comm'[of t1 corder t2 "\<lambda>t. (the (if t = t2 then Some Y else wtxn_cts s t), Z t)"
      "(X, Z t1)"]
  apply (auto simp add: timestamp_update)
  apply (intro arg_cong[where f="insort_key _ t2"])
  by (smt (verit, ccfv_SIG) fun_upd_other insort_key_same_f map_upd_Some_unfold)+

lemma ext_corder_twist:
  "t1 \<noteq> t2 \<Longrightarrow> \<forall>k. t1 \<notin> set (corder k) \<Longrightarrow> \<forall>k. t2 \<notin> set (corder k) \<Longrightarrow> (Y, Z t2) \<noteq> (X, Z t1) \<Longrightarrow>
   ext_corder t1 kv_map (\<lambda>t. (the (if t = t2 then Some Y else (wtxn_cts s(t1 \<mapsto> X)) t), Z t))
     (ext_corder t2 kv_map'
       (\<lambda>t. (the (if t = t2 then Some Y else wtxn_cts s t), Z t)) corder) =
   ext_corder t2 kv_map' (\<lambda>t. (the (if t = t2 then Some Y else (wtxn_cts s(t1 \<mapsto> X)) t), Z t))
     (ext_corder t1 kv_map
       (\<lambda>t. (the (if t = t1 then Some X else wtxn_cts s t), Z t)) corder)"
  apply (simp add: ext_corder_def)
  apply (rule ext, simp, rule conjI)
   apply (smt (verit, ccfv_SIG) fun_upd_other insort_key_same_f)
  apply (rule impI, rule conjI)
   apply (smt (verit, best) fun_upd_other fun_upd_same insort_key_same_f)
  apply (rule impI, rule conjI)
   apply (metis option.distinct(1))
  apply (rule conjI, rule impI)
   apply (metis option.distinct(1))
  using insort_key_twist by blast

lemma write_commit_write_commit_indep:    
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s by (auto simp add: tps_trans_defs fun_upd_twist)
  subgoal for s by (auto simp add: tps_trans_defs fun_upd_twist)
  apply (auto simp add: tps_trans_defs fun_upd_twist)
  apply (intro global_conf.unfold_congs, simp_all add: unique_ts_def)
  subgoal for s
    using ext_corder_twist[of "get_wtxn s cl" "get_wtxn s cl'" "cts_order s"
       "Max {get_ts (svr_state (svrs s k) (get_wtxn s cl')) |k. k \<in> dom kv_map'}"
       "\<lambda>t. if t = T0 then 0 else Suc (get_cl_w t)"
       "Max {get_ts (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map}"
       kv_map s kv_map'] CO_Tid_def[of s cl] CO_Tid_def[of s cl']
    by (smt (verit) Suc_inject get_cl_w.simps(2) less_irrefl_nat old.prod.inject reach_co_tid
        txid.distinct(1) txn_state.simps(18))
  done

lemma write_commit_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (WDone cl' kv_map' sn')"
  by (auto simp add: left_commute_def tps_trans_defs ext)

lemma write_commit_register_read_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (RegR k' t' t_wr' rts')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  apply (auto simp add: tps_trans_GU_defs)
  subgoal
    by (smt (verit, ccfv_SIG) add_to_readerset_prep_inv domI option.sel svr_conf.select_convs(1) 
            svr_conf.surjective svr_conf.update_convs(1) svr_conf.update_convs(2))
  subgoal
    by (metis add_to_readerset_pres_get_ts) 
  done

lemma write_commit_prepare_write_indep:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (PrepW k' t' v')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  apply (auto simp add: tps_trans_GU_defs)
  subgoal
    by (smt (verit, ccfv_SIG) domI fun_upd_other option.sel svr_conf.select_convs(1)
          svr_conf.surjective svr_conf.update_convs(1) svr_conf.update_convs(2) txid.inject)
  subgoal 
    by metis
  done

lemma write_commit_commit_write_indep:   
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'') (CommitW k' t' v' cts')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: tps_trans_GU_defs)
    subgoal 
      by (smt (verit, ccfv_SIG) domI fun_upd_other option.sel svr_conf.select_convs(1) 
              svr_conf.simps(7) svr_conf.surjective svr_conf.update_convs(1-2) txid.inject) 
    subgoal
      by metis
    done

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    by (simp add: write_commit_U_def commit_write_U_def)

  done

\<comment> \<open>write_done\<close>

lemma write_done_read_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map sn) (RInvoke cl' keys' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist ext)

lemma write_done_read_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map sn) (Read cl' k' v' t' rts' rlst' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist ext)

lemma write_done_read_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map sn) (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_defs fun_upd_twist global_conf_rtxn_cls_twisted_update_cong)
  apply (intro global_conf.unfold_congs, simp_all)
  by (intro fun_upd2_cong cl_conf.fold_congs, auto)

lemma write_done_write_invoke_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map sn) (WInvoke cl' kv_map' sn')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist ext)

lemma write_done_write_commit_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map sn) (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_defs fun_upd_twist global_conf_wtxn_cts_cls_twisted_update_cong)
  by (intro global_conf.unfold_congs fun_upd2_cong cl_conf.fold_congs, auto)

lemma write_done_write_done_indep:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map sn) (WDone cl' kv_map' sn')"
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
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WDone cl kv_map sn) (RegR k' t' t_wr' rts')"
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
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WDone cl kv_map sn) (PrepW k' t' v')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: tps_trans_GU_defs)
    by (smt (verit, ccfv_SIG) domI fun_upd_apply get_cl_w.simps(2) option.inject svr_conf.select_convs(1) 
            svr_conf.simps(5) svr_conf.simps(6) svr_conf.simps(7) svr_conf.surjective txid0.collapse)

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
  "\<lbrakk> cl \<noteq> get_cl t' \<rbrakk>
  \<Longrightarrow> left_commute tps (WDone cl kv_map sn) (CommitW k' t' v' cts')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: tps_trans_GU_defs) 
    by (smt (verit) domI fun_upd_apply get_cl_w.simps(2) option.sel svr_conf.select_convs(1) 
        svr_conf.simps(5) svr_conf.simps(6) svr_conf.simps(7) svr_conf.surjective txid0.collapse)

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    by (auto simp add: tps_trans_GU_defs write_done_commit_write_indep_lemmas)  (* SLOW *)
  done


\<comment> \<open>register_read\<close>

lemma register_read_read_invoke_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (RInvoke cl' keys' sn')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma register_read_read_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (Read cl' k' v' t' rts' rlst' sn')"
  by (auto simp add: left_commute_def tps_trans_defs add_to_readerset_def split: ver_state.split)

lemma register_read_read_done_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)
  done 

lemma register_read_write_invoke_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (WInvoke cl' kv_map' sn')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma register_read_write_commit_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (simp_all add: tps_trans_GU_defs)

  subgoal for s
    apply (auto simp add: tps_trans_GU_defs)

    subgoal for keys kv_map v
      by (metis add_to_readerset_prep_inv domIff option.inject option.simps(3))

    subgoal for keys kv_map
      by (metis add_to_readerset_pres_get_ts)
    done

  subgoal for s
    by (simp_all add: tps_trans_GU_defs)
  done


lemma register_read_write_done_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts) (WDone cl' kv_map' sn')"
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
             split: if_split_asm ver_state.split) (* SLOW *)
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
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (RInvoke cl' keys' sn')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma prepare_write_read_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (Read cl' k' v' t' rts' rlst' sn')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma prepare_write_read_done_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute_def read_done_def prepare_write_def)
  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    by (auto simp add: tps_trans_defs)

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)
  done 

lemma prepare_write_write_invoke_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (WInvoke cl' kv_map' sn')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma prepare_write_write_commit_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: tps_trans_GU_defs)
  
  subgoal for s
    apply (auto simp add: tps_trans_GU_defs)
    by metis

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)
  done

lemma prepare_write_write_done_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v) (WDone cl' kv_map' sn')"
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
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (RInvoke cl' keys' sn')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma commit_write_read_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (Read cl' k' v' t' rts' rlst' sn')"
  by (auto simp add: left_commute_def tps_trans_defs) 

lemma commit_write_read_done_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (RDone cl' kv_map' sn' u''')"
  apply (auto simp add: left_commute_def read_done_def commit_write_def)
  subgoal for s
    by (auto simp add: tps_trans_defs)

  subgoal for s
    by (auto simp add: tps_trans_defs)

  subgoal for s
    by (auto simp add: tps_trans_defs)
  done 

lemma commit_write_write_invoke_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (WInvoke cl' kv_map' sn')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma commit_write_write_commit_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (WCommit cl' kv_map' cts' sn' u''')"
  apply (auto simp add: left_commute_def tps_trans_top_defs) 
  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    apply (auto simp add: tps_trans_GU_defs)
    by metis+

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)
  done

lemma commit_write_write_done_indep:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts) (WDone cl' kv_map' sn')"
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


\<comment> \<open>Skip\<close>
lemma skip_e_indep:
  "left_commute tps Skip2 e"
  by (auto simp add: left_commute_def)

lemma e_skip_indep:
  "left_commute tps e Skip2"
  by (auto simp add: left_commute_def)


(***********************)

subsection \<open>Reduction\<close>

fun ev_cl :: "'v ev \<Rightarrow> cl_id" where
  "ev_cl (RInvoke cl keys sn)           = cl" |
  "ev_cl (Read cl k v t rts rlst sn)    = cl" |
  "ev_cl (RDone cl kv_map sn u'')       = cl" |
  "ev_cl (WInvoke cl kv_map sn)         = cl" |
  "ev_cl (WCommit cl kv_map cts sn u'') = cl" |
  "ev_cl (WDone cl kv_map sn)           = cl" |
  "ev_cl (RegR svr t t_wr rts)          = get_cl t" |
  "ev_cl (PrepW svr t v)                = get_cl t" |
  "ev_cl (CommitW svr t v cts)          = get_cl t" |
  "ev_cl Skip2                          = 0" \<comment> \<open>dummy value\<close>

fun ev_key :: "'v ev \<Rightarrow> key option" where
  "ev_key (RegR svr t t_wr rts)         = Some svr" |
  "ev_key (PrepW svr t v)               = Some svr" |
  "ev_key (CommitW svr t v cts)         = Some svr" |
  "ev_key _ = None"

fun ev_ects :: "'v ev \<Rightarrow> (tstmp \<times> cl_id) option" where
  "ev_ects (WCommit cl kv_map cts sn u'') = Some (ects cts cl)" |
  "ev_ects _ = None"

\<comment> \<open>still needed?\<close>
fun ev_txn :: "'v ev \<Rightarrow> txid0" where
  "ev_txn (RInvoke cl keys sn)           = Tn_cl sn cl" |
  "ev_txn (Read cl k v t rts rlst sn)    = Tn_cl sn cl" |
  "ev_txn (RDone cl kv_map sn u'')       = Tn_cl sn cl" |
  "ev_txn (WInvoke cl kv_map sn)         = Tn_cl sn cl" |
  "ev_txn (WCommit cl kv_map cts sn u'') = Tn_cl sn cl" |
  "ev_txn (WDone cl kv_map sn)           = Tn_cl sn cl" |
  "ev_txn (RegR svr t t_wr rts)          = t" |
  "ev_txn (PrepW svr t v)                = t" |
  "ev_txn (CommitW svr t v cts)          = t" |
  "ev_txn Skip2                          = Tn_cl 0 0" \<comment> \<open>dummy value\<close>

datatype movt = Lm | Rm

definition mover_type :: "'v ev list \<Rightarrow> nat \<Rightarrow> movt" where
  "mover_type tr i \<equiv> (let e = tr ! i in
    (if ev_cl e = ev_cl (hd tr) then Rm else
     (if ev_cl e = ev_cl (last tr) then Lm else
      (if (\<exists>j l. l < j \<and> j \<le> i \<and>
            ev_cl (tr ! j) = ev_cl (tr ! i) \<and>
            ev_cl (tr ! l) = ev_cl (hd tr) \<and>
            ev_key (tr ! l) = ev_key (tr ! j) \<and> ev_key (tr ! j) \<noteq> None) then Rm else Lm)))
  )"

definition Lm_dist_left where
  "Lm_dist_left i j tr \<equiv>
    Sum {d | d. mover_type (take (Suc (j - i)) (drop i tr)) d = Lm}"

definition left_most_pair :: "'v ev list \<Rightarrow> (nat \<times> nat)" where
  "left_most_pair tr \<equiv> (ARG_MIN (fst) (i, j). (i, j) \<in> inverted_pairs ev_ects tr \<and>
    (\<forall>l. i < l \<and> l < j \<longrightarrow>
      (i, l) \<notin> inverted_pairs ev_ects tr \<and>
      (l, j) \<notin> inverted_pairs ev_ects tr))"

definition lmp_dist_left :: "('v ev, ('v, 'm) global_conf_scheme) exec_frag \<Rightarrow> nat" where
  "lmp_dist_left ef \<equiv>
    let (i, j) = left_most_pair (trace_of_efrag ef) in
      Lm_dist_left i j (trace_of_efrag ef)"

definition measure_R :: "('v ev, ('v, 'm) global_conf_scheme) exec_frag rel" where
  "measure_R \<equiv> measures [card o inverted_pairs ev_ects o trace_of_efrag, lmp_dist_left]"


end