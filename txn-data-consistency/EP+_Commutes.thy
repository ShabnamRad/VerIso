section \<open>Event commutes for EP+\<close>

theory "EP+_Commutes"
  imports "EP+" "EP+_Trace" Reductions
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
  "add_to_readerset wtxns t rclk rlst t' t'' = No_Ver \<longleftrightarrow> wtxns t'' = No_Ver"
  by (simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_prep_inv:
  "add_to_readerset wtxns t rclk rlst t' t'' = Prep ts v \<longleftrightarrow> wtxns t'' = Prep ts v"
  by (simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_commit:
  "add_to_readerset wtxns t rclk rlst t' t'' = Commit cts sts lst v rs \<Longrightarrow>
    \<exists>rs'. wtxns t'' = Commit cts sts lst v rs'"
  apply (simp add: add_to_readerset_def)
  by (cases "wtxns t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_pres_get_ts:
  "get_ts (add_to_readerset wtxns t rclk rlst t_wr t') = get_ts (wtxns t')"
  by (smt (verit, ccfv_SIG) add_to_readerset_commit add_to_readerset_no_ver_inv
      add_to_readerset_prep_inv ver_state.exhaust_sel ver_state.sel(2))

lemma add_to_readerset_pres_is_committed:
  "is_committed (add_to_readerset wtxns t rclk rlst t_wr t') = is_committed (wtxns t')"
  by (smt (verit, best) add_to_readerset_no_ver_inv add_to_readerset_prep_inv is_committed.elims(1))

lemma add_to_readerset_pres_at:
  "at (add_to_readerset wtxns t rclk rlst t_wr) ts = at wtxns ts"
  by (simp add: at_def ver_committed_before_def add_to_readerset_pres_get_ts o_def
      add_to_readerset_pres_is_committed)

lemma add_to_readerset_pres_newest_own_write:
  "newest_own_write (add_to_readerset wtxns t rclk rlst t_wr) ts cl = newest_own_write wtxns ts cl"
  by (auto simp add: newest_own_write_def ver_committed_after_def add_to_readerset_pres_get_ts o_def
      add_to_readerset_pres_is_committed)

lemma add_to_readerset_pres_read_at:
  "read_at (add_to_readerset wtxns t rclk rlst t_wr) ts cl = read_at wtxns ts cl"
  by (simp add: read_at_def add_to_readerset_pres_at add_to_readerset_pres_get_ts
      add_to_readerset_pres_newest_own_write)


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
lemma read_invoke_read_invoke_commute:
  "left_commute tps (RInvoke cl keys sn clk) (RInvoke cl' keys' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_invoke_read_commute:
  "left_commute tps (RInvoke cl keys sn clk) (Read cl' k' v' t' sn' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_invoke_read_done_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys sn clk) (RDone cl' kv_map' sn' u''' clk')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_invoke_write_invoke_commute:
  "left_commute tps (RInvoke cl keys sn clk) (WInvoke cl' kv_map' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_invoke_write_commit_commute:
  "left_commute tps (RInvoke cl keys sn clk) (WCommit cl' kv_map' cts' sn' u''' clk' mmap')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist) (* SLOW, ~10s *)

lemma read_invoke_write_done_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RInvoke cl keys sn clk) (WDone cl' kv_map' sn' clk' mmap')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist ext)

lemma read_invoke_register_read_commute:
  "left_commute tps (RInvoke cl keys sn clk) (RegR k' t' t_wr' rts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma read_invoke_prepare_write_commute:
  "left_commute tps (RInvoke cl keys sn clk) (PrepW k' t' v' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma read_invoke_commit_write_commute:
  "left_commute tps (RInvoke cl keys sn clk) (CommitW k' t' v' cts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs)


\<comment> \<open>read\<close>

lemma read_read_invoke_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t sn clk m) (RInvoke cl' keys' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_read_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t sn clk m) (Read cl' k' v' t' sn' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_read_done_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t sn clk m) (RDone cl' kv_map' sn' u''' clk')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_write_invoke_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t sn clk m) (WInvoke cl' kv_map' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_write_commit_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t sn clk m) (WCommit cl' kv_map' cts' sn' u''' clk' mmap')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_write_done_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (Read cl k v t sn clk m) (WDone cl' kv_map' sn' clk' mmap')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist ext)

lemma read_register_read_commute:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (Read cl k v t sn clk m) (RegR k' t' t_wr' rts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs add_to_readerset_def split: ver_state.split)

lemma read_prepare_write_commute:
  "left_commute tps (Read cl k v t sn clk m) (PrepW k' t' v' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma read_commit_write_commute:
  "left_commute tps (Read cl k v t sn clk m) (CommitW k' t' v' cts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs)


\<comment> \<open>read_done\<close>

lemma read_done_read_invoke_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'' clk) (RInvoke cl' keys' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_done_read_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'' clk) (Read cl' k' v' t' sn' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_done_read_done_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'' clk) (RDone cl' kv_map' sn' u''' clk')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_done_write_invoke_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'' clk) (WInvoke cl' kv_map' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_done_write_commit_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'' clk) (WCommit cl' kv_map' cts' sn' u''' clk' mmap')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma read_done_write_done_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (RDone cl kv_map sn u'' clk) (WDone cl' kv_map' sn' clk' mmap')"
  apply (auto simp add: left_commute_def tps_trans_defs fun_upd_twist global_conf_rtxn_cls_twisted_update_cong)
  apply (intro global_conf.unfold_congs, simp_all)
  by (intro fun_upd2_cong cl_conf.fold_congs, auto)

lemma read_done_register_read_commute:
  "left_commute tps (RDone cl kv_map sn u'' clk) (RegR k' t' t_wr' rts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma read_done_prepare_write_commute:
  "left_commute tps (RDone cl kv_map sn u'' clk) (PrepW k' t' v' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma read_done_commit_write_commute:
  "left_commute tps (RDone cl kv_map sn u'' clk) (CommitW k' t' v' cts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs)


\<comment> \<open>write_invoke\<close>

lemma write_invoke_read_invoke_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map sn clk) (RInvoke cl' keys' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma write_invoke_read_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map sn clk) (Read cl' k' v' t' sn' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma write_invoke_read_done_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map sn clk) (RDone cl' kv_map' sn' u''' clk')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma write_invoke_write_invoke_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map sn clk) (WInvoke cl' kv_map' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma write_invoke_write_commit_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map sn clk) (WCommit cl' kv_map' cts' sn' u''' clk' mmap')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)
  

lemma write_invoke_write_done_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WInvoke cl kv_map sn clk) (WDone cl' kv_map' sn' clk' mmap')"
  by (auto simp add: left_commute_def tps_trans_defs ext)

lemma write_invoke_register_read_commute:
  "left_commute tps (WInvoke cl kv_map sn clk) (RegR k' t' t_wr' rts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma write_invoke_prepare_write_commute:
  "left_commute tps (WInvoke cl kv_map sn clk) (PrepW k' t' v' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma write_invoke_commit_write_commute:
  "left_commute tps (WInvoke cl kv_map sn clk) (CommitW k' t' v' cts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs)


\<comment> \<open>write_commit\<close>

lemma write_commit_read_invoke_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'' clk mmap) (RInvoke cl' keys' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma write_commit_read_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'' clk mmap) (Read cl' k' v' t' sn' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma write_commit_read_done_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'' clk mmap) (RDone cl' kv_map' sn' u''' clk')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma write_commit_write_invoke_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'' clk mmap) (WInvoke cl' kv_map' sn' clk')"
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

lemma write_commit_write_commit_commute:    
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'' clk mmap) (WCommit cl' kv_map' cts' sn' u''' clk' mmap')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s by (auto simp add: tps_trans_defs fun_upd_twist)
  subgoal for s by (auto simp add: tps_trans_defs fun_upd_twist)
  apply (auto simp add: tps_trans_defs fun_upd_twist) (* SLOW, ~15s *)
  apply (intro global_conf.unfold_congs, simp_all add: unique_ts_def)
  subgoal for s
    using ext_corder_twist[of "get_wtxn s cl" "get_wtxn s cl'" "cts_order s"
       "max (cl_clock (cls s cl')) (Max {get_ts (svr_state (svrs s k) (get_wtxn s cl')) |k. k \<in> dom kv_map'})"
       "\<lambda>t. if t = T0 then 0 else Suc (get_cl_w t)"
       "max (cl_clock (cls s cl)) (Max {get_ts (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map})"
       kv_map s kv_map'] CO_Tid_def[of s cl] CO_Tid_def[of s cl']
    by (smt (verit) Suc_inject get_cl_w.simps(2) less_irrefl_nat old.prod.inject reach_co_tid
        txid.distinct(1) txn_state.simps(18))
  done

lemma write_commit_write_done_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'' clk mmap) (WDone cl' kv_map' sn' clk' mmap')"
  by (auto simp add: left_commute_def tps_trans_defs ext)

lemma write_commit_register_read_commute:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'' clk mmap) (RegR k' t' t_wr' rts' clk' lst' m')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
  apply (auto simp add: write_commit_G_def register_read_U_def)
    subgoal
      by (smt (verit, ccfv_SIG) add_to_readerset_prep_inv domI option.sel svr_conf.select_convs(1) 
              svr_conf.surjective svr_conf.update_convs(1) svr_conf.update_convs(2))

    subgoal using add_to_readerset_pres_get_ts[of "(svr_state (svrs s k'))"]
      apply (intro ext) subgoal for x by (cases "kv_map x", auto).
      
    subgoal by (metis add_to_readerset_pres_get_ts)
    done

  subgoal for s
    by (auto simp add: write_commit_U_def register_read_G_def)

  subgoal for s
    by (simp add: write_commit_U_def register_read_U_def)
  done

lemma write_commit_prepare_write_commute:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'' clk mmap) (PrepW k' t' v' clk' m')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: write_commit_G_def prepare_write_U_def)
    subgoal
      by (smt (verit, ccfv_SIG) domI fun_upd_other option.sel svr_conf.select_convs(1)
            svr_conf.surjective svr_conf.update_convs(1) svr_conf.update_convs(2) txid.inject)
    subgoal 
      by metis
    done

  subgoal for s
    by (auto simp add: write_commit_U_def prepare_write_G_def)

  subgoal for s
    by (simp add: write_commit_U_def prepare_write_U_def)
  done

lemma write_commit_commit_write_commute:   
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'' clk mmap) (CommitW k' t' v' cts' clk' lst' m')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: write_commit_G_def write_commit_U_def commit_write_U_def)
    subgoal 
      by (smt (verit, ccfv_SIG) domI fun_upd_other option.sel svr_conf.select_convs(1) 
              svr_conf.simps(7) svr_conf.surjective svr_conf.update_convs(1-2) txid.inject) 
    subgoal
      by metis
    done

  subgoal for s
    by (auto simp add: write_commit_U_def commit_write_G_def)

  subgoal for s
    by (simp add: write_commit_U_def commit_write_U_def)

  done

\<comment> \<open>write_done\<close>

lemma write_done_read_invoke_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map sn clk mmap) (RInvoke cl' keys' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist ext)

lemma write_done_read_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map sn clk mmap) (Read cl' k' v' t' sn' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist ext)

lemma write_done_read_done_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map sn clk mmap) (RDone cl' kv_map' sn' u''' clk')"
  apply (auto simp add: left_commute_def tps_trans_defs fun_upd_twist global_conf_rtxn_cls_twisted_update_cong)
  apply (intro global_conf.unfold_congs, simp_all)
  by (intro fun_upd2_cong cl_conf.fold_congs, auto)

lemma write_done_write_invoke_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map sn clk mmap) (WInvoke cl' kv_map' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist ext)

lemma write_done_write_commit_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map sn clk mmap) (WCommit cl' kv_map' cts' sn' u''' clk' mmap')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: write_done_G_def write_commit_U_def clk_WDone_def)

  subgoal for s
    by (auto simp add: write_done_U_def write_commit_G_def)
  
  subgoal for s
    apply (auto simp add: write_done_U_def write_commit_U_def fun_upd_twist global_conf_wtxn_cts_cls_twisted_update_cong)
    by (intro global_conf.unfold_congs fun_upd2_cong cl_conf.fold_congs, auto)
  done

lemma write_done_write_done_commute:
  "cl \<noteq> cl' \<Longrightarrow> left_commute tps (WDone cl kv_map sn clk mmap) (WDone cl' kv_map' sn' clk' mmap')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist ext)

lemma write_done_server_ev_indep_L:
  "{u.
      \<exists>k. (k = k' \<longrightarrow> u = get_sclk (svr_state (svrs s k') (get_wtxn s cl)) \<and> 
                      k' \<in> dom kv_map) \<and>
          (k \<noteq> k' \<longrightarrow> u = get_sclk (svr_state (svrs s k) (get_wtxn s cl)) \<and> k \<in> dom kv_map)} = 
   {get_sclk (svr_state (svrs s k) (get_wtxn s cl)) |k. k \<in> dom kv_map}"
  by auto

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
                     svr_state := (svr_state (svrs s k')) (t_wr := Commit cts sts lst v (rs (Y \<mapsto> (x, y)))),
                     svr_clock := B\<rparr>)\<rparr>) k)
                  (get_wtxn (s\<lparr>svrs := (svrs s)(k' := X)\<rparr>) cl))) = 
    (if kv_map k = None 
     then lst_map (cls s cl) k 
     else get_lst (svr_state (svrs s k) (get_wtxn s cl)))"
  by auto

lemmas write_done_register_read_indep_lemmas = 
  write_done_server_ev_indep_L write_done_register_read_indep_L1
  write_done_register_read_indep_L2 write_done_register_read_indep_L3

lemma write_done_register_read_commute:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WDone cl kv_map sn clk mmap) (RegR k' t' t_wr' rts' clk' lst' m')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: write_done_G_def register_read_G_def register_read_U_def clk_WDone_def
        add_to_readerset_def write_done_register_read_indep_L1 split: if_split_asm ver_state.split)
    apply (metis (no_types, opaque_lifting) domI option.inject)
    apply (metis (no_types, opaque_lifting) domI option.inject)
    by metis

  subgoal for s
    by (auto simp add: write_done_U_def register_read_G_def)

  subgoal for s
    by (auto simp add: write_done_U_def register_read_U_def add_to_readerset_def
        write_done_register_read_indep_lemmas split: if_split_asm ver_state.split)
  done


lemma write_done_prepare_write_indep_L2:
   "get_cl t' \<noteq> cl \<Longrightarrow>
    (if kv_map k = None
     then lst_map (cls (s\<lparr>svrs := Z\<rparr>) cl) k
     else get_lst (svr_state (svrs (s\<lparr>svrs := (svrs s)(k' := svrs s k'\<lparr>
                     svr_state := (svr_state (svrs s k'))(Tn t' := A),
                     svr_clock := B\<rparr>)\<rparr>) k)
                  (get_wtxn (s\<lparr>svrs := (svrs s)(k' := X)\<rparr>) cl))) = 
    (if kv_map k = None 
     then lst_map (cls s cl) k 
     else get_lst (svr_state (svrs s k) (get_wtxn s cl)))"
  by auto

lemma prepare_write_preserves_clk_WDone:
  "get_txn s cl' \<noteq> t
  \<Longrightarrow> clk_WDone cl' clk' mmap' s 
  \<Longrightarrow> clk_WDone cl' clk' mmap'
        (s\<lparr>svrs := (svrs s)
          (k := svrs s k
             \<lparr>svr_state := (svr_state (svrs s k))(Tn t := X),
                svr_clock := Y\<rparr>)\<rparr>)"
  by (simp add: clk_WDone_def write_done_server_ev_indep_L)

lemmas write_done_prepare_write_indep_lemmas = 
  write_done_server_ev_indep_L write_done_prepare_write_indep_L2
  prepare_write_preserves_clk_WDone

lemma write_done_prepare_write_commute:
  "cl \<noteq> get_cl t' \<Longrightarrow> left_commute tps (WDone cl kv_map sn clk mmap) (PrepW k' t' v' clk' m')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: write_done_G_def prepare_write_U_def clk_WDone_def)
    apply (smt (verit, ccfv_SIG) domI fun_upd_apply get_cl_w.simps(2) option.inject svr_conf.select_convs(1) 
            svr_conf.simps(5) svr_conf.simps(6) svr_conf.simps(7) svr_conf.surjective txid0.collapse)
    by metis

  subgoal for s
    by (auto simp add: write_done_U_def prepare_write_G_def)

  subgoal for s
    by (auto simp add: write_done_U_def prepare_write_U_def write_done_prepare_write_indep_lemmas)
  done

lemma write_done_commit_write_indep_L2:
   "get_cl t' \<noteq> cl \<Longrightarrow>
    (if kv_map k = None
     then lst_map (cls (s\<lparr>svrs := Z\<rparr>) cl) k
     else get_lst (svr_state (svrs (s\<lparr>svrs := (svrs s)(k' := svrs s k'\<lparr>
                     svr_state := (svr_state (svrs s k'))(Tn t' := A),
                     svr_clock := B, 
                     svr_lst := C\<rparr>)\<rparr>) k)
                  (get_wtxn (s\<lparr>svrs := (svrs s)(k' := X)\<rparr>) cl))) = 
    (if kv_map k = None 
     then lst_map (cls s cl) k 
     else get_lst (svr_state (svrs s k) (get_wtxn s cl)))"
  by auto

lemma commit_write_preserves_clk_WDone:
  "get_txn s cl' \<noteq> t
  \<Longrightarrow> clk_WDone cl' kv_map' clk' s 
  \<Longrightarrow> clk_WDone cl' kv_map' clk'
        (s\<lparr>svrs := (svrs s)
          (k := svrs s k
             \<lparr>svr_state := (svr_state (svrs s k))(Tn t := X),
              svr_clock := Y,
              svr_lst := Z\<rparr>)\<rparr>)"
  by (simp add: clk_WDone_def write_done_server_ev_indep_L)

lemmas write_done_commit_write_indep_lemmas = 
  write_done_server_ev_indep_L write_done_commit_write_indep_L2
  commit_write_preserves_clk_WDone

lemma write_done_commit_write_commute:  
  "\<lbrakk> cl \<noteq> get_cl t' \<rbrakk>
  \<Longrightarrow> left_commute tps (WDone cl kv_map sn clk mmap) (CommitW k' t' v' cts' clk' lst' m')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: write_done_G_def commit_write_U_def clk_WDone_def)
    apply (smt (verit) domI fun_upd_apply get_cl_w.simps(2) option.sel svr_conf.select_convs(1) 
        svr_conf.simps(5) svr_conf.simps(6) svr_conf.simps(7) svr_conf.surjective txid0.collapse)
    by metis

  subgoal for s
    by (auto simp add: write_done_G_def write_done_U_def commit_write_G_def)

  subgoal for s
    by (auto simp add: write_done_U_def commit_write_U_def write_done_commit_write_indep_lemmas)
  done


\<comment> \<open>register_read\<close>

lemma register_read_read_invoke_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts clk lst m) (RInvoke cl' keys' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma register_read_read_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts clk lst m) (Read cl' k' v' t' sn' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs add_to_readerset_def split: ver_state.split)

lemma register_read_read_done_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts clk lst m) (RDone cl' kv_map' sn' u''' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma register_read_write_invoke_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts clk lst m) (WInvoke cl' kv_map' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma register_read_write_commit_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts clk lst m) (WCommit cl' kv_map' cts' sn' u''' clk' mmap')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: register_read_G_def write_commit_U_def)

  subgoal for s
    apply (auto simp add: register_read_U_def write_commit_G_def)
    subgoal for v
      by (metis add_to_readerset_prep_inv domI option.inject)

    subgoal
      apply (intro ext)
      subgoal for x by (cases "kv_map' x", auto simp add: add_to_readerset_pres_get_ts).

    subgoal
      by (metis add_to_readerset_pres_get_ts)
    done

  subgoal for s
    by (simp add: register_read_U_def write_commit_U_def)
  done


lemma register_read_write_done_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts clk lst m) (WDone cl' kv_map' sn' clk' mmap')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: register_read_G_def write_done_U_def)

  subgoal for s
    apply (auto simp add: tps_trans_GU_defs add_to_readerset_def split: if_split_asm ver_state.split) (* SLOW, ~20s *)
    apply (metis domI ver_state.sel(2))
    apply (metis domI option.inject ver_state.inject(2))
    apply (metis ver_state.sel(5))
    by metis

  subgoal for s
    by (auto simp add: register_read_U_def write_done_U_def clk_WDone_def add_to_readerset_def
        write_done_register_read_indep_lemmas split: if_split_asm ver_state.split) (* SLOW,  ~10s *)
  done

lemma register_read_register_read_commute:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (RegR k t t_wr rts clk lst m) (RegR k' t' t_wr' rts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma register_read_prepare_write_commute:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (RegR k t t_wr rts clk lst m) (PrepW k' t' v' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma register_read_commit_write_commute:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (RegR k t t_wr rts clk lst m) (CommitW k' t' v' cts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)


\<comment> \<open>prepare_write\<close>

lemma prepare_write_read_invoke_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v clk m) (RInvoke cl' keys' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma prepare_write_read_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v clk m) (Read cl' k' v' t' sn' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma prepare_write_read_done_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v clk m) (RDone cl' kv_map' sn' u''' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma prepare_write_write_invoke_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v clk m) (WInvoke cl' kv_map' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma prepare_write_write_commit_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v clk m) (WCommit cl' kv_map' cts' sn' u''' clk' mmap')"
  apply (auto simp add: left_commute_def tps_trans_defs) by metis

lemma prepare_write_write_done_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (PrepW k t v clk m) (WDone cl' kv_map' sn' clk' mmap')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: prepare_write_G_def write_done_U_def)
    
  subgoal for s
    by (auto simp add: prepare_write_U_def write_done_G_def write_done_prepare_write_indep_lemmas)

  subgoal for s
    by (auto simp add: write_done_U_def prepare_write_U_def write_done_prepare_write_indep_lemmas)
  done

lemma prepare_write_register_read_commute:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (PrepW k t v clk m) (RegR k' t' t_wr' rts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma prepare_write_prepare_write_commute:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (PrepW k t v clk m) (PrepW k' t' v' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma prepare_write_commit_write_commute:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (PrepW k t v clk m) (CommitW k' t' v' cts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

\<comment> \<open>commit_write\<close>

lemma commit_write_read_invoke_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts clk lst m) (RInvoke cl' keys' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma commit_write_read_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts clk lst m) (Read cl' k' v' t' sn' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs) 

lemma commit_write_read_done_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts clk lst m) (RDone cl' kv_map' sn' u''' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma commit_write_write_invoke_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts clk lst m) (WInvoke cl' kv_map' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma commit_write_write_commit_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts clk lst m) (WCommit cl' kv_map' cts' sn' u''' clk' mmap')"
  apply (auto simp add: left_commute_def tps_trans_top_defs) 
  subgoal for s
    by (auto simp add: commit_write_G_def write_commit_U_def)

  subgoal for s
    apply (auto simp add: commit_write_U_def write_commit_G_def)
    by metis

  subgoal for s
    by (auto simp add: commit_write_U_def write_commit_U_def)
  done

lemma commit_write_write_done_commute:
  "get_cl t \<noteq> cl' \<Longrightarrow> left_commute tps (CommitW k t v cts clk lst m) (WDone cl' kv_map' sn' clk' mmap')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: commit_write_G_def write_done_U_def)

  subgoal for s
    by (auto simp add: commit_write_U_def write_done_G_def write_done_commit_write_indep_lemmas)

  subgoal for s 
    by (auto simp add: commit_write_U_def write_done_U_def write_done_commit_write_indep_lemmas)
  done                                                                                                               

lemma commit_write_register_read_commute:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (CommitW k t v cts clk lst m) (RegR k' t' t_wr' rts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma commit_write_prepare_write_commute:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (CommitW k t v cts clk lst m) (PrepW k' t' v' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma commit_write_commit_write_commute:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (CommitW k t v cts clk lst m) (CommitW k' t' v' cts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

end