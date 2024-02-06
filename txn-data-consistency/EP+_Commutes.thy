section \<open>Event commutes for EP+\<close>

theory "EP+_Commutes"
  imports "EP+_Trace"
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
  "add_to_readerset wtxns t rclk rlst t' t'' = Prep pd ts v \<longleftrightarrow> wtxns t'' = Prep pd ts v"
  by (simp add: add_to_readerset_def split: ver_state.split)

lemma add_to_readerset_commit:
  "add_to_readerset wtxns t rclk rlst t' t'' = Commit cts sts lst v rs \<Longrightarrow>
    \<exists>rs'. wtxns t'' = Commit cts sts lst v rs'"
  apply (simp add: add_to_readerset_def)
  by (cases "wtxns t'"; cases "t'' = t'"; auto)

lemma add_to_readerset_pres_get_ts:
  "get_ts (add_to_readerset wtxns t rclk rlst t_wr t') = get_ts (wtxns t')"
  by (smt (verit, ccfv_SIG) add_to_readerset_commit add_to_readerset_no_ver_inv
      add_to_readerset_prep_inv ver_state.exhaust_sel ver_state.sel(3))

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
                      \<lparr>svr_state := (svr_state (svrs s k))(t := Prep pd ts v),
                       svr_clock := clk \<rparr>)\<rparr>) cl 
       = get_view s cl"
  using assms
  apply (auto simp add: get_view_def wtxns_dom_def)
  apply (intro ext)
  by auto

lemma get_view_update_svr_commit:
   "cl \<noteq> get_cl_w t \<Longrightarrow>
    svr_state (svrs s k) t = Prep pd ts v \<Longrightarrow>
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
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: read_invoke_G_def write_commit_U_def)

  subgoal for s
    apply (auto simp add: read_invoke_U_def write_commit_G_def)
    by (auto simp add: read_invoke_G_def write_commit_U_def)

  subgoal for s
    by (auto simp add: read_invoke_G_def read_invoke_U_def write_commit_U_def fun_upd_twist)
  done

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


lemmas read_invoke_commutes = read_invoke_read_invoke_commute read_invoke_read_commute
  read_invoke_read_done_commute read_invoke_write_invoke_commute read_invoke_write_commit_commute
  read_invoke_write_done_commute read_invoke_register_read_commute
  read_invoke_prepare_write_commute read_invoke_commit_write_commute


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
  "t' \<noteq> Tn_cl sn cl \<or> k \<noteq> k' \<Longrightarrow> left_commute tps (Read cl k v t sn clk m) (RegR k' t' t_wr' rts' clk' lst' m')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal by (auto simp add: tps_trans_GU_defs add_to_readerset_def split: if_split_asm)
  by (auto simp add: tps_trans_GU_defs)

lemma read_prepare_write_commute:
  "left_commute tps (Read cl k v t sn clk m) (PrepW k' t' v' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma read_commit_write_commute:
  "left_commute tps (Read cl k v t sn clk m) (CommitW k' t' v' cts' clk' lst' m')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: read_G_def commit_write_U_def split: if_split_asm)

  subgoal for s
    apply (auto simp add: read_G_def commit_write_U_def)
    by (auto simp add: read_U_def commit_write_G_def split: if_split_asm)

  subgoal for s
    by (simp add: read_U_def commit_write_U_def)
  done


lemmas read_commutes = read_read_invoke_commute read_read_commute read_read_done_commute
  read_write_invoke_commute read_write_commit_commute read_write_done_commute
  read_register_read_commute read_prepare_write_commute read_commit_write_commute


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


lemmas read_done_commutes = read_done_read_invoke_commute read_done_read_commute
  read_done_read_done_commute read_done_write_invoke_commute read_done_write_commit_commute
  read_done_write_done_commute read_done_register_read_commute read_done_prepare_write_commute
  read_done_commit_write_commute


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


lemmas write_invoke_commutes = write_invoke_read_invoke_commute write_invoke_read_commute 
  write_invoke_read_done_commute write_invoke_write_invoke_commute write_invoke_write_commit_commute
  write_invoke_write_done_commute write_invoke_register_read_commute 
  write_invoke_prepare_write_commute write_invoke_commit_write_commute


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
   (\<lambda>t. (the (if t = t2 then Some Y else ((wtxn_cts s)(t1 \<mapsto> X)) t), Z t))"
  by auto

lemma insort_key_twist:
  "t1 \<noteq> t2 \<Longrightarrow> t1 \<notin> set corder \<Longrightarrow> t2 \<notin> set corder \<Longrightarrow> (Y, Z t2) \<noteq> (X, Z t1) \<Longrightarrow>
    insort_key (\<lambda>t. (the (if t = t2 then Some Y else ((wtxn_cts s)(t1 \<mapsto> X)) t), Z t)) t1
      (insort_key (\<lambda>t. (the (if t = t2 then Some Y else wtxn_cts s t), Z t)) t2 corder) =
    insort_key (\<lambda>t. (the (if t = t2 then Some Y else ((wtxn_cts s)(t1 \<mapsto> X)) t), Z t)) t2
      (insort_key (\<lambda>t. (the (if t = t1 then Some X else wtxn_cts s t), Z t)) t1 corder)"
  using insort_key_comm'[of t1 corder t2 "\<lambda>t. (the (if t = t2 then Some Y else wtxn_cts s t), Z t)"
      "(X, Z t1)"]
  apply (auto simp add: timestamp_update)
  apply (intro arg_cong[where f="insort_key _ t2"])
  by (smt (verit, ccfv_SIG) fun_upd_other insort_key_same_f map_upd_Some_unfold)+

lemma ext_corder_twist:
  "t1 \<noteq> t2 \<Longrightarrow> \<forall>k. t1 \<notin> set (corder k) \<Longrightarrow> \<forall>k. t2 \<notin> set (corder k) \<Longrightarrow> (Y, Z t2) \<noteq> (X, Z t1) \<Longrightarrow>
   ext_corder t1 kv_map (\<lambda>t. (the (if t = t2 then Some Y else ((wtxn_cts s)(t1 \<mapsto> X)) t), Z t))
     (ext_corder t2 kv_map'
       (\<lambda>t. (the (if t = t2 then Some Y else wtxn_cts s t), Z t)) corder) =
   ext_corder t2 kv_map' (\<lambda>t. (the (if t = t2 then Some Y else ((wtxn_cts s)(t1 \<mapsto> X)) t), Z t))
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
  subgoal for s by (auto simp add: write_commit_G_def write_commit_U_def)
  subgoal for s by (auto simp add: write_commit_G_def write_commit_U_def)
  subgoal for s
    apply (auto simp add: tps_trans_defs fun_upd_twist) (* SLOW, ~15s *)
    apply (intro global_conf.unfold_congs, simp_all add: unique_ts_def)
  
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
  "left_commute tps (WCommit cl kv_map cts sn u'' clk mmap) (RegR k' t' t_wr' rts' clk' lst' m')"
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
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    by (simp add: write_commit_U_def register_read_U_def)
  done

lemma write_commit_prepare_write_commute:
  "t' \<noteq> Tn_cl sn cl \<Longrightarrow> left_commute tps (WCommit cl kv_map cts sn u'' clk mmap) (PrepW k' t' v' clk' m')"
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
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    by (simp add: write_commit_U_def prepare_write_U_def)
  done

lemma write_commit_commit_write_commute:   
  "left_commute tps (WCommit cl kv_map cts sn u'' clk mmap) (CommitW k' t' v' cts' clk' lst' m')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: write_commit_G_def commit_write_U_def)
    apply (simp_all add: commit_write_G_def)
    subgoal
      by (smt (verit, ccfv_SIG) domI fun_upd_other option.sel svr_conf.select_convs(1) 
              svr_conf.simps(7) svr_conf.surjective svr_conf.update_convs(1-2) txid.inject) 
    subgoal
      by metis
    done

  subgoal for s
    apply (auto simp add: write_commit_U_def commit_write_G_def commit_write_U_def
                split: if_split_asm) (* SLOW, ~10s *)
    by (simp add: write_commit_G_def)+

  subgoal for s
    by (simp add: write_commit_U_def commit_write_U_def)

  done


lemmas write_commit_commutes = write_commit_read_invoke_commute write_commit_read_commute 
  write_commit_read_done_commute write_commit_write_invoke_commute write_commit_write_commit_commute
  write_commit_write_done_commute write_commit_register_read_commute 
  write_commit_prepare_write_commute write_commit_commit_write_commute


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
  by (metis ver_state.sel(6))

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
  "left_commute tps (WDone cl kv_map sn clk mmap) (RegR k' t' t_wr' rts' clk' lst' m')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: write_done_G_def register_read_G_def register_read_U_def clk_WDone_def
        add_to_readerset_def write_done_register_read_indep_L1 split: if_split_asm)
    apply (metis (no_types, opaque_lifting) domI option.inject)
    apply (metis (no_types, opaque_lifting) domI option.inject)
    by metis

  subgoal for s
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    by (auto simp add: write_done_U_def register_read_U_def add_to_readerset_def
        write_done_register_read_indep_lemmas split: if_split_asm ver_state.split)
  done


lemma write_done_prepare_write_indep_L2:
  "t' \<noteq> get_txn s cl \<Longrightarrow>
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
  "t' \<noteq> get_txn s cl \<Longrightarrow>
    clk_WDone cl clk mmap s \<longleftrightarrow>
    clk_WDone cl clk mmap
      (s\<lparr>svrs := (svrs s)
        (k := svrs s k
           \<lparr>svr_state := (svr_state (svrs s k))(Tn t' := X),
              svr_clock := Y\<rparr>)\<rparr>)"
  by (simp add: clk_WDone_def write_done_server_ev_indep_L)

lemmas write_done_prepare_write_indep_lemmas = 
  write_done_server_ev_indep_L write_done_prepare_write_indep_L2
  prepare_write_preserves_clk_WDone

lemma write_done_prepare_write_commute:
  "left_commute tps (WDone cl kv_map sn clk mmap) (PrepW k' t' v' clk' m')"
proof (auto simp add: left_commute_def tps_trans_top_defs)
  fix s
  assume a: "reach tps s" "prepare_write_G k' t' v' clk' m' s"
          "write_done_G cl kv_map sn clk mmap (prepare_write_U k' t' v' clk' s)"
  then have "t' \<noteq> Tn_cl sn cl"
    by (auto simp add: write_done_G_def prepare_write_G_def prepare_write_U_def)
  then show "write_done_G cl kv_map sn clk mmap s" using a
    apply (auto simp add: write_done_G_def prepare_write_U_def
        dest: prepare_write_preserves_clk_WDone split: if_split_asm)
    by (metis (no_types, opaque_lifting) domI option.inject)
next
  fix s
  assume "reach tps s" "prepare_write_G k' t' v' clk' m' s"
          "write_done_G cl kv_map sn clk mmap (prepare_write_U k' t' v' clk' s)"
  then show "prepare_write_G k' t' v' clk' m' (write_done_U cl kv_map clk s)"
    apply (auto simp add: write_done_U_def prepare_write_G_def)
    by (auto simp add: write_done_G_def prepare_write_U_def)
next
  fix s 
  assume a: "reach tps s" "prepare_write_G k' t' v' clk' m' s"
          "write_done_G cl kv_map sn clk mmap (prepare_write_U k' t' v' clk' s)"
  then have "t' \<noteq> Tn_cl sn cl"
    by (auto simp add: write_done_G_def prepare_write_G_def prepare_write_U_def)
  then show "write_done_U cl kv_map clk (prepare_write_U k' t' v' clk' s) =
              prepare_write_U k' t' v' clk' (write_done_U cl kv_map clk s)" using a
    by (auto simp add: write_done_G_def write_done_U_def prepare_write_U_def
        write_done_prepare_write_indep_lemmas)
qed

lemma write_done_commit_write_indep_L2:
   "t' \<noteq> get_txn s cl \<Longrightarrow>
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
  "t' \<noteq> get_txn s cl \<Longrightarrow>
    clk_WDone cl kv_map clk s \<longleftrightarrow>
    clk_WDone cl kv_map clk
        (s\<lparr>svrs := (svrs s)
          (k := svrs s k
             \<lparr>svr_state := (svr_state (svrs s k))(Tn t' := X),
              svr_clock := Y,
              svr_lst := Z\<rparr>)\<rparr>)"
  by (simp add: clk_WDone_def write_done_server_ev_indep_L)

lemmas write_done_commit_write_indep_lemmas = 
  write_done_server_ev_indep_L write_done_commit_write_indep_L2
  commit_write_preserves_clk_WDone

lemma write_done_commit_write_commute:  
  "t' \<noteq> Tn_cl sn cl \<Longrightarrow> left_commute tps (WDone cl kv_map sn clk mmap) (CommitW k' t' v' cts' clk' lst' m')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    apply (auto simp add: write_done_G_def commit_write_U_def
        dest: commit_write_preserves_clk_WDone split: if_split_asm)
    by (metis (no_types, opaque_lifting) domI option.inject)

  subgoal for s
    apply (auto simp add: tps_trans_GU_defs)
    by (metis empty_iff)

  subgoal for s
    by (auto simp add: write_done_G_def write_done_U_def commit_write_U_def
        write_done_commit_write_indep_lemmas)
  done


lemmas write_done_commutes = write_done_read_invoke_commute write_done_read_commute 
  write_done_read_done_commute write_done_write_invoke_commute write_done_write_commit_commute
  write_done_write_done_commute write_done_register_read_commute 
  write_done_prepare_write_commute write_done_commit_write_commute


\<comment> \<open>register_read\<close>

lemma register_read_read_invoke_commute:
  "t \<noteq> Tn_cl sn' cl' \<Longrightarrow> left_commute tps (RegR k t t_wr rts clk lst m) (RInvoke cl' keys' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma register_read_read_commute:
  "left_commute tps (RegR k t t_wr rts clk lst m) (Read cl' k' v' t' sn' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs add_to_readerset_def)

lemma register_read_read_done_commute:
  "left_commute tps (RegR k t t_wr rts clk lst m) (RDone cl' kv_map' sn' u''' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma register_read_write_invoke_commute:
  "left_commute tps (RegR k t t_wr rts clk lst m) (WInvoke cl' kv_map' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma register_read_write_commit_commute:
  "left_commute tps (RegR k t t_wr rts clk lst m) (WCommit cl' kv_map' cts' sn' u''' clk' mmap')"
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
  "left_commute tps (RegR k t t_wr rts clk lst m) (WDone cl' kv_map' sn' clk' mmap')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: register_read_G_def write_done_U_def)

  subgoal for s
    apply (auto simp add: tps_trans_GU_defs add_to_readerset_def split: if_split_asm)
    apply (metis domI ver_state.sel(3))
    apply (metis domI option.inject ver_state.inject(2))
    apply (metis domI option.inject)
    apply (metis ver_state.sel(6))
    by metis

  subgoal for s
    by (auto simp add: register_read_U_def write_done_U_def clk_WDone_def add_to_readerset_def
        write_done_register_read_indep_lemmas split: if_split_asm ver_state.split)
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


lemmas register_read_commutes = register_read_read_invoke_commute register_read_read_commute 
  register_read_read_done_commute register_read_write_invoke_commute
  register_read_write_commit_commute register_read_write_done_commute
  register_read_register_read_commute register_read_prepare_write_commute
  register_read_commit_write_commute


\<comment> \<open>prepare_write\<close>

lemma prepare_write_read_invoke_commute:
  "left_commute tps (PrepW k t v clk m) (RInvoke cl' keys' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma prepare_write_read_commute:
  "left_commute tps (PrepW k t v clk m) (Read cl' k' v' t' sn' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma prepare_write_read_done_commute:
  "left_commute tps (PrepW k t v clk m) (RDone cl' kv_map' sn' u''' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma prepare_write_write_invoke_commute:
  "t \<noteq> Tn_cl sn' cl' \<Longrightarrow> left_commute tps (PrepW k t v clk m) (WInvoke cl' kv_map' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma prepare_write_write_commit_commute:
  "left_commute tps (PrepW k t v clk m) (WCommit cl' kv_map' cts' sn' u''' clk' mmap')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: prepare_write_G_def write_commit_U_def)

  subgoal for s
    apply (auto simp add: prepare_write_G_def write_commit_U_def)
    apply (auto simp add: prepare_write_U_def write_commit_G_def)
    by metis

  subgoal for s
    by (auto simp add: prepare_write_U_def write_commit_U_def)
  done

lemma prepare_write_write_done_commute:
  "left_commute tps (PrepW k t v clk m) (WDone cl' kv_map' sn' clk' mmap')"
proof (auto simp add: left_commute_def tps_trans_top_defs)
  fix s
  assume "reach tps s" "write_done_G cl' kv_map' sn' clk' mmap' s"
          "prepare_write_G k t v clk m (write_done_U cl' kv_map' clk' s)"
  then show "prepare_write_G k t v clk m s"
    by (auto simp add: prepare_write_G_def write_done_U_def)
next
  fix s
  assume "reach tps s" "write_done_G cl' kv_map' sn' clk' mmap' s"
          "prepare_write_G k t v clk m (write_done_U cl' kv_map' clk' s)"
  then show "write_done_G cl' kv_map' sn' clk' mmap' (prepare_write_U k t v clk s)"
    apply (simp add: prepare_write_G_def write_done_U_def)
    apply (auto simp add: prepare_write_U_def write_done_G_def)
    by (simp add: clk_WDone_def write_done_server_ev_indep_L)
next
  fix s 
  assume a: "reach tps s" "write_done_G cl' kv_map' sn' clk' mmap' s"
          "prepare_write_G k t v clk m (write_done_U cl' kv_map' clk' s)"
  then have "t \<noteq> Tn_cl sn' cl'" by (auto simp add: prepare_write_G_def write_done_U_def)
  then show "prepare_write_U k t v clk (write_done_U cl' kv_map' clk' s) =
    write_done_U cl' kv_map' clk' (prepare_write_U k t v clk s)" using a
    by (auto simp add: write_done_G_def write_done_U_def prepare_write_U_def
        write_done_prepare_write_indep_lemmas)
qed

lemma prepare_write_register_read_commute:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (PrepW k t v clk m) (RegR k' t' t_wr' rts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma prepare_write_prepare_write_commute:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (PrepW k t v clk m) (PrepW k' t' v' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma prepare_write_commit_write_commute:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (PrepW k t v clk m) (CommitW k' t' v' cts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)


lemmas prepare_write_commutes = prepare_write_read_invoke_commute prepare_write_read_commute 
  prepare_write_read_done_commute prepare_write_write_invoke_commute
  prepare_write_write_commit_commute prepare_write_write_done_commute
  prepare_write_register_read_commute prepare_write_prepare_write_commute
  prepare_write_commit_write_commute


\<comment> \<open>commit_write\<close>

lemma commit_write_read_invoke_commute:
  "left_commute tps (CommitW k t v cts clk lst m) (RInvoke cl' keys' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma commit_write_read_commute:
  "left_commute tps (CommitW k t v cts clk lst m) (Read cl' k' v' t' sn' clk' m')"
  apply (auto simp add: left_commute_def tps_trans_top_defs)
  subgoal for s
    by (auto simp add: commit_write_G_def read_G_def read_U_def split: if_split_asm)

  subgoal for s 
    by (auto simp add: tps_trans_GU_defs)

  subgoal for s
    by (simp add: commit_write_U_def read_U_def)
  done

lemma commit_write_read_done_commute:
  "left_commute tps (CommitW k t v cts clk lst m) (RDone cl' kv_map' sn' u''' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma commit_write_write_invoke_commute:
  "left_commute tps (CommitW k t v cts clk lst m) (WInvoke cl' kv_map' sn' clk')"
  by (auto simp add: left_commute_def tps_trans_defs)

lemma commit_write_write_commit_indep_L:
  "Min (pending_wtxns_ts (
        (svr_state (svrs (s\<lparr>cls := (cls s)
                            (cl' := cls s cl'
                              \<lparr>cl_state := B,
                               cl_clock := C\<rparr>),
                            wtxn_cts := Z,
                            cts_order := Y\<rparr>) k)) (Tn t := X))) =
   Min (pending_wtxns_ts ((svr_state (svrs s k)) (Tn t := X)))"
  by auto

lemma commit_write_write_commit_commute:
  "t \<noteq> Tn_cl sn' cl' \<Longrightarrow> left_commute tps (CommitW k t v cts clk lst m) (WCommit cl' kv_map' cts' sn' u''' clk' mmap')"
  apply (auto simp add: left_commute_def tps_trans_top_defs) 
  subgoal for s
    apply (auto simp add: commit_write_G_def write_commit_U_def split: if_split_asm)
    by (metis txid0.collapse write_commit_G_def)+

  subgoal for s
    apply (auto simp add: commit_write_U_def write_commit_G_def)
    by metis

  subgoal for s
    by (auto simp add: commit_write_U_def write_commit_U_def)
  done

lemma commit_write_write_done_commute:
  "left_commute tps (CommitW k t v cts clk lst m) (WDone cl' kv_map' sn' clk' mmap')"
proof (auto simp add: left_commute_def tps_trans_top_defs)
  fix s
  assume "reach tps s" "write_done_G cl' kv_map' sn' clk' mmap' s"
          "commit_write_G k t v cts clk lst m (write_done_U cl' kv_map' clk' s)"
  then show "commit_write_G k t v cts clk lst m s"
    by (auto simp add: commit_write_G_def write_done_U_def split: if_split_asm)
next
  fix s
  assume "reach tps s" "write_done_G cl' kv_map' sn' clk' mmap' s"
          "commit_write_G k t v cts clk lst m (write_done_U cl' kv_map' clk' s)"
  then show "write_done_G cl' kv_map' sn' clk' mmap' (commit_write_U k t v cts clk lst s)"
    apply (simp add: commit_write_G_def write_done_U_def)
    apply (auto simp add: commit_write_U_def write_done_G_def)
    by (simp add: clk_WDone_def write_done_server_ev_indep_L)
next
  fix s 
  assume a: "reach tps s" "write_done_G cl' kv_map' sn' clk' mmap' s"
          "commit_write_G k t v cts clk lst m (write_done_U cl' kv_map' clk' s)"
  then have "t \<noteq> Tn_cl sn' cl'" by (auto simp add: commit_write_G_def write_done_U_def)
  then show "commit_write_U k t v cts clk lst (write_done_U cl' kv_map' clk' s) =
              write_done_U cl' kv_map' clk' (commit_write_U k t v cts clk lst s)" using a
    by (auto simp add: write_done_G_def write_done_U_def commit_write_U_def
        write_done_commit_write_indep_lemmas)
qed                                                                                                            

lemma commit_write_register_read_commute:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (CommitW k t v cts clk lst m) (RegR k' t' t_wr' rts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma commit_write_prepare_write_commute:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (CommitW k t v cts clk lst m) (PrepW k' t' v' clk' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)

lemma commit_write_commit_write_commute:
  "k \<noteq> k' \<Longrightarrow> left_commute tps (CommitW k t v cts clk lst m) (CommitW k' t' v' cts' clk' lst' m')"
  by (auto simp add: left_commute_def tps_trans_defs fun_upd_twist)


lemmas commit_write_commutes = commit_write_read_invoke_commute commit_write_read_commute 
  commit_write_read_done_commute commit_write_write_invoke_commute commit_write_write_commit_commute
  commit_write_write_done_commute commit_write_register_read_commute 
  commit_write_prepare_write_commute commit_write_commit_write_commute


subsection\<open>Commute of independent events\<close>

lemma wtxns_domIff [iff, simp del, code_unfold]: "t \<in> wtxns_dom wtxns \<longleftrightarrow> wtxns t \<noteq> No_Ver"
  by (simp add: wtxns_dom_def)

lemma wtxns_dom_fun_upd [simp]:
  "wtxns_dom(wtxns(t := x)) = (if x = No_Ver then wtxns_dom wtxns - {t} else insert t (wtxns_dom wtxns))"
  by (auto simp: wtxns_dom_def)

lemma add_to_readerset_wtxns_dom:
  "wtxns_dom (add_to_readerset wtxns t rts rlst t') = wtxns_dom wtxns"
  by (auto simp add: add_to_readerset_def split: ver_state.split)

\<comment> \<open>Value of svr_state for future transaction ids\<close>
definition FTid_Wtxn_Inv where
  "FTid_Wtxn_Inv s cl \<longleftrightarrow> (\<forall>n k. n > cl_sn (cls s cl) \<longrightarrow> svr_state (svrs s k) (Tn (Tn_cl n cl)) = No_Ver)"

lemmas FTid_Wtxn_InvI = FTid_Wtxn_Inv_def[THEN iffD2, rule_format]
lemmas FTid_Wtxn_InvE[elim] = FTid_Wtxn_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_ftid_wtxn_inv [simp, dest]: "reach tps s \<Longrightarrow> FTid_Wtxn_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: FTid_Wtxn_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x71 x72 x73 x74 x75 x76 x77)
    then show ?case
      apply (auto simp add: tps_trans_defs FTid_Wtxn_Inv_def)
      by (metis add_to_readerset_no_ver_inv)
  qed (auto simp add: tps_trans_defs FTid_Wtxn_Inv_def)
qed

\<comment> \<open>Next 4 invariants: cl_state + cl_sn \<longrightarrow> svr_state\<close>
definition Cl_Rtxn_Inv where
  "Cl_Rtxn_Inv s cl \<longleftrightarrow> (\<forall>k cclk keys kvm. cl_state (cls s cl) \<in> {Idle, RtxnInProg cclk keys kvm}
    \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver)"

lemmas Cl_Rtxn_InvI = Cl_Rtxn_Inv_def[THEN iffD2, rule_format]
lemmas Cl_Rtxn_InvE[elim] = Cl_Rtxn_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_rtxn_inv [simp, dest]: "reach tps s \<Longrightarrow> Cl_Rtxn_Inv s cl"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Cl_Rtxn_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Rtxn_Inv_def tps_trans_defs)
      by (metis add_to_readerset_no_ver_inv)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Cl_Rtxn_Inv_def tps_trans_defs)
      by (metis get_cl_w.simps(2) txn_state.distinct(3) txn_state.distinct(7) txid0.collapse)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Rtxn_Inv_def tps_trans_defs)
      by force
  qed (auto simp add: Cl_Rtxn_Inv_def tps_trans_defs)
qed

definition Cl_Wtxn_Idle_Svr where
  "Cl_Wtxn_Idle_Svr s cl k \<longleftrightarrow>
    (\<forall>cts kv_map. cl_state (cls s cl) \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map}
        \<and> kv_map k = None \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver)"

lemmas Cl_Wtxn_Idle_SvrI = Cl_Wtxn_Idle_Svr_def[THEN iffD2, rule_format]
lemmas Cl_Wtxn_Idle_SvrE[elim] = Cl_Wtxn_Idle_Svr_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_wtxn_idle_svr [simp]: "reach tps s \<Longrightarrow> Cl_Wtxn_Idle_Svr s cl k"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Cl_Wtxn_Idle_Svr_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Wtxn_Idle_Svr_def tps_trans_defs)
      by (metis add_to_readerset_no_ver_inv)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Cl_Wtxn_Idle_Svr_def tps_trans_defs)
      by (smt (z3) domIff get_cl_w.simps(2) txn_state.distinct(11) txn_state.inject(2) txid0.collapse)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Wtxn_Idle_Svr_def tps_trans_defs)
      by force
  qed (auto simp add: Cl_Wtxn_Idle_Svr_def tps_trans_defs, blast?)
qed

definition Cl_Prep_Inv where
  "Cl_Prep_Inv s \<longleftrightarrow> (\<forall>cl k kvm. \<exists>pend_t prep_t v. cl_state (cls s cl) = WtxnPrep kvm
    \<longrightarrow> (k \<in> dom kvm \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) \<in> {No_Ver, Prep pend_t prep_t v}) \<and>
    (k \<notin> dom kvm \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver))"

lemmas Cl_Prep_InvI = Cl_Prep_Inv_def[THEN iffD2, rule_format]
lemmas Cl_Prep_InvE[elim] = Cl_Prep_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_prep_inv [simp]: "reach tps s \<Longrightarrow> Cl_Prep_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Cl_Prep_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (WInvoke x1 x2 x3 x4)
    then show ?case by (simp add: Cl_Prep_Inv_def tps_trans_defs, blast)
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Prep_Inv_def tps_trans_defs)
      by (smt (verit) add_to_readerset_wtxns_dom add_to_readerset_prep_inv wtxns_domIff)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Cl_Prep_Inv_def tps_trans_defs)
      by (metis domI get_cl_w.simps(2) txn_state.inject(2) txid0.collapse)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Prep_Inv_def tps_trans_defs)
      using get_cl_w.simps(2) txn_state.distinct(11) txn_state.simps(19) by force
  qed (auto simp add: Cl_Prep_Inv_def tps_trans_defs)
qed

definition Cl_Commit_Inv where
  "Cl_Commit_Inv s \<longleftrightarrow> (\<forall>cl k cts kv_map. cl_state (cls s cl) = WtxnCommit cts kv_map \<longrightarrow>
    (\<forall>v. kv_map k = Some v \<longrightarrow>
      (\<exists>pend_t prep_t sts lst rs. svr_state (svrs s k) (get_wtxn s cl) \<in> {Prep pend_t prep_t v, Commit cts sts lst v rs})) \<and>
    (kv_map k = None \<longrightarrow> svr_state (svrs s k) (get_wtxn s cl) = No_Ver))"

lemmas Cl_Commit_InvI = Cl_Commit_Inv_def[THEN iffD2, rule_format]
lemmas Cl_Commit_InvE[elim] = Cl_Commit_Inv_def[THEN iffD1, elim_format, rule_format]

lemma reach_cl_commit_inv [simp]: "reach tps s \<Longrightarrow> Cl_Commit_Inv s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
  by (auto simp add: Cl_Commit_Inv_def tps_defs)
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Commit_Inv_def tps_trans_defs)
      by (metis (no_types, lifting) Cl_Prep_Inv_def domI domIff option.inject reach_cl_prep_inv)
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Commit_Inv_def tps_trans_defs)
      by (smt add_to_readerset_commit add_to_readerset_no_ver_inv add_to_readerset_prep_inv
          ver_state.exhaust ver_state.inject(2))
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: Cl_Commit_Inv_def tps_trans_defs)
      by (smt (verit) fun_upd_other get_cl_w.simps(2) txn_state.distinct(11) txid0.collapse)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: Cl_Commit_Inv_def tps_trans_defs)
      by (metis domD get_cl_w.simps(2) txn_state.inject(3) ver_state.distinct(5) ver_state.inject(1) txid0.collapse)
  qed (auto simp add: Cl_Commit_Inv_def tps_trans_defs)
qed

lemma indep_cl_neq:
  assumes
    \<open>\<not>EVI \<tau> i < EVI \<tau> j\<close>
    \<open>i < j\<close>
    \<open>ev_cl (\<tau> ! j) \<noteq> None\<close>
  shows "ev_cl (\<tau> ! i) \<noteq> ev_cl (\<tau> ! j)"
  using assms
  by (auto simp add: less_ev_i_def causal_dep0_def cl_ord_def)

lemma indep_svr_neq:
  assumes
    \<open>\<not>EVI \<tau> i < EVI \<tau> j\<close>
    \<open>i < j\<close>
    \<open>ev_key (\<tau> ! j) \<noteq> None\<close>
  shows "ev_key (\<tau> ! i) \<noteq> ev_key (\<tau> ! j)"
  using assms
  by (auto simp add: less_ev_i_def causal_dep0_def svr_ord_def)

lemma trancl_into_r: "(a, b) \<notin> r\<^sup>+ \<Longrightarrow> (a, b) \<notin> r"
  by auto

\<comment> \<open> PW \<longrightarrow> WC \<close>
lemma prepw_in_tr:
  assumes 
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>PrepW k t v clk m \<in> set \<tau>\<close>
  shows \<open>\<exists>pd cts ts lst rs. svr_state (svrs s' k) (Tn t) \<in> {Prep pd clk v, Commit cts ts lst v rs}\<close>
  using assms
proof (induction \<tau> s' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case by (auto simp add: tps_trans_defs add_to_readerset_def split: if_split_asm)
  qed (auto simp add: tps_trans_defs)
qed simp

lemma prepw_wcommit_m:
  assumes 
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>PrepW k' t' v' clk' m' \<in> set \<tau>\<close>
    \<open>write_commit_G cl kv_map cts sn clk mmap s'\<close>
    \<open>t' = Tn_cl sn cl\<close>
  shows "mmap k' = Some clk'"
  using assms
proof (induction \<tau> s' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then have a: "kv_map k' \<noteq> None"
    apply (auto simp add: write_commit_G_def)
    using Cl_Wtxn_Idle_Svr_def[of s'' cl k']
        prepw_in_tr[of s "\<tau> @ [e]" s'' k' "get_txn s'' cl"]
     apply auto using trace_snoc.hyps(2)
    by (blast, meson reach_cl_wtxn_idle_svr reach_trace_extend trace.trace_snoc)+
  show ?case using trace_snoc
    apply (auto simp add: write_commit_G_def del: disjE)
    subgoal using a by auto
    using prepw_in_tr[of s "\<tau> @ [e]" s'' k' "get_txn s'' cl"]
      by (smt (verit) domI empty_iff insert_iff trace.trace_snoc trace_snoc.hyps(2)
          trace_snoc.prems(2) ver_state.distinct(5) ver_state.sel(2))
qed simp


\<comment> \<open> WI \<longrightarrow> PW \<close>
lemma winvoke_in_tr_sn:
  assumes 
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>WInvoke cl' kv_map' sn' clk' \<in> set \<tau>\<close>
  shows \<open>cl_sn (cls s' cl') > sn' \<or> (cl_sn (cls s' cl') = sn' \<and>
    (\<exists>kv_map cts. cl_state (cls s' cl') \<in> {WtxnPrep kv_map, WtxnCommit cts kv_map}))\<close>
  using assms
proof (induction \<tau> s' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
    by (induction e) (auto simp add: tps_trans_defs split: if_split_asm)
qed simp

lemma winvoke_in_tr:
  assumes 
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>WInvoke cl' kv_map' sn' clk' \<in> set \<tau>\<close>
    \<open>cl_state (cls s' cl') = WtxnPrep kv_map\<close>
    \<open>cl_sn (cls s' cl') = sn'\<close>
    \<open>svr_state (svrs s' k) (get_wtxn s' cl') = No_Ver\<close>
    \<open>kv_map k = Some v\<close>
  shows \<open>cl_clock (cls s' cl') = clk'\<close>
  using assms
proof (induction \<tau> s' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WInvoke x1 x2 x3 x4)
    then show ?case apply (auto simp add: tps_trans_defs split: if_split_asm)
      by (metis empty_iff insert_iff nat_neq_iff txn_state.distinct(3) txn_state.distinct(5) winvoke_in_tr_sn)
  qed (auto simp add: tps_trans_defs add_to_readerset_def split: if_split_asm)
qed simp


lemma winvoke_prepw_m:
  assumes 
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>WInvoke cl' kv_map' sn' clk' \<in> set \<tau>\<close>
    \<open>prepare_write_G k t v clk m s'\<close>
    \<open>t = Tn_cl sn' cl'\<close>
  shows "m = clk'"
  using assms
proof (induction \<tau> s' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WInvoke x1 x2 x3 x4)
    then show ?case apply (simp add: prepare_write_G_def)
      by (smt (verit) WInvoke.prems(2,5) trace.trace_snoc winvoke_in_tr)
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: prepare_write_G_def)
      by (smt (verit) RegR.prems(2,5) trace.trace_snoc winvoke_in_tr)
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case apply (simp add: prepare_write_G_def)
      by (smt (verit) PrepW.prems(2,5) trace.trace_snoc winvoke_in_tr)
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: prepare_write_G_def)
      by (smt (verit) CommitW.prems(2,5) trace.trace_snoc winvoke_in_tr)
  qed (auto simp add: tps_trans_defs split: if_split_asm)
qed simp


\<comment> \<open> RReg \<longrightarrow> Read \<close>
lemma regr_in_tr:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>RegR k t' t_wr' rts' clk' lst' m' \<in> set \<tau>\<close>
  shows "\<exists>cts ts lst v rs. svr_state (svrs s' k) t_wr' = Commit cts ts lst v rs \<and> rs t' = Some (clk', lst')"
  using assms
proof (induction \<tau> s' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case by (auto simp add: tps_trans_defs add_to_readerset_def)
  qed (auto simp add: tps_trans_defs)
qed simp
  

lemma regr_read_m:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>RegR k t' t_wr' rts' clk' lst' m' \<in> set \<tau>\<close>
    \<open>read_G cl k v t_wr sn clk m s'\<close>
    \<open>t' = Tn_cl sn cl\<close>
  shows "m = (clk', lst')"
  using assms
proof (induction \<tau> s' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (RInvoke x1 x2 x3 x4)
    then have "tps: s \<midarrow>\<langle>\<tau> @ [RInvoke x1 x2 x3 x4]\<rangle>\<rightarrow> s''" by blast
    then show ?case using RInvoke  apply (auto simp add: read_G_def)
      using regr_in_tr[of s "\<tau> @ [RInvoke x1 x2 x3 x4]" s'' k "(get_txn s'' cl)" t_wr' rts' clk' lst' m']
      apply auto sorry
  next
    case (Read x1 x2 x3 x4 x5 x6 x7)
    then show ?case sorry
  next
    case (RDone x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (WInvoke x1 x2 x3 x4)
    then show ?case sorry
  next
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case sorry
  next
    case (WDone x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (RegR x1 x2 x3 x4 x5 x6 x7)
    then show ?case sorry
  next
    case (PrepW x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (CommitW x1 x2 x3 x4 x5 x6 x7)
    then show ?case sorry
  qed
qed simp


lemma indep_evs_commute:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>\<not>EVI \<tau> i < EVI \<tau> j\<close>
    \<open>i < j\<close>
    \<open>j < length \<tau>\<close>
  shows "left_commute tps (\<tau> ! j) (\<tau> ! i)"
  using assms
proof (induction \<tau> s' arbitrary: j rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (cases "j = length \<tau>")
    case True
    then show ?thesis using trace_snoc
    proof (induction e)
      case (RInvoke x1 x2 x3 x4)
      then show ?case
        by (induction "\<tau> ! i") (smt append_eq_conv_conj nth_append_length nth_take ev_cl.simps
            indep_cl_neq not_None_eq read_invoke_commutes)+
    next
      case (Read x1 x2 x3 x4 x5 x6 x7)
      then show ?case
      proof (induction "\<tau> ! i")
        case (RegR x71 x72 x73 x74 x75 x76 x77)
        then have "x2 = x71 \<Longrightarrow> x72 = Tn_cl x5 x1 \<Longrightarrow> x7 = (x75, x76)"
          apply (simp add: read_def)
          by (metis regr_read_m nth_mem)
        then show ?case using RegR
          apply (auto simp add: less_ev_i_def causal_dep0_def txn_ord.simps tps_trans_defs
           nth_append dest!: trancl_into_r)
          by (metis read_register_read_commute)
      qed (smt append_eq_conv_conj nth_append_length nth_take ev_cl.simps
            indep_cl_neq not_None_eq read_commutes)+
    next
      case (RDone x1 x2 x3 x4 x5)
      then show ?case
        by (induction "\<tau> ! i") (smt append_eq_conv_conj nth_append_length nth_take ev_cl.simps
            indep_cl_neq not_None_eq read_done_commutes)+
    next
      case (WInvoke x1 x2 x3 x4)
      then show ?case
        by (induction "\<tau> ! i") (smt append_eq_conv_conj nth_append_length nth_take ev_cl.simps
            indep_cl_neq not_None_eq write_invoke_commutes)+
    next
      case (WCommit x1 x2 x3 x4 x5 x6 x7)
      then show ?case
      proof (induction "\<tau> ! i")
        case (PrepW x81 x82 x83 x84 x85)
        then have "x82 = Tn_cl x4 x1 \<Longrightarrow> x7 x81 = Some x84"
          apply (simp add: write_commit_def)
          by (metis prepw_wcommit_m nth_mem)
        then show ?case using PrepW
          apply (auto simp add: less_ev_i_def causal_dep0_def txn_ord.simps tps_trans_defs
           nth_append dest!: trancl_into_r)
          by (metis (no_types, lifting) not_None_eq option.inject write_commit_prepare_write_commute)
      qed (smt append_eq_conv_conj nth_append_length nth_take ev_cl.simps
            indep_cl_neq not_None_eq write_commit_commutes)+
    next
      case (WDone x1 x2 x3 x4 x5)
      then show ?case
      proof (induction "\<tau> ! i")
        case (CommitW x91 x92 x93 x94 x95 x96 x97)
        then have "x92 = Tn_cl x3 x1 \<Longrightarrow> x5 x91 = Some (x95, x96)"
          apply (simp add: write_done_def)
          (*by (metis regr_read_m nth_mem)*) sorry
        then show ?case using CommitW
          apply (auto simp add: less_ev_i_def causal_dep0_def txn_ord.simps tps_trans_defs
           nth_append dest!: trancl_into_r)
          by (metis (no_types, lifting) Pair_inject option.discI option.inject
              write_done_commit_write_commute)
      qed (smt append_eq_conv_conj nth_append_length nth_take ev_cl.simps
            indep_cl_neq not_None_eq write_done_commutes)+
    next
      case (RegR x1 x2 x3 x4 x5 x6 x7)
      then show ?case
      proof (induction "\<tau> ! i")
        case (RInvoke x11 x12 x13 x14)
        then have a: "x2 = Tn_cl x13 x11 \<Longrightarrow> x7 = x14"
          apply (simp add: prepare_write_def) sorry
          (*by (metis prepw_wcommit_m nth_mem)*)
        then show ?case using RInvoke
          apply (auto simp add: less_ev_i_def causal_dep0_def txn_ord.simps tps_trans_defs
           nth_append dest!: trancl_into_r) using a
          by (smt (verit) register_read_read_invoke_commute)
      qed (smt append_eq_conv_conj nth_append_length nth_take ev_key.simps
            indep_svr_neq not_None_eq register_read_commutes)+
    next
      case (PrepW x1 x2 x3 x4 x5)
      then show ?case
      proof (induction "\<tau> ! i")
        case (WInvoke x41 x42 x43 x44)
        then have a: "x2 = Tn_cl x43 x41 \<Longrightarrow> x5 = x44"
          apply (simp add: prepare_write_def)
          by (metis winvoke_prepw_m nth_mem)
        then show ?case using WInvoke
          apply (auto simp add: less_ev_i_def causal_dep0_def txn_ord.simps tps_trans_defs
           nth_append dest!: trancl_into_r) using a
          by (smt (verit) prepare_write_write_invoke_commute)
      qed (smt append_eq_conv_conj nth_append_length nth_take ev_key.simps
            indep_svr_neq not_None_eq prepare_write_commutes)+
    next                                    
      case (CommitW x1 x2 x3 x4 x5 x6 x7)
      then show ?case
      proof (induction "\<tau> ! i")
        case (WCommit x51 x52 x53 x54 x55 x56 x57)
        then have a: "x2 = Tn_cl x54 x51 \<Longrightarrow> x7 = x56"
          apply (simp add: prepare_write_def) sorry
          (*by (metis prepw_wcommit_m nth_mem)*)
        then show ?case using WCommit
          apply (auto simp add: less_ev_i_def causal_dep0_def txn_ord.simps tps_trans_defs
           nth_append dest!: trancl_into_r) using a
          by (smt (verit) commit_write_write_commit_commute)
      qed (smt append_eq_conv_conj nth_append_length nth_take ev_key.simps
            indep_svr_neq not_None_eq commit_write_commutes)+
    qed
  next
    case False
    then show ?thesis using trace_snoc apply (simp add: nth_append)
      by (meson causal_dep_nth_append_rev less_SucE less_ev_i_def)
  qed
qed simp

end