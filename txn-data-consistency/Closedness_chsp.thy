theory Closedness_chsp
  imports CCv_Eiger_Port_plus
begin

section \<open>Lemmas about relational image and transititve closure\<close>

lemma L1: "x \<notin> (r\<^sup>*) `` V \<Longrightarrow> ({z. (z, x) \<in> r\<^sup>*} \<times> B) `` V = {}"
  by auto

lemma Image_trancl_insert_max:
  assumes "x \<notin> (r\<^sup>*) `` V" 
  shows "(insert (x, y) r)\<^sup>+ `` V  = (r\<^sup>+) `` V" 
  using assms
  by (auto simp add: trancl_insert Un_Image L1)

thm rtrancl_trancl_reflcl

lemma Image_trancl_union_max:
  assumes "finite B" "x \<notin> (r\<^sup>*) `` V" 
  shows "((\<Union>y\<in>B. {(x, y)}) \<union> r)\<^sup>+ `` V = (r\<^sup>+) `` V" 
  using assms
  by (induction rule: finite.induct) 
     (simp_all, metis Image_trancl_insert_max Un_Image rtrancl_trancl_reflcl)


section \<open>Closedness: general definition and basic lemmas\<close>

text \<open>Original general definition\<close>

definition closed_general' :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "closed_general' V r N \<longleftrightarrow> V = ((r\<^sup>*) `` V) - N"

prop "V \<inter> N = {}"        \<comment> \<open>we can always assume this\<close>


text \<open>Alternative def, equivalent under our conditions; probably easier to understand; 
obviates need for some assumptions in lemmas below; also somewhat easier to work with?\<close>

definition closed_general :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "closed_general V r N \<longleftrightarrow> (r\<^sup>+) `` V \<subseteq> V \<union> N"

lemma closed_generalI: "(r\<^sup>+) `` V \<subseteq> V \<union> N \<Longrightarrow> closed_general V r N"
  by (simp add: closed_general_def)

lemma closed_generalE [elim]: 
  "\<lbrakk> closed_general V r N; (r\<^sup>+) `` V \<subseteq> V \<union> N \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add: closed_general_def)

lemma closed_general_equiv:
  assumes "V \<inter> N = {}"
  shows "closed_general V r N \<longleftrightarrow> closed_general' V r N"
  using assms
  by (unfold closed_general_def closed_general'_def rtrancl_trancl_reflcl) 
     blast  \<comment> \<open>rest just by general set theory\<close>


text \<open>Empty set, monotonicity, and unions; note that monotonicity holds in @{term N}, but it
does not hold in @{term V}.\<close>

lemma closed_general_empty [simp, intro!]: 
  shows "closed_general {} r N"
  by (auto simp add: closed_general_def)

lemma closed_general_mono_N [elim]:
  assumes "closed_general V r N" 
  and "N \<subseteq> N'"
  shows "closed_general V r N'"
  using assms
  by (auto simp add: closed_general_def)

lemma closed_general_set_union_closed:   
  assumes "closed_general V\<^sub>1 r N\<^sub>1"
      and "closed_general V\<^sub>2 r N\<^sub>2"
      and "V = V\<^sub>1 \<union> V\<^sub>2"
      and "N\<^sub>1 \<union> N\<^sub>2 \<subseteq> V \<union> N"
  shows "closed_general V r N"
  using assms
  by (auto simp add: closed_general_def)

lemma closed_general_set_Union_closed:   
  assumes "finite I"
      and "\<And>i. i \<in> I \<Longrightarrow> closed_general (V i) r (N i)"
      and "V' = (\<Union>i\<in>I. V i)"
      and "(\<Union>i\<in>I. N i) \<subseteq> V' \<union> N'"
  shows "closed_general V' r N'"
  using assms
  apply (induction arbitrary: N' V' rule: finite.induct)
   apply simp_all
  by (rule closed_general_set_union_closed[where 
             V\<^sub>1="V i" and V\<^sub>2="\<Union> (V ` I)" and N\<^sub>1="N i" and N\<^sub>2="\<Union> (N ` I)" for i I]) 
     (auto) 

text \<open>Extending the relation\<close>

lemma closed_general_insert_rel_max:
  assumes "closed_general V r N" 
  and "r' = insert (x, y) r" 
  and "x \<notin> (r\<^sup>*) `` V"                   \<comment> \<open>implies @{prop "x \<notin> V"} and @{prop "x \<notin> r``V"}\<close>
  shows "closed_general V r' N"
  using assms
  by (auto simp add: closed_general_def Image_trancl_insert_max)

lemma closed_general_extend_rel_max:    \<comment> \<open>generalizes previous lemma\<close>
  assumes "closed_general V r N" 
  and "r' = (\<Union>y\<in>Y. {(x, y)}) \<union> r" 
  and "x \<notin> (r\<^sup>*) `` V" 
  and "finite Y"
  shows "closed_general V r' N"
  using assms
  by (auto simp add: closed_general_def Image_trancl_union_max)


text  \<open>all at once ;-)\<close>

lemma closed_general_union_V_extend_N_extend_rel:
  assumes "closed_general V\<^sub>1 r N\<^sub>1"
      and "closed_general V\<^sub>2 r N\<^sub>2"
      and "V = V\<^sub>1 \<union> V\<^sub>2"
      and "N\<^sub>1 \<union> N\<^sub>2 \<subseteq> V \<union> N"
      and "x \<notin> (r\<^sup>*) `` V"
      and "r' = (\<Union>y\<in>Y. {(x, y)}) \<union> r"
      and "finite Y"
    shows "closed_general V r' N"         \<comment> \<open>r changes as well!\<close>
  using assms
  by (auto intro: closed_general_set_union_closed[THEN closed_general_extend_rel_max])


text \<open>
  Q: Sufficent conditions to satisfy premise @{prop "x \<notin> (r\<^sup>*) `` V"} in the two previous lemmas?
  In lemma below, first premise below does not necessarily hold for SO!
\<close>
lemma "\<lbrakk> x \<notin> Range r; x \<notin> V \<rbrakk> \<Longrightarrow> x \<notin> (r\<^sup>*) `` V"
  by (metis ImageE Range_iff rtranclE)


text \<open>Implications between closedness for different relations\<close>

lemma closed_general_hierarchy:
  assumes "closed_general V r N"
  and "r'\<^sup>+ `` V \<subseteq> r\<^sup>+ `` V"
  shows "closed_general V r' N"
  using assms
  by (simp add: closed_general_def)

lemma closed_general_anti_mono:
  assumes "closed_general V r N"
  and "r' \<subseteq> r"
  shows "closed_general V r' N"
  using assms
  by (auto elim!: closed_general_hierarchy elim: trancl_mono intro: Image_mono)

text \<open>
Q: Does the implication of closedness for different R_ET relations imply an ordering of 
isolation guarantees? Not sure, since the execution test includes an initial view extension, 
which need not be the same for different ETs to satisfy their respective commit conditions.
\<close>


(****************************************************************************************)
(****************************************************************************************)

(* except for lemma closed'_generalize, no further unfolding of closed_general(')_def below *)
text \<open>NOTE: @{term closed'} should be defined in terms of @{term "closed_general"}!\<close>

lemma closed'_generalize: 
  "closed' K u r = closed_general (visTx' K u) (r\<inverse>) (read_only_Txs K)"
proof -
  have "visTx' K u \<inter> read_only_Txs K = {}"
    by (simp add: diff_eq read_only_Txs_def visTx'_def) 
  then show ?thesis
    by (simp add: closed'_def closed_general_equiv closed_general'_def rtrancl_converse)
qed

lemma visTx'_union_distr: "visTx' K (u\<^sub>1 \<union> u\<^sub>2) = visTx' K u\<^sub>1 \<union> visTx' K u\<^sub>2"
  by (auto simp add: visTx'_def)

lemma visTx'_Union_distr: "visTx' K (\<Union>i\<in>I. u i) = (\<Union>i\<in>I. visTx' K (u i))"
  by (auto simp add: visTx'_def)

lemma visTx'_same_writers: "kvs_writers K' = kvs_writers K \<Longrightarrow> visTx' K' u = visTx' K u"
  by (simp add: visTx'_def)

lemma union_closed':
  assumes "closed' K u\<^sub>1 r"
    and "closed' K u\<^sub>2 r"
    and "kvs_writers K' = kvs_writers K" 
    and "read_only_Txs K \<subseteq> read_only_Txs K'"
  shows "closed' K' (u\<^sub>1 \<union> u\<^sub>2) r"
  using assms
  by (auto simp add: closed'_generalize visTx'_union_distr visTx'_same_writers[of K']
           intro: closed_general_set_union_closed)

lemma Union_closed':
  assumes "\<And>i. i \<in> I \<Longrightarrow> closed' K (u i) r"
    and "finite I" 
    and "kvs_writers K' = kvs_writers K" 
    and "read_only_Txs K \<subseteq> read_only_Txs K'"
  shows "closed' K' (\<Union>i\<in>I. u i) r"
  using assms                                  
  apply (simp add: closed'_generalize visTx'_Union_distr visTx'_same_writers[of K'])
  apply (rule closed_general_set_Union_closed)
  apply auto
  done

lemma union_closed'_extend_rel:
  assumes "closed' K u\<^sub>1 r"
    and "closed' K u\<^sub>2 r"
    and "kvs_writers K' = kvs_writers K" 
    and "read_only_Txs K \<subseteq> read_only_Txs K'"
    and "x \<notin> (r\<inverse>)\<^sup>* `` (visTx' K u\<^sub>1 \<union> visTx' K u\<^sub>2)"
    and "r' = (\<Union>y\<in>Y. {(y, x)}) \<union> r"
    and "finite Y"
  shows "closed' K' (u\<^sub>1 \<union> u\<^sub>2) r'"
  using assms
  by (auto simp add: closed'_generalize visTx'_union_distr visTx'_same_writers[of K']
      intro: closed_general_union_V_extend_N_extend_rel)


lemma visTx'_new_writer: "kvs_writers K' = insert t (kvs_writers K) \<Longrightarrow>
  snd ` t_wr_deps = {t} \<Longrightarrow> visTx' K' (u \<union> t_wr_deps) = insert t (visTx' K u)"
  by (auto simp add: visTx'_def)

lemma insert_wr_t_closed':
  assumes "closed' K u r"
    and "closed_general {t} (r\<inverse>) (visTx' K u \<union> read_only_Txs K)"
    and "read_only_Txs K' = read_only_Txs K"
    and "kvs_writers K' = insert t (kvs_writers K)"
    and "snd ` t_wr_deps = {t}"
  shows "closed' K' (u \<union> t_wr_deps) r"
  using assms
  by (auto simp add: closed'_generalize visTx'_new_writer intro: closed_general_set_union_closed)

\<comment> \<open>insert (k, t) in version's deps - used in get_ctx\<close>
lemma visTx'_observes_t:
  "t \<in> kvs_writers K \<Longrightarrow> visTx' K (insert (k, t) deps) = insert t (visTx' K deps)"
  by (simp add: visTx'_def)

lemma insert_kt_to_deps_closed':
  assumes "closed' K deps r"
    and "t \<in> kvs_writers K"
    and "closed_general {t} (r\<inverse>) (visTx' K deps \<union> read_only_Txs K)"
  shows "closed' K (insert (k, t) deps) r"
  using assms
  by (auto simp add: closed'_generalize visTx'_observes_t intro: closed_general_set_union_closed)


\<comment> \<open>concrete read_done closedness\<close>

value "foldr (\<union>) [{2 :: nat}, {3 :: nat}] ({1 :: nat})"

lemma "finite (dom kvt_map) \<Longrightarrow>
  Finite_Set.fold (\<union>) {} {insert (k, t) deps | k t deps. kvt_map k = Some (v, t) \<and> P k t deps} =
    \<Union>{insert (k, t) deps | k t deps. kvt_map k = Some (v, t) \<and> P k t deps}"
  apply auto oops
  
lemma get_ctx_closed:
  assumes "closed' K (insert (k, t) deps) r"
    and "cl_state (cls s cl) = RtxnInProg keys kvt_map"
  shows "closed' K (get_ctx s kvt_map) r"
  using assms
  apply (simp add: get_ctx_def)
  thm Union_closed'   (* does not help yet, as union not of form \<Union> (u`I) for a (finite) index set I *)
  oops

lemma fresh_rtxn_not_vis:
  assumes "Tn (get_txn s cl) \<notin> kvs_writers (kvs_of_s s)"
    and "\<forall>t \<in> kvs_writers (kvs_of_s s). get_sn_w t < cl_sn (cls s cl)"
  shows "Tn (get_txn s cl) \<notin> ((R_CC (kvs_of_s s))\<inverse>)\<^sup>* `` (visTx' (kvs_of_s s) (cl_ctx (cls s cl) \<union> get_ctx s kvt_map))"
  apply (auto simp add: visTx'_def R_CC_def)
  subgoal for k t apply (induction t "Tn (get_txn s cl)" rule: rtrancl.induct, auto)
      apply (simp add: assms(1))
     apply (simp add: SO_def SO0_def) oops

lemma read_done_WR_onK:
  assumes "read_done cl kvt_map sn u'' s s'"
  shows "R_onK WR (kvs_of_s s') = (\<Union>y\<in>Y. {(y, Tn (get_txn s cl))}) \<union> R_onK WR (kvs_of_s s)"
  apply (auto simp add: R_onK_def) oops

lemma read_done_extend_rel:
  assumes "read_done cl kvt_map sn u'' s s'"
  shows "R_CC (kvs_of_s s') = (\<Union>y\<in>Y. {(y, Tn (get_txn s cl))}) \<union> R_CC (kvs_of_s s)"
  apply (auto simp add: R_CC_def)
  (*subgoal for k i t' apply (cases t') subgoal for m cl'
    apply (rule exI[where x="Tn_cl (m - 1) cl'"], auto)*) oops

lemma read_done_ctx_closed:
  assumes "closed' (kvs_of_s s) (cl_ctx (cls s cl)) (R_CC (kvs_of_s s))"
    and "closed' (kvs_of_s s) (get_ctx s kvt_map) (R_CC (kvs_of_s s))"
    and "kvs_writers (kvs_of_s s') = kvs_writers (kvs_of_s s)"
    and "read_only_Txs (kvs_of_s s') = insert (Tn (get_txn s cl)) (read_only_Txs (kvs_of_s s))"
    and "Tn (get_txn s cl) \<notin> ((R_CC (kvs_of_s s))\<inverse>)\<^sup>* `` (visTx' (kvs_of_s s) (cl_ctx (cls s cl) \<union> get_ctx s kvt_map))"
    and "R_CC (kvs_of_s s') = (\<Union>y\<in>Y. {(y, Tn (get_txn s cl))}) \<union> R_CC (kvs_of_s s)"
    and "finite Y"
    and "cl_state (cls s cl) = RtxnInProg keys kvt_map"
  shows "closed' (kvs_of_s s') (cl_ctx (cls s cl) \<union> get_ctx s kvt_map) (R_CC (kvs_of_s s'))"
  using assms
  by (auto simp add: closed'_generalize visTx'_union_distr visTx'_same_writers[of "kvs_of_s s'"]
      intro: closed_general_union_V_extend_N_extend_rel)                                 


end
