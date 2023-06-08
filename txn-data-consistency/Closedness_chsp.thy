theory Closedness_chsp
  imports CCv_Eiger_Port_plus
begin

section \<open>Lemmas about relational image and transititve closure\<close>

lemma Image_rtrancl_insert_max:
  assumes "x \<notin> (r\<^sup>*) `` V" 
  shows "(insert (x, y) r)\<^sup>* `` V  = (r\<^sup>*) `` V" 
  using assms
proof - 
  from assms have "\<And>B. ({xa. (xa, x) \<in> r\<^sup>*} \<times> B) `` V = {}" by auto
  then show ?thesis using assms
    by (auto simp add: rtrancl_insert Un_Image)
qed

lemma Image_rtrancl_union_max:
  assumes "finite B" "x \<notin> (r\<^sup>*) `` V" 
  shows "((\<Union>y\<in>B. {(x, y)}) \<union> r)\<^sup>* `` V = (r\<^sup>*) `` V" 
  using assms
by (induction rule: finite.induct) (simp_all add: Image_rtrancl_insert_max)


section \<open>Closedness: general definition and basic lemmas\<close>

text \<open>Original general definition\<close>

definition closed_general' :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "closed_general' V r N \<longleftrightarrow> V = ((r\<^sup>*) `` V) - N"

prop "V \<inter> N = {}"        \<comment> \<open>we can always assume this\<close>


text \<open>Alternative def, equivalent under our conditions; probably easier to understand; 
obviates need for some assumptions in lemmas below; also somewhat easier to work with?\<close>

definition closed_general :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "closed_general V r N \<longleftrightarrow> (r\<^sup>*) `` V \<subseteq> V \<union> N"

lemma closed_generalI: "(r\<^sup>*) `` V \<subseteq> V \<union> N \<Longrightarrow> closed_general V r N"
  by (simp add: closed_general_def)

lemma closed_generalE [elim]: 
  "\<lbrakk> closed_general V r N; (r\<^sup>*) `` V \<subseteq> V \<union> N \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add: closed_general_def)

lemma closed_general_equiv:
  assumes "V \<inter> N = {}"
  shows "closed_general V r N \<longleftrightarrow> closed_general' V r N"
  using assms
  by (unfold closed_general_def closed_general'_def) blast    \<comment> \<open>just by general set theory\<close>


text \<open>Empty set, monotonicity, and unions; note that monotonicity holds in @{term N}, but it
does not hold in @{term V}.\<close>

lemma closed_general_empty [simp, intro!]: 
  shows "closed_general {} r N"
  by (auto simp add: closed_general_def)

lemma closed_general_mono_N [elim]:
  assumes "closed_general V r N" 
  and "N \<subseteq> N'" (* "N' \<inter> V = {}"; assumption not needed with alternative def *)
  shows "closed_general V r N'"
  using assms
  by (auto simp add: closed_general_def)

lemma closed_general_set_union_closed:   
  assumes "closed_general V\<^sub>1 r N\<^sub>1"
      and "closed_general V\<^sub>2 r N\<^sub>2"
      and "V = V\<^sub>1 \<union> V\<^sub>2"
      and "N\<^sub>1 \<union> N\<^sub>2 \<subseteq> V\<^sub>1 \<union> V\<^sub>2 \<union> N"
  shows "closed_general V r N"
  using assms
  by (auto simp add: closed_general_def)


text \<open>Extending the relation\<close>

lemma closed_general_insert_rel_max:
  assumes "closed_general V r N" 
  and "r' = insert (x, y) r" 
  and "x \<notin> (r\<^sup>*) `` V"                   \<comment> \<open>implies @{prop "x \<notin> V"} and @{prop "x \<notin> r``V"}\<close>
  shows "closed_general V r' N"
  using assms
  by (auto simp add: closed_general_def Image_rtrancl_insert_max)

lemma closed_general_extend_rel_max:    \<comment> \<open>generalizes previous lemma\<close>
  assumes "closed_general V r N" 
  and "r' = (\<Union>y\<in>Y. {(x, y)}) \<union> r" 
  and "x \<notin> (r\<^sup>*) `` V" 
  and "finite Y"
  shows "closed_general V r' N"
  using assms
  by (auto simp add: closed_general_def Image_rtrancl_union_max)


text \<open>
  Q: Sufficent conditions to satisfy premise @{prop "x \<notin> (r\<^sup>*) `` V"} in the two previous lemmas?
  In lemma below, first premise below does not necessarily hold for SO!
\<close>
lemma "\<lbrakk> x \<notin> Range r; x \<notin> V \<rbrakk> \<Longrightarrow> x \<notin> (r\<^sup>*) `` V"
  by (metis ImageE Range_iff rtranclE)


text \<open>Implications between closedness for different relations\<close>

lemma closed_general_hierarchy:
  assumes "closed_general V r N"
  and "r'\<^sup>* `` V \<subseteq> r\<^sup>* `` V"
  shows "closed_general V r' N"
  using assms
  by (simp add: closed_general_def)

lemma closed_general_anti_mono:
  assumes "closed_general V r N"
  and "r' \<subseteq> r"
  shows "closed_general V r' N"
  using assms
  by (auto intro: closed_general_hierarchy rtrancl_mono Image_mono del: subsetI)

text \<open>
Q: Does the implication of closedness for different R_ET relations imply an ordering of 
isolation guarantees? Not sure, since the execution test includes an initial view extension, 
which need not be the same for different ETs to satisfy their respective commit conditions.
\<close>


(****************************************************************************************)
(****************************************************************************************)

(* except for lemma closed'_generalize, no further unfolding of closed_general(')_def below *)

(*
  some combinations, still with closed_general
*)

\<comment> \<open>union read version + deps\<close>

lemma closed_general_union_V_extend_N:
  assumes "closed_general vis\<^sub>1 r r_only"
      and "closed_general vis\<^sub>2 r r_only"
      and "r_only \<subseteq> r_only'"
      (* and "r_only' \<inter> (vis\<^sub>1 \<union> vis\<^sub>2) = {}"; not needed with alternative def *)
    shows "closed_general (vis\<^sub>1 \<union> vis\<^sub>2) r r_only'"
  using assms
  by (auto intro: closed_general_set_union_closed)


\<comment> \<open>all at once ;-)\<close>

lemma closed_general_union_V_extend_N_extend_rel:
  assumes "closed_general vis\<^sub>1 r r_only"
      and "closed_general vis\<^sub>2 r r_only"
      and "r_only \<subseteq> r_only'"
      (* and "r_only' \<inter> (vis\<^sub>1 \<union> vis\<^sub>2) = {}"; not needed with alternative def *)
      and "r' = (\<Union>y\<in>V. {(x, y)}) \<union> r" 
      and "x \<notin> (r\<^sup>*) `` (vis\<^sub>1 \<union> vis\<^sub>2)" 
      (* and "V \<subseteq> vis\<^sub>1 \<union> vis\<^sub>2";  assumption not needed  *)
      and "finite V"
    shows "closed_general (vis\<^sub>1 \<union> vis\<^sub>2) r' r_only'"         \<comment> \<open>r changes as well!\<close>
  using assms
  by (auto intro: closed_general_set_union_closed[THEN closed_general_extend_rel_max])


(****************************************************************************************)
(****************************************************************************************)
(****************************************************************************************)
(****************************************************************************************)

text \<open>NOTE: @{term closed'} should be defined in terms of @{term "closed_general"}!\<close>

lemma closed'_generalize: 
  "closed' K u r = closed_general (visTx' K u) (r^-1) (read_only_Txs K)"
proof -
  have "visTx' K u \<inter> read_only_Txs K = {}"
    by (simp add: diff_eq read_only_Txs_def visTx'_def) 
  then show ?thesis
    by (simp add: closed'_def closed_general_equiv closed_general'_def rtrancl_converse)
qed

lemma visTx'_union_distr: "visTx' K (u\<^sub>1 \<union> u\<^sub>2) = visTx' K u\<^sub>1 \<union> visTx' K u\<^sub>2"
  by (auto simp add: visTx'_def)

lemma visTx'_same_writers: "kvs_writers K' = kvs_writers K \<Longrightarrow> visTx' K' u = visTx' K u"
  by (simp add: visTx'_def)

lemma union_closed':
  assumes "closed' K u\<^sub>1 r"
    and "closed' K u\<^sub>2 r"
    and "kvs_writers K' = kvs_writers K" 
    and "read_only_Txs K \<subseteq> read_only_Txs K'"
    (* and "read_only_Txs K' \<inter> (visTx' K' u\<^sub>1 \<union> visTx' K' u\<^sub>2) = {}"; not needed with alt def! *)
  shows "closed' K' (u\<^sub>1 \<union> u\<^sub>2) r"
  using assms
  by (auto simp add: closed'_generalize visTx'_union_distr visTx'_same_writers[of K']
           intro: closed_general_set_union_closed)


lemma visTx'_new_writer: "kvs_writers K' = insert t (kvs_writers K) \<Longrightarrow>
  snd ` t_wr_deps = {t} \<Longrightarrow> visTx' K' (u \<union> t_wr_deps) = insert t (visTx' K u)"
  by (auto simp add: visTx'_def)

lemma insert_wr_t_closed':
  assumes "closed' K u r"
    (* and "t \<notin> visTx' K u";  not needed with alternative def! *)
    and "closed_general {t} (r^-1) (visTx' K u \<union> read_only_Txs K)"
    (* and "(r^-1)\<^sup>* `` {t} \<subseteq> insert t (visTx' K u \<union> read_only_Txs K)"; same previous premise *)
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
    (* and "t \<notin> visTx' K deps";  not needed with alternative def! *)
    and "closed_general {t} (r^-1) (visTx' K deps \<union> read_only_Txs K)"
    (* and "(r^-1)\<^sup>* `` {t} \<subseteq> insert t (visTx' K deps \<union> read_only_Txs K)"; same as prvious premise *) 

  shows "closed' K (insert (k, t) deps) r"
  using assms
  by (auto simp add: closed'_generalize visTx'_observes_t intro: closed_general_set_union_closed)


\<comment> \<open>concrete read_done closedness\<close>

lemma read_done_ctx_closed:
  assumes "closed' (kvs_of_s s) (cl_ctx (cls s cl)) (R_CC (kvs_of_s s))"
  shows "closed' (kvs_of_s s') (cl_ctx (cls s cl) \<union> get_ctx s kvt_map) (R_CC (kvs_of_s s'))"
  oops (* not the same r !!!*)
  (*
     TBC
  *)


end
