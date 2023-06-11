theory Closedness
  imports Main
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

text \<open> (* TODO: remove *)
Q: Does the implication of closedness for different R_ET relations imply an ordering of 
isolation guarantees? Not sure, since the execution test includes an initial view extension, 
which need not be the same for different ETs to satisfy their respective commit conditions.
\<close>

end
