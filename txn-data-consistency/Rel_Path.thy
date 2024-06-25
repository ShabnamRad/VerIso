theory Rel_Path
  imports Main
begin

\<comment> \<open>rel_path with cons extension\<close>

inductive rel_path :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> bool" for R where
  no_hop:    "rel_path R x [] x" | 
  one_hop:   "(x, y) \<in> R \<Longrightarrow> rel_path R x [(x, y)] y" |
  more_hops: "\<lbrakk> (x, y) \<in> R; rel_path R y \<pi> z \<rbrakk> \<Longrightarrow> rel_path R x ((x, y) # \<pi>) z"

thm converse_trancl_induct

lemma rel_path_for_transitive_rel:
  assumes "(x, y) \<in> R\<^sup>+"
  shows "\<exists>\<pi>. rel_path R x \<pi> y"
  using assms 
  by (induction x rule: converse_trancl_induct)
     (auto intro: rel_path.intros)


\<comment> \<open>prove snoc version as a lemma\<close>

lemma rel_path_snoc:
  assumes "rel_path R x \<pi> y" "(y, z) \<in> R"
  shows "rel_path R x (\<pi> @ [(y, z)]) z"
  using assms
proof (induction \<pi> y rule: rel_path.induct)
  case no_hop
  then show ?case by (auto intro: rel_path.intros)
next
  case (one_hop z)
  then show ?case 
    by (smt (verit) append_eq_Cons_conv rel_path.one_hop rel_path.simps)
next
  case (more_hops \<pi> y z)
  then show ?case by (simp add: rel_path.more_hops) 
qed

inductive_cases rel_path_snoc_invert: "rel_path R x (\<pi>' @ [(y, z)]) z"
inductive_cases rel_path_cons_invert: "rel_path R x ((x, y) # \<pi>') z"


lemma rel_path_non_empty:
  assumes \<open>rel_path R x \<pi> z\<close> \<open>\<pi> \<noteq> []\<close>
  shows \<open>\<exists>\<pi>' y. rel_path R x ((x, y) # \<pi>' ) z\<close>
  using assms
proof (cases rule: rel_path.cases)
  case no_hop
  then show ?thesis using \<open>\<pi> \<noteq> []\<close> by simp
qed (auto intro: rel_path.intros)


thm trancl.induct
thm trancl_induct

lemma rel_path_for_refl_trans_rel:
  shows "(x, y) \<in> R\<^sup>* \<longleftrightarrow> (\<exists>\<pi>. rel_path R x \<pi> y)" 
proof (intro iffI; (elim exE)?)
  assume "(x, y) \<in> R\<^sup>*"
  then show "\<exists>\<pi>. rel_path R x \<pi> y"
    by (induction y rule: rtrancl_induct) 
       (auto intro: rel_path.intros rel_path_for_transitive_rel rtrancl_into_trancl1) 
next
  fix \<pi>
  assume "rel_path R x \<pi> y" 
  then show "(x, y) \<in> R\<^sup>*" 
    by (induction \<pi> y rule: rel_path.induct) (auto intro: rel_path.intros)
qed

lemma rel_path_for_trans_rel:
  "(x, y) \<in> R\<^sup>+ \<longleftrightarrow> (\<exists>\<pi>. rel_path R x \<pi> y \<and> \<pi> \<noteq> [])" 
proof (safe)
  assume "(x, y) \<in> R\<^sup>+"
  then obtain z where "(x, z) \<in> R" "(z, y) \<in> R\<^sup>*" by (meson tranclD)
  then obtain \<pi> where "rel_path R z \<pi> y" by (auto simp add: rel_path_for_refl_trans_rel)
  then show "\<exists>\<pi>. rel_path R x \<pi> y \<and> \<pi> \<noteq> []" using \<open>(x, z) \<in> R\<close>
    by (intro exI[where x="(x, z) # \<pi>"]) (auto intro: rel_path.intros)
next
  fix \<pi>
  assume "rel_path R x \<pi> y" "\<pi> \<noteq> []"
  then obtain \<pi>' z where "rel_path R x ((x, z) # \<pi>') y" by (auto dest: rel_path_non_empty)
  then obtain "rel_path R z \<pi>' y" "(x, z) \<in> R"  
    by (elim rel_path_cons_invert) (auto intro: rel_path.intros)
  then have "\<exists>\<pi>. rel_path R z \<pi>' y" by auto
  then have "(z, y) \<in> R\<^sup>*" by (auto simp add: rel_path_for_refl_trans_rel) 
  then show "(x, y) \<in> R\<^sup>+" using \<open>(x, z) \<in> R\<close> by auto
qed


thm rel_path.induct
thm rel_path.intros

lemma rel_path_split1:
  assumes 
    "rel_path (R \<union> S) x \<pi> z" "(u, x) \<in> R"
    \<comment> \<open>induction did not work with assumption @{prop "z \<in> Z"} here\<close>
    \<comment> \<open>induction worked after removing it and adding disjunct @{prop "y = z"} to conclusion instead\<close>
    "\<And>a b. (a, b) \<in> S \<Longrightarrow> a \<in> Z"
  shows "\<exists>\<pi>\<^sub>1 \<pi>\<^sub>2 y. rel_path R x \<pi>\<^sub>1 y \<and> rel_path (R \<union> S) y \<pi>\<^sub>2 z \<and> \<pi> = \<pi>\<^sub>1 @ \<pi>\<^sub>2 \<and> (y \<in> Z \<or> y = z)"
  using assms(1-2)
proof (induction \<pi> z arbitrary: u rule: rel_path.induct)
  case no_hop
  then show ?case by (auto intro: rel_path.intros)
next
  case (one_hop x y)
  then show ?case 
    apply (elim UnE)
    subgoal by (rule exI[where x="[(x, y)]"]) 
               (auto intro: rel_path.intros(1,3))
    subgoal by (rule exI[where x="[]"])
               (auto intro: rel_path.intros(1,2) assms(3))
    done
next
  case (more_hops x y \<pi> z)
  then show ?case using assms(3)
  proof (safe)
    assume a: "rel_path (R \<union> S) y \<pi> z" "(x, y) \<in> R"
    then obtain \<pi>\<^sub>1 \<pi>\<^sub>2 y' where
      "rel_path R y \<pi>\<^sub>1 y'"
      "rel_path (R \<union> S) y' \<pi>\<^sub>2 z"
      "\<pi> = \<pi>\<^sub>1 @ \<pi>\<^sub>2"
      "y' \<in> Z \<or> y' = z"
      using more_hops.IH by blast
    then show ?thesis using a
      apply (simp)
      by (rule exI[where x="(x, y) # \<pi>\<^sub>1"])
         (auto intro: rel_path.intros)
  next
    assume "rel_path (R \<union> S) y \<pi> z" "(x, y) \<in> S"
    then show ?thesis
      by (auto intro: rel_path.intros assms(3))
  qed
qed

text \<open>This seems to be +/- the lemma we need for SO; right?\<close>

lemma rel_path_split2:
  assumes 
    "rel_path (R \<union> S) x \<pi> z" "(u, x) \<in> R" "z \<in> Z"
    "\<And>a b. (a, b) \<in> S \<Longrightarrow> a \<in> Z"
  shows "\<exists>\<pi>\<^sub>1 \<pi>\<^sub>2 y. rel_path R x \<pi>\<^sub>1 y \<and> rel_path (R \<union> S) y \<pi>\<^sub>2 z \<and> \<pi> = \<pi>\<^sub>1 @ \<pi>\<^sub>2 \<and> y \<in> Z"
  using assms rel_path_split1[where u=u and Z=Z] by blast

end