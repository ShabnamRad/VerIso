theory Closedness
  imports CCv_Eiger_Port_plus
begin

section \<open>General lemmas about the closedness\<close>
definition closed_general :: "'txn set \<Rightarrow> 'txn rel \<Rightarrow> 'txn set \<Rightarrow> bool" where
  "closed_general vis r r_only \<equiv> vis = ((r\<^sup>*) `` (vis)) - r_only"

lemma closed'_generalize: "closed' K u r = closed_general (visTx' K u) (r^-1) (read_only_Txs K)"
  by (simp add: closed'_def closed_general_def rtrancl_converse)

\<comment> \<open>union read version + deps\<close>
lemma union_closed_general:
  assumes "closed_general vis\<^sub>1 r r_only"
      and "closed_general vis\<^sub>2 r r_only"
      and "r_only \<subseteq> r_only'"
      and "(r_only' - r_only) \<inter> (vis\<^sub>1 \<union> vis\<^sub>2) = {}"
    shows "closed_general (vis\<^sub>1 \<union> vis\<^sub>2) r r_only'"
  using assms
  by (auto simp add: closed_general_def)

lemma union_closed_general':
  assumes "closed_general vis\<^sub>1 r r_only"
      and "closed_general vis\<^sub>2 r r_only"
      and "r_only \<subseteq> r_only'"
      and "(r_only' - r_only) \<inter> (vis\<^sub>1 \<union> vis\<^sub>2) = {}"
      and "r \<subseteq> r'"
      and "Domain (r' - r) \<subseteq> r_only' - r_only"
      and "Range (r' - r) \<inter> (r_only' - r_only) = {}"
    shows "closed_general (vis\<^sub>1 \<union> vis\<^sub>2) r' r_only'"
  using assms
  apply (auto simp add: closed_general_def) oops

lemma visTx'_union_distr: "visTx' K (u\<^sub>1 \<union> u\<^sub>2) = visTx' K u\<^sub>1 \<union> visTx' K u\<^sub>2"
  by (auto simp add: visTx'_def)

lemma visTx'_same_writers: "kvs_writers K' = kvs_writers K \<Longrightarrow> visTx' K' u = visTx' K u"
  by (simp add: visTx'_def)

lemma union_closed':
  assumes "closed' K u\<^sub>1 r"
    and "closed' K u\<^sub>2 r"
    and "kvs_writers K' = kvs_writers K"
    and "read_only_Txs K \<subseteq> read_only_Txs K'"
    and "(read_only_Txs K' - read_only_Txs K) \<inter> (visTx' K' u\<^sub>1 \<union> visTx' K' u\<^sub>2) = {}"
  shows "closed' K' (u\<^sub>1 \<union> u\<^sub>2) r"
  using assms
  by (auto simp add: closed'_generalize visTx'_union_distr visTx'_same_writers[of K']
           intro!: union_closed_general)

\<comment> \<open>insert new write\<close>
lemma insert_t_closed_general:
  assumes "closed_general vis r r_only"
    and "t \<notin> vis"
    and "t \<notin> r_only"
    and "\<And>x. (t, x) \<in> r\<^sup>* \<Longrightarrow> x \<in> vis \<or> x \<in> r_only \<or> x = t"
  shows "closed_general (insert t vis) r r_only"
  using assms
  by (auto simp add: closed_general_def)

lemma visTx'_new_writer: "kvs_writers K' = insert t (kvs_writers K) \<Longrightarrow>
  snd ` t_wr_deps = {t} \<Longrightarrow> visTx' K' (u \<union> t_wr_deps) = insert t (visTx' K u)"
  by (auto simp add: visTx'_def)

lemma insert_wr_t_closed':
  assumes "closed' K u r"
    and "t \<notin> visTx' K u"
    and "\<And>x. (t, x) \<in> (r^-1)\<^sup>* \<Longrightarrow> x \<in> visTx' K u \<or> x \<in> read_only_Txs K \<or> x = t"
    and "read_only_Txs K' = read_only_Txs K"
    and "kvs_writers K' = insert t (kvs_writers K)"
    and "snd ` t_wr_deps = {t}"
  shows "closed' K' (u \<union> t_wr_deps) r"
  using assms
  apply (auto simp add: closed'_generalize visTx'_new_writer intro!: insert_t_closed_general)
  by (metis insert_disjoint(2) inter_write_read_only)

\<comment> \<open>insert (k, t) in version's deps - used in get_ctx\<close>
lemma visTx'_observes_t:
  "t \<in> kvs_writers K \<Longrightarrow> visTx' K (insert (k, t) deps) = insert t (visTx' K deps)"
  by (simp add: visTx'_def)

lemma insert_kt_to_deps_closed':
  assumes "closed' K deps r"
    and "t \<in> kvs_writers K"
    and "t \<notin> visTx' K deps"
    and "\<And>x. (t, x) \<in> (r^-1)\<^sup>* \<Longrightarrow> x \<in> visTx' K deps \<or> x \<in> read_only_Txs K \<or> x = t"
  shows "closed' K (insert (k, t) deps) r"
  using assms
  apply (auto simp add: closed'_generalize visTx'_observes_t intro!: insert_t_closed_general)
  by (metis disjoint_insert(2) insert_absorb inter_write_read_only)

\<comment> \<open>concrete read_done closedness\<close>

lemma read_done_ctx_closed:
  assumes "closed' (kvs_of_s s) (cl_ctx (cls s cl)) (R_CC (kvs_of_s s))"
  shows "closed' (kvs_of_s s') (cl_ctx (cls s cl) \<union> get_ctx s kvt_map) (R_CC (kvs_of_s s'))"
  oops (* not the same r !!!*)

end