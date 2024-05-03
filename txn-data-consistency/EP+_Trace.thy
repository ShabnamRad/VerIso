section \<open>lemmas connecting the trace to tps states\<close>

theory "EP+_Trace"
  imports "EP+_Invariants_Proof" Reductions
begin

definition cl_ord :: "'v ev rel" where
  "cl_ord \<equiv> {(ev1, ev2). ev_cl ev1 \<noteq> None \<and> ev_cl ev1 = ev_cl ev2}"

definition svr_ord :: "'v ev rel" where
  "svr_ord \<equiv> {(ev1, ev2). ev_key ev1 \<noteq> None \<and> ev_key ev1 = ev_key ev2}"

inductive_set txn_ord :: "'v ev rel" where
  "\<lbrakk>t = Tn_cl sn cl; m = clk\<rbrakk> \<Longrightarrow> (RInvoke cl _ sn _ clk, RegR _ t _ _ _ _ m) \<in> txn_ord"
| "\<lbrakk>t = Tn_cl sn cl; m = clk\<rbrakk> \<Longrightarrow> (WInvoke cl _ sn clk, PrepW _ t _ _ m) \<in> txn_ord"
| "\<lbrakk>t = Tn_cl sn cl; m = clk\<rbrakk> \<Longrightarrow> (WCommit cl _ _ sn _ clk _, CommitW _ t _ _ _ _ m) \<in> txn_ord"
| "\<lbrakk>t = Tn_cl sn cl; m = (clk, lst)\<rbrakk> \<Longrightarrow> (RegR k t _ _ clk lst _, Read cl k _ _ sn _ m) \<in> txn_ord"
| "\<lbrakk>t = Tn_cl sn cl; mmap k = Some clk\<rbrakk> \<Longrightarrow> (PrepW k t _ clk _, WCommit cl _ _ sn _ _ mmap) \<in> txn_ord"
| "\<lbrakk>t = Tn_cl sn cl; mmap k = Some (clk, lst)\<rbrakk> \<Longrightarrow>(CommitW k t _ _ clk lst _, WDone cl _ sn _ mmap) \<in> txn_ord"

definition causal_dep0 :: "'v ev list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" ("(3_: _ \<prec>\<^sup>0 _)" [50,50,50] 110) where
  "\<tau>: i \<prec>\<^sup>0 j \<longleftrightarrow> (\<tau> ! i, \<tau> ! j) \<in> cl_ord \<union> svr_ord \<union> txn_ord \<and> i < j"

abbreviation causal_dep :: "'v ev list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" ("(3_: _ \<prec> _)" [50,50,50] 110) where
  "\<tau>: i \<prec> j \<equiv> (i, j) \<in> {(x, y). \<tau>: x \<prec>\<^sup>0 y}\<^sup>+"

lemma causal_dep0I_cl:
  "\<lbrakk>(\<tau> ! i, \<tau> ! j) \<in> cl_ord; i < j\<rbrakk> \<Longrightarrow> \<tau>: i \<prec>\<^sup>0 j"
  by (simp add: causal_dep0_def)

lemma causal_dep0I_svr:
  "\<lbrakk>(\<tau> ! i, \<tau> ! j) \<in> svr_ord; i < j\<rbrakk> \<Longrightarrow> \<tau>: i \<prec>\<^sup>0 j"
  by (simp add: causal_dep0_def)

lemma causal_dep0I_txn:
  "\<lbrakk>(\<tau> ! i, \<tau> ! j) \<in> txn_ord; i < j\<rbrakk> \<Longrightarrow> \<tau>: i \<prec>\<^sup>0 j"
  by (simp add: causal_dep0_def)

lemmas causal_dep0I = causal_dep0I_cl causal_dep0I_svr causal_dep0I_txn

lemma causal_dep0_ind_lt: "\<tau>: x \<prec>\<^sup>0 y \<Longrightarrow>  x < y"
  by (simp add: causal_dep0_def)

lemma causal_dep_ind_lt: "\<tau>: x \<prec> y \<Longrightarrow> x < y"
proof -
  assume a: "\<tau>: x \<prec> y"
  then show "x < y"
    apply (induction x y rule: trancl_trans_induct)
    using a causal_dep0_ind_lt by auto
qed

lemma causal_dep0_tr_trim:
  "(\<tau> @ \<tau>'): j \<prec>\<^sup>0 k \<Longrightarrow> k < length \<tau> \<Longrightarrow>  \<tau>: j \<prec>\<^sup>0 k"
  by (auto simp add: causal_dep0_def nth_append)

lemma causal_dep_tr_trim:
  "(\<tau> @ \<tau>'): j \<prec> k \<Longrightarrow> k < length \<tau> \<Longrightarrow> \<tau>: j \<prec> k"
proof -
  assume *: "(\<tau> @ \<tau>'): j \<prec> k" and **: "k < length \<tau>"
  then show "\<tau>: j \<prec> k"
  proof (induction j k rule: trancl.induct)
    case (trancl_into_trancl a b c)
    then show ?case 
      using causal_dep0_ind_lt[of "\<tau> @ \<tau>'" b c]
        causal_dep0_tr_trim
      by (metis (mono_tags, lifting) case_prodD case_prodI
          mem_Collect_eq order.strict_trans trancl.simps)
  qed (auto simp add: causal_dep0_tr_trim)
qed

lemma causal_dep0_tr_trimprefix:
  "(\<tau> @ \<tau>'): j \<prec>\<^sup>0 k \<Longrightarrow> j \<ge> length \<tau> \<Longrightarrow> \<tau>': (j - length \<tau>) \<prec>\<^sup>0 (k - length \<tau>)"
  by (auto simp add: causal_dep0_def nth_append)

lemma causal_dep_tr_trimprefix:
  "(\<tau> @ \<tau>'): j \<prec> k \<Longrightarrow> j \<ge> length \<tau> \<Longrightarrow> \<tau>': (j - length \<tau>) \<prec> (k - length \<tau>)"
proof -
  assume *: "(\<tau> @ \<tau>'): j \<prec> k" and **: "j \<ge> length \<tau>"
  then show "\<tau>': (j - length \<tau>) \<prec> (k - length \<tau>)"
  proof (induction j k rule: trancl.induct)
    case (trancl_into_trancl a b c)
    then show ?case 
      using causal_dep0_ind_lt[of "\<tau> @ \<tau>'" b c]
        causal_dep0_tr_trimprefix
      by (metis (mono_tags, lifting) causal_dep_ind_lt in_rel_Collect_case_prod_eq
          in_rel_def leD leI order.strict_trans trancl.simps)
  qed (auto simp add: causal_dep0_tr_trimprefix)
qed

lemma causal_dep0_tr_append:
  "\<tau>: j \<prec>\<^sup>0 k \<Longrightarrow> k < length \<tau> \<Longrightarrow> (\<tau> @ \<tau>'): j \<prec>\<^sup>0 k"
  by (simp add: causal_dep0_def nth_append)

lemma causal_dep_tr_append:
  "\<tau>: j \<prec> k \<Longrightarrow> k < length \<tau> \<Longrightarrow> (\<tau> @ \<tau>'): j \<prec> k"
proof -
  assume "\<tau>: j \<prec> k" and "k < length \<tau>"
  then show "(\<tau> @ \<tau>'): j \<prec> k"
  proof (induction j k rule: trancl.induct)
    case (trancl_into_trancl a b c)
    then show ?case 
      using causal_dep0_ind_lt[of \<tau> b c]
        causal_dep0_tr_append
      by (metis Transitive_Closure.trancl_into_trancl case_prod_conv
          less_than_def less_than_iff mem_Collect_eq trancl_trans)
  qed (auto simp add: causal_dep0_tr_append)
qed

lemma causal_dep0_tr_prepend:
  "\<tau>': j \<prec>\<^sup>0 k \<Longrightarrow> (\<tau> @ \<tau>'): (j + length \<tau>) \<prec>\<^sup>0 (k + length \<tau>)"
  by (simp add: causal_dep0_def nth_append)

lemma causal_dep_tr_prepend:
  "\<tau>': j \<prec> k \<Longrightarrow> (\<tau> @ \<tau>'): (j + length \<tau>) \<prec> (k + length \<tau>)"
proof -
  assume "\<tau>': j \<prec> k"
  then show "(\<tau> @ \<tau>'): (j + length \<tau>) \<prec> (k + length \<tau>)"
  proof (induction j k rule: trancl.induct)
    case (trancl_into_trancl a b c)
    then show ?case 
      using causal_dep0_ind_lt[of \<tau> b c]
      by (metis Transitive_Closure.trancl_into_trancl causal_dep0_tr_prepend
          mem_Collect_eq old.prod.case)
  qed (auto simp add: causal_dep0_tr_prepend)
qed

lemma adj_causal_dep_dep0:
  "\<tau>: i \<prec> Suc i \<longleftrightarrow> \<tau>: i \<prec>\<^sup>0 Suc i"
proof
  assume "\<tau>: i \<prec> Suc i"
  then show "\<tau>: i \<prec>\<^sup>0 Suc i"
  proof (induction i "Suc i" rule: trancl.induct)
    case (trancl_into_trancl a b)
    then show ?case
      using causal_dep0_ind_lt causal_dep_ind_lt not_less_eq
      by blast
  qed simp
qed auto


\<comment> \<open>Lemmas for cl_ord and svr_ord: independent events have different clients/keys\<close>

lemma indep_cl_neq:
  assumes
    \<open>\<not> \<tau>: i \<prec> j\<close>
    \<open>i < j\<close>
    \<open>ev_cl (\<tau> ! j) \<noteq> None\<close>
  shows "ev_cl (\<tau> ! i) \<noteq> ev_cl (\<tau> ! j)"
  using assms
  by (auto simp add: causal_dep0_def cl_ord_def)

lemma indep_svr_neq:
  assumes
    \<open>\<not> \<tau>: i \<prec> j\<close>
    \<open>i < j\<close>
    \<open>ev_key (\<tau> ! j) \<noteq> None\<close>
  shows "ev_key (\<tau> ! i) \<noteq> ev_key (\<tau> ! j)"
  using assms
  by (auto simp add: causal_dep0_def svr_ord_def)

lemma trancl_into_r: "(a, b) \<notin> r\<^sup>+ \<Longrightarrow> (a, b) \<notin> r"
  by auto



\<comment> \<open>Lemmas: causal_dep when the trace changes (for \<prec>: swapping a pair of events)\<close>

lemma causal_dep0_ev_pres:
  assumes
    \<open>\<tau>: i \<prec>\<^sup>0 j\<close>
    \<open>\<tau>' ! i' = \<tau> ! i\<close>
    \<open>\<tau>' ! j' = \<tau> ! j\<close>
    \<open>i' < j'\<close>
  shows "\<tau>': i' \<prec>\<^sup>0 j'"
  using assms
  by (simp add: causal_dep0_def)

lemma nth_append_Suc_length [simp]:
  "(l @ e1 # e2 # l') ! Suc (length l) = e2"
  by (metis append.left_neutral append_Cons append_assoc length_append_singleton nth_append_length)

lemma nth_larger_Suc_length:
  "a > Suc (length l) \<Longrightarrow> (l @ e2 # e1 # l') ! a = (l @ e1 # e2 # l') ! a"
proof -
  assume a: "a > Suc (length l)"
  then have "((l @ e2 # [e1]) @ l') ! a = ((l @ e1 # [e2]) @ l') ! a"
    by (smt (verit, ccfv_threshold) One_nat_def Suc_eq_plus1 add_Suc_right length_Cons length_append
        list.size(3) not_less_eq nth_append)
  then show ?thesis by force
qed

lemma causal_indep_swap:
  assumes
    \<open>tps: s0 \<midarrow>\<langle>\<tau> @ e1 # e2 # \<tau>'\<rangle>\<rightarrow> sf\<close>
    \<open>reach tps s0\<close>
    \<open>\<not>(\<tau> @ e1 # e2 # \<tau>'): i \<prec> Suc i\<close>
    \<open>i = length \<tau>\<close>
  shows "\<not>(\<tau> @ e2 # e1 # \<tau>'): i \<prec> Suc i"
  using assms unfolding adj_causal_dep_dep0
proof -
  assume "tps: s0 \<midarrow>\<langle>\<tau> @ e1 # e2 # \<tau>'\<rangle>\<rightarrow> sf" "reach tps s0" and
    a: "\<not>(\<tau> @ e1 # e2 # \<tau>'): i \<prec>\<^sup>0 Suc i" "i = length \<tau>"
  then obtain s s' s'' where
    "tps: s0 \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s" "tps: s \<midarrow>e1\<rightarrow> s'" "tps: s' \<midarrow>e2\<rightarrow> s''"
    by (meson trace_append_invert trace_consD trace_snoc)
  then show "\<not>(\<tau> @ e2 # e1 # \<tau>'): i \<prec>\<^sup>0 Suc i" using a
  proof (auto simp add: causal_dep0_def) \<comment> \<open>make a lemma\<close>
    assume "(e2, e1) \<in> txn_ord"
      "state_trans s e1 s'" "state_trans s' e2 s''"
      "(e1, e2) \<notin> cl_ord" "(e1, e2) \<notin> svr_ord" "(e1, e2) \<notin> txn_ord"
    then show False
    proof (induction e2 e1 rule: txn_ord.induct) 
      case (3 t sn cl m clk) \<comment> \<open>CW \<rightarrow> WC\<close>
      then have "\<exists>cts kv_map. cl_state (cls s' cl) = WtxnCommit cts kv_map"
        by (auto simp add: tps_trans_top_defs commit_write_G_def commit_write_U_def)
      then show ?case using 3
        by (simp add: write_commit_def write_commit_G_def)
    next
      case (4 t sn cl m clk lst k) \<comment> \<open>R \<rightarrow> RR\<close>
      then have
        "\<exists>cclk keys kv_map v. cl_state (cls s' cl) = RtxnInProg cclk keys kv_map \<and>
         kv_map k = Some v"
        by (auto simp add: tps_trans_top_defs read_G_def read_U_def)
      then show ?case using 4
        by (auto simp add: register_read_def register_read_G_def)
    qed (simp_all add: tps_trans_defs)
  qed (auto simp add: cl_ord_def svr_ord_def nth_append)
qed


lemma causal_dep_swap_left_len:
  assumes
    \<open>(\<tau> @ e1 # e2 # \<tau>'): i \<prec> j\<close>
    \<open>i < length \<tau>\<close>
    \<open>j = length \<tau>\<close>
  shows "(\<tau> @ e2 # e1 # \<tau>'): i \<prec> Suc j"
  using assms(1-3)
proof (induction i j rule: trancl.induct)
  case (r_into_trancl a b)
  then show ?case
    using causal_dep0_ev_pres[of "\<tau> @ e1 # e2 # \<tau>'" a b "\<tau> @ e2 # e1 # \<tau>'" a "Suc b"]
    by (simp add: nth_append trancl.r_into_trancl)
next
  case (trancl_into_trancl a b c)
  then have b_lt_len: "b < length \<tau>" using causal_dep_ind_lt by blast
  then have "(\<tau> @ e2 # e1 # \<tau>'): a \<prec> b"
    using  trancl_into_trancl(1) causal_dep_tr_append causal_dep_tr_trim
    by blast
  then show ?case using trancl_into_trancl(2,5)
    using causal_dep0_ev_pres[of "\<tau> @ e1 # e2 # \<tau>'" b c "\<tau> @ e2 # e1 # \<tau>'" b "Suc c"]
    by (metis (no_types) nth_append case_prodI mem_Collect_eq trancl.simps case_prodD less_SucI
        b_lt_len nth_append_Suc_length nth_append_length)
qed

lemma causal_dep_swap_left_Suc_len:
  assumes
    \<open>(\<tau> @ e1 # e2 # \<tau>'): i \<prec> j\<close>
    \<open>i < length \<tau>\<close>
    \<open>j = Suc (length \<tau>)\<close>
    \<open>\<not> (\<tau> @ e1 # e2 # \<tau>'): length \<tau> \<prec> Suc (length \<tau>)\<close>
  shows "(\<tau> @ e2 # e1 # \<tau>'): i \<prec> (j - 1)"
  using assms(1-3)
proof (induction i j rule: trancl.induct)
  case (r_into_trancl a b)
  then show ?case
    using causal_dep0_ev_pres[of "\<tau> @ e1 # e2 # \<tau>'" a b "\<tau> @ e2 # e1 # \<tau>'" a "b - 1"]
    by (simp add: nth_append trancl.r_into_trancl)
next
  case (trancl_into_trancl a b c)
  then have b_lt_len: "b < length \<tau>" using assms(4) causal_dep_ind_lt Suc_lessI by blast
  then have "(\<tau> @ e2 # e1 # \<tau>'): a \<prec> b"
    using  trancl_into_trancl(1) causal_dep_tr_append causal_dep_tr_trim
    by blast
  then show ?case using trancl_into_trancl(2,5)
    using causal_dep0_ev_pres[of "\<tau> @ e1 # e2 # \<tau>'" b c "\<tau> @ e2 # e1 # \<tau>'" b "c - 1"]
    by (metis (no_types, lifting) b_lt_len case_prodD case_prodI diff_Suc_1 mem_Collect_eq
        nth_append nth_append_Suc_length nth_append_length trancl.simps)
qed

lemma causal_dep_swap_len_right:
  assumes
    \<open>(\<tau> @ e1 # e2 # \<tau>'): i \<prec> j\<close>
    \<open>i = length \<tau>\<close>
    \<open>j \<ge> Suc (Suc (length \<tau>))\<close>
    \<open>\<not> (\<tau> @ e1 # e2 # \<tau>'): length \<tau> \<prec> Suc (length \<tau>)\<close>
  shows "(\<tau> @ e2 # e1 # \<tau>'): Suc i \<prec> j"
  using assms(1-3)
proof (induction i j rule: trancl.induct)
  case (r_into_trancl a b)
  then show ?case
    using causal_dep0_ev_pres[of "\<tau> @ e1 # e2 # \<tau>'" a b "\<tau> @ e2 # e1 # \<tau>'" "Suc a" b]
    by (metis Suc_le_lessD case_prodD case_prodI mem_Collect_eq nth_append_Suc_length
        nth_append_length nth_larger_Suc_length r_into_trancl')
next
  case (trancl_into_trancl a b c)
  then have b_gt_Sucl: "b > Suc (length \<tau>)" using assms(4) causal_dep_ind_lt Suc_lessI by blast
  then have "(\<tau> @ e2 # e1 # \<tau>') ! b = (\<tau> @ e1 # e2 # \<tau>') ! b" by (metis nth_larger_Suc_length)
  then show ?case using trancl_into_trancl
    using causal_dep0_ind_lt[of "\<tau> @ e1 # e2 # \<tau>'" b c]
          causal_dep0_ev_pres[of "\<tau> @ e1 # e2 # \<tau>'" b c "\<tau> @ e2 # e1 # \<tau>'" b c]
    by (metis b_gt_Sucl case_prodD case_prodI less_eq_Suc_le mem_Collect_eq nth_larger_Suc_length trancl.simps)
qed

lemma causal_dep_swap_Suc_len_right:
  assumes
    \<open>(\<tau> @ e1 # e2 # \<tau>'): i \<prec> j\<close>
    \<open>i = Suc (length \<tau>)\<close>
    \<open>j \<ge> Suc (Suc (length \<tau>))\<close>
  shows "(\<tau> @ e2 # e1 # \<tau>'): (i - 1) \<prec> j"
  using assms(1-3)
proof (induction i j rule: trancl.induct)
  case (r_into_trancl a b)
  then show ?case
    using causal_dep0_ev_pres[of "\<tau> @ e1 # e2 # \<tau>'" a b "\<tau> @ e2 # e1 # \<tau>'" "a - 1" b]
    by (metis Suc_leD Suc_le_lessD case_prodD case_prodI diff_Suc_1 mem_Collect_eq
        nth_append_Suc_length nth_append_length nth_larger_Suc_length r_into_trancl')
next
  case (trancl_into_trancl a b c)
  then have b_gt_Sucl: "b > Suc (length \<tau>)" using causal_dep_ind_lt by blast
  then have "(\<tau> @ e2 # e1 # \<tau>') ! b = (\<tau> @ e1 # e2 # \<tau>') ! b" by (metis nth_larger_Suc_length)
  then show ?case using trancl_into_trancl
    using causal_dep0_ind_lt[of "\<tau> @ e1 # e2 # \<tau>'" b c]
          causal_dep0_ev_pres[of "\<tau> @ e1 # e2 # \<tau>'" b c "\<tau> @ e2 # e1 # \<tau>'" b c]
    by (metis b_gt_Sucl case_prodD case_prodI less_eq_Suc_le mem_Collect_eq nth_larger_Suc_length trancl.simps)
qed

lemma causal_dep_swap_within:
  assumes
    \<open>(\<tau> @ e1 # e2 # \<tau>'): i \<prec> j\<close>
    \<open>i < length \<tau>\<close>
    \<open>j \<ge> Suc (Suc (length \<tau>))\<close>
    \<open>\<not> (\<tau> @ e1 # e2 # \<tau>'): length \<tau> \<prec> Suc (length \<tau>)\<close>
  shows "(\<tau> @ e2 # e1 # \<tau>'): i \<prec> j"
  using assms(1-3)
proof (induction i j rule: trancl.induct)
  case (r_into_trancl a b)
  then show ?case
    using causal_dep0_ev_pres[of "\<tau> @ e1 # e2 # \<tau>'" a b "\<tau> @ e2 # e1 # \<tau>'" a b]
    by (metis Suc_le_lessD case_prodD case_prodI causal_dep0_ind_lt mem_Collect_eq
        nth_append nth_larger_Suc_length trancl.r_into_trancl)
next
  case (trancl_into_trancl a b c)
  then have "\<exists>b'. (\<tau> @ e2 # e1 # \<tau>') ! b' = (\<tau> @ e1 # e2 # \<tau>') ! b \<and>
    (\<tau> @ e2 # e1 # \<tau>'): a \<prec> b' \<and> b' < c"
  proof (cases "b < length \<tau>")
    case b_lt_l: False
    then show ?thesis
      using assms(4) trancl_into_trancl causal_dep_swap_left_len[of a b]
    proof (cases "b = length \<tau>")
      case b_not_l: False
      then show ?thesis
        using assms(4) trancl_into_trancl causal_dep_swap_left_Suc_len[of a b]
        proof (cases "b = Suc (length \<tau>)")
          case False
          then show ?thesis using b_lt_l b_not_l trancl_into_trancl
            by (metis Suc_leI Suc_lessI causal_dep_ind_lt linorder_neqE_nat
                nth_larger_Suc_length trancl.simps trancl_into_trancl.IH)
        qed (intro exI[where x="length \<tau>"], auto)
    qed (intro exI[where x="Suc (length \<tau>)"], auto)
  qed (smt Suc_le_eq Suc_lessD causal_dep_tr_append causal_dep_tr_trim dual_order.strict_trans nth_append)
  then obtain b' where
    "(\<tau> @ e2 # e1 # \<tau>') ! b' = (\<tau> @ e1 # e2 # \<tau>') ! b" "(\<tau> @ e2 # e1 # \<tau>'): a \<prec> b'" "b' < c" by blast
  then show ?case using trancl_into_trancl(2,5)
    using causal_dep0_ev_pres[of "\<tau> @ e1 # e2 # \<tau>'" b c "\<tau> @ e2 # e1 # \<tau>'" b' c]
    by (metis Suc_le_lessD case_prodD case_prodI mem_Collect_eq nth_larger_Suc_length trancl.simps)
qed


subsection \<open>Lemmas\<close>

lemma trace_cts_order_tps:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>init tps s\<close>
  shows "Tn (Tn_cl sn cl) \<in> set (cts_order s' k) \<longleftrightarrow>
    (\<exists>kv_map cts u'' clk mmap. k \<in> dom kv_map \<and> WCommit cl kv_map cts sn u'' clk mmap \<in> set \<tau>)"
  using assms(1)
proof (induction \<tau> s' rule: trace.induct)
  case trace_nil
  then show ?case using assms(2) by (simp add: tps_defs)
next
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (simp add: tps_trans_all_defs set_insort_key)
      by (metis domIff option.discI)
  qed (auto simp add: tps_trans_defs)
qed

lemma wtxn_cts_immutable:
  assumes
    \<open>wtxn_cts s t = Some c\<close>
    \<open>tps: s \<midarrow>e\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
  shows
    \<open>wtxn_cts s' t = Some c\<close>
  using assms
proof (induction e)
  case (WCommit x1 x2 x3 x4 x5)
  then show ?case apply (simp add: write_commit_def write_commit_U_def write_commit_G_def)
    apply (cases "t = get_wtxn s x1", auto) using Wtxn_Cts_Tn_None_def
    by (metis (lifting) reach_wtxn_cts_tn_none domI domIff insertCI less_imp_neq linorder_not_le)
qed (auto simp add: tps_trans_defs)

lemma WC_in_\<tau>_wtxn_cts:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>WCommit cl kv_map cts sn u'' clk mmap \<in> set \<tau>\<close>
  shows "wtxn_cts s' (Tn (Tn_cl sn cl)) = Some cts"
  using assms
proof (induction \<tau> s' arbitrary: cl kv_map cts sn u'' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: set_insort_key)
      subgoal by (simp add: tps_trans_all_defs) 
      subgoal using wtxn_cts_immutable[of s' "Tn (Tn_cl sn cl)" cts "WCommit x1 x2 x3 x4 x5 x6 x7" s'']
        apply (simp add: trace_is_trace_of_exec_frag reach_last_exec valid_exec_def)
        apply (cases "get_txn s' x1 = Tn_cl sn cl")
        apply (meson valid_exec_frag_append)
        by (auto simp add: tps_trans_all_defs)
      done
  qed (auto simp add: tps_trans_defs)
qed simp

lemma wtxn_cts_WC_in_\<tau>:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>init tps s\<close>
    \<open>wtxn_cts s' (Tn (Tn_cl sn cl)) = Some cts\<close>
  shows "\<exists>kv_map u'' clk mmap. WCommit cl kv_map cts sn u'' clk mmap \<in> set \<tau>"
  using assms
proof (induction \<tau> s' arbitrary: cl cts sn rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case apply (auto simp add: set_insort_key tps_trans_defs)
      by (metis option.inject)
  qed (auto simp add: tps_trans_defs)
qed (simp add: tps_defs)

lemma WC_in_\<tau>_kv_map_non_emp:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>WCommit cl kv_map cts sn u'' clk mmap \<in> set \<tau>\<close>
  shows "\<exists>k v. kv_map k = Some v"
  using assms
proof (induction \<tau> s' arbitrary: cl kv_map cts sn u'' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6 x7)
    then show ?case using Dom_Kv_map_Not_Emp_def[of s' x1]
    by (auto simp add: reach_trace_extend tps_trans_defs)
  qed (auto simp add: tps_trans_defs)
qed simp


subsubsection \<open>cl_ord clock invariant\<close>

lemma last_clk_max_in_cl:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>ev_cl (\<tau> ! i) = Some cl\<close>
    \<open>i < length \<tau>\<close>
  shows \<open>ev_clk (\<tau> ! i) \<le> cl_clock (cls s' cl)\<close>
  using assms
proof (induction \<tau> s' arbitrary: i rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (cases "i = length \<tau>")
    case True
    then show ?thesis using trace_snoc
      by (induction e) (auto simp add: tps_trans_defs)
  next
    case False
    then show ?thesis using trace_snoc
      apply (simp add: nth_append)
      using cl_clock_monotonic le_trans not_less_less_Suc_eq
      by (metis (mono_tags, lifting) reach_trace_extend)
  qed
qed simp

lemma cl_ord_implies_clk_order:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>(\<tau> ! j, \<tau> ! k) \<in> cl_ord\<close>
    \<open>j < k\<close>
    \<open>k < length \<tau>\<close>
  shows \<open>ev_clk (\<tau> ! j) < ev_clk (\<tau> ! k)\<close>
  using assms
proof (induction \<tau> s' arbitrary: j k rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (cases "k = length \<tau>")
    case True
    then show ?thesis using trace_snoc
    proof (induction e)
      case (WCommit x1 x2 x3 x4 x5 x6 x7)
      then have "cl_clock (cls s' x1) < cl_clock (cls s'' x1)"
        using cl_clock_monotonic_WCommit[of s']
        by (simp add: reach_trace_extend)
      then show ?case using WCommit
        apply (auto simp add: tps_trans_defs nth_append cl_ord_def last_clk_max_in_cl le_imp_less_Suc)
        using last_clk_max_in_cl[of s \<tau> s' j x1] by auto
    qed (auto simp add: tps_trans_defs nth_append cl_ord_def last_clk_max_in_cl le_imp_less_Suc,
          ((meson last_clk_max_in_cl le_imp_less_Suc le_trans max.coboundedI1)+)?)
  next
    case False
    then show ?thesis using trace_snoc by (simp add: nth_append)
  qed
qed simp


subsubsection \<open>svr_ord clock invariant\<close>

lemma last_clk_max_in_svr:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>ev_key (\<tau> ! i) = Some k\<close>
    \<open>i < length \<tau>\<close>
  shows \<open>ev_clk (\<tau> ! i) \<le> svr_clock (svrs s' k)\<close>
  using assms
proof (induction \<tau> s' arbitrary: i rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (cases "i = length \<tau>")
    case True
    then show ?thesis using trace_snoc
      by (induction e) (auto simp add: tps_trans_defs)
  next
    case False
    then show ?thesis using trace_snoc
      apply (simp add: nth_append)
      using svr_clock_monotonic le_trans not_less_less_Suc_eq by blast
  qed
qed simp

lemma svr_ord_implies_clk_order:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>(\<tau> ! j, \<tau> ! k) \<in> svr_ord\<close>
    \<open>j < k\<close>
    \<open>k < length \<tau>\<close>
  shows \<open>ev_clk (\<tau> ! j) < ev_clk (\<tau> ! k)\<close>
  using assms
proof (induction \<tau> s' arbitrary: j k rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (cases "k = length \<tau>")
    case True
    then show ?thesis using trace_snoc
      by (induction e)
        (auto simp add: tps_trans_defs nth_append svr_ord_def last_clk_max_in_svr le_imp_less_Suc,
          ((meson last_clk_max_in_svr le_imp_less_Suc le_trans max.coboundedI1)+)?)
  next
    case False
    then show ?thesis using trace_snoc by (simp add: nth_append)
  qed
qed simp


subsubsection \<open>txn_ord clock invariant\<close>

lemma helper:
  "x k = Some y \<Longrightarrow> finite (dom x) \<Longrightarrow> f k < Suc (Max {f k |k. k \<in> dom x})"
  apply (simp add: Setcompr_eq_image)
  by (metis Max.coboundedI domI finite_imageI le_imp_less_Suc not_in_image)

lemma sc_ord_implies_clk_order:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>(\<tau> ! j, \<tau> ! k) \<in> txn_ord\<close>
    \<open>j < k\<close>
    \<open>k < length \<tau>\<close>
  shows \<open>ev_clk (\<tau> ! j) < ev_clk (\<tau> ! k)\<close>
  using assms
proof (induction \<tau> s' arbitrary: j k rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (cases "k = length \<tau>")
    case True
    then show ?thesis using trace_snoc
    proof (induction e)
      case (Read x1 x2 x3 x4 x5 x6 x7)
      then show ?case 
      proof (cases "\<tau> ! j")
        case (RegR x71 x72 x73 x74 x75 x76 x77)
        then show ?thesis using Read by (simp add: nth_append txn_ord.simps tps_trans_defs)
      qed (simp_all add: nth_append txn_ord.simps)
    next
      case (WCommit x1 x2 x3 x4 x5 x6 x7)
      then show ?case 
      proof (cases "\<tau> ! j")
        case (PrepW x81 x82 x83 x84 x85)
        then show ?thesis using WCommit
          apply (auto simp add: nth_append txn_ord.simps tps_trans_defs)
          using Finite_Dom_Kv_map_def[of s' x1]
            helper[of x2 x81 _ "\<lambda>k. get_ts (svr_state (svrs s' k) (get_wtxn s' x1))"] 
          apply simp
          by (smt not_None_eq option.inject reach_finite_dom_kv_map reach_trace_extend)
      qed (simp_all add: nth_append txn_ord.simps)
    next
      case (WDone x1 x2 x3 x4 x5)
      then show ?case 
      proof (cases "\<tau> ! j")
        case (CommitW x91 x92 x93 x94 x95 x96 x97)
        then show ?thesis using WDone
          apply (cases "x2 x91", auto simp add: nth_append txn_ord.simps tps_trans_defs)
          using Finite_Dom_Kv_map_def[of s' x1]
            helper[of x2 x91 _ "\<lambda>k. get_sclk (svr_state (svrs s' k) (get_wtxn s' x1))"] 
          apply simp
          by (meson less_Suc_eq_le max.coboundedI2 reach_finite_dom_kv_map reach_trace_extend)
         qed (simp_all add: nth_append txn_ord.simps)
    next
      case (RegR x1 x2 x3 x4 x5 x6 x7)
      then show ?case 
      proof (cases "\<tau> ! j")
        case (RInvoke x11 x12 x13 x14 x15)
        then show ?thesis using RegR by (auto simp add: nth_append txn_ord.simps tps_trans_defs)
      qed (simp_all add: nth_append txn_ord.simps)
    next
      case (PrepW x1 x2 x3 x4 x5)
      then show ?case 
      proof (cases "\<tau> ! j")
        case (WInvoke x41 x42 x43 x44)
        then show ?thesis using PrepW by (auto simp add: nth_append txn_ord.simps tps_trans_defs)
      qed (simp_all add: nth_append txn_ord.simps)
    next
      case (CommitW x1 x2 x3 x4 x5 x6 x7)
      then show ?case 
      proof (cases "\<tau> ! j")
        case (WCommit x51 x52 x53 x54 x55 x56 x57)
        then show ?thesis using CommitW by (auto simp add: nth_append txn_ord.simps tps_trans_defs)
      qed (simp_all add: nth_append txn_ord.simps)
    qed (auto simp add: txn_ord.simps)
  next
    case False
    then show ?thesis using trace_snoc by (simp add: nth_append)
  qed
qed simp


subsubsection \<open>causal_dep clock invariant\<close>
lemma causal_dep0_implies_clk_order:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>\<tau>: j \<prec>\<^sup>0 k\<close>
    \<open>k < length \<tau>\<close>
  shows \<open>ev_clk (\<tau> ! j) < ev_clk (\<tau> ! k)\<close>
  using assms
proof (induction \<tau> s' arbitrary: j k rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (cases "k = length \<tau>")
    case True
    then show ?thesis using trace_snoc
        causal_dep0_tr_trim[of \<tau>]
        causal_dep0_ind_lt[of "\<tau> @ [e]" j k]
      apply (auto simp add: causal_dep0_def)
      subgoal by (metis (mono_tags, lifting) cl_ord_implies_clk_order nth_append_length
          trace.trace_snoc trace_snoc.hyps(2) trace_snoc.prems(3)) \<comment> \<open>cl_ord\<close>
      subgoal by (metis (mono_tags, lifting) svr_ord_implies_clk_order nth_append_length
          trace.trace_snoc trace_snoc.hyps(2) trace_snoc.prems(3)) \<comment> \<open>svr_ord\<close>
      subgoal by (metis (no_types, lifting) sc_ord_implies_clk_order nth_append_length
            trace.trace_snoc trace_snoc.hyps(2) trace_snoc.prems(3)) \<comment> \<open>txn_ord\<close>
      done
  next
    case False
    then show ?thesis using trace_snoc
        causal_dep0_tr_trim[of \<tau>]
        causal_dep0_ind_lt[of "\<tau> @ [e]" j k]
      by (simp add: nth_append)
    qed
qed simp


lemma causal_dep_implies_clk_order:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>\<tau>: j \<prec> k\<close>
    \<open>k < length \<tau>\<close>
  shows \<open>ev_clk (\<tau> ! j) < ev_clk (\<tau> ! k)\<close>
  using assms(3-)
proof (induction j k rule: trancl.induct)
  case (r_into_trancl a b)
  then show ?case using assms(1,2) causal_dep0_implies_clk_order by blast
next
  case (trancl_into_trancl a b c)
  then show ?case 
    using assms(1,2) causal_dep0_ind_lt[of \<tau> b c] apply auto
    by (smt (verit, best) add_diff_inverse_nat causal_dep0_implies_clk_order less_SucI
        not_less_eq trans_less_add1)
qed


lemma WCommit_clk_Suc_cts:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>i < length \<tau>\<close>
    \<open>\<tau> ! i = WCommit cl kv_map cts sn u'' clk mmap\<close>
  shows \<open>clk = Suc cts\<close>
  using assms
proof (induction \<tau> s' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6)
    then show ?case
      apply (cases "i = length \<tau>", simp add: tps_trans_defs)
      by (simp add: length_append_singleton not_less_less_Suc_eq nth_append)
  qed (simp_all, (smt ev.distinct less_SucE nth_append nth_append_length)+)
qed simp

lemma WCommit_cts_causal_dep_gt_past:
  assumes
    \<open>tps: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close>
    \<open>reach tps s\<close>
    \<open>k < length \<tau>\<close>
    \<open>\<tau> ! j = WCommit cl kv_map cts sn u'' clk mmap\<close>
    \<open>\<tau> ! k = WCommit cl' kv_map' cts' sn' u''' clk' mmap'\<close>
    \<open>\<tau>: j \<prec> k\<close>
  shows \<open>(cts, Suc cl) < (cts', Suc cl')\<close>
  using assms
proof (induction \<tau> s' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case
  proof (induction e)
    case (WCommit x1 x2 x3 x4 x5 x6)
    then show ?case apply (simp add: less_prod_def) using WCommit_clk_Suc_cts
    by (smt (verit) add_less_imp_less_left assms causal_dep_implies_clk_order causal_dep_ind_lt
        ev_clk.simps(5) less_trans_Suc nth_append plus_1_eq_Suc)
  qed (simp_all, (smt (verit) append_eq_conv_conj causal_dep_ind_lt ev.distinct
      causal_dep_tr_trim less_SucE less_supI2 nth_append_length nth_take sup.strict_order_iff)+)
qed simp


end