section \<open>Event Systems\<close>

text\<open>This theory contains definitions of event systems, trace, traces, reachability, simulation,
and proves the soundness of simulation for proving trace inclusion. We also derive some related
simulation rules.\<close>

theory Event_Systems
  imports Main 
begin

record ('e, 's) ES =
  init :: "'s \<Rightarrow> bool"
  trans :: "'s \<Rightarrow> 'e \<Rightarrow> 's \<Rightarrow> bool"   ("(4_: _ \<midarrow>_\<rightarrow> _)" [50, 50, 50, 50] 90)


(********************************************************************************)
subsection \<open>Reachable states and invariants\<close>
(********************************************************************************)

inductive
  reach :: "('e, 's) ES \<Rightarrow> 's \<Rightarrow> bool" for E
  where
    reach_init [simp, intro]:  "init E s \<Longrightarrow> reach E s"
  | reach_trans [intro]: "\<lbrakk> E: s \<midarrow>e\<rightarrow> s'; reach E s \<rbrakk> \<Longrightarrow> reach E s'"


text \<open>Abbreviation for stating that a predicate is an invariant of an event system.\<close>

definition Inv :: "('e, 's) ES \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
  "Inv E I \<longleftrightarrow> (\<forall>s. reach E s \<longrightarrow> I s)"

lemmas InvI = Inv_def [THEN iffD2, rule_format]
lemmas InvE [elim] = Inv_def [THEN iffD1, elim_format, rule_format]

lemma Invariant_rule [case_names Inv_init Inv_trans]:
  assumes "\<And>s0. init E s0 \<Longrightarrow> I s0"
     and  "\<And>s e s'. \<lbrakk>E: s \<midarrow>e\<rightarrow> s'; reach E s; I s\<rbrakk> \<Longrightarrow> I s'"
  shows "Inv E I"
  unfolding Inv_def
proof (intro allI impI)
  fix s
  assume "reach E s"
  then show "I s" using assms
    by (induction s rule: reach.induct) (auto)
qed


text \<open>Invariant rule that allows strengthening the proof with another invariant.\<close>
lemma Invariant_rule_Inv [case_names Inv_other Inv_init Inv_trans]:
  assumes "Inv E J"
     and  "\<And>s0. init E s0 \<Longrightarrow> I s0"
     and  "\<And>s e s'. \<lbrakk>E: s \<midarrow>e\<rightarrow> s'; reach E s; I s; J s; J s'\<rbrakk> \<Longrightarrow> I s'"
  shows "Inv E I"
  unfolding Inv_def
proof (intro allI impI)
  fix s
  assume "reach E s"
  then show "I s" using assms
    by (induction s rule: reach.induct)(auto 3 4)
qed


(********************************************************************************)
subsection \<open>Traces\<close>
(********************************************************************************)

type_synonym 'e trace = "'e list"

inductive
  trace :: "('e, 's) ES \<Rightarrow> 's \<Rightarrow> 'e trace \<Rightarrow> 's \<Rightarrow> bool"  ("(4_: _ \<midarrow>\<langle>_\<rangle>\<rightarrow> _)" [50, 50, 50] 110)  
  for E s 
  where
    trace_nil [simp,intro!]: 
      "E: s \<midarrow>\<langle>[]\<rangle>\<rightarrow> s"
  | trace_snoc [intro]: 
      "\<lbrakk> E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'; E: s' \<midarrow>e\<rightarrow> s'' \<rbrakk> \<Longrightarrow> E: s \<midarrow>\<langle>\<tau> @ [e]\<rangle>\<rightarrow> s''"

inductive_cases trace_nil_invert [elim!]: "E: s \<midarrow>\<langle>[]\<rangle>\<rightarrow> t"
inductive_cases trace_snoc_invert [elim]: "E: s \<midarrow>\<langle>\<tau> @ [e]\<rangle>\<rightarrow> t"


lemma trace_init_independence [elim]: 
  assumes "E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'" "trans E = trans F" 
  shows "F: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'"
  using assms
by (induction rule: trace.induct) auto

lemma trace_single [simp, intro!]: "\<lbrakk> E: s \<midarrow>e\<rightarrow> s' \<rbrakk> \<Longrightarrow> E: s \<midarrow>\<langle>[e]\<rangle>\<rightarrow> s'"
  by (auto intro: trace_snoc[where \<tau> = "[]", simplified])


text \<open>Next, we prove an introduction rule for a "cons" trace and a case analysis rule 
distinguishing the empty trace and a "cons" trace.\<close>

lemma trace_consI:
  assumes 
    "E: s'' \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'" "E: s \<midarrow>e\<rightarrow> s''" 
  shows
    "E: s \<midarrow>\<langle>e # \<tau>\<rangle>\<rightarrow> s'"
  using assms
by (induction rule: trace.induct) (auto dest: trace_snoc) 

lemma trace_cases_cons:
  assumes 
    "E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'"
    "\<lbrakk> \<tau> = []; s' = s \<rbrakk> \<Longrightarrow> P"
    "\<And>e \<tau>' s''. \<lbrakk> \<tau> = e # \<tau>'; E: s \<midarrow>e\<rightarrow> s''; E: s'' \<midarrow>\<langle>\<tau>'\<rangle>\<rightarrow> s' \<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms
by (induction rule: trace.induct) fastforce+

lemma trace_consD: "(E: s \<midarrow>\<langle>e # \<tau>\<rangle>\<rightarrow> s') \<Longrightarrow> \<exists> s''. (E: s \<midarrow>e\<rightarrow> s'') \<and> (E: s'' \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s')" 
  by(auto elim: trace_cases_cons)


text \<open>We show how a trace can be appended to another.\<close>

lemma trace_append: "\<lbrakk> E: s \<midarrow>\<langle>\<tau>\<^sub>1\<rangle>\<rightarrow> s'; E: s' \<midarrow>\<langle>\<tau>\<^sub>2\<rangle>\<rightarrow> s''\<rbrakk> \<Longrightarrow> E: s \<midarrow>\<langle>\<tau>\<^sub>1@\<tau>\<^sub>2\<rangle>\<rightarrow> s''"
  by(induction \<tau>\<^sub>1 arbitrary: s)
    (auto dest!: trace_consD intro: trace_consI)

lemma trace_append_invert: "(E: s \<midarrow>\<langle>\<tau>\<^sub>1@\<tau>\<^sub>2\<rangle>\<rightarrow> s'') \<Longrightarrow> \<exists>s' . (E: s \<midarrow>\<langle>\<tau>\<^sub>1\<rangle>\<rightarrow> s') \<and> (E: s' \<midarrow>\<langle>\<tau>\<^sub>2\<rangle>\<rightarrow> s'')"
  by (induction \<tau>\<^sub>1 arbitrary: s) (auto intro!: trace_consI dest!: trace_consD)


text\<open>We prove an induction scheme for combining two traces, similar to @{text list_induct2}.\<close>

lemma trace_induct2 [consumes 3, case_names Nil Snoc]: 
  "\<lbrakk>E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s''; F: t \<midarrow>\<langle>\<sigma>\<rangle>\<rightarrow> t''; length \<tau> = length \<sigma>;
    P [] s [] t; 
    \<And>\<tau> s' e s'' \<sigma> t' f t''. 
    \<lbrakk>E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'; E: s'\<midarrow>e\<rightarrow> s''; F: t \<midarrow>\<langle>\<sigma>\<rangle>\<rightarrow> t'; F: t'\<midarrow>f\<rightarrow> t''; P \<tau> s' \<sigma> t'\<rbrakk> 
      \<Longrightarrow> P (\<tau> @ [e]) s'' (\<sigma> @ [f]) t''\<rbrakk> 
  \<Longrightarrow> P \<tau> s'' \<sigma> t''" 
proof (induction \<tau> s'' arbitrary: \<sigma> t'' rule: trace.induct)
  case trace_nil
  then show ?case by auto 
next
  case (trace_snoc \<tau> s' e s'')
  from \<open>length (\<tau> @ [e]) = length \<sigma>\<close> and \<open>F: t \<midarrow>\<langle>\<sigma>\<rangle>\<rightarrow> t''\<close>
  obtain f \<sigma>' t' 
    where "\<sigma> = \<sigma>' @ [f]" "length \<tau> = length \<sigma>'" "F: t \<midarrow>\<langle>\<sigma>'\<rangle>\<rightarrow> t'" "F: t' \<midarrow>f\<rightarrow> t''"
    by (auto elim: trace.cases)
  then show ?case using trace_snoc by blast
qed


subsubsection \<open>Relate traces to reachability and invariants\<close> 
(********************************************************************************)

lemma reach_trace_equiv: "reach E s \<longleftrightarrow> (\<exists>s0 \<tau>. init E s0 \<and> E: s0 \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s)"  (is "?A \<longleftrightarrow> ?B")
proof
  assume "?A" then show "?B" 
    by (induction s rule: reach.induct) auto
next
  assume "?B" 
  then obtain s0 \<tau> where "E: s0 \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s" "init E s0" by blast
  then show "?A"
    by (induction \<tau> s rule: trace.induct) auto
qed

lemma reach_traceI: "\<lbrakk>init E s0; E: s0 \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s\<rbrakk> \<Longrightarrow> reach E s" 
  by(auto simp add: reach_trace_equiv)

lemma reach_trace_extend [elim]: "\<lbrakk>E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'; reach E s\<rbrakk> \<Longrightarrow> reach E s'"
  by (induction \<tau> s' rule: trace.induct) auto

lemma Inv_trace: "\<lbrakk>Inv E I; init E s0; E: s0 \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<rbrakk> \<Longrightarrow> I s'"
  by (auto simp add: Inv_def reach_trace_equiv)


subsubsection \<open>Trace semantics of event systems\<close>
(********************************************************************************)

text \<open>We define the set of traces of an event system.\<close>

definition traces :: "('e, 's) ES \<Rightarrow> 'e trace set" where
  "traces E = {\<tau>. \<exists>s s'. init E s \<and> E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'}"

lemma tracesI [intro]: "\<lbrakk> init E s; E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s' \<rbrakk> \<Longrightarrow> \<tau> \<in> traces E"
  by (auto simp add: traces_def)

lemma tracesE [elim]: "\<lbrakk> \<tau> \<in> traces E; \<And>s s'. \<lbrakk> init E s; E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp add: traces_def)

lemma traces_nil [simp, intro!]: "init E s \<Longrightarrow> [] \<in> traces E"
  by (auto simp add: traces_def)


text\<open>We now define a trace property satisfaction relation: an event system satisfies a property 
@{term "\<phi>"}, if its traces are contained in @{term \<phi>}.\<close>

definition trace_property :: "('e, 's) ES \<Rightarrow> 'e trace set \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>E\<^sub>S" 90) where 
  "E \<Turnstile>\<^sub>E\<^sub>S \<phi> \<longleftrightarrow> traces E \<subseteq> \<phi>" 

lemmas trace_propertyI = trace_property_def [THEN iffD2, OF subsetI, rule_format]
lemmas trace_propertyE [elim] = trace_property_def [THEN iffD1, THEN subsetD, elim_format]
lemmas trace_propertyD = trace_property_def [THEN iffD1, THEN subsetD, rule_format]


text \<open>Rules for showing trace properties using a stronger trace-state invariant.\<close>

lemma trace_invariant: 
  assumes 
    "\<tau> \<in> traces E"
    "\<And>s s'. \<lbrakk> init E s; E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s' \<rbrakk> \<Longrightarrow> I \<tau> s'"
    "\<And>s. I \<tau> s \<Longrightarrow> \<tau> \<in> \<phi>"
  shows "\<tau> \<in> \<phi>" using assms
  by (auto)

lemma trace_property_rule: 
  assumes 
    "\<And>s0. init E s0 \<Longrightarrow> I [] s0"
    "\<And>s s' \<tau> e s''. 
       \<lbrakk> init E s; E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'; E: s' \<midarrow>e\<rightarrow> s''; I \<tau> s'; reach E s' \<rbrakk> \<Longrightarrow> I (\<tau>@[e]) s''"
    "\<And>\<tau> s. \<lbrakk> I \<tau> s; reach E s \<rbrakk> \<Longrightarrow> \<tau> \<in> \<phi>"
  shows "E \<Turnstile>\<^sub>E\<^sub>S \<phi>"
proof (rule trace_propertyI, erule trace_invariant[where I="\<lambda>\<tau> s. I \<tau> s \<and> reach E s"])
  fix \<tau> s s'
  assume "E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'" and "init E s" 
  then show "I \<tau> s' \<and> reach E s'" 
    by (induction \<tau> s' rule: trace.induct) (auto simp add: assms)
qed (auto simp add: assms)

text \<open>Similar to @{thm trace_property_rule}, but allows matching pure state invariants directly.\<close>
lemma Inv_trace_property:
  assumes "Inv E I" and "[] \<in> \<phi>" 
      and "(\<And>s \<tau> s' e s''. 
      \<lbrakk>init E s; E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'; E: s' \<midarrow>e\<rightarrow> s''; I s; I s'; reach E s'; \<tau> \<in> \<phi>\<rbrakk> \<Longrightarrow> \<tau>@[e] \<in> \<phi>)" 
    shows "E \<Turnstile>\<^sub>E\<^sub>S \<phi>"
  using assms(1,2)
  by (intro trace_property_rule[where I="\<lambda>\<tau> s. \<tau> \<in> \<phi>"]) (auto intro: assms(3))


(********************************************************************************)
subsection \<open>Simulation\<close>
(********************************************************************************)

subsubsection \<open>Simulation for event systems\<close>
(********************************************************************************)

inductive 
  sim_ES_R :: "('e, 's ) ES \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow> ('f, 't ) ES \<Rightarrow> bool"  
     ("(4_ \<sqsubseteq>\<^bsub>_,_\<^esub> _)" [50, 60, 60, 50] 95) for E R \<pi> F
  where 
    "\<lbrakk> \<And>s0. init E s0 \<Longrightarrow> (\<exists>t0. init F t0 \<and> R s0 t0);
       \<And>s e s' t. \<lbrakk> R s t; reach E s; reach F t; E: s \<midarrow>e\<rightarrow> s' \<rbrakk> \<Longrightarrow> \<exists>t'. (F: t \<midarrow>\<pi> e\<rightarrow> t') \<and> R s' t' \<rbrakk>
      \<Longrightarrow> E \<sqsubseteq>\<^bsub>R,\<pi>\<^esub> F"

lemmas simulation_with_rel = sim_ES_R.intros

thm sim_ES_R.intros sim_ES_R.cases


text \<open>Abbreviation for a functional simulation relation\<close>
abbreviation sim_ES_h ("(4_ \<sqsubseteq>\<^bsub>[_,_]\<^esub> _)" [50, 60, 60, 50] 95) where
  "E \<sqsubseteq>\<^bsub>[h,\<pi>]\<^esub> F \<equiv> E \<sqsubseteq>\<^bsub>(\<lambda>s t. t = h s),\<pi>\<^esub> F"


text \<open>Simulation without exposing R\<close>
definition 
  sim_ES :: "('e, 's ) ES \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow> ('f, 't ) ES \<Rightarrow> bool"  ("(3_ \<sqsubseteq>\<^sub>_ _)" [50, 60, 50] 95) 
where 
  "E \<sqsubseteq>\<^sub>\<pi> F \<longleftrightarrow> (\<exists>R. E \<sqsubseteq>\<^bsub>R,\<pi>\<^esub> F)"

lemmas sim_ES_I = sim_ES_def[THEN iffD2, OF exI]
lemmas sim_ES_E = sim_ES_def[THEN iffD1, elim_format]

lemmas simulate_ES = simulation_with_rel[THEN sim_ES_I]

lemma simulate_ES_with_invariants: 
  assumes
    init: "\<And>s0. init E s0 \<Longrightarrow> (\<exists>t0. init F t0 \<and> R s0 t0)" and
    step: "\<And>s t a s'.  
             \<lbrakk> R s t; I s; J t; E: s\<midarrow>a\<rightarrow> s' \<rbrakk> \<Longrightarrow> (\<exists>t'. (F: t\<midarrow>\<pi> a\<rightarrow> t') \<and> R s' t')" and
    invE: "\<And>s. reach E s \<longrightarrow> I s" and
    invE: "\<And>t. reach F t \<longrightarrow> J t"
  shows "E \<sqsubseteq>\<^sub>\<pi> F" using assms
  by (auto intro: simulate_ES[where R=R])

lemmas simulate_ES_with_invariant = simulate_ES_with_invariants[where J="\<lambda>s. True", simplified]



text \<open>Variants with a functional simulation relation, aka refinement mapping.\<close>

lemma simulate_ES_fun_h: 
  assumes 
    init: "\<And>s0. init E s0 \<Longrightarrow> init F (h s0)" and
    step: "\<And>s a s'. \<lbrakk> E: s\<midarrow>a\<rightarrow> s'; reach E s; reach F (h s) \<rbrakk> \<Longrightarrow> F: h s\<midarrow>\<pi> a\<rightarrow> h s'"
  shows "E \<sqsubseteq>\<^bsub>[h,\<pi>]\<^esub> F"
  using assms
  by (auto intro!: simulation_with_rel[where R="\<lambda>s t. t = h s"])

lemmas simulate_ES_fun = simulate_ES_fun_h[THEN sim_ES_I]

lemma simulate_ES_fun_with_invariants: 
  assumes 
    init: "\<And>s0. init E s0 \<Longrightarrow> init F (h s0)" and
    step: "\<And>s a s'. \<lbrakk> E: s\<midarrow>a\<rightarrow> s'; I s; J (h s) \<rbrakk> \<Longrightarrow> F: h s\<midarrow>\<pi> a\<rightarrow> h s'" and
    invE: "\<And>s. reach E s \<longrightarrow> I s" and
    invF: "\<And>t. reach F t \<longrightarrow> J t"
  shows "E \<sqsubseteq>\<^sub>\<pi> F"
  using assms
  by (auto intro!: simulate_ES_fun)

lemmas simulate_ES_fun_with_invariant = 
  simulate_ES_fun_with_invariants[where J="\<lambda>t. True", simplified]


subsubsection \<open>Soundness for inclusion of reachable states\<close>
(********************************************************************************)

lemma simulation_fun_reach_soundness: 
  assumes "E \<sqsubseteq>\<^bsub>[h,\<pi>]\<^esub> F" 
  shows "h ` {s. reach E s} \<subseteq> {s. reach F s}"
  using assms
proof -
  {
    assume
      init: "\<And>s0. init E s0 \<Longrightarrow> init F (h s0)" and
      step: "\<And>s a s'. \<lbrakk> E: s\<midarrow>a\<rightarrow> s'; reach E s; reach F (h s) \<rbrakk> \<Longrightarrow> F: h s\<midarrow>\<pi> a\<rightarrow> h s'"
    have "h ` {s. reach E s} \<subseteq> {s. reach F s}"
    proof 
      fix t
      assume "t \<in> h ` {s. reach E s}"
      then obtain s where "t = h s" and "reach E s" by auto
      from \<open>reach E s\<close> have "reach F (h s)" 
        by (induction) (auto intro: init step)
      then show "t \<in> {s. reach F s}" using \<open>t = h s\<close> by simp
    qed
  }
  then show ?thesis using assms
    by (elim sim_ES_R.cases) (auto)
qed


subsubsection \<open>Soundness for trace inclusion and property preservation\<close>
(********************************************************************************)

text \<open>Extend transition simulation to traces.\<close>

lemma trace_sim:
  assumes 
    "E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'" "R s t" "reach E s" "reach F t"
    "\<And>s e t s'. \<lbrakk> R s t; reach E s; reach F t; E: s \<midarrow>e\<rightarrow> s' \<rbrakk> \<Longrightarrow> \<exists>t'. (F: t \<midarrow>\<pi> e\<rightarrow> t') \<and> R s' t'"
  shows "\<exists>t'. (F: t \<midarrow>\<langle>map \<pi> \<tau>\<rangle>\<rightarrow> t') \<and> (R s' t')"
  using assms
proof (induction \<tau> s' rule: trace.induct)
  case trace_nil
  then show ?case by auto
next
  case (trace_snoc \<tau> s' e s'')
  then obtain t' where "F: t \<midarrow>\<langle>map \<pi> \<tau>\<rangle>\<rightarrow> t'" "R s' t'" by auto
  have \<open>reach E s'\<close> \<open>reach F t'\<close> using \<open>E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close> \<open>F: t \<midarrow>\<langle>map \<pi> \<tau>\<rangle>\<rightarrow> t'\<close> \<open>reach E s\<close> \<open>reach F t\<close>
    by auto
  with \<open>R s' t'\<close> \<open>E: s'\<midarrow>e\<rightarrow> s''\<close> 
  obtain t'' where "F: t' \<midarrow>\<pi> e\<rightarrow> t''" "R s'' t''" using trace_snoc.prems(4) by fastforce
  then show ?case using \<open>F: t \<midarrow>\<langle>map \<pi> \<tau>\<rangle>\<rightarrow> t'\<close> \<open>E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close> \<open>E: s'\<midarrow>e\<rightarrow> s''\<close> by auto
qed 

lemma simulation_soundness: 
  assumes "E \<sqsubseteq>\<^sub>\<pi> F" 
  shows "map \<pi> ` traces E \<subseteq> traces F"
proof (intro subsetI, elim imageE, simp)
  fix \<tau> 
  assume "\<tau> \<in> traces E"
  then obtain s s' where "E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'" "init E s" by auto
  from \<open>E \<sqsubseteq>\<^sub>\<pi> F\<close> obtain R where "E \<sqsubseteq>\<^bsub>R,\<pi>\<^esub> F" by (auto simp add: sim_ES_def)
  then obtain t where "init F t" "R s t" using \<open>init E s\<close> by (elim sim_ES_R.cases) fastforce
  then show \<open>map \<pi> \<tau> \<in> traces F\<close> using \<open>E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close> \<open>E \<sqsubseteq>\<^bsub>R,\<pi>\<^esub> F\<close> \<open>init E s\<close>
    by (auto elim!: sim_ES_R.cases dest!: trace_sim[where R=R])
qed


lemmas simulation_rule = simulate_ES [THEN simulation_soundness]
lemmas simulation_rule_id = simulation_rule[where \<pi>="id", simplified]


text \<open>This allows us to show that properties are preserved under simulation.\<close>

lemma property_preservation_trivial: 
  "\<lbrakk>  map \<pi>`traces E \<subseteq> traces F; F \<Turnstile>\<^sub>E\<^sub>S P; \<And>\<tau>. map \<pi> \<tau> \<in> P \<Longrightarrow> \<tau> \<in> Q \<rbrakk> \<Longrightarrow> E \<Turnstile>\<^sub>E\<^sub>S Q" 
  by (auto simp add: trace_property_def)

corollary property_preservation: 
  "\<lbrakk>E \<sqsubseteq>\<^sub>\<pi> F; F \<Turnstile>\<^sub>E\<^sub>S P; \<And>\<tau>. map \<pi> \<tau> \<in> P \<Longrightarrow> \<tau> \<in> Q \<rbrakk> \<Longrightarrow> E \<Turnstile>\<^sub>E\<^sub>S Q" 
  by (auto simp add: trace_property_def dest: simulation_soundness)


end
