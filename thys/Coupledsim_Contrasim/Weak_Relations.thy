
subsection \<open>Weak Simulation\<close>

theory Weak_Relations
imports
  Weak_Transition_Systems
  Strong_Relations
begin

context lts_tau
begin

definition weak_simulation :: 
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>weak_simulation R \<equiv> \<forall> p q. R p q \<longrightarrow> 
    (\<forall> p' a. p \<longmapsto>a p' \<longrightarrow> (\<exists> q'. R p' q'
      \<and> (q \<Rightarrow>^a q')))\<close>

text \<open>Note: Isabelle won't finish the proofs needed for the introduction of the following
  coinductive predicate if it unfolds the abbreviation of @{text \<open>\<Rightarrow>^\<close>}. Therefore we use
  @{text \<open>\<Rightarrow>^^\<close>} as a barrier. There is no mathematical purpose in this.\<close>

definition weak_step_tau2 :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close>
    ("_ \<Rightarrow>^^ _  _" [70, 70, 70] 80)
where [simp]:
  \<open>(p \<Rightarrow>^^ a q) \<equiv> p \<Rightarrow>^a q\<close>

coinductive greatest_weak_simulation :: 
  \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
where
  \<open>(\<forall> p' a. p \<longmapsto>a p' \<longrightarrow> (\<exists> q'. greatest_weak_simulation p' q' \<and> (q \<Rightarrow>^^ a q')))
  \<Longrightarrow> greatest_weak_simulation p q\<close>
  
lemma weak_sim_ruleformat:
assumes \<open>weak_simulation R\<close>
  and \<open>R p q\<close>
shows
  \<open>p \<longmapsto>a p' \<Longrightarrow> \<not>tau a \<Longrightarrow> (\<exists> q'. R p' q' \<and> (q \<Rightarrow>a q'))\<close>
  \<open>p \<longmapsto>a p' \<Longrightarrow>  tau a \<Longrightarrow> (\<exists> q'. R p' q' \<and> (q \<longmapsto>* tau q'))\<close>
  using assms unfolding weak_simulation_def by (blast+)

abbreviation weakly_simulated_by :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> ("_ \<sqsubseteq>ws  _" [60, 60] 65)
  where \<open>weakly_simulated_by p q \<equiv> \<exists> R . weak_simulation R \<and> R p q\<close>

lemma weaksim_greatest:
  shows \<open>weak_simulation (\<lambda> p q . p \<sqsubseteq>ws q)\<close>
  unfolding weak_simulation_def
  by (metis (no_types, lifting))


lemma gws_is_weak_simulation:
  shows \<open>weak_simulation greatest_weak_simulation\<close>
  unfolding weak_simulation_def
proof safe
  fix p q p' a
  assume ih:
    \<open>greatest_weak_simulation p q\<close>
    \<open>p \<longmapsto>a  p'\<close>
  hence \<open>(\<forall>x xa. p \<longmapsto>x xa \<longrightarrow> (\<exists>q'. q \<Rightarrow>^^ x  q' \<and> greatest_weak_simulation xa q'))\<close>
    by (meson greatest_weak_simulation.simps)
  then obtain q' where \<open>q \<Rightarrow>^^ a  q' \<and> greatest_weak_simulation p' q'\<close> using ih by blast
  thus \<open>\<exists>q'. greatest_weak_simulation p' q' \<and> q \<Rightarrow>^a  q'\<close>
    unfolding weak_step_tau2_def by blast
qed

lemma weakly_sim_by_implies_gws:
  assumes \<open>p \<sqsubseteq>ws q\<close>
  shows \<open>greatest_weak_simulation p q\<close>
  using assms
proof coinduct
  case (greatest_weak_simulation p q)
  then obtain R where \<open>weak_simulation R\<close> \<open>R p q\<close>
    unfolding weak_simulation_def by blast
  with weak_sim_ruleformat[OF this] show ?case
    unfolding weak_step_tau2_def
    by metis
qed

lemma gws_eq_weakly_sim_by:
  shows \<open>p \<sqsubseteq>ws q = greatest_weak_simulation p q\<close>
  using weakly_sim_by_implies_gws gws_is_weak_simulation by blast

lemma steps_retain_weak_sim:
assumes 
  \<open>weak_simulation R\<close>
  \<open>R p q\<close>
  \<open>p \<longmapsto>*A  p'\<close>
  \<open>\<And> a . tau a \<Longrightarrow> A a\<close>
shows \<open>\<exists>q'. R p' q' \<and> q \<longmapsto>*A  q'\<close>
  using assms(3,2,4) proof (induct)
  case (refl p' A)
  hence \<open>R p' q  \<and> q \<longmapsto>* A  q\<close> using assms(2) by (simp add: steps.refl)
  then show ?case by blast
next
  case (step p A p' a p'')
  then obtain q' where q': \<open>R p' q'\<close> \<open>q \<longmapsto>* A  q'\<close> by blast
  obtain q'' where q'':
    \<open>R p'' q''\<close> \<open>(\<not> tau a \<longrightarrow> q' \<Rightarrow>a  q'') \<and> (tau a \<longrightarrow> q' \<longmapsto>* tau  q'')\<close>
    using `weak_simulation R` q'(1) step(3) unfolding weak_simulation_def by blast
  have \<open>q' \<longmapsto>* A  q''\<close>
    using q''(2) steps_spec[of q'] step(4) step(6) weak_steps[of q' a q''] by blast
  hence \<open>q \<longmapsto>* A  q''\<close> using steps_concat[OF _ q'(2)] by blast
  thus ?case using q''(1) by blast
qed

lemma weak_sim_weak_premise:
  \<open>weak_simulation R =
    (\<forall> p q . R p q \<longrightarrow> 
      (\<forall> p' a. p \<Rightarrow>^a p' \<longrightarrow> (\<exists> q'. R p' q' \<and> q \<Rightarrow>^a q')))\<close>
proof 
  assume \<open>\<forall> p q . R p q \<longrightarrow> (\<forall>p' a. p \<Rightarrow>^a  p' \<longrightarrow> (\<exists>q'. R p' q' \<and> q \<Rightarrow>^a  q'))\<close>
  thus \<open>weak_simulation R\<close>
    unfolding weak_simulation_def using step_weak_step_tau by simp
next
  assume ws: \<open>weak_simulation R\<close>
  show \<open>\<forall>p q. R p q \<longrightarrow> (\<forall>p' a. p \<Rightarrow>^a  p' \<longrightarrow> (\<exists>q'. R p' q' \<and> q \<Rightarrow>^a  q'))\<close>
  proof safe
    fix p q p' a pq1 pq2
    assume case_assms:
      \<open>R p q\<close>
      \<open>p \<longmapsto>* tau  pq1\<close>
      \<open>pq1 \<longmapsto>a  pq2\<close>
      \<open>pq2 \<longmapsto>* tau  p'\<close>
    then obtain q' where q'_def: \<open>q \<longmapsto>* tau  q'\<close> \<open>R pq1 q'\<close>
      using steps_retain_weak_sim[OF ws] by blast
    then moreover obtain q'' where q''_def: \<open>R pq2 q''\<close> \<open>q' \<Rightarrow>^a  q''\<close>
      using ws case_assms(3) unfolding weak_simulation_def by blast
    then moreover obtain q''' where q''_def: \<open>R p' q'''\<close> \<open>q'' \<longmapsto>* tau  q'''\<close>
      using case_assms(4) steps_retain_weak_sim[OF ws] by blast
    ultimately show \<open>\<exists> q'''. R p' q''' \<and> q \<Rightarrow>^a  q'''\<close> using weak_step_extend by blast
  next
    fix p q p' a
    assume
      \<open>R p q\<close>
      \<open>p \<longmapsto>* tau  p'\<close>
      \<open>\<nexists>q'. R p' q' \<and> q \<Rightarrow>^a  q'\<close>
      \<open>tau a\<close>
    thus \<open>False\<close>
      using steps_retain_weak_sim[OF ws] by blast
  next
    \<comment>\<open>case identical to first case\<close>
    fix p q p' a pq1 pq2
    assume case_assms:
      \<open>R p q\<close>
      \<open>p \<longmapsto>* tau  pq1\<close>
      \<open>pq1 \<longmapsto>a  pq2\<close>
      \<open>pq2 \<longmapsto>* tau  p'\<close>
    then obtain q' where q'_def: \<open>q \<longmapsto>* tau  q'\<close> \<open>R pq1 q'\<close>
      using steps_retain_weak_sim[OF ws] by blast
    then moreover obtain q'' where q''_def: \<open>R pq2 q''\<close> \<open>q' \<Rightarrow>^a  q''\<close>
      using ws case_assms(3) unfolding weak_simulation_def by blast
    then moreover obtain q''' where q''_def: \<open>R p' q'''\<close> \<open>q'' \<longmapsto>* tau  q'''\<close>
      using case_assms(4) steps_retain_weak_sim[OF ws] by blast
    ultimately show \<open>\<exists> q'''. R p' q''' \<and> q \<Rightarrow>^a  q'''\<close> using weak_step_extend by blast
  qed
qed

lemma weak_sim_enabled_subs:
  assumes
    \<open>p \<sqsubseteq>ws q\<close>
    \<open>weak_enabled p a\<close>
    \<open>\<not> tau a\<close>
  shows \<open>weak_enabled q a\<close>
proof -
  obtain p' where p'_spec: \<open>p \<Rightarrow>a p'\<close>
    using \<open>weak_enabled p a\<close> weak_enabled_step by blast
  obtain R where \<open>R p q\<close> \<open>weak_simulation R\<close> using assms(1) by blast
  then obtain q' where \<open>q \<Rightarrow>^a q'\<close>
    unfolding weak_sim_weak_premise using weak_step_impl_weak_tau[OF p'_spec] by blast
  thus ?thesis using weak_enabled_step assms(3) by blast
qed

lemma weak_sim_union_cl:
  assumes
    \<open>weak_simulation RA\<close>
    \<open>weak_simulation RB\<close>
  shows
    \<open>weak_simulation (\<lambda> p q. RA p q \<or> RB p q)\<close>
  using assms unfolding weak_simulation_def by blast

lemma weak_sim_remove_dead_state:
  assumes
    \<open>weak_simulation R\<close>
    \<open>\<And> a p . \<not> d \<longmapsto>a p \<and> \<not> p \<longmapsto>a d\<close>
  shows
    \<open>weak_simulation (\<lambda> p q . R p q \<and> q \<noteq> d)\<close>
  unfolding weak_simulation_def
proof safe
  fix p q p' a
  assume
    \<open>R p q\<close>
    \<open>q \<noteq> d\<close>
    \<open>p \<longmapsto>a  p'\<close>
  then obtain q' where \<open>R p' q'\<close> \<open>q \<Rightarrow>^a  q'\<close>
    using assms(1) unfolding weak_simulation_def by blast
  moreover hence \<open>q' \<noteq> d\<close>
    using assms(2) `q \<noteq> d`
    by (metis steps.simps)
  ultimately show \<open>\<exists>q'. (R p' q' \<and> q' \<noteq> d) \<and> q \<Rightarrow>^a  q'\<close> by blast
qed

lemma weak_sim_tau_step:
  \<open>weak_simulation (\<lambda> p1 q1 . q1 \<longmapsto>* tau p1)\<close>
  unfolding weak_simulation_def
  using lts.steps.simps by metis

lemma weak_sim_trans_constructive:
  fixes R1 R2
  defines
    \<open>R \<equiv> \<lambda> p q . \<exists> pq . (R1 p pq \<and> R2 pq q) \<or> (R2 p pq \<and> R1 pq q)\<close>
  assumes
    R1_def: \<open>weak_simulation R1\<close> \<open>R1 p pq\<close> and
    R2_def: \<open>weak_simulation R2\<close> \<open>R2 pq q\<close>
  shows
    \<open>R p q\<close> \<open>weak_simulation R\<close>
proof-
  show \<open>R p q\<close> unfolding R_def using R1_def(2) R2_def(2) by blast
next
  show \<open>weak_simulation R\<close>
    unfolding weak_sim_weak_premise R_def
  proof (safe)
    fix p q pq p' a pq1 pq2
    assume
      \<open>R1 p pq\<close>
      \<open>R2 pq q\<close>
      \<open>\<not> tau a\<close>
      \<open>p \<longmapsto>* tau  pq1\<close>
      \<open>pq1 \<longmapsto>a  pq2\<close>
      \<open>pq2 \<longmapsto>* tau  p'\<close>
    thus \<open>\<exists>q'. (\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q') \<and> q \<Rightarrow>^a  q'\<close>
      using R1_def(1) R2_def(1) unfolding weak_sim_weak_premise by blast
  next
    fix p q pq p' a
    assume
      \<open>R1 p pq\<close>
      \<open>R2 pq q\<close>
      \<open>p \<longmapsto>* tau  p'\<close>
      \<open>\<nexists>q'.(\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q')\<and> q \<Rightarrow>^a  q'\<close>
      \<open>tau a\<close>
    thus \<open>False\<close>
      using R1_def(1) R2_def(1) unfolding weak_sim_weak_premise by blast
  next
    fix p q pq p' a pq1 pq2
    assume 
      \<open>R1 p pq\<close>
      \<open>R2 pq q\<close>
      \<open>p \<longmapsto>* tau  p'\<close>
      \<open>p \<longmapsto>* tau  pq1\<close>
      \<open>pq1 \<longmapsto>a  pq2\<close>
      \<open>pq2 \<longmapsto>* tau  p'\<close>
    then obtain pq' q' where \<open>R1 p' pq'\<close> \<open>pq \<Rightarrow>^a  pq'\<close> \<open>R2 pq' q'\<close> \<open>q \<Rightarrow>^a  q'\<close>
      using R1_def(1) R2_def(1) assms(3) unfolding weak_sim_weak_premise by blast
    thus \<open>\<exists>q'. (\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q') \<and> q \<Rightarrow>^a  q'\<close>
      by blast
  next
    fix p q pq p' a pq1 pq2
    assume sa:
      \<open>R2 p pq\<close>
      \<open>R1 pq q\<close>
      \<open>\<not> tau a\<close>
      \<open>p \<longmapsto>* tau  pq1\<close>
      \<open>pq1 \<longmapsto>a  pq2\<close>
      \<open>pq2 \<longmapsto>* tau  p'\<close>
    then obtain pq' q'  where \<open>R2 p' pq'\<close> \<open>pq \<Rightarrow>^a  pq'\<close> \<open>R1 pq' q'\<close> \<open>q \<Rightarrow>^a  q'\<close>
      using R2_def(1) R1_def(1) unfolding weak_sim_weak_premise by blast
    thus \<open>\<exists>q'. (\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q') \<and> q \<Rightarrow>^a  q'\<close>
      by blast
  next
    fix p q pq p' a
    assume
      \<open>R2 p pq\<close>
      \<open>R1 pq q\<close>
      \<open>p \<longmapsto>* tau  p'\<close>
      \<open>\<nexists>q'.(\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q')\<and> q \<Rightarrow>^a  q'\<close>
      \<open>tau a\<close>
    thus \<open>False\<close>
      using R1_def(1) R2_def(1) weak_step_tau_tau[OF `p \<longmapsto>* tau  p'` tau_tau]
      unfolding weak_sim_weak_premise by (metis (no_types, lifting))
  next
    fix p q pq p' a pq1 pq2
    assume sa:
      \<open>R2 p pq\<close>
      \<open>R1 pq q\<close>
      \<open>p \<longmapsto>* tau  p'\<close>
      \<open>p \<longmapsto>* tau  pq1\<close>
      \<open>pq1 \<longmapsto>a  pq2\<close>
      \<open>pq2 \<longmapsto>* tau  p'\<close>
    then obtain pq'  where \<open>R2 p' pq'\<close> \<open>pq \<Rightarrow>^a  pq'\<close>
      using R1_def(1) R2_def(1) weak_step_impl_weak_tau[of p a p']
      unfolding weak_sim_weak_premise by blast
    moreover then obtain q' where \<open>R1 pq' q'\<close> \<open>q \<Rightarrow>^a  q'\<close> 
      using R1_def(1) sa(2) unfolding weak_sim_weak_premise by blast
    ultimately show \<open>\<exists>q'. (\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q') \<and> q \<Rightarrow>^a  q'\<close>
      by blast
  qed
qed

lemma weak_sim_trans:
  assumes
    \<open>p \<sqsubseteq>ws pq\<close>
    \<open>pq \<sqsubseteq>ws q\<close>
  shows
    \<open>p \<sqsubseteq>ws q\<close>
  using assms(1,2)
proof -
  obtain R1 R2  where  \<open>weak_simulation R1\<close> \<open>R1 p pq\<close> \<open>weak_simulation R2\<close> \<open>R2 pq q\<close>
    using assms(1,2) by blast
  thus ?thesis
    using weak_sim_trans_constructive tau_tau
    by blast
qed

lemma weak_sim_word_impl:
  fixes
    p q p' A
  assumes
    \<open>weak_simulation R\<close> \<open>R p q\<close> \<open>p \<Rightarrow>$ A  p'\<close>
  shows
    \<open>\<exists>q'. R p' q' \<and> q \<Rightarrow>$ A  q'\<close>
using assms(2,3) proof (induct A arbitrary: p q)
  case Nil
  then show ?case
    using assms(1) steps_retain_weak_sim by auto
next
  case (Cons a A)
  then obtain p'' where p''_spec: \<open>p \<Rightarrow>^a p''\<close> \<open>p'' \<Rightarrow>$ A p'\<close> by auto
  with Cons(2) assms(1) obtain q'' where q''_spec: \<open>q \<Rightarrow>^a q''\<close> \<open>R p'' q''\<close>
    unfolding weak_sim_weak_premise by blast
  then show ?case using Cons(1) p''_spec(2)
    using weak_step_seq.simps(2) by blast
qed

lemma weak_sim_word_impl_contra:
  assumes
    \<open>\<forall> p q . R p q \<longrightarrow>
      (\<forall> p' A. p \<Rightarrow>$A p' \<longrightarrow> (\<exists> q'. R p' q' \<and> q \<Rightarrow>$A q'))\<close>
  shows
    \<open>weak_simulation R\<close>
proof -
  from assms have
    \<open>\<forall> p q p' A . R p q \<longrightarrow> p \<Rightarrow>$A p' \<longrightarrow> (\<exists> q'. R p' q' \<and> q \<Rightarrow>$A q')\<close> by blast
  hence \<open>\<forall> p q p' a . R p q \<longrightarrow> p \<Rightarrow>$[a] p' \<longrightarrow> (\<exists> q'. R p' q' \<and> q \<Rightarrow>$[a] q')\<close> by blast
  thus ?thesis unfolding weak_single_step weak_sim_weak_premise by blast
qed

lemma weak_sim_word:
  \<open>weak_simulation R =
    (\<forall> p q . R p q \<longrightarrow>
      (\<forall> p' A. p \<Rightarrow>$A p' \<longrightarrow> (\<exists> q'. R p' q' \<and> q \<Rightarrow>$A q')))\<close>
  using weak_sim_word_impl weak_sim_word_impl_contra by blast

subsection \<open>Weak Bisimulation\<close>

definition weak_bisimulation :: 
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>weak_bisimulation R \<equiv> \<forall> p q. R p q \<longrightarrow> 
    (\<forall> p' a. p \<longmapsto>a p' \<longrightarrow> (\<exists> q'. R p' q'
      \<and> (q \<Rightarrow>^a q'))) \<and>
    (\<forall> q' a. q \<longmapsto>a q' \<longrightarrow> (\<exists> p'. R p' q'
      \<and> ( p \<Rightarrow>^a p')))\<close>
  
lemma weak_bisim_ruleformat:
assumes \<open>weak_bisimulation R\<close>
  and \<open>R p q\<close>
shows
  \<open>p \<longmapsto>a p' \<Longrightarrow> \<not>tau a \<Longrightarrow> (\<exists> q'. R p' q' \<and> (q \<Rightarrow>a q'))\<close>
  \<open>p \<longmapsto>a p' \<Longrightarrow>  tau a \<Longrightarrow> (\<exists> q'. R p' q' \<and> (q \<longmapsto>* tau q'))\<close>
  \<open>q \<longmapsto>a q' \<Longrightarrow> \<not>tau a \<Longrightarrow> (\<exists> p'. R p' q' \<and> (p \<Rightarrow>a p'))\<close>
  \<open>q \<longmapsto>a q' \<Longrightarrow>  tau a \<Longrightarrow> (\<exists> p'. R p' q' \<and> (p \<longmapsto>* tau p'))\<close>
  using assms unfolding weak_bisimulation_def by (blast+)
  
definition tau_weak_bisimulation :: 
  \<open>('s \<Rightarrow> 's \<Rightarrow>  bool) \<Rightarrow>  bool\<close>
where
  \<open>tau_weak_bisimulation R \<equiv> \<forall> p q. R p q \<longrightarrow> 
    (\<forall> p' a. p \<longmapsto>a p' \<longrightarrow> 
      (\<exists> q'. R p' q' \<and> (q \<Rightarrow>a q'))) \<and>
    (\<forall> q' a. q \<longmapsto>a q' \<longrightarrow> 
      (\<exists> p'. R p' q' \<and> (p \<Rightarrow>a p')))\<close>

lemma weak_bisim_implies_tau_weak_bisim:
  assumes
    \<open>tau_weak_bisimulation R\<close>
  shows
    \<open>weak_bisimulation R\<close>
unfolding weak_bisimulation_def proof (safe)
  fix p q p' a
  assume \<open>R p q\<close> \<open>p \<longmapsto>a  p'\<close>
  thus \<open>\<exists>q'. R p' q' \<and> (q \<Rightarrow>^a  q')\<close>
    using assms weak_steps[of q a _ tau] unfolding tau_weak_bisimulation_def by blast
next
  fix p q q' a
  assume \<open>R p q\<close> \<open>q \<longmapsto>a  q'\<close>
  thus \<open>\<exists>p'. R p' q' \<and> (p \<Rightarrow>^a  p')\<close>
    using assms weak_steps[of p a _ tau] unfolding tau_weak_bisimulation_def by blast
qed

lemma weak_bisim_invert:
  assumes
    \<open>weak_bisimulation R\<close>
  shows
    \<open>weak_bisimulation (\<lambda> p q. R q p)\<close>
using assms unfolding weak_bisimulation_def by auto

lemma bisim_weak_bisim:
  assumes \<open>bisimulation R\<close>
  shows \<open>weak_bisimulation R\<close>
  unfolding weak_bisimulation_def
proof (clarify, rule)
  fix p q
  assume R: \<open>R p q\<close>
  show \<open>\<forall>p' a. p \<longmapsto>a  p' \<longrightarrow> (\<exists>q'. R p' q' \<and> (q \<Rightarrow>^a  q'))\<close>
  proof (clarify)
    fix p' a
    assume p'a: \<open>p \<longmapsto>a  p'\<close>
    have
      \<open>\<not> tau a \<longrightarrow> (\<exists>q'. R p' q' \<and> q \<Rightarrow>a  q')\<close>
      \<open>(tau a \<longrightarrow> (\<exists>q'. R p' q' \<and> q \<longmapsto>* tau  q'))\<close> 
      using bisim_ruleformat(1)[OF assms R p'a] step_weak_step step_weak_step_tau by auto
    thus \<open>\<exists>q'. R p' q' \<and> (q \<Rightarrow>^a  q')\<close> by blast
  qed
next 
  fix p q
  assume R: \<open>R p q\<close>
  have \<open>\<forall>q' a. q \<longmapsto>a  q' \<longrightarrow> (\<not> tau a \<longrightarrow> (\<exists>p'. R p' q' \<and> p \<Rightarrow>a  p'))
     \<and> (tau a \<longrightarrow> (\<exists>p'. R p' q' \<and> p \<longmapsto>* tau  p'))\<close>
  proof (clarify)
    fix q' a
    assume q'a: \<open>q \<longmapsto>a  q'\<close>
    show
      \<open>(\<not> tau a \<longrightarrow> (\<exists>p'. R p' q' \<and> p \<Rightarrow>a  p')) \<and>
      (tau a \<longrightarrow> (\<exists>p'. R p' q' \<and> p \<longmapsto>* tau  p'))\<close> 
      using bisim_ruleformat(2)[OF assms R q'a] step_weak_step
        step_weak_step_tau steps_one_step by auto
  qed
  thus \<open>\<forall>q' a. q \<longmapsto>a  q' \<longrightarrow> (\<exists>p'. R p' q' \<and> (p \<Rightarrow>^a  p'))\<close> by blast
qed
  
lemma weak_bisim_weak_sim:
  shows \<open>weak_bisimulation R = (weak_simulation R \<and> weak_simulation (\<lambda> p q . R q p))\<close>
unfolding weak_bisimulation_def weak_simulation_def by auto

lemma steps_retain_weak_bisim:
  assumes 
    \<open>weak_bisimulation R\<close>
    \<open>R p q\<close>
    \<open>p \<longmapsto>*A  p'\<close>
    \<open>\<And> a . tau a \<Longrightarrow> A a\<close>
  shows \<open>\<exists>q'. R p' q' \<and> q \<longmapsto>*A  q'\<close>
    using assms weak_bisim_weak_sim steps_retain_weak_sim
    by auto
  
lemma weak_bisim_union:
  assumes
    \<open>weak_bisimulation R1\<close>
    \<open>weak_bisimulation R2\<close>
  shows
    \<open>weak_bisimulation (\<lambda> p q . R1 p q \<or> R2 p q)\<close>
  using assms unfolding weak_bisimulation_def by blast

lemma weak_bisim_taufree_strong:
  assumes
    \<open>weak_bisimulation R\<close>
    \<open>\<And> p q a. p \<longmapsto> a q \<Longrightarrow> \<not> tau a\<close>
  shows
    \<open>bisimulation R\<close>
  using assms strong_weak_transition_system
  unfolding weak_bisimulation_def bisimulation_def
  by auto

subsection \<open>Trace Inclusion\<close>

definition trace_inclusion ::
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>trace_inclusion R  \<equiv> \<forall> p q p' A . (\<forall> a \<in> set(A). a \<noteq> \<tau>) 
  \<and> R p q \<and> p \<Rightarrow>$ A p' \<longrightarrow> (\<exists> q'. q \<Rightarrow>$ A q')\<close>

abbreviation weakly_trace_included_by :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> ("_ \<sqsubseteq>T  _" [60, 60] 65)
  where \<open>weakly_trace_included_by p q \<equiv> \<exists> R . trace_inclusion R \<and> R p q\<close>

lemma weak_trace_inlcusion_greatest:
  shows \<open>trace_inclusion (\<lambda> p q . p \<sqsubseteq>T q)\<close>
  unfolding trace_inclusion_def
  by blast

subsection \<open>Delay Simulation\<close>

definition delay_simulation :: 
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>delay_simulation R \<equiv> \<forall> p q. R p q \<longrightarrow> 
    (\<forall> p' a. p \<longmapsto>a p' \<longrightarrow> 
      (tau a \<longrightarrow> R p' q) \<and>
      (\<not>tau a \<longrightarrow> (\<exists> q'. R p' q'\<and> (q =\<rhd>a q'))))\<close>

lemma delay_simulation_implies_weak_simulation:
  assumes
    \<open>delay_simulation R\<close>
  shows
    \<open>weak_simulation R\<close>
  using assms weak_step_delay_implies_weak_tau steps.refl
  unfolding delay_simulation_def weak_simulation_def by blast

subsection \<open>Coupled Equivalences\<close>

abbreviation coupling ::
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>coupling R \<equiv> \<forall> p q . R p q \<longrightarrow> (\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p)\<close>

lemma coupling_tau_max_symm:
  assumes
    \<open>R p q \<longrightarrow> (\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p)\<close>
    \<open>tau_max q\<close>
    \<open>R p q\<close>
  shows
    \<open>R q p\<close>
  using assms steps_no_step_pos[of q tau] by blast

corollary coupling_stability_symm:
  assumes
    \<open>R p q \<longrightarrow> (\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p)\<close>
    \<open>stable_state q\<close>
    \<open>R p q\<close>
  shows
    \<open>R q p\<close>
  using coupling_tau_max_symm stable_tauclosure_only_loop assms by metis

end \<comment>\<open>context @{locale lts_tau}\<close>
end