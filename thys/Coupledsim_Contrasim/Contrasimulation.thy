section \<open>Contrasimulation\<close>

theory Contrasimulation
imports
  Weak_Relations
begin

context lts_tau
begin

subsection \<open>Definition of Contrasimulation\<close>

definition contrasimulation ::
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>contrasimulation R \<equiv> \<forall> p q p' A . (\<forall> a \<in> set(A). a \<noteq> \<tau>) \<and> R p q \<and> (p \<Rightarrow>$ A p') \<longrightarrow>
    (\<exists> q'. (q \<Rightarrow>$ A q') \<and> R q' p')\<close>

lemma contrasim_simpler_def:
  shows \<open>contrasimulation R =
    (\<forall> p q p' A . R p q \<and> (p \<Rightarrow>$ A p') \<longrightarrow> (\<exists> q'. (q \<Rightarrow>$ A q') \<and> R q' p'))\<close>
proof -
  have \<open>\<And>A. \<forall>a\<in>set (filter (\<lambda>a. a \<noteq> \<tau>) A). a \<noteq> \<tau>\<close> by auto
  then show ?thesis
    unfolding contrasimulation_def
    using word_steps_ignore_tau_addition word_steps_ignore_tau_removal
    by metis
qed

abbreviation contrasimulated_by :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> ("_ \<sqsubseteq>c  _" [60, 60] 65)
  where \<open>contrasimulated_by p q \<equiv> \<exists> R . contrasimulation R \<and> R p q\<close>

lemma contrasim_preorder_is_contrasim:
  shows \<open>contrasimulation (\<lambda> p q . p \<sqsubseteq>c q)\<close>
  unfolding contrasimulation_def
  by metis

lemma contrasim_preorder_is_greatest:
  assumes \<open>contrasimulation R\<close>
  shows \<open>\<And> p q. R p q \<Longrightarrow> p \<sqsubseteq>c q\<close>
  using assms by auto

lemma contrasim_tau_step:
  \<open>contrasimulation (\<lambda> p1 q1 . q1 \<longmapsto>* tau p1)\<close>
  unfolding contrasimulation_def
  using steps.simps tau_tau tau_word_concat
  by metis

lemma contrasim_trans_constructive:
  fixes R1 R2
  defines
    \<open>R \<equiv> \<lambda> p q . \<exists> pq . (R1 p pq \<and> R2 pq q) \<or> (R2 p pq \<and> R1 pq q)\<close>
  assumes
    R1_def: \<open>contrasimulation R1\<close> \<open>R1 p pq\<close> and
    R2_def: \<open>contrasimulation R2\<close> \<open>R2 pq q\<close>
  shows
    \<open>R p q\<close> \<open>contrasimulation R\<close>
  using assms(2,3,4,5) unfolding R_def contrasimulation_def by metis+

lemma contrasim_trans:
  assumes
    \<open>p \<sqsubseteq>c pq\<close>
    \<open>pq \<sqsubseteq>c q\<close>
  shows
    \<open>p \<sqsubseteq>c q\<close>
  using assms contrasim_trans_constructive by blast

lemma contrasim_refl:
  shows
    \<open>p \<sqsubseteq>c p\<close>
  using contrasim_tau_step steps.refl by blast

lemma contrasimilarity_equiv:
  defines \<open>contrasimilarity \<equiv> \<lambda> p q. p \<sqsubseteq>c q \<and> q \<sqsubseteq>c p\<close>
  shows \<open>equivp contrasimilarity\<close>
proof -
  have \<open>reflp contrasimilarity\<close>
    using contrasim_refl unfolding contrasimilarity_def reflp_def by blast
  moreover have \<open>symp contrasimilarity\<close>
    unfolding contrasimilarity_def symp_def by blast
  moreover have \<open>transp contrasimilarity\<close>
    using contrasim_trans unfolding contrasimilarity_def transp_def by meson
  ultimately show ?thesis using equivpI by blast
qed

lemma contrasim_implies_trace_incl:
  assumes \<open>contrasimulation R\<close>
  shows \<open>trace_inclusion R\<close>
by (metis assms contrasim_simpler_def trace_inclusion_def) 

lemma contrasim_coupled:
  assumes
    \<open>contrasimulation R\<close>
    \<open>R p q\<close>
  shows
    \<open>\<exists> q'. q \<longmapsto>* tau q' \<and> R q' p\<close>
  using assms steps.refl[of p tau] weak_step_seq.simps(1)
  unfolding contrasim_simpler_def by blast

lemma contrasim_taufree_symm:
  assumes
    \<open>contrasimulation R\<close>
    \<open>R p q\<close>
    \<open>stable_state q\<close>
  shows
    \<open>R q p\<close>
  using contrasim_coupled assms stable_tauclosure_only_loop by blast

lemma symm_contrasim_is_weak_bisim:
  assumes
    \<open>contrasimulation R\<close>
    \<open>\<And> p q. R p q \<Longrightarrow> R q p\<close>
  shows
    \<open>weak_bisimulation R\<close>
  using assms unfolding contrasim_simpler_def weak_sim_word weak_bisim_weak_sim by blast

lemma contrasim_weakest_bisim:
  assumes
    \<open>contrasimulation R\<close>
    \<open>\<And> p q a. p \<longmapsto> a q \<Longrightarrow> \<not> tau a\<close>
  shows
    \<open>bisimulation R\<close>
  using assms contrasim_taufree_symm symm_contrasim_is_weak_bisim weak_bisim_taufree_strong
  by blast

lemma symm_weak_sim_is_contrasim:
  assumes
    \<open>weak_simulation R\<close>
    \<open>\<And> p q. R p q \<Longrightarrow> R q p\<close>
  shows
    \<open>contrasimulation R\<close>
  using assms unfolding contrasim_simpler_def weak_sim_word by blast

subsection \<open>Intermediate Relation Mimicking Contrasim\<close>

definition mimicking :: "('s \<Rightarrow> 's set \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where 
\<open>mimicking R p' Q' \<equiv> \<exists>p Q A.
  R p Q \<and> p \<Rightarrow>$A p' \<and> 
  (\<forall>a \<in> set A. a \<noteq> \<tau>) \<and> 
  Q' = (dsuccs_seq_rec (rev A) Q)\<close>

definition set_lifted :: "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where 
\<open>set_lifted R p Q \<equiv> \<exists>q. R p q \<and> Q = {q}\<close>

lemma R_is_in_mimicking_of_R : 
  assumes \<open>R p Q\<close>
  shows \<open>mimicking R p Q\<close>
  using assms steps.refl lts_tau.weak_step_seq.simps(1)
  unfolding mimicking_def by fastforce

lemma mimicking_of_C_guarantees_tau_succ:
  assumes
    \<open>contrasimulation C\<close>
    \<open>mimicking (set_lifted C) p Q\<close>
    \<open>p \<Rightarrow>^\<tau> p'\<close>
  shows \<open>\<exists>q'. q' \<in> (weak_tau_succs Q) \<and> mimicking (set_lifted C) q' {p'}\<close>
proof -
  obtain p0 Q0 A q0
      where \<open>(set_lifted C) p0 Q0\<close> \<open>p0 \<Rightarrow>$A p\<close> \<open>\<forall>a \<in> set A. a \<noteq> \<tau>\<close> \<open>Q0 = {q0}\<close> 
        and Q_def: \<open>Q = (dsuccs_seq_rec (rev A) Q0)\<close> 
      using mimicking_def assms set_lifted_def by metis
  hence \<open>C p0 q0\<close> using set_lifted_def by auto 
  have \<open>p0 \<Rightarrow>$(A@[\<tau>]) p'\<close> using \<open>p0 \<Rightarrow>$A p\<close>  \<open>p \<Rightarrow>^\<tau>  p'\<close> rev_seq_step_concat by auto
  hence word: \<open>p0 \<Rightarrow>$A p'\<close> 
    by (metis \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close> app_tau_taufree_list tau_def weak_step_over_tau)
  then obtain q' where \<open>q0 \<Rightarrow>$A q'\<close> \<open>C q' p'\<close> 
    using assms contrasimulation_def[of \<open>C\<close>] \<open>C p0 q0\<close> \<open>\<forall>a \<in> set A. a \<noteq> \<tau>\<close> by blast
  hence \<open>(set_lifted C) q' {p'}\<close> using set_lifted_def by auto
  hence in_mimicking: \<open>mimicking (set_lifted C) q' {p'}\<close> using R_is_in_mimicking_of_R  by auto
  have \<open>q' \<in> weak_tau_succs (dsuccs_seq_rec (rev A) Q0)\<close> 
    using \<open>Q0 = {q0}\<close> \<open>q0 \<Rightarrow>$ A q'\<close>
    by (simp add: word_reachable_implies_in_dsuccs) 
  hence \<open>q' \<in> weak_tau_succs Q\<close> using Q_def by simp 
  thus \<open>\<exists>q'. q' \<in> weak_tau_succs Q \<and> mimicking (set_lifted C) q' {p'}\<close> using in_mimicking by auto
qed

lemma mimicking_of_C_guarantees_action_succ:
 assumes 
    \<open>contrasimulation C\<close>
    \<open>mimicking (set_lifted C) p Q\<close>
    \<open>p =\<rhd>a p'\<close>
    \<open>a \<noteq> \<tau>\<close>
  shows \<open>mimicking (set_lifted C) p' (dsuccs a Q)\<close>
proof -
  obtain p0 Q0 A q0
    where \<open>(set_lifted C) p0 Q0\<close> \<open>p0 \<Rightarrow>$A p\<close> \<open>Q0 = {q0}\<close> \<open>\<forall>a \<in> set A. a \<noteq> \<tau> \<close> 
      and Q_def: \<open>Q = (dsuccs_seq_rec (rev A) Q0)\<close> 
    using mimicking_def assms set_lifted_def by metis
  then obtain CS where CS_def: \<open>contrasimulation CS \<and> CS p0 q0\<close> 
    using assms set_lifted_def by (metis singleton_inject) 
  have notau: \<open>\<forall>a \<in> set (A@[a]). a \<noteq> \<tau>\<close> 
    using \<open>a \<noteq> \<tau>\<close> \<open>\<forall>a \<in> set A. a \<noteq> \<tau> \<close> by auto
  have  \<open>p \<Rightarrow>a  p'\<close> using assms(3,4) steps.refl tau_def by auto 
  hence word: \<open>p0 \<Rightarrow>$(A@[a]) p'\<close>
    using \<open>p0 \<Rightarrow>$A p\<close>  rev_seq_step_concat
    by (meson steps.step steps_concat)
  then obtain q' where \<open>q0 \<Rightarrow>$(A@[a]) q' \<and> CS q' p'\<close> 
    using CS_def contrasimulation_def[of \<open>CS\<close>] notau
    by fastforce
  hence \<open>q' \<in> weak_tau_succs (dsuccs_seq_rec (rev (A@[a])) {q0})\<close> 
    using word_reachable_implies_in_dsuccs by blast
  then obtain q1 where \<open>q1 \<in> dsuccs_seq_rec (rev (A@[a])) {q0}\<close> \<open>q1 \<Rightarrow>^\<tau> q'\<close>
    using weak_tau_succs_def[of \<open>dsuccs_seq_rec (rev (A@[a])) {q0}\<close>] by auto
  thus ?thesis
    using word mimicking_def[of \<open>(set_lifted C)\<close>] \<open>(set_lifted C) p0 Q0\<close> 
      \<open>Q0 = {q0}\<close> Q_def notau simp_dsuccs_seq_rev by meson
qed

subsection \<open>Over-Approximating Contrasimulation by a Single-Step Version\<close>

definition contrasim_step ::
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>contrasim_step R \<equiv> \<forall> p q p' a .
    R p q \<and> (p \<Rightarrow>^a p') \<longrightarrow>
    (\<exists> q'. (q \<Rightarrow>^a q')
         \<and> R q' p')\<close>

lemma contrasim_step_weaker_than_seq:
  assumes
    \<open>contrasimulation R\<close>
  shows
    \<open>contrasim_step R\<close>
  unfolding contrasim_step_def
proof ((rule allI impI)+)
  fix p q p' a
  assume
    \<open>R p q \<and> p \<Rightarrow>^a  p'\<close>
  hence
    \<open>R p q\<close> \<open>p \<Rightarrow>^a  p'\<close> by safe
  hence \<open>p \<Rightarrow>$ [a]  p'\<close> by safe
  then obtain q' where \<open>R q' p'\<close> \<open>q \<Rightarrow>$ [a]  q'\<close>
    using assms `R p q` unfolding contrasim_simpler_def by blast
  hence \<open>q \<Rightarrow>^a  q'\<close> by blast
  thus \<open>\<exists>q'. q \<Rightarrow>^a  q' \<and> R q' p'\<close> using `R q' p'` by blast
qed

lemma contrasim_step_seq_coincide_for_sims:
  assumes
    \<open>contrasim_step R\<close>
    \<open>weak_simulation R\<close>
  shows
    \<open>contrasimulation R\<close>
  unfolding contrasimulation_def
proof (clarify)
  fix p q p' A
  assume
    \<open>R p q\<close>
    \<open>p \<Rightarrow>$ A  p'\<close>
  thus \<open>\<exists>q'. q \<Rightarrow>$ A  q' \<and> R q' p'\<close>
  proof (induct A arbitrary: p p' q)
    case Nil
    then show ?case using assms(1) unfolding contrasim_step_def
      using tau_tau weak_step_seq.simps(1) by blast
  next
    case (Cons a A)
    then obtain p1 where p1_def: \<open>p \<Rightarrow>^a p1\<close> \<open>p1 \<Rightarrow>$ (A)  p'\<close> by auto
    then obtain q1 where q1_def: \<open>q \<Rightarrow>^a q1\<close> \<open>R p1 q1\<close>
      using assms(2) `R p q` unfolding weak_sim_weak_premise by blast
    then obtain q' where \<open>q1 \<Rightarrow>$ (A)  q'\<close> \<open>R q' p'\<close> using p1_def(2) Cons(1) by blast
    then show ?case using q1_def(1) by auto
  qed
qed

end
end
