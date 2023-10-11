section \<open>Coupled Simulation\<close>

theory Coupled_Simulation
  imports Contrasimulation
begin

context lts_tau
begin

subsection \<open>Van Glabbeeks's Coupled Simulation\<close>
  
text \<open>We mainly use van Glabbeek's coupled simulation from his 2017 CSP paper @{cite "glabbeek2017"}.
  Later on, we will compare it to other definitions of coupled (delay/weak) simulations.\<close>

definition coupled_simulation ::
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>coupled_simulation R  \<equiv> \<forall> p q . 
    R p q \<longrightarrow> 
      (\<forall> p' a. p \<longmapsto>a p' \<longrightarrow> 
        (\<exists> q'. R p' q' \<and> q \<Rightarrow>^a q')) \<and>
      (\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p)\<close>

abbreviation coupled_simulated_by :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> ("_ \<sqsubseteq>cs  _" [60, 60] 65)
  where \<open>coupled_simulated_by p q \<equiv> \<exists> R . coupled_simulation R \<and> R p q\<close>
    
abbreviation coupled_similar :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> ("_ \<equiv>cs  _" [60, 60] 65)
  where \<open>coupled_similar p q \<equiv> p \<sqsubseteq>cs q \<and> q \<sqsubseteq>cs p\<close>

text \<open>We call \<open>\<sqsubseteq>cs\<close> "coupled simulation preorder" and \<open>\<equiv>cs\<close> coupled similarity.\<close>

subsection \<open>Position between Weak Simulation and Weak Bisimulation\<close>

text \<open>Coupled simulations are special weak simulations, and symmetric weak bisimulations also
  are coupled simulations.\<close>

lemma coupled_simulation_weak_simulation:
  \<open>coupled_simulation R =
    (weak_simulation R \<and> (\<forall> p q . R p q \<longrightarrow> (\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p)))\<close>
  unfolding coupled_simulation_def weak_simulation_def by blast

corollary coupled_simulation_implies_weak_simulation:
  assumes \<open>coupled_simulation R\<close>
  shows \<open>weak_simulation R\<close>
  using assms unfolding coupled_simulation_weak_simulation ..

corollary coupledsim_enabled_subs:
  assumes
    \<open>p \<sqsubseteq>cs q\<close>
    \<open>weak_enabled p a\<close>
    \<open>\<not> tau a\<close>
  shows \<open>weak_enabled q a\<close>
  using assms weak_sim_enabled_subs coupled_simulation_implies_weak_simulation by blast

lemma coupled_simulation_implies_coupling:
  assumes
    \<open>coupled_simulation R\<close>
    \<open>R p q\<close>
  shows
    \<open>\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p\<close>
  using assms unfolding coupled_simulation_weak_simulation by blast

lemma weak_bisim_implies_coupled_sim_gla17:
  assumes
    wbisim:   \<open>weak_bisimulation R\<close> and
    symmetry: \<open>\<And> p q . R p q \<Longrightarrow> R q p\<close>
    \<comment>\<open>symmetry is needed here, which is alright because bisimilarity is symmetric.\<close>
  shows \<open>coupled_simulation R\<close>
unfolding coupled_simulation_def proof safe
  fix p q p' a
  assume \<open>R p q\<close> \<open>p \<longmapsto>a  p'\<close>
  thus \<open>\<exists>q'. R p' q' \<and> (q \<Rightarrow>^a  q')\<close>
    using wbisim unfolding weak_bisimulation_def by simp
next
  fix p q 
  assume \<open>R p q\<close>
  thus \<open>\<exists>q'. q \<longmapsto>* tau  q' \<and> R q' p\<close> 
    using symmetry steps.refl[of q tau] by auto
qed

subsection \<open>Coupled Simulation and Silent Steps\<close>

text \<open>Coupled simulation shares important patterns with weak simulation when it comes to the
  treatment of silent steps.\<close>

lemma coupledsim_step_gla17:
  \<open>coupled_simulation (\<lambda> p1 q1 . q1 \<longmapsto>* tau p1)\<close>
  unfolding coupled_simulation_def
  using lts.steps.simps by metis

corollary coupledsim_step:
  assumes
    \<open>p \<longmapsto>* tau  q\<close>
  shows
    \<open>q \<sqsubseteq>cs p\<close>
  using assms coupledsim_step_gla17 by auto

text \<open>A direct implication of this is that states on a tau loop are coupled similar.\<close>
corollary strongly_tau_connected_coupled_similar:
  assumes
    \<open>p \<longmapsto>* tau  q\<close>
    \<open>q \<longmapsto>* tau  p\<close>
  shows \<open>p \<equiv>cs q\<close>
  using assms coupledsim_step by auto

lemma silent_steps_retain_coupled_simulation:
assumes 
  \<open>coupled_simulation R\<close>
  \<open>R p q\<close>
  \<open>p \<longmapsto>* A  p'\<close>
  \<open>A = tau\<close>
shows \<open>\<exists> q' . q \<longmapsto>* A q' \<and> R p' q'\<close>
  using assms(1,3,2,4) steps_retain_weak_sim
  unfolding coupled_simulation_weak_simulation by blast

lemma coupled_simulation_weak_premise:
  \<open>coupled_simulation R =
   (\<forall> p q . R p q \<longrightarrow>
      (\<forall> p' a. p \<Rightarrow>^a p' \<longrightarrow>
        (\<exists> q'. R p' q' \<and> q \<Rightarrow>^a q')) \<and>
      (\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p))\<close>
  unfolding coupled_simulation_weak_simulation weak_sim_weak_premise by blast

subsection \<open>Closure, Preorder and Symmetry Properties\<close>

text \<open>The coupled simulation preorder \<open>\<sqsubseteq>cs\<close> @{emph \<open>is\<close>} a preoder and symmetric at the
  stable states.\<close>

lemma coupledsim_union:
  assumes
    \<open>coupled_simulation R1\<close>
    \<open>coupled_simulation R2\<close>
  shows
    \<open>coupled_simulation (\<lambda> p q . R1 p q \<or> R2 p q)\<close>
  using assms unfolding coupled_simulation_def by (blast)  
  
lemma coupledsim_refl:
  \<open>p \<sqsubseteq>cs p\<close>
  using coupledsim_step steps.refl by auto
    
lemma coupledsim_trans:
  assumes
    \<open>p \<sqsubseteq>cs pq\<close>
    \<open>pq \<sqsubseteq>cs q\<close>
  shows
    \<open>p \<sqsubseteq>cs q\<close>
proof -
  obtain R1 where R1_def: \<open>coupled_simulation R1\<close> \<open>R1 p pq\<close>
    using assms(1) by blast
  obtain R2 where R2_def: \<open>coupled_simulation R2\<close> \<open>R2 pq q\<close>
    using assms(2) by blast
  define R where R_def: \<open>R \<equiv> \<lambda> p q . \<exists> pq . (R1 p pq \<and> R2 pq q) \<or> (R2 p pq \<and> R1 pq q)\<close>
  have \<open>weak_simulation R\<close> \<open>R p q\<close>
    using weak_sim_trans_constructive
      R1_def(2) R2_def(2)
      coupled_simulation_implies_weak_simulation[OF R1_def(1)]
      coupled_simulation_implies_weak_simulation[OF R2_def(1)] 
    unfolding R_def by auto
  moreover have \<open>(\<forall> p q . R p q \<longrightarrow> (\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p))\<close>
    unfolding R_def
  proof safe
    fix p q pq
    assume r1r2: \<open>R1 p pq\<close> \<open>R2 pq q\<close>
    then obtain pq' where \<open>R1 pq' p\<close> \<open>pq \<longmapsto>* tau  pq'\<close>
      using r1r2 R1_def(1) unfolding coupled_simulation_weak_premise by blast
    then moreover obtain q' where \<open>R2 pq' q'\<close> \<open>q \<longmapsto>* tau q'\<close>
      using r1r2 R2_def(1) weak_step_tau_tau[OF `pq \<longmapsto>* tau  pq'`] tau_tau
      unfolding coupled_simulation_weak_premise by blast
    then moreover obtain q'' where \<open>R2 q'' pq'\<close> \<open>q' \<longmapsto>* tau  q''\<close>
      using R2_def(1) unfolding coupled_simulation_weak_premise by blast
    ultimately show \<open>\<exists>q'. q \<longmapsto>* tau  q' \<and> (\<exists>pq. R1 q' pq \<and> R2 pq p \<or> R2 q' pq \<and> R1 pq p)\<close>
      using steps_concat by blast
  next \<comment>\<open>analogous with R2 and R1 swapped\<close>
    fix p q pq
    assume r2r1: \<open>R2 p pq\<close> \<open>R1 pq q\<close>
    then obtain pq' where \<open>R2 pq' p\<close> \<open>pq \<longmapsto>* tau  pq'\<close>
      using r2r1 R2_def(1) unfolding coupled_simulation_weak_premise by blast
    then moreover obtain q' where \<open>R1 pq' q'\<close> \<open>q \<longmapsto>* tau q'\<close>
      using r2r1 R1_def(1) weak_step_tau_tau[OF `pq \<longmapsto>* tau  pq'`] tau_tau
      unfolding coupled_simulation_weak_premise by blast
    then moreover obtain q'' where \<open>R1 q'' pq'\<close> \<open>q' \<longmapsto>* tau  q''\<close>
      using R1_def(1) unfolding coupled_simulation_weak_premise by blast
    ultimately show \<open>\<exists>q'. q \<longmapsto>* tau  q' \<and> (\<exists>pq. R1 q' pq \<and> R2 pq p \<or> R2 q' pq \<and> R1 pq p)\<close>
      using steps_concat by blast
  qed
  ultimately have \<open>R p q\<close> \<open>coupled_simulation R\<close>
    using coupled_simulation_weak_simulation by auto
  thus ?thesis by blast
qed

interpretation preorder \<open>\<lambda> p q. p \<sqsubseteq>cs q\<close> \<open>\<lambda> p q. p \<sqsubseteq>cs q \<and> \<not>(q \<sqsubseteq>cs p)\<close>
  by (standard, blast, fact coupledsim_refl, fact coupledsim_trans)

lemma coupled_similarity_equivalence:
  \<open>equivp (\<lambda> p q. p \<equiv>cs q)\<close>
proof (rule equivpI)
  show \<open>reflp coupled_similar\<close>
    unfolding reflp_def by blast
next
  show \<open>symp coupled_similar\<close>
    unfolding symp_def by blast
next
  show \<open>transp coupled_similar\<close>
    unfolding transp_def using coupledsim_trans by meson
qed

lemma coupledsim_tau_max_eq:
  assumes
    \<open>p \<sqsubseteq>cs q\<close>
    \<open>tau_max q\<close>
  shows  \<open>p \<equiv>cs q\<close> 
  using assms using coupled_simulation_weak_simulation coupling_tau_max_symm by metis

corollary coupledsim_stable_eq:
  assumes
    \<open>p \<sqsubseteq>cs q\<close>
    \<open>stable_state q\<close>
  shows  \<open>p \<equiv>cs q\<close> 
  using assms using coupled_simulation_weak_simulation coupling_stability_symm by metis

subsection \<open>Coinductive Coupled Simulation Preorder\<close>

text \<open>\<open>\<sqsubseteq>cs\<close> can also be characterized coinductively. \<open>\<sqsubseteq>cs\<close> is the greatest
  coupled simulation.\<close>

coinductive greatest_coupled_simulation :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
  where gcs:
    \<open>\<lbrakk>\<And> a p' . p \<longmapsto>a p' \<Longrightarrow> \<exists>q'. q \<Rightarrow>^^ a q' \<and> greatest_coupled_simulation p' q'; 
      \<exists> q' . q \<longmapsto>* tau q' \<and> greatest_coupled_simulation q' p\<rbrakk>
  \<Longrightarrow> greatest_coupled_simulation p q\<close>

lemma gcs_implies_gws:
  assumes \<open>greatest_coupled_simulation p q\<close>
  shows \<open>greatest_weak_simulation p q\<close>
  using assms by (metis greatest_coupled_simulation.cases greatest_weak_simulation.coinduct)

lemma gcs_is_coupled_simulation:
  shows \<open>coupled_simulation greatest_coupled_simulation\<close>
  unfolding coupled_simulation_def
proof safe
  \<comment>\<open>identical to ws\<close>
  fix p q p' a
  assume ih:
    \<open>greatest_coupled_simulation p q\<close>
    \<open>p \<longmapsto>a  p'\<close>
  hence \<open>(\<forall>x xa. p \<longmapsto>x xa \<longrightarrow> (\<exists>q'. q \<Rightarrow>^^ x  q' \<and> greatest_coupled_simulation xa q'))\<close>
    by (meson greatest_coupled_simulation.simps)
  then obtain q' where \<open>q \<Rightarrow>^^ a  q' \<and> greatest_coupled_simulation p' q'\<close> using ih by blast
  thus \<open>\<exists>q'. greatest_coupled_simulation p' q' \<and> q \<Rightarrow>^a  q'\<close>
    unfolding weak_step_tau2_def by blast
next
  fix p q
  assume
    \<open>greatest_coupled_simulation p q\<close>
  thus \<open>\<exists>q'. q \<longmapsto>* tau  q' \<and> greatest_coupled_simulation q' p\<close>
    by (meson greatest_coupled_simulation.simps)
qed

lemma coupled_similarity_implies_gcs:
  assumes \<open>p \<sqsubseteq>cs q\<close>
  shows \<open>greatest_coupled_simulation p q\<close>
  using assms
proof (coinduct)
  case (greatest_coupled_simulation p1 q1)
  then obtain R where \<open>coupled_simulation R\<close> \<open>R p1 q1\<close>
    \<open>weak_simulation R\<close> using coupled_simulation_implies_weak_simulation by blast
  then have \<open>(\<forall>x xa. p1 \<longmapsto>x  xa \<longrightarrow>
          (\<exists>q'. q1 \<Rightarrow>^x  q' \<and> (xa \<sqsubseteq>cs  q' \<or> greatest_coupled_simulation xa q'))) \<and>
        (\<exists>q'. q1 \<longmapsto>* tau  q' \<and>
          (q' \<sqsubseteq>cs  p1 \<or> greatest_coupled_simulation q' p1))\<close>
    unfolding weak_step_tau2_def
    using coupled_simulation_implies_coupling
       weak_sim_ruleformat[OF \<open>weak_simulation R\<close>]
    by (metis (no_types, lifting))
  thus ?case by simp
qed

lemma gcs_eq_coupled_sim_by:
  shows \<open>p \<sqsubseteq>cs q = greatest_coupled_simulation p q\<close>
  using coupled_similarity_implies_gcs gcs_is_coupled_simulation by blast

lemma coupled_sim_by_is_coupled_sim:
  shows
    \<open>coupled_simulation (\<lambda> p q . p \<sqsubseteq>cs q)\<close>
  unfolding gcs_eq_coupled_sim_by using gcs_is_coupled_simulation .

lemma coupledsim_unfold:
  shows \<open>p \<sqsubseteq>cs q =
    ((\<forall>a p'. p \<longmapsto>a  p' \<longrightarrow> (\<exists>q'. q \<Rightarrow>^a  q' \<and> p' \<sqsubseteq>cs q')) \<and>
       (\<exists>q'. q \<longmapsto>* tau  q' \<and> q' \<sqsubseteq>cs p))\<close>
  unfolding gcs_eq_coupled_sim_by weak_step_tau2_def[symmetric]
  by (metis lts_tau.greatest_coupled_simulation.simps)

subsection \<open>Coupled Simulation Join\<close>

text \<open>The following lemmas reproduce Proposition 3 from @{cite glabbeek2017} that internal choice
  acts as a least upper bound within the semi-lattice of CSP terms related by \<open>\<sqsubseteq>cs\<close> taking \<open>\<equiv>cs\<close>
  as equality.\<close>

lemma coupledsim_choice_1:
  assumes 
    \<open>p \<sqsubseteq>cs q\<close>
    \<open>\<And> pq a . pqc \<longmapsto>a pq \<longleftrightarrow> (a = \<tau> \<and> (pq = p \<or> pq = q))\<close>
  shows
    \<open>pqc \<sqsubseteq>cs q\<close>
    \<open>q \<sqsubseteq>cs pqc\<close>
proof -
  define R1 where \<open>R1 \<equiv> (\<lambda>p1 q1. q1 \<longmapsto>* tau  p1)\<close>
  have \<open>R1 q pqc\<close>
    using assms(2) steps_one_step R1_def by simp
  moreover have \<open>coupled_simulation R1\<close>
    unfolding R1_def using coupledsim_step_gla17 .
  ultimately show q_pqc: \<open>q \<sqsubseteq>cs pqc\<close> by blast
\<comment>\<open>next case\<close>
  define R where \<open>R \<equiv> \<lambda> p0 q0 . p0 = q \<and> q0 = pqc \<or> p0 = pqc \<and> q0 = q \<or> p0 = p \<and> q0 = q\<close>
  hence \<open>R pqc q\<close> by blast
  thus \<open>pqc \<sqsubseteq>cs  q\<close>
    unfolding gcs_eq_coupled_sim_by
  proof (coinduct)
    case (greatest_coupled_simulation p1 q1)
    then show ?case
      unfolding weak_step_tau2_def R_def
    proof safe
      assume \<open>q1 = pqc\<close> \<open>p1 = q\<close>
      thus \<open>\<exists>pa qa.
        q = pa \<and> pqc = qa \<and>
        (\<forall>x xa. pa \<longmapsto>x  xa \<longrightarrow>
          (\<exists>q'. qa \<Rightarrow>^x  q' \<and> ((xa = q \<and> q' = pqc \<or> xa = pqc \<and> q' = q \<or> xa = p \<and> q' = q)
            \<or> greatest_coupled_simulation xa q'))) \<and>
        (\<exists>q'. qa \<longmapsto>* tau  q' \<and>
            ((q' = q \<and> pa = pqc \<or> q' = pqc \<and> pa = q \<or> q' = p \<and> pa = q)
            \<or> greatest_coupled_simulation q' pa))\<close>
        using `q \<sqsubseteq>cs pqc` step_tau_refl weak_sim_ruleformat tau_def
          coupled_simulation_implies_weak_simulation[OF gcs_is_coupled_simulation] 
        unfolding gcs_eq_coupled_sim_by by fastforce
    next
      assume \<open>q1 = q\<close> \<open>p1 = pqc\<close>
      thus \<open>\<exists>pa qa.
        pqc = pa \<and> q = qa \<and>
        (\<forall>x xa. pa \<longmapsto>x  xa \<longrightarrow>
          (\<exists>q'. qa \<Rightarrow>^x  q' \<and> ((xa = q \<and> q' = pqc \<or> xa = pqc \<and> q' = q \<or> xa = p \<and> q' = q)
            \<or> greatest_coupled_simulation xa q'))) \<and>
        (\<exists>q'. qa \<longmapsto>* tau  q' \<and>
          ((q' = q \<and> pa = pqc \<or> q' = pqc \<and> pa = q \<or> q' = p \<and> pa = q)
            \<or> greatest_coupled_simulation q' pa))\<close>
        using R1_def \<open>coupled_simulation R1\<close> assms(2)
          coupled_similarity_implies_gcs step_tau_refl by fastforce
    next
      assume \<open>q1 = q\<close> \<open>p1 = p\<close>
      thus \<open>\<exists>pa qa.
       p = pa \<and> q = qa \<and>
       (\<forall>x xa. pa \<longmapsto>x  xa \<longrightarrow> (\<exists>q'. qa \<Rightarrow>^x  q' \<and> ((xa = q \<and> q' = pqc \<or> xa = pqc \<and> q' = q \<or> xa = p \<and> q' = q) \<or> greatest_coupled_simulation xa q'))) \<and>
       (\<exists>q'. qa \<longmapsto>* tau  q' \<and> ((q' = q \<and> pa = pqc \<or> q' = pqc \<and> pa = q \<or> q' = p \<and> pa = q) \<or> greatest_coupled_simulation q' pa))\<close>
        using `p \<sqsubseteq>cs q` weak_sim_ruleformat
          coupled_simulation_implies_weak_simulation[OF gcs_is_coupled_simulation]
          coupled_simulation_implies_coupling[OF gcs_is_coupled_simulation]
        unfolding gcs_eq_coupled_sim_by
        by (auto, metis+)
    qed
  qed
qed

lemma coupledsim_choice_2:
  assumes 
    \<open>pqc \<sqsubseteq>cs q\<close> 
    \<open>\<And> pq a . pqc \<longmapsto>a pq \<longleftrightarrow> (a = \<tau> \<and> (pq = p \<or> pq = q))\<close>
  shows
    \<open>p \<sqsubseteq>cs q\<close>
proof -
  have \<open>pqc \<longmapsto>\<tau> p\<close> using assms(2) by blast
  then obtain q' where \<open>q \<longmapsto>* tau q'\<close> \<open>p \<sqsubseteq>cs q'\<close>
    using assms(1) tau_tau unfolding coupled_simulation_def by blast
  then moreover have \<open>q' \<sqsubseteq>cs q\<close> using coupledsim_step_gla17 by blast
  ultimately show ?thesis using coupledsim_trans tau_tau by blast
qed

lemma coupledsim_choice_join:
  assumes 
    \<open>\<And> pq a . pqc \<longmapsto>a pq \<longleftrightarrow> (a = \<tau> \<and> (pq = p \<or> pq = q))\<close>
  shows
    \<open>p \<sqsubseteq>cs q \<longleftrightarrow> pqc \<equiv>cs q\<close>
  using  coupledsim_choice_1[OF _ assms] coupledsim_choice_2[OF _ assms] by blast

subsection \<open>Coupled Delay Simulation\<close>

text \<open>\<open>\<sqsubseteq>cs\<close> can also be characterized in terms of coupled delay simulations, which are
 conceptionally simpler than van Glabbeek's coupled simulation definition.\<close>

text \<open>In the greatest coupled simulation, \<open>\<tau>\<close>-challenges can be answered by stuttering.\<close>
lemma coupledsim_tau_challenge_trivial:
  assumes 
    \<open>p \<sqsubseteq>cs q\<close>
    \<open>p \<longmapsto>* tau p'\<close>
  shows
    \<open>p' \<sqsubseteq>cs q\<close>
  using assms coupledsim_trans coupledsim_step by blast

lemma coupled_similarity_s_delay_simulation:
  \<open>delay_simulation (\<lambda> p q. p \<sqsubseteq>cs q)\<close>
  unfolding delay_simulation_def
proof safe
  fix p q R p' a
  assume assms:
    \<open>coupled_simulation R\<close>
    \<open>R p q\<close>
    \<open>p \<longmapsto>a p'\<close>
  {
    assume \<open>tau a\<close>
    then show \<open>p' \<sqsubseteq>cs  q\<close>
      using assms coupledsim_tau_challenge_trivial steps_one_step by blast
  } {
    show \<open>\<exists>q'. p' \<sqsubseteq>cs  q' \<and> q =\<rhd>a  q'\<close>
    proof -
      obtain q''' where q'''_spec: \<open>q \<Rightarrow>^a q'''\<close> \<open>p' \<sqsubseteq>cs q'''\<close>
        using assms coupled_simulation_implies_weak_simulation weak_sim_ruleformat by metis
      show ?thesis
      proof (cases \<open>tau a\<close>)
        case True
        then have \<open>q \<longmapsto>* tau q'''\<close> using q'''_spec by blast
        thus ?thesis using q'''_spec(2) True assms(1) steps.refl by blast
      next
        case False
        then obtain q' q'' where q'q''_spec:
            \<open>q \<longmapsto>* tau q'\<close> \<open>q' \<longmapsto>a q''\<close> \<open>q'' \<longmapsto>* tau q'''\<close>
          using q'''_spec by blast
        hence \<open>q''' \<sqsubseteq>cs q''\<close> using coupledsim_step by blast
        hence \<open>p' \<sqsubseteq>cs q''\<close> using q'''_spec(2) coupledsim_trans by blast
        thus ?thesis using q'q''_spec(1,2) False by blast
      qed
    qed
  }
qed

definition coupled_delay_simulation ::
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
  \<open>coupled_delay_simulation R  \<equiv>
    delay_simulation R \<and> coupling R\<close>

lemma coupled_sim_by_eq_coupled_delay_simulation:
  \<open>(p \<sqsubseteq>cs q) = (\<exists>R. R p q \<and> coupled_delay_simulation R)\<close>
  unfolding coupled_delay_simulation_def
proof
  assume \<open>p \<sqsubseteq>cs q\<close>
  define R where \<open>R \<equiv> coupled_simulated_by\<close>
  hence \<open>R p q \<and> delay_simulation R \<and> coupling R\<close>
    using coupled_similarity_s_delay_simulation coupled_sim_by_is_coupled_sim
        coupled_simulation_implies_coupling \<open>p \<sqsubseteq>cs q\<close> by blast
  thus \<open>\<exists>R. R p q \<and> delay_simulation R \<and> coupling R\<close> by blast
next
  assume \<open>\<exists>R. R p q \<and> delay_simulation R \<and> coupling R\<close>
  then obtain R where \<open>R p q\<close> \<open>delay_simulation R\<close> \<open>coupling R\<close> by blast
  hence \<open>coupled_simulation R\<close>
    using delay_simulation_implies_weak_simulation coupled_simulation_weak_simulation by blast
  thus \<open>p \<sqsubseteq>cs q\<close> using \<open>R p q\<close> by blast
qed

subsection \<open>Relationship to Contrasimulation and Weak Simulation\<close>

text \<open>Coupled simulation is precisely the intersection of contrasimulation and weak simulation.\<close>

lemma weak_sim_and_contrasim_implies_coupled_sim:
  assumes
    \<open>contrasimulation R\<close>
    \<open>weak_simulation R\<close>
  shows
    \<open>coupled_simulation R\<close>
  unfolding coupled_simulation_weak_simulation
  using contrasim_coupled assms by blast

lemma coupledsim_implies_contrasim:
  assumes
    \<open>coupled_simulation R\<close>
  shows 
    \<open>contrasimulation R\<close>
proof -
  have \<open>contrasim_step R\<close>
  unfolding contrasim_step_def
  proof (rule allI impI)+
    fix p q p' a
    assume
      \<open>R p q \<and> p \<Rightarrow>^a  p'\<close>
    then obtain q' where q'_def: \<open>R p' q'\<close> \<open>q \<Rightarrow>^a  q'\<close>
      using assms unfolding coupled_simulation_weak_premise by blast
    then obtain q'' where q''_def: \<open>R q'' p'\<close> \<open>q' \<longmapsto>* tau  q''\<close>
      using assms unfolding coupled_simulation_weak_premise by blast
    then have \<open>q \<Rightarrow>^a  q''\<close> using q'_def(2) steps_concat by blast
    thus \<open>\<exists>q'. q \<Rightarrow>^a  q' \<and> R q' p'\<close>
      using q''_def(1) by blast
  qed
  thus \<open>contrasimulation R\<close> using contrasim_step_seq_coincide_for_sims
      coupled_simulation_implies_weak_simulation[OF assms] by blast 
qed

lemma coupled_simulation_iff_weak_sim_and_contrasim:
  shows \<open>coupled_simulation R \<longleftrightarrow> contrasimulation R \<and> weak_simulation R\<close>
  using weak_sim_and_contrasim_implies_coupled_sim
    coupledsim_implies_contrasim coupled_simulation_weak_simulation by blast

subsection \<open>\<open>\<tau>\<close>-Reachability (and Divergence)\<close>

text \<open>
  Coupled similarity comes close to (weak) bisimilarity in two respects:

  \<^item> If there are no \<open>\<tau>\<close> transitions, coupled similarity coincides with bisimilarity.

  \<^item> If there are only finite \<open>\<tau>\<close> reachable portions, then coupled similarity contains a
  bisimilarity on the \<open>\<tau>\<close>-maximal states. (For this,  \<open>\<tau>\<close>-cycles have to be ruled out, which, as
  we show, is no problem because their removal is transparent to coupled similarity.)
\<close>

lemma taufree_coupledsim_symm:
  assumes
    \<open>\<And> p1 a p2 . (p1 \<longmapsto>a p2 \<Longrightarrow> \<not> tau a)\<close>
    \<open>coupled_simulation R\<close>
    \<open>R p q\<close>
  shows \<open>R q p\<close>
  using assms(1,3) coupledsim_implies_contrasim[OF assms(2)] contrasim_taufree_symm
  by blast

lemma taufree_coupledsim_weak_bisim:
  assumes
    \<open>\<And> p1 a p2 . (p1 \<longmapsto>a p2 \<Longrightarrow> \<not> tau a)\<close>
    \<open>coupled_simulation R\<close>
  shows \<open>weak_bisimulation R\<close>
  using assms contrasim_taufree_symm symm_contrasim_is_weak_bisim coupledsim_implies_contrasim[OF assms(2)]
  by blast

lemma coupledsim_stable_state_symm:
  assumes
    \<open>coupled_simulation R\<close>
    \<open>R p q\<close>
    \<open>stable_state q\<close>
  shows
    \<open>R q p\<close>
  using assms steps_left unfolding coupled_simulation_def by metis

text \<open>In finite systems, coupling is guaranteed to happen through \<open>\<tau>\<close>-maximal states.\<close>
lemma coupledsim_max_coupled:
  assumes 
    \<open>p \<sqsubseteq>cs q\<close>
    \<open>\<And> r1 r2 . r1 \<longmapsto>* tau r2 \<and> r2 \<longmapsto>* tau r1 \<Longrightarrow> r1 = r2\<close> \<comment>\<open>contracted tau cycles\<close>
    \<open>\<And> r. finite {r'. r \<longmapsto>* tau r'}\<close>
  shows
    \<open>\<exists> q' . q \<longmapsto>* tau q' \<and> q' \<sqsubseteq>cs p \<and> tau_max q'\<close>
proof -
  obtain q1 where q1_spec: \<open>q \<longmapsto>* tau q1\<close> \<open>q1 \<sqsubseteq>cs p\<close> 
    using assms(1) coupled_simulation_implies_coupling coupledsim_implies_contrasim by blast
  then obtain q' where \<open>q1 \<longmapsto>* tau q'\<close> \<open>(\<forall>q''. q' \<longmapsto>* tau q'' \<longrightarrow> q' = q'')\<close>
    using tau_max_deadlock assms(2,3) by blast
  then moreover have \<open>q' \<sqsubseteq>cs p\<close> \<open>q \<longmapsto>* tau q'\<close>
    using q1_spec coupledsim_trans coupledsim_step steps_concat[of q1 tau q' q]
    by blast+
  ultimately show ?thesis by blast
qed

text \<open>In the greatest coupled simulation, \<open>a\<close>-challenges can be answered by a weak move without
  trailing \<open>\<tau>\<close>-steps. (This property is what bridges the gap between weak and delay simulation for 
  coupled simulation.)\<close>
lemma coupledsim_step_challenge_short_answer:
  assumes 
    \<open>p \<sqsubseteq>cs q\<close>
    \<open>p \<longmapsto>a p'\<close>
    \<open>\<not> tau a\<close>
  shows
    \<open>\<exists> q' q1. p' \<sqsubseteq>cs q' \<and> q \<longmapsto>* tau q1 \<and> q1 \<longmapsto>a q'\<close>
  using assms
  unfolding coupled_sim_by_eq_coupled_delay_simulation
    coupled_delay_simulation_def delay_simulation_def by blast

text \<open>If two states share the same outgoing edges with except for one \<open>\<tau>\<close>-loop, then they cannot
  be distinguished by coupled similarity.\<close>
lemma coupledsim_tau_loop_ignorance:
  assumes
    \<open>\<And> a p'. p \<longmapsto>a p' \<or> p' = pp \<and> a = \<tau> \<longleftrightarrow> pp \<longmapsto>a p'\<close>
  shows
    \<open>pp \<equiv>cs p\<close>
proof -
  define R where \<open>R \<equiv> \<lambda> p1 q1. p1 = q1 \<or> p1 = pp \<and> q1 = p \<or> p1 = p \<and> q1 = pp\<close>
  have \<open>coupled_simulation R\<close>
    unfolding coupled_simulation_def R_def
  proof (safe)
    fix pa q p' a
    assume
      \<open>q \<longmapsto>a  p'\<close>
    thus \<open>\<exists>q'. (p' = q' \<or> p' = pp \<and> q' = p \<or> p' = p \<and> q' = pp) \<and> q \<Rightarrow>^a  q'\<close>
      using assms step_weak_step_tau by auto
  next
    fix pa q
    show \<open>\<exists>q'. q \<longmapsto>* tau  q' \<and> (q' = q \<or> q' = pp \<and> q = p \<or> q' = p \<and> q = pp)\<close>
      using steps.refl by blast
  next
    fix pa q p' a
    assume
      \<open>pp \<longmapsto>a  p'\<close>
    thus \<open>\<exists>q'. (p' = q' \<or> p' = pp \<and> q' = p \<or> p' = p \<and> q' = pp) \<and> p \<Rightarrow>^a  q'\<close>
      using assms by (metis lts.steps.simps tau_def)
  next
    fix pa q
    show \<open>\<exists>q'. p \<longmapsto>* tau  q' \<and> (q' = pp \<or> q' = pp \<and> pp = p \<or> q' = p \<and> pp = pp)\<close>
      using steps.refl[of p tau] by blast
  next
    fix pa q p' a
    assume
      \<open>p \<longmapsto>a  p'\<close>
    thus \<open>\<exists>q'. (p' = q' \<or> p' = pp \<and> q' = p \<or> p' = p \<and> q' = pp) \<and> pp \<Rightarrow>^a  q'\<close>
      using assms step_weak_step_tau by fastforce
  next
    fix pa q
    show \<open>\<exists>q'. pp \<longmapsto>* tau  q' \<and> (q' = p \<or> q' = pp \<and> p = p \<or> q' = p \<and> p = pp)\<close>
      using steps.refl[of pp tau] by blast
  qed
  moreover have \<open>R p pp\<close> \<open>R pp p\<close> unfolding R_def by auto
  ultimately show ?thesis by blast
qed

subsection \<open>On the Connection to Weak Bisimulation\<close>

text \<open>When one only considers steps leading to \<open>\<tau>\<close>-maximal states in a system without infinite
  \<open>\<tau>\<close>-reachable regions (e.g. a finite system), then \<open>\<equiv>cs\<close> on these steps is a bisimulation.\<close>

text \<open>This lemma yields a neat argument why one can use a signature refinement algorithm to
  pre-select the tuples which come into question for further checking of coupled simulation
  by contraposition.\<close>
lemma coupledsim_eventual_symmetry:
  assumes
    contracted_cycles: \<open>\<And> r1 r2 . r1 \<longmapsto>* tau r2 \<and> r2 \<longmapsto>* tau r1 \<Longrightarrow> r1 = r2\<close> and
    finite_taus: \<open>\<And> r. finite {r'. r \<longmapsto>* tau r'}\<close> and
    cs: \<open>p \<sqsubseteq>cs q\<close> and
    step: \<open>p \<Rightarrow>^a p'\<close> and
    tau_max_p': \<open>tau_max p'\<close>
  shows
    \<open>\<exists> q'. tau_max q' \<and> q \<Rightarrow>^a q' \<and> p' \<equiv>cs q'\<close>
proof-
  obtain q' where q'_spec: \<open>q \<Rightarrow>^a q'\<close> \<open>p' \<sqsubseteq>cs q'\<close>
    using cs step unfolding coupled_simulation_weak_premise by blast
  then obtain q'' where q''_spec: \<open>q' \<longmapsto>* tau q''\<close> \<open>q'' \<sqsubseteq>cs p'\<close>
    using cs unfolding coupled_simulation_weak_simulation by blast
  then obtain q_max where q_max_spec: \<open>q'' \<longmapsto>* tau q_max\<close> \<open>tau_max q_max\<close> 
    using tau_max_deadlock contracted_cycles finite_taus by force
  hence \<open>q_max \<sqsubseteq>cs p'\<close> using q''_spec coupledsim_tau_challenge_trivial by blast
  hence \<open>q_max \<equiv>cs p'\<close> using tau_max_p' coupledsim_tau_max_eq by blast
  moreover have \<open>q \<Rightarrow>^a q_max\<close> using q_max_spec q'_spec q''_spec steps_concat by blast
  ultimately show ?thesis using q_max_spec(2) by blast
qed

text \<open>Even without the assumption that the left-hand-side step \<open>p \<Rightarrow>^a p'\<close> ends in a \<open>\<tau>\<close>-maximal state,
a situation resembling bismulation can be set up -- with the drawback that it only refers to
a \<open>\<tau>\<close>-maximal sibling of \<open>p'\<close>.\<close>
lemma coupledsim_eventuality_2:
  assumes
    contracted_cycles: \<open>\<And> r1 r2 . r1 \<longmapsto>* tau r2 \<and> r2 \<longmapsto>* tau r1 \<Longrightarrow> r1 = r2\<close> and
    finite_taus: \<open>\<And> r. finite {r'. r \<longmapsto>* tau r'}\<close> and
    cbisim: \<open>p \<equiv>cs q\<close> and
    step: \<open>p \<Rightarrow>^a p'\<close>
  shows
    \<open>\<exists> p'' q'. tau_max p'' \<and> tau_max q' \<and> p \<Rightarrow>^a p'' \<and> q \<Rightarrow>^a q' \<and> p'' \<equiv>cs q'\<close>
proof-
  obtain q' where q'_spec: \<open>q \<Rightarrow>^a q'\<close>
    using cbisim step unfolding coupled_simulation_weak_premise by blast
  then obtain q_max where q_max_spec: \<open>q' \<longmapsto>* tau q_max\<close> \<open>tau_max q_max\<close>
    using tau_max_deadlock contracted_cycles finite_taus by force
  hence \<open>q \<Rightarrow>^a q_max\<close> using q'_spec steps_concat by blast
  then obtain p'' where p''_spec: \<open>p \<Rightarrow>^a p''\<close> \<open>q_max \<sqsubseteq>cs p''\<close>
    using cbisim unfolding coupled_simulation_weak_premise by blast
  then obtain p''' where p'''_spec: \<open>p'' \<longmapsto>* tau p'''\<close> \<open>p''' \<sqsubseteq>cs q_max\<close>
    using cbisim unfolding coupled_simulation_weak_simulation  by blast
  then obtain p_max where p_max_spec: \<open>p''' \<longmapsto>* tau p_max\<close> \<open>tau_max p_max\<close>
    using tau_max_deadlock contracted_cycles finite_taus by force
  hence \<open>p_max \<sqsubseteq>cs p'''\<close> using coupledsim_step by blast
  hence \<open>p_max \<sqsubseteq>cs q_max\<close> using p'''_spec coupledsim_trans by blast
  hence \<open>q_max \<equiv>cs p_max\<close> using coupledsim_tau_max_eq q_max_spec by blast
  moreover have  \<open>p \<Rightarrow>^a p_max\<close>
    using  p''_spec(1) steps_concat[OF p_max_spec(1) p'''_spec(1)] steps_concat by blast
  ultimately show ?thesis using p_max_spec(2) q_max_spec(2) `q \<Rightarrow>^a q_max` by blast
qed

lemma coupledsim_eq_reducible_1:
  assumes
    contracted_cycles: \<open>\<And> r1 r2 . r1 \<longmapsto>* tau r2 \<and> r2 \<longmapsto>* tau r1 \<Longrightarrow> r1 = r2\<close> and
    finite_taus: \<open>\<And> r. finite {r'. r \<longmapsto>* tau r'}\<close> and
    tau_shortcuts:
      \<open>\<And>r a r'. r \<longmapsto>* tau r' \<Longrightarrow> \<exists>r''. tau_max r'' \<and> r \<longmapsto>\<tau> r'' \<and> r' \<sqsubseteq>cs r''\<close>  and
    sim_vis_p:
      \<open>\<And>p' a. \<not>tau a \<Longrightarrow> p \<Rightarrow>^a p' \<Longrightarrow> \<exists>p'' q'. q \<Rightarrow>^a q' \<and> p' \<sqsubseteq>cs q'\<close> and
    sim_tau_max_p:
      \<open>\<And>p'. tau_max p' \<Longrightarrow> p \<longmapsto>* tau p' \<Longrightarrow> \<exists>q'. tau_max q' \<and> q \<longmapsto>* tau q' \<and> p' \<equiv>cs q'\<close>
  shows
    \<open>p \<sqsubseteq>cs q\<close>
proof-
  have
    \<open>((\<forall>a p'. p \<longmapsto>a  p' \<longrightarrow> (\<exists>q'. q \<Rightarrow>^a  q' \<and> p' \<sqsubseteq>cs q')) \<and>
    (\<exists>q'. q \<longmapsto>* tau  q' \<and> q' \<sqsubseteq>cs p))\<close>
  proof safe
    fix a p'
    assume
      step: \<open>p \<longmapsto>a  p'\<close>
    thus \<open>\<exists>q'. q \<Rightarrow>^a  q' \<and> p' \<sqsubseteq>cs  q'\<close>
    proof (cases \<open>tau a\<close>)
      case True
      then obtain p'' where p''_spec: \<open>p \<longmapsto>\<tau> p''\<close> \<open>tau_max p''\<close> \<open>p' \<sqsubseteq>cs p''\<close>
        using tau_shortcuts step tau_def steps_one_step[of p \<tau> p']
        by (metis (no_types, lifting))
      then obtain q' where q'_spec: \<open>q \<longmapsto>* tau q'\<close> \<open>p'' \<equiv>cs q'\<close>
        using sim_tau_max_p steps_one_step[OF step, of tau, OF `tau a`]
          steps_one_step[of p \<tau> p''] tau_def
        by metis
      then show ?thesis using `tau a` p''_spec(3) using coupledsim_trans by blast
    next
      case False
      then show ?thesis using sim_vis_p step_weak_step_tau[OF step] by blast
    qed
  next
    obtain p_max where \<open>p \<longmapsto>* tau p_max\<close> \<open>tau_max p_max\<close>
      using tau_max_deadlock contracted_cycles finite_taus by blast
    then obtain q_max where \<open>q \<longmapsto>* tau  q_max\<close> \<open>q_max \<sqsubseteq>cs p_max\<close>
      using sim_tau_max_p[of p_max] by force
    moreover have \<open>p_max \<sqsubseteq>cs  p\<close> using `p \<longmapsto>* tau p_max` coupledsim_step by blast
    ultimately show \<open>\<exists>q'. q \<longmapsto>* tau  q' \<and> q' \<sqsubseteq>cs  p\<close>
      using coupledsim_trans by blast
  qed
  thus \<open>p \<sqsubseteq>cs q\<close> using coupledsim_unfold[symmetric] by auto
qed

lemma coupledsim_eq_reducible_2:
  assumes
    cs: \<open>p \<sqsubseteq>cs q\<close> and
    contracted_cycles: \<open>\<And>r1 r2 . r1 \<longmapsto>* tau r2 \<and> r2 \<longmapsto>* tau r1 \<Longrightarrow> r1 = r2\<close> and
    finite_taus: \<open>\<And>r. finite {r'. r \<longmapsto>* tau r'}\<close>
  shows
    sim_vis_p:
      \<open>\<And>p' a. \<not>tau a \<Longrightarrow> p \<Rightarrow>^a p' \<Longrightarrow> \<exists>q'. q \<Rightarrow>^a q' \<and> p' \<sqsubseteq>cs q'\<close> and
    sim_tau_max_p:
      \<open>\<And>p'. tau_max p' \<Longrightarrow> p \<longmapsto>* tau p' \<Longrightarrow> \<exists>q'. tau_max q' \<and> q \<longmapsto>* tau q' \<and> p' \<equiv>cs q'\<close>
proof-
  fix p' a
  assume
    \<open>\<not> tau a\<close>
    \<open>p \<Rightarrow>^a  p'\<close>
  thus \<open>\<exists>q'. q \<Rightarrow>^a  q' \<and> p' \<sqsubseteq>cs  q'\<close>
    using cs unfolding coupled_simulation_weak_premise by blast
next
  fix p'
  assume step:
    \<open>p \<longmapsto>* tau p'\<close>
    \<open>tau_max p'\<close>
  hence \<open>p \<Rightarrow>^\<tau>  p'\<close>  by auto
  hence \<open>\<exists> q'. tau_max q' \<and> q \<Rightarrow>^\<tau> q' \<and> p' \<equiv>cs q'\<close>
    using coupledsim_eventual_symmetry[OF _ finite_taus, of p q \<tau> p']
      contracted_cycles cs step(2) by blast
  thus \<open>\<exists> q'. tau_max q' \<and> q \<longmapsto>* tau q' \<and> p' \<equiv>cs q'\<close>
    by auto
qed

subsection \<open>Reduction Semantics Coupled Simulation\<close>

text \<open>The tradition to describe coupled simulation as special delay/weak simulation is quite
  common for coupled simulations on reduction semantics as in @{cite "gp15" and "Fournet2005"},
  of which @{cite "gp15"} can also be found in the AFP @{cite "Encodability_Process_Calculi-AFP"}.
  The notions coincide (for systems just with \<open>\<tau>\<close>-transitions).\<close>

definition coupled_simulation_gp15 ::
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>coupled_simulation_gp15 R \<equiv> \<forall> p q p'. R p q \<and> (p \<longmapsto>* (\<lambda>a. True) p') \<longrightarrow>
    (\<exists> q'. (q \<longmapsto>* (\<lambda>a. True) q') \<and> R p' q') \<and>
    (\<exists> q'. (q \<longmapsto>* (\<lambda>a. True) q') \<and> R q' p')\<close>

lemma weak_bisim_implies_coupled_sim_gp15:
  assumes
    wbisim: \<open>weak_bisimulation R\<close> and 
    symmetry: \<open>\<And> p q . R p q \<Longrightarrow> R q p\<close>
  shows \<open>coupled_simulation_gp15 R\<close>
unfolding coupled_simulation_gp15_def proof safe
  fix p q p'
  assume Rpq: \<open>R p q\<close> \<open>p \<longmapsto>* (\<lambda>a. True)  p'\<close>
  have always_tau: \<open>\<And>a. tau a \<Longrightarrow> (\<lambda>a. True) a\<close> by simp
  hence \<open>\<exists>q'. q \<longmapsto>* (\<lambda>a. True)  q' \<and> R p' q'\<close>
    using steps_retain_weak_bisim[OF wbisim Rpq] by auto
  moreover hence \<open>\<exists>q'. q \<longmapsto>* (\<lambda>a. True)  q' \<and> R q' p'\<close>
    using symmetry by auto
  ultimately show
    \<open>(\<exists>q'. q \<longmapsto>* (\<lambda>a. True)  q' \<and> R p' q')\<close>
    \<open>(\<exists>q'. q \<longmapsto>* (\<lambda>a. True)  q' \<and> R q' p')\<close> .
qed

lemma coupledsim_gla17_implies_gp15:
  assumes
    \<open>coupled_simulation R\<close>
  shows 
    \<open>coupled_simulation_gp15 R\<close>
  unfolding coupled_simulation_gp15_def
proof safe
  fix p q p'
  assume challenge:
    \<open>R p q\<close>
    \<open>p \<longmapsto>*(\<lambda>a. True)p'\<close>
  have tau_true: \<open>\<And>a. tau a \<Longrightarrow> (\<lambda>a. True) a\<close> by simp
  thus \<open>\<exists>q'. q \<longmapsto>* (\<lambda>a. True)  q' \<and> R p' q'\<close>
    using steps_retain_weak_sim assms challenge
    unfolding coupled_simulation_weak_simulation by meson
  then obtain q' where q'_def: \<open>q \<longmapsto>* (\<lambda>a. True)  q'\<close> \<open>R p' q'\<close> by blast
  then obtain q'' where \<open>q' \<longmapsto>* tau  q''\<close> \<open>R q'' p'\<close>
    using assms unfolding coupled_simulation_weak_simulation by blast
  moreover hence \<open>q \<longmapsto>* (\<lambda>a. True)  q''\<close>
    using q'_def(1) steps_concat steps_spec tau_true by meson
  ultimately show \<open>\<exists>q'. q \<longmapsto>* (\<lambda>a. True)  q' \<and> R q' p'\<close> by blast
qed

lemma coupledsim_gp15_implies_gla17_on_tau_systems:
  assumes
    \<open>coupled_simulation_gp15 R\<close>
    \<open>\<And> a . tau a\<close>
  shows 
    \<open>coupled_simulation R\<close>
  unfolding coupled_simulation_def
proof safe
  fix p q p' a
  assume challenge:
    \<open>R p q\<close>
    \<open>p \<longmapsto>a  p'\<close>
  hence \<open>p \<longmapsto>* (\<lambda>a. True)  p'\<close> using steps_one_step by metis
  then obtain q' where \<open>q \<longmapsto>* (\<lambda>a. True)  q'\<close> \<open>R p' q'\<close>
    using challenge(1) assms(1) unfolding coupled_simulation_gp15_def by blast
  hence \<open>q \<Rightarrow>^a  q'\<close> using assms(2) steps_concat steps_spec by meson
  thus \<open>\<exists>q'. R p' q' \<and> q \<Rightarrow>^a  q'\<close> using `R p' q'` by blast
next
  fix p q
  assume
    \<open>R p q\<close>
  moreover have \<open>p \<longmapsto>* (\<lambda>a. True) p\<close> using steps.refl by blast
  ultimately have \<open>\<exists>q'. q \<longmapsto>* (\<lambda>a. True)  q' \<and> R q' p\<close>
    using assms(1) unfolding coupled_simulation_gp15_def by blast
  thus \<open>\<exists>q'. q \<longmapsto>* tau  q' \<and> R q' p\<close> using assms(2) steps_spec by blast
qed


subsection \<open>Coupled Simulation as Two Simulations\<close>

text \<open>Historically, coupled similarity has been defined in terms of @{emph \<open>two\<close>} weak simulations
  coupled in some way @{cite "sangiorgi2012" and "ps1994"}.
  We reproduce these (more well-known) formulations and show that they are equivalent to the
  coupled (delay) simulations we are using.\<close>

\<comment>\<open>From @{cite "sangiorgi2012"}\<close>
definition coupled_simulation_san12 :: 
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>coupled_simulation_san12 R1 R2 \<equiv>
    weak_simulation R1 \<and> weak_simulation (\<lambda> p q . R2 q p)
  \<and> (\<forall> p q . R1 p q \<longrightarrow> (\<exists> q' . q \<longmapsto>* tau q' \<and> R2 p q'))
  \<and> (\<forall> p q . R2 p q \<longrightarrow> (\<exists> p' . p \<longmapsto>* tau p' \<and> R1 p' q))\<close>
  
lemma weak_bisim_implies_coupled_sim_san12:
  assumes \<open>weak_bisimulation R\<close>
  shows \<open>coupled_simulation_san12 R R\<close>
  using assms weak_bisim_weak_sim steps.refl[of _ tau]
  unfolding coupled_simulation_san12_def
  by blast

lemma coupledsim_gla17_resembles_san12:
  shows
    \<open>coupled_simulation R1 =
    coupled_simulation_san12 R1 (\<lambda> p q . R1 q p)\<close>
  unfolding coupled_simulation_weak_simulation coupled_simulation_san12_def by blast

lemma coupledsim_san12_impl_gla17:
  assumes
    \<open>coupled_simulation_san12 R1 R2\<close>
  shows
    \<open>coupled_simulation (\<lambda> p q. R1 p q \<or> R2 q p)\<close>
  unfolding coupled_simulation_weak_simulation
proof safe
  have \<open>weak_simulation R1\<close> \<open>weak_simulation (\<lambda>p q. R2 q p)\<close>
    using assms unfolding coupled_simulation_san12_def by auto
  thus \<open>weak_simulation (\<lambda>p q. R1 p q \<or> R2 q p)\<close>
    using weak_sim_union_cl by blast
next
  fix p q
  assume
    \<open>R1 p q\<close>
  hence \<open>\<exists>q'. q \<longmapsto>* tau  q' \<and> R2 p q'\<close>
    using assms unfolding coupled_simulation_san12_def by auto
  thus \<open>\<exists>q'. q \<longmapsto>* tau  q' \<and> (R1 q' p \<or> R2 p q')\<close> by blast
next
  fix p q
  assume
    \<open>R2 q p\<close>
  hence \<open>\<exists>q'. q \<longmapsto>* tau  q' \<and> R1 q' p\<close>
    using assms unfolding coupled_simulation_san12_def by auto
  thus \<open>\<exists>q'. q \<longmapsto>* tau  q' \<and> (R1 q' p \<or> R2 p q')\<close> by blast
qed

subsection \<open>S-coupled Simulation\<close>

text \<open>Originally coupled simulation was introduced as two weak simulations coupled at the stable
  states. We give the definitions from @{cite "parrow1992" and "ps1994"} and a proof connecting
  this notion to “our” coupled similarity in the absence of divergences following
  @{cite "sangiorgi2012"}.\<close>

\<comment>\<open>From @{cite "parrow1992"}\<close>
definition coupled_simulation_p92 :: 
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>coupled_simulation_p92 R1 R2 \<equiv> \<forall> p q . 
    (R1 p q \<longrightarrow> 
      ((\<forall> p' a. p \<longmapsto>a p' \<longrightarrow> 
        (\<exists> q'. R1 p' q' \<and> 
          (q \<Rightarrow>^a q'))) \<and>
      (stable_state p \<longrightarrow> R2 p q))) \<and>
    (R2 p q \<longrightarrow> 
      ((\<forall> q' a. q \<longmapsto>a q' \<longrightarrow>
        (\<exists> p'. R2 p' q' \<and> 
          (p \<Rightarrow>^a p'))) \<and>
      (stable_state q \<longrightarrow> R1 p q)))\<close>

lemma weak_bisim_implies_coupled_sim_p92:
  assumes \<open>weak_bisimulation R\<close>
  shows \<open>coupled_simulation_p92 R R\<close>
using assms unfolding weak_bisimulation_def coupled_simulation_p92_def by blast
  
lemma coupled_sim_p92_symm:
  assumes \<open>coupled_simulation_p92 R1 R2\<close>
  shows \<open>coupled_simulation_p92 (\<lambda> p q. R2 q p) (\<lambda> p q. R1 q p)\<close>
using assms unfolding coupled_simulation_p92_def by blast
  
definition s_coupled_simulation_san12 :: 
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>s_coupled_simulation_san12 R1 R2 \<equiv>
    weak_simulation R1 \<and> weak_simulation (\<lambda> p q . R2 q p)
  \<and> (\<forall> p q . R1 p q \<longrightarrow> stable_state p \<longrightarrow> R2 p q)
  \<and> (\<forall> p q . R2 p q \<longrightarrow> stable_state q \<longrightarrow> R1 p q)\<close>

abbreviation s_coupled_simulated_by :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> ("_ \<sqsubseteq>scs  _" [60, 60] 65)
  where \<open>s_coupled_simulated_by p q \<equiv>
    \<exists> R1 R2 . s_coupled_simulation_san12 R1 R2 \<and> R1 p q\<close>
    
abbreviation s_coupled_similar :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> ("_ \<equiv>scs  _" [60, 60] 65)
  where \<open>s_coupled_similar p q \<equiv>
    \<exists> R1 R2 . s_coupled_simulation_san12 R1 R2 \<and> R1 p q \<and> R2 p q\<close>

lemma s_coupled_sim_is_original_coupled:
  \<open>s_coupled_simulation_san12 = coupled_simulation_p92\<close>
unfolding coupled_simulation_p92_def
  s_coupled_simulation_san12_def weak_simulation_def by blast
 
corollary weak_bisim_implies_s_coupled_sim:
  assumes \<open>weak_bisimulation R\<close>
  shows \<open>s_coupled_simulation_san12 R R\<close>
  using assms s_coupled_sim_is_original_coupled weak_bisim_implies_coupled_sim_p92 by simp
   
corollary s_coupled_sim_symm:
  assumes \<open>s_coupled_simulation_san12 R1 R2\<close>
  shows \<open>s_coupled_simulation_san12 (\<lambda> p q. R2 q p) (\<lambda> p q. R1 q p)\<close>
  using assms coupled_sim_p92_symm s_coupled_sim_is_original_coupled by simp
   
corollary s_coupled_sim_union_cl:
  assumes
    \<open>s_coupled_simulation_san12 RA1 RA2\<close>
    \<open>s_coupled_simulation_san12 RB1 RB2\<close>
  shows
    \<open>s_coupled_simulation_san12 (\<lambda> p q. RA1 p q \<or> RB1 p q) (\<lambda> p q. RA2 p q \<or> RB2 p q)\<close>
  using assms weak_sim_union_cl unfolding s_coupled_simulation_san12_def by auto
    
corollary s_coupled_sim_symm_union:
  assumes \<open>s_coupled_simulation_san12 R1 R2\<close>
  shows \<open>s_coupled_simulation_san12 (\<lambda> p q. R1 p q \<or> R2 q p) (\<lambda> p q. R2 p q \<or> R1 q p)\<close>
  using s_coupled_sim_union_cl[OF assms s_coupled_sim_symm[OF assms]] .

lemma s_coupledsim_stable_eq:
  assumes
    \<open>p \<sqsubseteq>scs q\<close>
    \<open>stable_state p\<close>
  shows  \<open>p \<equiv>scs q\<close> 
proof -
  obtain R1 R2 where
      \<open>R1 p q\<close>
      \<open>weak_simulation R1\<close>
      \<open>weak_simulation (\<lambda>p q. R2 q p)\<close>
      \<open>\<forall>p q. R1 p q \<longrightarrow> stable_state p \<longrightarrow> R2 p q\<close>
      \<open>\<forall>p q. R2 p q \<longrightarrow> stable_state q \<longrightarrow> R1 p q\<close>
    using assms(1)  unfolding s_coupled_simulation_san12_def by blast
  moreover hence \<open>R2 p q\<close> using assms(2) by blast
  ultimately show ?thesis unfolding s_coupled_simulation_san12_def by blast
qed

lemma s_coupledsim_symm:
  assumes
    \<open>p \<equiv>scs q\<close> 
  shows 
    \<open>q \<equiv>scs p\<close> 
  using assms s_coupled_sim_symm by blast

lemma s_coupledsim_eq_parts:
  assumes
    \<open>p \<equiv>scs q\<close>
  shows
    \<open>p \<sqsubseteq>scs q\<close>
    \<open>q \<sqsubseteq>scs p\<close>
  using assms s_coupledsim_symm by metis+

\<comment>\<open>From @{cite "sangiorgi2012"}, p.~226\<close>
lemma divergence_free_coupledsims_coincidence_1:
  defines 
    \<open>R1 \<equiv> (\<lambda> p q . p \<sqsubseteq>cs q \<and> (stable_state p \<longrightarrow> stable_state q))\<close> and
    \<open>R2 \<equiv> (\<lambda> p q . q \<sqsubseteq>cs p \<and> (stable_state q \<longrightarrow> stable_state p))\<close>
  assumes
    non_divergent_system: \<open>\<And> p . \<not> divergent_state p\<close>
  shows
    \<open>s_coupled_simulation_san12 R1 R2\<close>
  unfolding s_coupled_simulation_san12_def
proof safe
  show \<open>weak_simulation R1\<close> unfolding weak_simulation_def
  proof safe
    fix p q p' a
    assume sub_assms:
      \<open>R1 p q\<close>
      \<open>p \<longmapsto>a  p'\<close>
    then obtain q' where q'_def: \<open>q \<Rightarrow>^a q'\<close> \<open>p' \<sqsubseteq>cs q'\<close>
      using coupled_sim_by_is_coupled_sim unfolding R1_def coupled_simulation_def by blast
    show \<open>\<exists>q'. R1 p' q' \<and> q \<Rightarrow>^a  q'\<close>
    proof (cases \<open>stable_state p'\<close>)
      case True
      obtain  q'' where q''_def: \<open>q' \<longmapsto>* tau q''\<close> \<open>q'' \<sqsubseteq>cs  p'\<close>
        using coupled_sim_by_is_coupled_sim q'_def(2)
        unfolding coupled_simulation_weak_simulation by blast
      then obtain q''' where q'''_def: \<open>q'' \<longmapsto>* tau q'''\<close> \<open>stable_state q'''\<close>
        using non_divergence_implies_eventual_stability non_divergent_system by blast
      hence \<open>q''' \<sqsubseteq>cs p'\<close>
        using coupledsim_step_gla17 coupledsim_trans[OF _ q''_def(2)] by blast
      hence \<open>p' \<sqsubseteq>cs q'''\<close>
        using `stable_state p'` coupled_sim_by_is_coupled_sim coupledsim_stable_state_symm
        by blast
      moreover have \<open>q \<Rightarrow>^a q'''\<close> using q'_def(1) q''_def(1) q'''_def(1) steps_concat by blast
      ultimately show ?thesis using q'''_def(2) unfolding R1_def by blast
    next
      case False
      then show ?thesis using q'_def unfolding R1_def by blast
    qed
  qed
  \<comment>\<open>analogous to previous case\<close>
  then show \<open>weak_simulation (\<lambda>p q. R2 q p)\<close> unfolding R1_def R2_def .
next
  fix p q
  assume
    \<open>R1 p q\<close>
    \<open>stable_state p\<close>
  thus \<open>R2 p q\<close>
    unfolding R1_def R2_def 
    using coupled_sim_by_is_coupled_sim coupledsim_stable_state_symm by blast
next \<comment>\<open>analogous\<close>
  fix p q
  assume
    \<open>R2 p q\<close>
    \<open>stable_state q\<close>
  thus \<open>R1 p q\<close>
    unfolding R1_def R2_def 
    using coupled_sim_by_is_coupled_sim coupledsim_stable_state_symm by blast
qed

\<comment>\<open>From @{cite "sangiorgi2012"}, p.~227\<close>
lemma divergence_free_coupledsims_coincidence_2:
  defines 
    \<open>R \<equiv> (\<lambda> p q . p \<sqsubseteq>scs q \<or> (\<exists> q' . q \<longmapsto>* tau q' \<and> p \<equiv>scs q'))\<close>
  assumes
    non_divergent_system: \<open>\<And> p . \<not> divergent_state p\<close>
  shows
    \<open>coupled_simulation R\<close>
  unfolding coupled_simulation_weak_simulation
proof safe
  show \<open>weak_simulation R\<close> 
    unfolding weak_simulation_def
  proof safe
    fix p q p' a
    assume sub_assms:
      \<open>R p q\<close>
      \<open>p \<longmapsto>a  p'\<close>
    thus \<open>\<exists>q'. R p' q' \<and> q \<Rightarrow>^a  q'\<close>
      unfolding R_def
    proof (cases \<open>p \<sqsubseteq>scs q\<close>)
      case True
      then obtain q' where \<open>p' \<sqsubseteq>scs  q'\<close> \<open>q \<Rightarrow>^a  q'\<close>
        using s_coupled_simulation_san12_def sub_assms(2) weak_sim_ruleformat by metis
      thus \<open>\<exists>q'. (p' \<sqsubseteq>scs  q' \<or> (\<exists>q'a. q' \<longmapsto>* tau  q'a \<and> p' \<equiv>scs  q'a)) \<and> q \<Rightarrow>^a  q'\<close>
        by blast
    next
      case False
      then obtain q' where \<open>q \<longmapsto>* tau  q'\<close> \<open>p \<equiv>scs  q'\<close>
          using sub_assms(1) unfolding R_def by blast
      then obtain q'' where \<open>q' \<Rightarrow>^a  q''\<close> \<open>p' \<sqsubseteq>scs  q''\<close> 
        using s_coupled_simulation_san12_def sub_assms(2) weak_sim_ruleformat by metis
      hence \<open>p' \<sqsubseteq>scs  q'' \<and> q \<Rightarrow>^a  q''\<close> using steps_concat `q \<longmapsto>* tau  q'` by blast
      thus \<open>\<exists>q'. (p' \<sqsubseteq>scs  q' \<or> (\<exists>q'a. q' \<longmapsto>* tau  q'a \<and> p' \<equiv>scs  q'a)) \<and> q \<Rightarrow>^a  q'\<close>
        by blast
    qed
  qed
next
  fix p q
  assume
    \<open>R p q\<close>
  thus \<open>\<exists>q'. q \<longmapsto>* tau  q' \<and> R q' p\<close> unfolding R_def
  proof safe
    fix R1 R2
    assume sub_assms:
      \<open>s_coupled_simulation_san12 R1 R2\<close>
      \<open>R1 p q\<close>
    thus \<open>\<exists>q'. q \<longmapsto>* tau  q' \<and> (q' \<sqsubseteq>scs  p \<or> (\<exists>q'a. p \<longmapsto>* tau  q'a \<and> q' \<equiv>scs  q'a))\<close>
    proof -
      \<comment>\<open>dropped a superfluous case distinction from @cite{sangiorgi2012}\<close>
      obtain p' where \<open>stable_state p'\<close> \<open>p \<longmapsto>* tau p'\<close>
        using non_divergent_system non_divergence_implies_eventual_stability by blast
      hence \<open>p \<Rightarrow>^\<tau>  p'\<close> using tau_tau by blast
      then obtain q' where \<open>q \<longmapsto>* tau q'\<close> \<open>p' \<sqsubseteq>scs q'\<close>
        using s_coupled_simulation_san12_def weak_sim_weak_premise sub_assms tau_tau
        by metis
      moreover hence \<open>p' \<equiv>scs q'\<close> using `stable_state p'` s_coupledsim_stable_eq by blast
      ultimately show ?thesis using `p \<longmapsto>* tau p'` s_coupledsim_symm by blast
    qed
  qed (metis s_coupledsim_symm)
qed

text \<open>While this proof follows @{cite "sangiorgi2012"}, we needed to deviate from them by also
  requiring rootedness (shared stability) for the compared states.\<close>
theorem divergence_free_coupledsims_coincidence:
  assumes
    non_divergent_system: \<open>\<And> p . \<not> divergent_state p\<close> and
    stability_rooted: \<open>stable_state p \<longleftrightarrow> stable_state q\<close>
  shows
    \<open>(p \<equiv>cs q) = (p \<equiv>scs q)\<close>
proof rule
  assume \<open>p \<equiv>cs q\<close>
  hence \<open>p \<sqsubseteq>cs q\<close> \<open>q \<sqsubseteq>cs p\<close> by auto
  thus \<open>p \<equiv>scs q\<close>
    using stability_rooted divergence_free_coupledsims_coincidence_1[OF non_divergent_system]
    by blast
next
  assume \<open>p \<equiv>scs q\<close>
  thus \<open>p \<equiv>cs q\<close>
    using stability_rooted divergence_free_coupledsims_coincidence_2[OF non_divergent_system]
      s_coupledsim_eq_parts by blast
qed

end \<comment>\<open>context @{locale lts_tau}\<close>
 
text \<open>The following example shows that a system might be related by s-coupled-simulation without
  being connected by coupled-simulation.\<close>

datatype ex_state = a0 | a1 | a2 | a3 | b0 | b1 | b2 
  
locale ex_lts = lts_tau trans \<tau>
  for trans :: \<open>ex_state \<Rightarrow> nat \<Rightarrow> ex_state \<Rightarrow> bool\<close> ("_ \<longmapsto>_  _" [70, 70, 70] 80) and \<tau> +
  assumes
    sys:
  \<open>trans = (\<lambda> p act q .
     1 = act \<and> (p = a0 \<and> q = a1 
              \<or> p = a0 \<and> q = a2 
              \<or> p = a2 \<and> q = a3 
              \<or> p = b0 \<and> q = b1 
              \<or> p = b1 \<and> q = b2) \<or>
     0 = act \<and> (p = a1 \<and> q = a1))\<close>
   \<open>\<tau> = 0\<close>
begin 
  
lemma no_root_coupled_sim:
  fixes R1 R2
  assumes
    coupled:
      \<open>coupled_simulation_san12 R1 R2\<close> and
    root:
      \<open>R1 a0 b0\<close> \<open>R2 a0 b0\<close>
  shows
    False
proof -
  have
    R1sim: 
      \<open>weak_simulation R1\<close> and
    R1coupling:
      \<open>\<forall>p q. R1 p q \<longrightarrow> (\<exists>q'. q \<longmapsto>* tau  q' \<and> R2 p q')\<close> and
    R2sim: 
      \<open>weak_simulation (\<lambda>p q. R2 q p)\<close>
    using coupled unfolding coupled_simulation_san12_def by auto
  hence R1sim_rf:
      \<open>\<And> p q. R1 p q \<Longrightarrow>
        (\<forall>p' a. p \<longmapsto>a  p' \<longrightarrow>
          (\<exists>q'. R1 p' q' \<and> (\<not> tau a \<longrightarrow> q \<Rightarrow>a  q') \<and>
          (tau a \<longrightarrow> q \<longmapsto>* tau  q')))\<close>
    unfolding weak_simulation_def by blast
  have \<open>a0 \<longmapsto>1 a1\<close> using sys by auto
  hence \<open>\<exists>q'. R1 a1 q' \<and> b0 \<Rightarrow>1 q'\<close>
    using R1sim_rf[OF root(1), rule_format, of 1 a1] tau_def
    by (auto simp add: sys)
  then obtain q' where q': \<open>R1 a1 q'\<close> \<open>b0 \<Rightarrow>1 q'\<close> by blast
  have b0_quasi_stable: \<open>\<forall> q' . b0 \<longmapsto>*tau q' \<longrightarrow> b0 = q'\<close>
    using steps_no_step[of b0 tau] tau_def by (auto simp add: sys)
  have b0_only_b1: \<open>\<forall> q' . b0 \<longmapsto>1 q' \<longrightarrow> q' = b1\<close> by (auto simp add: sys)
  have b1_quasi_stable: \<open>\<forall> q' . b1 \<longmapsto>*tau q' \<longrightarrow> b1 = q'\<close>
    using steps_no_step[of b1 tau] tau_def by (auto simp add: sys)
  have \<open>\<forall> q' . b0 \<Rightarrow>1 q' \<longrightarrow> q' = b1\<close>
    using b0_quasi_stable b0_only_b1 b1_quasi_stable by auto
  hence \<open>q' = b1\<close> using q'(2) by blast
  hence \<open>R1 a1 b1\<close> using q'(1) by simp
  hence \<open>R2 a1 b1\<close>
    using b1_quasi_stable R1coupling by auto
  have b1_b2: \<open>b1 \<longmapsto>1 b2\<close>
    by (auto simp add: sys)
  hence a1_sim: \<open>\<exists> q' . R2 q' b2 \<and> a1 \<Rightarrow>1  q'\<close>
    using `R2 a1 b1` R2sim b1_b2
    unfolding weak_simulation_def tau_def by (auto simp add: sys)
  have a1_quasi_stable: \<open>\<forall> q' . a1 \<longmapsto>*tau q' \<longrightarrow> a1 = q'\<close>
    using steps_loop[of a1] by (auto simp add: sys)
  hence a1_stuck: \<open>\<forall> q' . \<not> a1 \<Rightarrow>1 q'\<close>
    by (auto simp add: sys)
  show ?thesis using a1_sim  a1_stuck by blast
qed

lemma root_s_coupled_sim:
  defines
    \<open>R1 \<equiv> \<lambda> a b .
      a = a0 \<and> b = b0 \<or>
      a = a1 \<and> b = b1 \<or>
      a = a2 \<and> b = b1 \<or>
      a = a3 \<and> b = b2\<close>
  and
    \<open>R2 \<equiv> \<lambda> a b .
      a = a0 \<and> b = b0 \<or>
      a = a2 \<and> b = b1 \<or>
      a = a3 \<and> b = b2\<close>
  shows
    coupled:
      \<open>s_coupled_simulation_san12 R1 R2\<close>
  unfolding s_coupled_simulation_san12_def
proof safe
  show \<open>weak_simulation R1\<close>
    unfolding weak_simulation_def proof (clarify)
    fix p q p' a
    show \<open>R1 p q \<Longrightarrow> p \<longmapsto>a  p' \<Longrightarrow> \<exists>q'. R1 p' q' \<and> (q \<Rightarrow>^a  q')\<close> 
      using step_tau_refl unfolding sys assms tau_def using sys(2) tau_def by (cases p, auto)
  qed
next
  show \<open>weak_simulation (\<lambda>p q. R2 q p)\<close>
    unfolding weak_simulation_def proof (clarify)
    fix p q p' a
    show \<open>R2 q p \<Longrightarrow> p \<longmapsto>a  p' \<Longrightarrow> \<exists>q'. R2 q' p' \<and> (q \<Rightarrow>^a  q')\<close> 
      using steps.refl[of _ tau] tau_def unfolding assms sys
      using sys(2) tau_def by (cases p, auto)
  qed
next
  fix p q
  assume \<open>R1 p q\<close> \<open>stable_state p\<close>
  thus \<open>R2 p q\<close> unfolding assms sys using sys(2) tau_def by auto
next
  fix p q
  assume \<open>R2 p q\<close> \<open>stable_state q\<close>
  thus \<open>R1 p q\<close> unfolding assms sys using tau_def by auto
qed

end \<comment>\<open>@{locale ex_lts}// example lts\<close>

end

