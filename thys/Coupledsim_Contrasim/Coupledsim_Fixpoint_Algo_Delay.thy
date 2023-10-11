section \<open>Fixed Point Algorithm for Coupled Similarity\<close>

subsection \<open>The Algorithm\<close>

theory Coupledsim_Fixpoint_Algo_Delay
imports
  Coupled_Simulation
  "HOL-Library.While_Combinator"
  "HOL-Library.Finite_Lattice"
begin

context lts_tau
begin

definition fp_step :: 
  \<open>'s rel \<Rightarrow> 's rel\<close>
where
  \<open>fp_step R1 \<equiv> { (p,q)\<in>R1.
    (\<forall> p' a. p \<longmapsto>a p' \<longrightarrow>
      (tau a \<longrightarrow> (p',q)\<in>R1) \<and>
      (\<not>tau a \<longrightarrow> (\<exists> q'. ((p',q')\<in>R1) \<and> (q =\<rhd>a q')))) \<and>
    (\<exists> q'. q \<longmapsto>*tau q' \<and> ((q',p)\<in>R1)) }\<close>

definition fp_compute_cs :: \<open>'s rel\<close>
where \<open>fp_compute_cs \<equiv> while (\<lambda>R. fp_step R \<noteq> R) fp_step top\<close>

subsection \<open>Correctness\<close>

lemma mono_fp_step:
  \<open>mono fp_step\<close>
proof (rule, safe)
  fix x y::\<open>'s rel\<close> and p q
  assume
    \<open>x \<subseteq> y\<close>
    \<open>(p, q) \<in> fp_step x\<close>
  thus  \<open>(p, q) \<in> fp_step y\<close>
    unfolding fp_step_def
    by (auto, blast)
qed

lemma fp_fp_step:
  assumes
    \<open>R = fp_step R\<close>
  shows
    \<open>coupled_delay_simulation (\<lambda> p q. (p, q) \<in> R)\<close>
  using assms unfolding fp_step_def coupled_delay_simulation_def delay_simulation_def 
  by (auto, blast, fastforce+)

lemma gfp_fp_step_subset_gcs:
  shows \<open>(gfp fp_step) \<subseteq> { (p,q) . greatest_coupled_simulation p q }\<close>
  unfolding  gcs_eq_coupled_sim_by[symmetric] 
proof clarify
  fix a b
  assume
    \<open>(a, b) \<in> gfp fp_step\<close>
  thus \<open>a \<sqsubseteq>cs  b\<close>
    unfolding coupled_sim_by_eq_coupled_delay_simulation
    using fp_fp_step mono_fp_step gfp_unfold
    by metis
qed

lemma fp_fp_step_gcs:
  assumes
    \<open>R = { (p,q) . greatest_coupled_simulation p q }\<close>
  shows
    \<open>fp_step R = R\<close>
  unfolding assms
proof safe
  fix p q
  assume
    \<open>(p, q) \<in> fp_step {(x, y). greatest_coupled_simulation x y}\<close>
  hence
    \<open>(\<forall>p' a. p \<longmapsto>a  p' \<longrightarrow>
      (tau a \<longrightarrow> greatest_coupled_simulation p' q) \<and>
      (\<not>tau a \<longrightarrow>  (\<exists>q'. greatest_coupled_simulation p' q' \<and> q =\<rhd>a  q'))) \<and>
    (\<exists>q'. q \<longmapsto>* tau  q' \<and> greatest_coupled_simulation q' p)\<close>
    unfolding fp_step_def by auto
  hence \<open>(\<forall>p' a. p \<longmapsto>a  p' \<longrightarrow> (\<exists>q'. greatest_coupled_simulation p' q' \<and> q \<Rightarrow>^a  q')) \<and>
    (\<exists>q'. q \<longmapsto>* tau  q' \<and> greatest_coupled_simulation q' p)\<close>
    unfolding fp_step_def using weak_step_delay_implies_weak_tau steps.refl by blast
  hence \<open>(\<forall>p' a. p \<longmapsto>a  p' \<longrightarrow> (\<exists>q'. greatest_coupled_simulation p' q' \<and> q \<Rightarrow>^^a  q')) \<and>
    (\<exists>q'. q \<longmapsto>* tau  q' \<and> greatest_coupled_simulation q' p)\<close>
    using weak_step_tau2_def by simp
  thus \<open>greatest_coupled_simulation p q\<close>
    using lts_tau.gcs by metis
next
  fix p q
  assume asm:
    \<open>greatest_coupled_simulation p q\<close>
  then have \<open>(p, q) \<in> {(x, y). greatest_coupled_simulation x y}\<close> by blast
  moreover from asm have \<open>\<exists> R. R p q \<and> coupled_delay_simulation R\<close>
    unfolding gcs_eq_coupled_sim_by[symmetric] coupled_sim_by_eq_coupled_delay_simulation.
  then obtain R where \<open>R p q\<close> \<open>coupled_delay_simulation R\<close> by blast
  moreover then have  \<open>\<forall> p' a. p \<longmapsto>a p' \<and> \<not>tau a \<longrightarrow>
      (\<exists> q'. (greatest_coupled_simulation p' q') \<and> (q =\<rhd>a q'))\<close>
    using coupled_delay_simulation_def delay_simulation_def
    by (metis coupled_similarity_implies_gcs coupled_simulation_weak_simulation
        delay_simulation_implies_weak_simulation)
  moreover from asm have  \<open>\<forall> p' a. p \<longmapsto>a p' \<and> tau a \<longrightarrow> greatest_coupled_simulation p' q\<close>
    unfolding  gcs_eq_coupled_sim_by[symmetric] coupled_sim_by_eq_coupled_delay_simulation
    by (metis coupled_delay_simulation_def delay_simulation_def)
  moreover have  \<open>(\<exists> q'. q \<longmapsto>*tau q' \<and> (greatest_coupled_simulation q' p))\<close>
    using asm gcs_is_coupled_simulation coupled_simulation_implies_coupling by blast
  ultimately show \<open>(p, q) \<in> fp_step {(x, y). greatest_coupled_simulation x y}\<close>
    unfolding fp_step_def by blast
qed

lemma gfp_fp_step_gcs: \<open>gfp fp_step = { (p,q) . greatest_coupled_simulation p q }\<close>
  using fp_fp_step_gcs gfp_fp_step_subset_gcs
  by (simp add: equalityI gfp_upperbound)

end

context lts_tau_finite
begin
lemma gfp_fp_step_while:
  shows
    \<open>gfp fp_step = fp_compute_cs\<close>
  unfolding fp_compute_cs_def
  using gfp_while_lattice[OF mono_fp_step] finite_state_rel Finite_Set.finite_set by blast

theorem coupled_sim_fp_step_while:
  shows \<open>fp_compute_cs = { (p,q) . greatest_coupled_simulation p q }\<close>
  using gfp_fp_step_while gfp_fp_step_gcs by blast

end

end
