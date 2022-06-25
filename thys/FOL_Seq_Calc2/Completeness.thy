section \<open>Completeness\<close>

theory Completeness
  imports Countermodel EPathHintikka
begin

text \<open>In this theory, we prove that the prover is complete with regards to the SeCaV proof system
  using the abstract completeness framework.\<close>

text \<open>We start out by specializing the abstract completeness theorem to our prover.
  It is necessary to reproduce the final theorem here so we can alter it to state that our prover
  produces a proof tree instead of simply stating that a proof tree exists.\<close>
theorem epath_prover_completeness:
  fixes A :: \<open>tm list\<close> and z :: \<open>fm list\<close>
  defines \<open>t \<equiv> secavProver (A, z)\<close>
  shows \<open>(fst (root t) = (A, z) \<and> wf t \<and> tfinite t) \<or>
    (\<exists> steps. fst (shd steps) = (A, z) \<and> epath steps \<and> Saturated steps)\<close>
    (is \<open>?A \<or> ?B\<close>)
proof -
  { assume \<open>\<not> ?A\<close>
    with assms have \<open>\<not> tfinite (mkTree rules (A, z))\<close>
      unfolding secavProver_def using wf_mkTree fair_rules by simp
    then obtain steps where \<open>ipath (mkTree rules (A, z)) steps\<close> using Konig by blast
    with assms have \<open>fst (shd steps) = (A, z) \<and> epath steps \<and> Saturated steps\<close>
      by (metis UNIV_I fair_rules ipath.cases ipath_mkTree_Saturated mkTree.simps(1) prod.sel(1)
          wf_ipath_epath wf_mkTree)
    then have ?B by blast
  }
  then show ?thesis by blast
qed

text \<open>This is an abbreviation for validity under our bounded semantics
  (for well-formed interpretations).\<close>
abbreviation
  \<open>uvalid z \<equiv> \<forall>u (e :: nat \<Rightarrow> tm) f g. is_env u e \<longrightarrow> is_fdenot u f \<longrightarrow>
    (\<exists>p \<in> set z. usemantics u e f g p)\<close>

text \<open>The sequent in the first state of a saturated escape path is not valid.
  This follows from our results in the theories EPathHintikka and Countermodel.\<close>
lemma epath_countermodel:
  assumes \<open>fst (shd steps) = (A, z)\<close> and \<open>epath steps\<close> and \<open>Saturated steps\<close>
  shows \<open>\<not> uvalid z\<close>
proof
  assume \<open>uvalid z\<close>
  moreover have \<open>Hintikka (tree_fms steps)\<close> (is \<open>Hintikka ?S\<close>)
    using assms escape_path_Hintikka assms by simp
  moreover have \<open>\<forall>p \<in> set z. p \<in> tree_fms steps\<close>
    using assms shd_sset by (metis Pair_inject prod.collapse pseq_def pseq_in_tree_fms)
  then have \<open>\<exists>g. \<forall>p \<in> set z. \<not> usemantics (terms ?S) (E ?S) (F ?S) g p\<close>
    using calculation(2) Hintikka_counter_model assms by blast
  moreover have \<open>is_env (terms ?S) (E ?S)\<close> \<open>is_fdenot (terms ?S) (F ?S)\<close>
    using is_env_E is_fdenot_F by blast+
  ultimately show False
    by blast
qed

text \<open>Combining the results above, we can prove completeness with regards to our bounded
  semantics: if a sequent is valid under our bounded semantics, the prover will produce a finite,
  well-formed proof tree with the sequent at its root.\<close>
theorem prover_completeness_usemantics:
  fixes A :: \<open>tm list\<close>
  assumes \<open>uvalid z\<close>
  defines \<open>t \<equiv> secavProver (A, z)\<close>
  shows \<open>fst (root t) = (A, z) \<and> wf t \<and> tfinite t\<close>
  using assms epath_prover_completeness epath_countermodel by blast

text \<open>Since our bounded semantics are sound, we can derive our main completeness theorem as
  a corollary: if a sequent is provable in the SeCaV proof system, the prover will produce a finite,
  well-formed proof tree with the sequent at its root.\<close>
corollary prover_completeness_SeCaV:
  fixes A :: \<open>tm list\<close>
  assumes \<open>\<tturnstile> z\<close>
  defines \<open>t \<equiv> secavProver (A, z)\<close>
  shows \<open>fst (root t) = (A, z) \<and> wf t \<and> tfinite t\<close>
proof -
  have \<open>uvalid z\<close>
    using assms sound_usemantics by blast
  then show ?thesis
    using assms prover_completeness_usemantics by blast
qed

end
