section \<open>Results\<close>

theory Results imports Soundness Completeness Sequent_Calculus_Verifier begin

text \<open>In this theory, we collect our soundness and completeness results and prove some extra results
  linking the SeCaV proof system, the usual semantics of SeCaV, and our bounded semantics.\<close>

subsection \<open>Alternate semantics\<close>

text \<open>The existence of a finite, well-formed proof tree with a formula at its root implies that the
  formula is valid under our bounded semantics.\<close>
corollary prover_soundness_usemantics:
  assumes \<open>tfinite t\<close> \<open>wf t\<close> \<open>is_env u e\<close> \<open>is_fdenot u f\<close>
  shows \<open>\<exists>p \<in> set (rootSequent t). usemantics u e f g p\<close>
  using assms prover_soundness_SeCaV sound_usemantics by blast

text \<open>The prover returns a finite, well-formed proof tree if and only if the sequent to be proved is
  valid under our bounded semantics.\<close>
theorem prover_usemantics:
  fixes A :: \<open>tm list\<close> and z :: \<open>fm list\<close>
  defines \<open>t \<equiv> secavProver (A, z)\<close>
  shows \<open>tfinite t \<and> wf t \<longleftrightarrow> uvalid z\<close>
  using assms prover_soundness_usemantics prover_completeness_usemantics
  unfolding secavProver_def by fastforce

text \<open>The prover returns a finite, well-formed proof tree for a single formula if and only if the
  formula is valid under our bounded semantics.\<close>
corollary
  fixes p :: fm
  defines \<open>t \<equiv> secavProver ([], [p])\<close>
  shows \<open>tfinite t \<and> wf t \<longleftrightarrow> uvalid [p]\<close>
  using assms prover_usemantics by simp

subsection \<open>SeCaV\<close>

text \<open>The prover returns a finite, well-formed proof tree if and only if the sequent to be proven is
  provable in the SeCaV proof system.\<close>
theorem prover_SeCaV:
  fixes A :: \<open>tm list\<close> and z :: \<open>fm list\<close>
  defines \<open>t \<equiv> secavProver (A, z)\<close>
  shows \<open>tfinite t \<and> wf t \<longleftrightarrow> (\<tturnstile> z)\<close>
  using assms prover_soundness_SeCaV prover_completeness_SeCaV
  unfolding secavProver_def by fastforce

text \<open>The prover returns a finite, well-formed proof tree if and only if the single formula to be
  proven is provable in the SeCaV proof system.\<close>
corollary
  fixes p :: fm
  defines \<open>t \<equiv> secavProver ([], [p])\<close>
  shows \<open>tfinite t \<and> wf t \<longleftrightarrow> (\<tturnstile> [p])\<close>
  using assms prover_SeCaV by blast

subsection \<open>Semantics\<close>

text \<open>If the prover returns a finite, well-formed proof tree, some formula in the sequent at the
  root of the tree is valid under the usual SeCaV semantics.\<close>
corollary prover_soundness_semantics:
  assumes \<open>tfinite t\<close> \<open>wf t\<close>
  shows \<open>\<exists>p \<in> set (rootSequent t). semantics e f g p\<close>
  using assms prover_soundness_SeCaV sound by blast

text \<open>If the prover returns a finite, well-formed proof tree, the single formula in the sequent at
  the root of the tree is valid under the usual SeCaV semantics.\<close>
corollary
  assumes \<open>tfinite t\<close> \<open>wf t\<close> \<open>snd (fst (root t)) = [p]\<close>
  shows \<open>semantics e f g p\<close>
  using assms prover_soundness_SeCaV complete_sound(2) by metis

text \<open>If a formula is valid under the usual SeCaV semantics, the prover will return a finite,
  well-formed proof tree with the formula at its root when called on it.\<close>
corollary prover_completeness_semantics:
  fixes A :: \<open>tm list\<close>
  assumes \<open>\<forall>(e :: nat \<Rightarrow> nat hterm) f g. semantics e f g p\<close>
  defines \<open>t \<equiv> secavProver (A, [p])\<close>
  shows \<open>fst (root t) = (A, [p]) \<and> wf t \<and> tfinite t\<close>
proof -
  have \<open>\<tturnstile> [p]\<close>
    using assms complete_sound(1) by blast
  then show ?thesis
    using assms prover_completeness_SeCaV by blast
qed

text \<open>The prover produces a finite, well-formed proof tree for a formula if and only if that formula
  is valid under the usual SeCaV semantics.\<close>
theorem prover_semantics:
  fixes A :: \<open>tm list\<close> and p :: fm
  defines \<open>t \<equiv> secavProver (A, [p])\<close>
  shows \<open>tfinite t \<and> wf t \<longleftrightarrow> (\<forall>(e :: nat \<Rightarrow> nat hterm) f g. semantics e f g p)\<close>
  using assms prover_soundness_semantics prover_completeness_semantics
  unfolding secavProver_def by fastforce

text \<open>Validity in the two semantics (in the proper universes) coincide.\<close>
theorem semantics_usemantics:
  \<open>(\<forall>(e :: nat \<Rightarrow> nat hterm) f g. semantics e f g p) \<longleftrightarrow>
   (\<forall>(u :: tm set) e f g. is_env u e \<longrightarrow> is_fdenot u f \<longrightarrow> usemantics u e f g p)\<close>
  using prover_semantics prover_usemantics by simp

end
