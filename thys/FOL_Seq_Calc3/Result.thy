section \<open>Result\<close>

theory Result imports Soundness Completeness begin

theorem prover_soundness_completeness:
  fixes A B :: \<open>fm list\<close>
  defines \<open>t \<equiv> prover (A, B)\<close>
  shows \<open>tfinite t \<and> wf t \<longleftrightarrow> (\<forall>(E :: _ \<Rightarrow> tm) F G. sc (E, F, G) (A, B))\<close>
  using assms prover_soundness prover_completeness unfolding prover_def by fastforce

corollary
  fixes p :: fm
  defines \<open>t \<equiv> prover ([], [p])\<close>
  shows \<open>tfinite t \<and> wf t \<longleftrightarrow> (\<forall>(E :: _ \<Rightarrow> tm) F G. \<lbrakk>E, F, G\<rbrakk> p)\<close>
  using assms prover_soundness_completeness by simp

end
