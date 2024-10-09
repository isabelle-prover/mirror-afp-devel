section \<open>\<open>Wlog\<close> – Setting up the command\<close>

theory Wlog
imports Main
keywords "wlog" :: prf_goal % "proof" (* and "goal" :: prf_decl % "proof" *)
  and "generalizing" and "keeping" and "goal"
begin

ML_file "wlog.ML"


text \<open>For symmetric predicates involving 3--5 variables on a linearly ordered type,
  the following lemmas are very useful for wlog-proofs.
  
  For two variables, we already have @{thm [source] linorder_wlog}.\<close>

lemma linorder_wlog_3:
  fixes x y z :: \<open>'a :: linorder\<close>
  assumes \<open>\<And>x y z. P x y z \<Longrightarrow> P y x z \<and> P x z y\<close>
  assumes \<open>\<And>x y z. x \<le> y \<and> y \<le> z \<Longrightarrow> P x y z\<close>
  shows \<open>P x y z\<close>
  using assms 
  by (metis linorder_le_cases)

lemma linorder_wlog_4:
  fixes x y z w :: \<open>'a :: linorder\<close>
  assumes \<open>\<And>x y z w. P x y z w \<Longrightarrow> P y x z w \<and> P x z y w \<and> P x y w z\<close>
  assumes \<open>\<And>x y z w. x \<le> y \<and> y \<le> z \<and> z \<le> w \<Longrightarrow> P x y z w\<close>
  shows \<open>P x y z w\<close>
  using assms 
  by (metis linorder_le_cases)

lemma linorder_wlog_5:
  fixes x y z w v :: \<open>'a :: linorder\<close>
  assumes \<open>\<And>x y z w v. P x y z w v \<Longrightarrow> P y x z w v \<and> P x z y w v \<and> P x y w z v \<and> P x y z v w\<close>
  assumes \<open>\<And>x y z w v. x \<le> y \<and> y \<le> z \<and> z \<le> w \<and> w \<le> v \<Longrightarrow> P x y z w v\<close>
  shows \<open>P x y z w v\<close>
  using assms
  by (smt linorder_le_cases)

end
