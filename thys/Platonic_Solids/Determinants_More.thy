section\<open>Determinants\<close>

theory Determinants_More
  imports "HOL-Analysis.Starlike"
begin

lemma hyperplane_subset_imp_scaled:
  fixes a :: "'a::euclidean_space"
  assumes "{x. a \<bullet> x = b} \<subseteq> {x. a' \<bullet> x = b'}"
      and "a \<noteq> 0"
      and "a' \<noteq> 0"
  shows "\<exists>c. a' = c *\<^sub>R a \<and> b' = c * b \<and> c \<noteq> 0"
proof -
  let ?c = "(a \<bullet> a') / (a \<bullet> a)"
  let ?v = "a' - ?c *\<^sub>R a"
  have "a \<bullet> ?v = 0"
    by (simp add: inner_diff)
  let ?w = "(b / (a \<bullet> a)) *\<^sub>R a"
  have "a \<bullet> ?w = b"
    using assms(2) by simp
  then have "a' \<bullet> ?w = b'"
    using assms(1) by blast
  have "a \<bullet> (?w + ?v) = b"
    using \<open>a \<bullet> ?w = b\<close> \<open>a \<bullet> ?v = 0\<close>
    by (simp add: inner_add_right)
  then have "a' \<bullet> (?w + ?v) = b'"
    using assms(1) by blast
  then have "a' \<bullet> ?v = 0"
    using \<open>a' \<bullet> ?w = b'\<close>
    by (simp add: inner_add_right)
  have "?v \<bullet> ?v = 0"
    using \<open>a' \<bullet> ?v = 0\<close> \<open>a \<bullet> ?v = 0\<close>
    by (simp add: inner_diff_left)
  then have "?v = 0"
    by simp
  then have "a' = ?c *\<^sub>R a"
    by auto
  moreover have "b' = ?c * b"
    by (metis (mono_tags, lifting) assms(1) Collect_mono_iff \<open>a' = ?c *\<^sub>R a\<close> hyperplane_eq_Ex
        inner_scaleR_left assms(2))
  moreover have "?c \<noteq> 0"
    using \<open>a' = ?c *\<^sub>R a\<close> assms(3) by fastforce
  ultimately show ?thesis
    by blast
qed

lemma subset_hyperplanes:
  fixes a :: "'a::euclidean_space"
  shows "({x. a \<bullet> x = b} \<subseteq> {x. a' \<bullet> x = b'}) =
         ({x. a \<bullet> x = b} = {} \<or> {x. a' \<bullet> x = b'} = UNIV \<or>
          {x. a \<bullet> x = b} = {x. a' \<bullet> x = b'})"
  (is "?lhs = ?rhs")
proof
  assume *: "?lhs"
  consider
    (a_zero) "a = 0" |
    (a'_zero) "a' = 0" |
    (nonzero) "a \<noteq> 0" "a' \<noteq> 0"
    by blast
  then show "?rhs"
  proof (cases)
    case a_zero
    then show ?thesis using * by auto
  next
    case a'_zero
    then show ?thesis using * by force
  next
    case nonzero
    then obtain c where \<open>a' = c *\<^sub>R a\<close> \<open>b' = c * b\<close>
      using * hyperplane_subset_imp_scaled by blast
    then show ?thesis
      by (smt (verit, ccfv_threshold) Collect_cong inner_scaleR_left
          nonzero(2) scaleR_eq_0_iff vector_space_over_itself.scale_left_imp_eq)
  qed
next
  assume "?rhs"
  then show "?lhs" by blast
qed

end
