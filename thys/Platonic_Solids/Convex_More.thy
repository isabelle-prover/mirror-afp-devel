theory Convex_More
  imports "HOL-Analysis.Starlike"
begin

lemma convex_hull_union_explicit:
  fixes S T :: "'a::euclidean_space set"
  assumes "convex S"
      and "convex T"
    shows "convex hull (S \<union> T) =
            S \<union> T \<union>
            {(1 - u) *\<^sub>R x + u *\<^sub>R y | x y u. x \<in> S \<and> y \<in> T \<and> 0 \<le> u \<and> u \<le> 1}"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix y
    assume "y \<in> convex hull (S \<union> T)"
    then obtain U f where U_facts:
      "finite U" "U \<subseteq> (S \<union> T)" "(\<forall>x\<in>U. 0 \<le> f x)" "sum f U = 1" "(\<Sum>v\<in>U. f v *\<^sub>R v) = y"
      unfolding convex_hull_explicit by auto
    have U_partition: "U = (U \<inter> S) \<union> (U - S)"
      by auto
    have disjoint: "(U \<inter> S) \<inter> (U - S) = {}"
      by auto
    have "finite (U \<inter> S)" "finite (U - S)" 
      using U_facts(1) by auto

    let ?a = "sum f (U \<inter> S)"
    let ?b = "sum f (U - S)"
    have "?a + ?b = 1"
      using sum.union_disjoint[of "U \<inter> S" "U - S" f] U_facts(1,4) U_partition disjoint
      by auto
    have vsum_eq: "y = (\<Sum>v\<in>U \<inter> S. f v *\<^sub>R v) + (\<Sum>v\<in>U - S. f v *\<^sub>R v)"
      using sum.union_disjoint[of "U \<inter> S" "U - S" "\<lambda>v. f v *\<^sub>R v"]
      using U_facts(1,5) U_partition disjoint
      by auto
    have "0 \<le> ?a" "0 \<le> ?b"
      using U_facts(3)
      by (auto intro: sum_nonneg)

    consider
      (a_zero) "?a = 0" |
      (b_zero) "?a \<noteq> 0" "?b = 0" |
      (both_pos) "?a \<noteq> 0" "?b \<noteq> 0"
      by auto
    then show "y \<in> ?rhs"
    proof cases
      case a_zero
      then have zero_on_S: "\<forall>x\<in>U \<inter> S. f x = 0"
        using U_facts(3) sum_nonneg_eq_0_iff[of "U \<inter> S" f]
        by (simp add: \<open>finite (U \<inter> S)\<close>)
      then have "y = (\<Sum>v\<in>U - S. f v *\<^sub>R v)"
        using vsum_eq by simp
      moreover have "sum f (U - S) = 1"
        using \<open>?a + ?b = 1\<close> a_zero
        by simp
      moreover have "U - S \<subseteq> T"
        using U_facts(2) by auto
      moreover have "\<forall>x\<in>U - S. 0 \<le> f x"
        using U_facts(3) by auto
      ultimately have "y \<in> T"
        using assms(2) \<open>finite (U - S)\<close> unfolding convex_explicit
        by blast
      then show ?thesis by auto
    next
      case b_zero
      then have zero_on_T: "\<forall>x\<in>U - S. f x = 0"
        using U_facts(3) sum_nonneg_eq_0_iff[of "U - S" f]
        by (simp add: \<open>finite (U - S)\<close>)
      then have "y = (\<Sum>v\<in>U \<inter> S. f v *\<^sub>R v)"
        using vsum_eq by simp
      moreover have "sum f (U \<inter> S) = 1"
        using \<open>?a + ?b = 1\<close> b_zero
        by simp
      moreover have "U \<inter> S \<subseteq> S"
        by auto
      moreover have "\<forall>x\<in>U \<inter> S. 0 \<le> f x"
        using U_facts(3) by auto
      ultimately have "y \<in> S"
        using assms(1) \<open>finite (U \<inter> S)\<close> unfolding convex_explicit
        by blast
      then show ?thesis by auto
    next
      case both_pos
      then have "0 < ?a" "0 < ?b"
        using \<open>0 \<le> ?a\<close> \<open>0 \<le> ?b\<close> by auto

      let ?x = "\<Sum>v\<in>U \<inter> S. (f v / ?a) *\<^sub>R v"
      let ?y' = "\<Sum>v\<in>U - S. (f v / ?b) *\<^sub>R v"

      have "sum (\<lambda>v. f v / ?a) (U \<inter> S) = 1"
        using \<open>0 < ?a\<close>
        by (metis both_pos(1) div_self sum_divide_distrib)
      moreover have "\<forall>v\<in>U \<inter> S. 0 \<le> f v / ?a"
        using U_facts(3) \<open>0 < ?a\<close> by auto
      ultimately have "?x \<in> S"
        using assms(1) \<open>finite (U \<inter> S)\<close> unfolding convex_explicit
        by simp

      have "sum (\<lambda>v. f v / ?b) (U - S) = 1"
        using \<open>0 < ?b\<close>
        by (metis both_pos(2) div_self sum_divide_distrib)
      moreover have "\<forall>v\<in>U - S. 0 \<le> f v / ?b"
        using U_facts(3) \<open>0 < ?b\<close> by auto
      moreover have "U - S \<subseteq> T"
        using U_facts(2) by auto
      ultimately have "?y' \<in> T"
        using assms(2) \<open>finite (U - S)\<close> unfolding convex_explicit
        by presburger

      have "(\<Sum>v\<in>U \<inter> S. f v *\<^sub>R v) = ?a *\<^sub>R ?x"
        by (smt (verit) both_pos(1) eq_vector_fraction_iff scaleR_right.sum sum.cong)
      moreover have "(\<Sum>v\<in>U - S. f v *\<^sub>R v) = ?b *\<^sub>R ?y'"
        by (smt (verit) both_pos(2) eq_vector_fraction_iff scaleR_right.sum sum.cong)
      ultimately have "y = (1 - ?b) *\<^sub>R ?x + ?b *\<^sub>R ?y'"
        using vsum_eq \<open>?a + ?b = 1\<close> by auto

      moreover have "?b \<le> 1"
        using \<open>0 \<le> ?a\<close> \<open>0 \<le> ?b\<close> \<open>?a + ?b = 1\<close>
        by auto

      ultimately show ?thesis
        using \<open>0 < ?b\<close> \<open>?x \<in> S\<close> \<open>?y' \<in> T\<close> by auto
    qed
  qed
next
  have "S \<union> T \<subseteq> convex hull (S \<union> T)"
    using hull_subset by fast
  then show "?rhs \<subseteq> ?lhs"
    by (smt (verit, ccfv_threshold) assms(1,2) convex_hull_union_two empty_iff le_sup_iff
        mem_Collect_eq subsetI)
qed

lemma convex_hull_union_nonempty_explicit:
  fixes S T :: "'a::euclidean_space set"
  assumes "convex S"
      and "S \<noteq> {}"
      and "convex T"
      and "T \<noteq> {}"
    shows "convex hull (S \<union> T) =
            {(1 - u) *\<^sub>R x + u *\<^sub>R y | x y u. x \<in> S \<and> y \<in> T \<and> 0 \<le> u \<and> u \<le> 1}"
  (is "_ = ?rhs")
proof -
  have "S \<subseteq> ?rhs"
    using assms(4) by fastforce
  moreover have "T \<subseteq> ?rhs"
    by (smt (verit, ccfv_threshold) add_0 assms(2) equals0I mem_Collect_eq scaleR_one scaleR_zero_left subset_iff)
  ultimately show ?thesis
    using convex_hull_union_explicit[OF assms(1,3)]
    by blast
qed

lemma convex_hull_isometry:
  assumes "orthogonal_transformation f"
  shows "(\<lambda>x. c + f x) ` (convex hull S) = convex hull ((\<lambda>x. c + f x) ` S)"
  using orthogonal_transformation_linear[OF assms] convex_hull_linear_image[of f S]
    convex_hull_translation[of c "f ` S"]
  by (metis image_image)

end
