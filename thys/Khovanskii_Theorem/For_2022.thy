section\<open>Temporary Preliminaries\<close>

text \<open>Everything here will become redundant in Isabelle 2022\<close>

theory For_2022
  imports
    "HOL-Analysis.Weierstrass_Theorems" \<comment> \<open>needed for polynomial function\<close>
    "HOL-Library.List_Lenlexorder"      \<comment> \<open>lexicographic ordering for the type @{typ \<open>nat list\<close>}\<close>
begin


thm card_UNION
text \<open>The famous inclusion-exclusion formula for the cardinality of a union\<close>
lemma int_card_UNION:
  assumes "finite A"
    and "\<forall>k \<in> A. finite k"
  shows "int (card (\<Union>A)) = (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * int (card (\<Inter>I)))"
    (is "?lhs = ?rhs")
proof -
  have "?rhs = (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * (\<Sum>_\<in>\<Inter>I. 1))"
    by simp
  also have "\<dots> = (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (\<Sum>_\<in>\<Inter>I. (- 1) ^ (card I + 1)))"
    by (subst sum_distrib_left) simp
  also have "\<dots> = (\<Sum>(I, _)\<in>Sigma {I. I \<subseteq> A \<and> I \<noteq> {}} Inter. (- 1) ^ (card I + 1))"
    using assms by (subst sum.Sigma) auto
  also have "\<dots> = (\<Sum>(x, I)\<in>(SIGMA x:UNIV. {I. I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I}). (- 1) ^ (card I + 1))"
    by (rule sum.reindex_cong [where l = "\<lambda>(x, y). (y, x)"]) (auto intro: inj_onI)
  also have "\<dots> = (\<Sum>(x, I)\<in>(SIGMA x:\<Union>A. {I. I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I}). (- 1) ^ (card I + 1))"
    using assms
    by (auto intro!: sum.mono_neutral_cong_right finite_SigmaI2 intro: finite_subset[where B="\<Union>A"])
  also have "\<dots> = (\<Sum>x\<in>\<Union>A. (\<Sum>I|I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I. (- 1) ^ (card I + 1)))"
    using assms by (subst sum.Sigma) auto
  also have "\<dots> = (\<Sum>_\<in>\<Union>A. 1)" (is "sum ?lhs _ = _")
  proof (rule sum.cong[OF refl])
    fix x
    assume x: "x \<in> \<Union>A"
    define K where "K = {X \<in> A. x \<in> X}"
    with \<open>finite A\<close> have K: "finite K"
      by auto
    let ?I = "\<lambda>i. {I. I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I}"
    have "inj_on snd (SIGMA i:{1..card A}. ?I i)"
      using assms by (auto intro!: inj_onI)
    moreover have [symmetric]: "snd ` (SIGMA i:{1..card A}. ?I i) = {I. I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I}"
      using assms
      by (auto intro!: rev_image_eqI[where x="(card a, a)" for a]
          simp add: card_gt_0_iff[folded Suc_le_eq]
          dest: finite_subset intro: card_mono)
    ultimately have "?lhs x = (\<Sum>(i, I)\<in>(SIGMA i:{1..card A}. ?I i). (- 1) ^ (i + 1))"
      by (rule sum.reindex_cong [where l = snd]) fastforce
    also have "\<dots> = (\<Sum>i=1..card A. (\<Sum>I|I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. (- 1) ^ (i + 1)))"
      using assms by (subst sum.Sigma) auto
    also have "\<dots> = (\<Sum>i=1..card A. (- 1) ^ (i + 1) * (\<Sum>I|I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. 1))"
      by (subst sum_distrib_left) simp
    also have "\<dots> = (\<Sum>i=1..card K. (- 1) ^ (i + 1) * (\<Sum>I|I \<subseteq> K \<and> card I = i. 1))"
      (is "_ = ?rhs")
    proof (rule sum.mono_neutral_cong_right[rule_format])
      show "finite {1..card A}"
        by simp
      show "{1..card K} \<subseteq> {1..card A}"
        using \<open>finite A\<close> by (auto simp add: K_def intro: card_mono)
    next
      fix i
      assume "i \<in> {1..card A} - {1..card K}"
      then have i: "i \<le> card A" "card K < i"
        by auto
      have "{I. I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I} = {I. I \<subseteq> K \<and> card I = i}"
        by (auto simp add: K_def)
      also have "\<dots> = {}"
        using \<open>finite A\<close> i by (auto simp add: K_def dest: card_mono[rotated 1])
      finally show "(- 1) ^ (i + 1) * (\<Sum>I | I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. 1 :: int) = 0"
        by (metis mult_zero_right sum.empty)
    next
      fix i
      have "(\<Sum>I | I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. 1) = (\<Sum>I | I \<subseteq> K \<and> card I = i. 1 :: int)"
        (is "?lhs = ?rhs")
        by (rule sum.cong) (auto simp add: K_def)
      then show "(- 1) ^ (i + 1) * ?lhs = (- 1) ^ (i + 1) * ?rhs"
        by simp
    qed
    also have "{I. I \<subseteq> K \<and> card I = 0} = {{}}"
      using assms by (auto simp add: card_eq_0_iff K_def dest: finite_subset)
    then have "?rhs = (\<Sum>i = 0..card K. (- 1) ^ (i + 1) * (\<Sum>I | I \<subseteq> K \<and> card I = i. 1 :: int)) + 1"
      by (subst (2) sum.atLeast_Suc_atMost) simp_all
    also have "\<dots> = (\<Sum>i = 0..card K. (- 1) * ((- 1) ^ i * int (card K choose i))) + 1"
      using K by (subst n_subsets[symmetric]) simp_all
    also have "\<dots> = - (\<Sum>i = 0..card K. (- 1) ^ i * int (card K choose i)) + 1"
      by (subst sum_distrib_left[symmetric]) simp
    also have "\<dots> =  - ((-1 + 1) ^ card K) + 1"
      by (subst binomial_ring) (simp add: ac_simps atMost_atLeast0)
    also have "\<dots> = 1"
      using x K by (auto simp add: K_def card_gt_0_iff)
    finally show "?lhs x = 1" .
  qed
  also have "\<dots> = int (card (\<Union>A))"
    by simp
  finally show ?thesis ..
qed

lemma card_UNION:
  assumes "finite A"
    and "\<forall>k \<in> A. finite k"
  shows "card (\<Union>A) = nat (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * int (card (\<Inter>I)))"
  by (simp only: flip: int_card_UNION [OF assms])

lemma card_UNION_nonneg:
  assumes "finite A"
    and "\<forall>k \<in> A. finite k"
  shows "(\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * int (card (\<Inter>I))) \<ge> 0"
  using int_card_UNION [OF assms] by presburger

lemma real_polynomial_function_divide [intro]:
  assumes "real_polynomial_function p" shows "real_polynomial_function (\<lambda>x. p x / c)"
proof -
  have "real_polynomial_function (\<lambda>x. p x * Fields.inverse c)"
    using assms by auto
  then show ?thesis
    by (simp add: divide_inverse)
qed

lemma real_polynomial_function_prod [intro]:
  "\<lbrakk>finite I; \<And>i. i \<in> I \<Longrightarrow> real_polynomial_function (\<lambda>x. f x i)\<rbrakk> \<Longrightarrow> real_polynomial_function (\<lambda>x. prod (f x) I)"
  by (induct I rule: finite_induct) auto

lemma real_polynomial_function_gchoose:
  obtains p where "real_polynomial_function p" "\<And>x. x gchoose r = p x"
proof
  show "real_polynomial_function (\<lambda>x. (\<Prod>i = 0..<r. x - real i) / fact r)"
    by (force simp add: )
qed (simp add: gbinomial_prod_rev)

lemma sorted_map_plus_iff [simp]:
  fixes a::"'a::linordered_cancel_ab_semigroup_add"
  shows "sorted (map ((+) a) xs) \<longleftrightarrow> sorted xs"
  by (induction xs) auto

lemma distinct_map_plus_iff [simp]:
  fixes a::"'a::linordered_cancel_ab_semigroup_add"
  shows "distinct (map ((+) a) xs) \<longleftrightarrow> distinct xs"
  by (induction xs) auto

subsection \<open>Preliminary type instantiations\<close>

instance list :: (wellorder) wellorder
proof
  show "P a"
    if "\<And>x. (\<And>y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x" for P and a :: "'a list"
    using that unfolding list_less_def
    by (metis wf_lenlex wf_induct wf_lenlex wf)
qed

end
