section \<open>Random XOR hash family\<close>

text \<open>This section defines a hash family based on random XORs and proves
  that this hash family is 3-universal. \<close>

theory RandomXORHashFamily imports
  RandomXOR
begin

lemma finite_dom:
  assumes "finite V"
  shows "finite {w :: 'a \<rightharpoonup> bool. dom w = V}"
proof -
  have *: "{w :: 'a \<rightharpoonup> bool. dom w = V} =
    {w. dom w = V \<and> ran w \<subseteq> {True,False}}"
    by auto
  show ?thesis unfolding *
    apply (intro finite_set_of_finite_maps)
    using assms by auto
qed

lemma xor_hash_eq_dom:
  assumes "xor_hash \<omega> xors = \<alpha>"
  shows "dom xors = dom \<alpha>"
  using assms unfolding xor_hash_def
  by auto

lemma prob_random_xors_xor_hash_indicat_real:
  assumes V: "finite V"
  shows"
  measure_pmf.prob (random_xors V n)
    {xors. xor_hash \<omega> xors = \<alpha>} =
     indicat_real {\<alpha>::nat \<rightharpoonup> bool. dom \<alpha> = {0..<n}} \<alpha> /
     real (card {\<alpha>::nat \<rightharpoonup> bool. dom \<alpha> = {0..<n}})"
proof -
  have *: "{\<alpha>::nat \<rightharpoonup> bool. dom \<alpha> = {0..<n}} =
     {\<alpha>. dom \<alpha> = {0..<n} \<and> ran \<alpha> \<subseteq> {True, False}}"
    by auto
  have **: "card {\<alpha>::nat \<rightharpoonup> bool. dom \<alpha> = {0..<n}} = 2^n"
    unfolding *
    apply (subst card_dom_ran)
    by (auto simp add: numerals(2))
  have "dom \<alpha> = {..<n} \<or> dom \<alpha> \<noteq> {..<n}"
    by auto
  moreover {
    assume "dom \<alpha> = {..<n}"
    from prob_random_xors_xor_hash[OF V this]
    have ?thesis
      unfolding **
      by (simp add: \<open>dom \<alpha> = {..<n}\<close> atLeast0LessThan)
  }
  moreover {
    assume *:"dom \<alpha> \<noteq> {..<n}"
    then have "x \<in> set_pmf (random_xors V n) \<Longrightarrow>
         \<alpha> \<noteq> xor_hash \<omega> x" for x
      by (metis (mono_tags, lifting) V mem_Collect_eq random_xors_set_pmf xor_hash_eq_dom)
    then have "measure_pmf.prob (random_xors V n)
     {xors. xor_hash \<omega> xors = \<alpha>} = 0"
      apply (intro measure_pmf.measure_exclude[where A = "set_pmf ((random_xors V n))"])
      by (auto simp add: Sigma_Algebra.measure_def emeasure_pmf xor_hash_eq_dom)
    then have ?thesis
      by (simp add: * atLeast0LessThan)
  }
  ultimately show ?thesis
    by auto
qed

lemma xor_hash_family_uniform:
  assumes V: "finite V"
  assumes "dom \<omega> = V"
  shows "prob_space.uniform_on
         (random_xors V n)
         (xor_hash i) {\<alpha>. dom \<alpha> = {0..<n}}"
  apply (intro measure_pmf.uniform_onI[where p = "random_xors V n"])
  subgoal by clarsimp
  subgoal  using finite_dom by blast
  using prob_random_xors_xor_hash_indicat_real[OF V]
  by (auto intro!: exI[where x = "(\<lambda>i. if i < n then Some True else None)"] split:if_splits)

lemma random_xors_xor_hash_pair_indicat:
  assumes V: "finite V"
  assumes \<omega>: "dom \<omega> = V"
  assumes \<omega>': "dom \<omega>' = V"
  assumes neq: "\<omega> \<noteq> \<omega>'"
  shows "
  measure_pmf.prob (random_xors V n)
    {xors.
      xor_hash \<omega> xors = \<alpha> \<and> xor_hash \<omega>' xors = \<alpha>'} =
  (measure_pmf.prob (random_xors V n)
    {xors.
      xor_hash \<omega> xors = \<alpha>} *
   measure_pmf.prob (random_xors V n)
    {xors.
      xor_hash \<omega>' xors = \<alpha>'})"
proof -
  have "dom \<alpha> = {..<n} \<and> dom \<alpha>' = {..<n} \<or>
    \<not>(dom \<alpha> = {..<n} \<and> dom \<alpha>' = {..<n})" by auto
  moreover {
    assume *: "dom \<alpha> = {..<n}" "dom \<alpha>' = {..<n}"
    have "measure_pmf.prob (random_xors V n)
     {xors.
      xor_hash \<omega> xors = \<alpha> \<and> xor_hash \<omega>' xors = \<alpha>'} = 1 / 4 ^n"
      by (simp add: "*"(1) "*"(2) assms(1) assms(2) assms(3) assms(4) random_xors_xor_hash_pair)
    moreover have "
    measure_pmf.prob (random_xors V n)
      {xors.  xor_hash \<omega> xors = \<alpha>} = 1/2^n"
      by (simp add: "*"(1) assms(1) prob_random_xors_xor_hash)
    moreover have "
    measure_pmf.prob (random_xors V n)
      {xors.  xor_hash \<omega>' xors = \<alpha>'} = 1/2^n"
      by (simp add: "*"(2) assms(1) prob_random_xors_xor_hash)
    ultimately have ?thesis
      by (metis (full_types) Groups.mult_ac(2) four_x_squared power2_eq_square power_mult power_one_over verit_prod_simplify(2))
  }
  moreover {
    assume *: "dom \<alpha> \<noteq> {..<n} \<or> dom \<alpha>' \<noteq> {..<n}"
    then have **: "x \<in> set_pmf (random_xors V n) \<Longrightarrow>
         \<alpha> = xor_hash \<omega> x \<Longrightarrow>
         \<alpha>' = xor_hash \<omega>' x \<Longrightarrow> False" for x
      by (metis (mono_tags, lifting) CollectD assms(1) random_xors_set_pmf xor_hash_eq_dom)
    have "measure_pmf.prob (random_xors V n)
    {xors.
      xor_hash \<omega> xors = \<alpha>} = 0 \<or>
     measure_pmf.prob (random_xors V n)
      {xors.
        xor_hash \<omega>' xors = \<alpha>'} = 0"
      unfolding prob_random_xors_xor_hash_indicat_real[OF V]
      by (metis (full_types) * atLeast0LessThan div_0 indicator_simps(2) mem_Collect_eq)
    moreover have "
    measure_pmf.prob (random_xors V n)
    {xors.
      xor_hash \<omega> xors = \<alpha> \<and> xor_hash \<omega>' xors = \<alpha>'} = 0"
      apply (intro measure_pmf.measure_exclude[where A = "set_pmf ((random_xors V n))"])
      using ** by (auto simp add: Sigma_Algebra.measure_def emeasure_pmf)
    ultimately have ?thesis by auto
  }
  ultimately show ?thesis by auto
qed

lemma prod_3_expand:
  assumes "a \<noteq> b" "b \<noteq> c" "c \<noteq> a"
  shows"(\<Prod>\<omega>\<in>{a, b, c}. f \<omega>) = f a * (f b * f c)"
  using assms by auto

lemma random_xors_xor_hash_three_indicat:
  assumes V: "finite V"
  assumes \<omega>: "dom \<omega> = V"
  assumes \<omega>': "dom \<omega>' = V"
  assumes \<omega>'': "dom \<omega>'' = V"
  assumes neq: "\<omega> \<noteq> \<omega>'" "\<omega>' \<noteq> \<omega>''" "\<omega>'' \<noteq> \<omega>"
  shows "
  measure_pmf.prob (random_xors V n)
    {xors.
      xor_hash \<omega> xors = \<alpha>
    \<and> xor_hash \<omega>' xors = \<alpha>'
    \<and> xor_hash \<omega>'' xors = \<alpha>''} =
  (measure_pmf.prob (random_xors V n)
    {xors.
      xor_hash \<omega> xors = \<alpha>} *
   measure_pmf.prob (random_xors V n)
    {xors.
      xor_hash \<omega>' xors = \<alpha>'} *
   measure_pmf.prob (random_xors V n)
    {xors.
      xor_hash \<omega>'' xors = \<alpha>''})"
proof -
  have "dom \<alpha> = {..<n} \<and> dom \<alpha>' = {..<n} \<and> dom \<alpha>'' = {..<n} \<or>
    \<not>(dom \<alpha> = {..<n} \<and> dom \<alpha>' = {..<n} \<and> dom \<alpha>'' = {..<n})" by auto
  moreover {
    assume *: "dom \<alpha> = {..<n}" "dom \<alpha>' = {..<n}" "dom \<alpha>'' = {..<n}"
    have 1:"measure_pmf.prob (random_xors V n)
     {xors.
      xor_hash \<omega> xors = \<alpha> \<and>
      xor_hash \<omega>' xors = \<alpha>' \<and>
      xor_hash \<omega>'' xors = \<alpha>''} = 1 / 8 ^n"
      apply (intro random_xors_xor_hash_three)
      using V * \<omega> \<omega>' \<omega>'' neq by auto
    have 2:"
    measure_pmf.prob (random_xors V n)
      {xors.  xor_hash \<omega> xors = \<alpha>} = 1/2^n"
      by (simp add: "*"(1) assms(1) prob_random_xors_xor_hash)
    have 3:"
    measure_pmf.prob (random_xors V n)
      {xors.  xor_hash \<omega>' xors = \<alpha>'} = 1/2^n"
      by (simp add: "*"(2) assms(1) prob_random_xors_xor_hash)
    have 4: "
    measure_pmf.prob (random_xors V n)
      {xors.  xor_hash \<omega>'' xors = \<alpha>''} = 1/2^n"
      by (simp add: "*"(3) assms(1) prob_random_xors_xor_hash)
    have ?thesis
      unfolding 1 2 3 4
      by (metis (mono_tags, opaque_lifting) arith_simps(11) arith_simps(12) arith_simps(58) divide_divide_eq_left mult.right_neutral power_mult_distrib times_divide_eq_right)
  }
  moreover {
    assume *: "dom \<alpha> \<noteq> {..<n} \<or> dom \<alpha>' \<noteq> {..<n} \<or> dom \<alpha>'' \<noteq> {..<n}"
    then have **: "x \<in> set_pmf (random_xors V n) \<Longrightarrow>
         \<alpha> = xor_hash \<omega> x \<Longrightarrow>
         \<alpha>' = xor_hash \<omega>' x \<Longrightarrow>
         \<alpha>'' = xor_hash \<omega>'' x \<Longrightarrow> False" for x
      by (metis (mono_tags, lifting) CollectD assms(1) random_xors_set_pmf xor_hash_eq_dom)
    have "measure_pmf.prob (random_xors V n)
    {xors.
      xor_hash \<omega> xors = \<alpha>} = 0 \<or>
     measure_pmf.prob (random_xors V n)
      {xors.
        xor_hash \<omega>' xors = \<alpha>'} = 0 \<or>
     measure_pmf.prob (random_xors V n)
      {xors.
        xor_hash \<omega>'' xors = \<alpha>''} = 0"
      unfolding prob_random_xors_xor_hash_indicat_real[OF V]
      by (metis (full_types) * atLeast0LessThan div_0 indicator_simps(2) mem_Collect_eq)
    moreover have "
    measure_pmf.prob (random_xors V n)
    {xors.
      xor_hash \<omega> xors = \<alpha> \<and> xor_hash \<omega>' xors = \<alpha>' \<and> xor_hash \<omega>'' xors = \<alpha>''} = 0"
      apply (intro measure_pmf.measure_exclude[where A = "set_pmf ((random_xors V n))"])
      using ** by (auto simp add: Sigma_Algebra.measure_def emeasure_pmf)
    ultimately have ?thesis by auto
  }
  ultimately show ?thesis
    by fastforce
qed

lemma xor_hash_3_indep:
  assumes V: "finite V"
  assumes J: "card J \<le> 3" "J \<subseteq> {\<alpha>. dom \<alpha> = V}"
  shows "
    measure_pmf.prob (random_xors V n)
      {xors. \<forall>\<omega>\<in>J. xor_hash \<omega> xors = f \<omega>} =
       (\<Prod>\<omega>\<in>J.
          measure_pmf.prob (random_xors V n)
           {xors. xor_hash \<omega> xors = f \<omega>})"
proof -
  have "card J = 0 \<or> card J = 1 \<or> card J = 2 \<or> card J = 3"
    using assms by auto
  moreover {
    assume" card J = 0"
    then have "J = {}"
      by (meson assms(1) assms(3) card_eq_0_iff finite_dom finite_subset)
    then have ?thesis
      by clarsimp
  }
  moreover {
    assume "card J = 1"
    then obtain x where "J = {x}"
      using card_1_singletonE by blast
    then have ?thesis
      by auto
  }
  moreover {
    assume "card J = 2"
    then obtain \<omega> \<omega>' where J:"J = {\<omega>, \<omega>'}" and
      \<omega>: "\<omega> \<noteq> \<omega>'" "dom \<omega> = V" "dom \<omega>' = V"
      unfolding card_2_iff
      using J
      by force
    have ?thesis unfolding J
      by (auto simp add: random_xors_xor_hash_pair_indicat V \<omega>)
  }
  moreover {
    assume "card J = 3"
    then obtain \<omega> \<omega>' \<omega>'' where J:"J = {\<omega>, \<omega>', \<omega>''}" and
      \<omega>: "\<omega> \<noteq> \<omega>'" "\<omega>' \<noteq> \<omega>''" "\<omega>'' \<noteq> \<omega>"
        "dom \<omega> = V" "dom \<omega>' = V" "dom \<omega>'' = V"
      unfolding card_3_iff
      using J
      by force
    have ?thesis unfolding J
      by (auto simp add: random_xors_xor_hash_three_indicat V \<omega>  prod_3_expand[OF \<omega>(1-3)])
  }
  ultimately show ?thesis by auto
qed

lemma xor_hash_3_wise_indep:
  assumes "finite V"
  shows "prob_space.k_wise_indep_vars
     (random_xors V n) 3
     (\<lambda>_. Universal_Hash_Families_More_Independent_Families.discrete) xor_hash
     {\<alpha>. dom \<alpha> = V}"
  apply (subst prob_space.k_wise_indep_vars_def)
  by (auto intro!: measure_pmf.indep_vars_pmf xor_hash_3_indep simp add: measure_pmf.prob_space_axioms assms card_mono dual_order.trans)

theorem xor_hash_family_3_universal:
  assumes "finite V"
  shows"prob_space.k_universal
    (random_xors V n) 3 xor_hash
    {\<alpha>::'a \<rightharpoonup> bool. dom \<alpha> = V}
    {\<alpha>::nat \<rightharpoonup> bool. dom \<alpha> = {0..<n}}"
  apply (subst prob_space.k_universal_def)
  subgoal by (clarsimp simp add: measure_pmf.prob_space_axioms )
  using xor_hash_3_wise_indep assms xor_hash_family_uniform assms by blast

corollary xor_hash_family_2_universal:
  assumes "finite V"
  shows"prob_space.k_universal
    (random_xors V n) 2 xor_hash
    {\<alpha>::'a \<rightharpoonup> bool. dom \<alpha> = V}
    {\<alpha>::nat \<rightharpoonup> bool. dom \<alpha> = {0..<n}}"
  using assms
  by (auto intro!: prob_space.k_universal_mono[OF _ _ xor_hash_family_3_universal] measure_pmf.prob_space_axioms)

end
