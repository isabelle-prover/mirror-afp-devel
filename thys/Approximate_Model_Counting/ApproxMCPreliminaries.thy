section \<open>Preliminary probability/UHF lemmas\<close>

text \<open> This section proves some simplified/specialized forms of lemmas
  that will be used in the algorithm's analysis later. \<close>

theory ApproxMCPreliminaries imports
  Frequency_Moments.Probability_Ext
  Concentration_Inequalities.Paley_Zygmund_Inequality
begin

lemma card_inter_sum_indicat_real:
  assumes "finite A"
  shows "card (A \<inter> B) = sum (indicat_real B) A"
  by (simp add: assms indicator_def)

(* Counting number of finite maps *)
lemma card_dom_ran:
  assumes "finite D"
  shows "card {w. dom w = D \<and> ran w \<subseteq> R} = card R ^ card D"
  using assms
proof (induct rule: finite_induct)
  case empty
  have "{w::'a \<Rightarrow> 'b option. w = Map.empty \<and> ran w \<subseteq> R} = {Map.empty}"
    by auto
  then show ?case
    by auto
next
  case (insert a A)
  have 1: "inj_on (\<lambda>(w, r). w(a \<mapsto> r))
     ({w. dom w = A \<and> ran w \<subseteq> R} \<times> R)"
    unfolding inj_on_def
    by (smt (verit, del_insts) CollectD SigmaE fun_upd_None_if_notin_dom local.insert(2) map_upd_eqD1 prod.simps(2) restrict_complement_singleton_eq restrict_upd_same)
  have 21: "(\<lambda>(w, r). w(a \<mapsto> r)) `
    ({w. dom w = A \<and> ran w \<subseteq> R} \<times> R) \<subseteq>
    {w. dom w = insert a A \<and> ran w \<subseteq> R}"
    unfolding image_def
    using CollectD local.insert(2) by force

  have "\<And>x. dom x = insert a A \<Longrightarrow>
         ran x \<subseteq> R \<Longrightarrow>
         \<exists>xa. dom xa = A \<and>
              ran xa \<subseteq> R \<and> (\<exists>y\<in>R. x = xa(a \<mapsto> y))"
    by (smt (verit, del_insts) Diff_insert_absorb domD dom_fun_upd fun_upd_triv fun_upd_upd insert.hyps(2) insertCI insert_subset ran_map_upd)
  then have 22: "
    {w. dom w = insert a A \<and> ran w \<subseteq> R} \<subseteq>
    (\<lambda>(w, r). w(a \<mapsto> r)) `
    ({w. dom w = A \<and> ran w \<subseteq> R} \<times> R)"
    by (clarsimp simp add: image_def)

  have "bij_betw (\<lambda>(w,r). w(a\<mapsto>r))
    ({w. dom w = A \<and> ran w \<subseteq> R} \<times> R)
    {w. dom w = insert a A \<and> ran w \<subseteq> R} "
    unfolding bij_betw_def
    using 1 21 22 by clarsimp

  then have "card {w. dom w = insert a A \<and> ran w \<subseteq> R} = card ({w. dom w = A \<and> ran w \<subseteq> R} \<times> R)"
    by (auto simp add: bij_betw_same_card 1 21 22)

  moreover have "... = card R ^ card A * card R"
    by(subst card_cartesian_product) (use insert.hyps(3) in auto)

  ultimately show ?case
    using insert.hyps by (auto simp add: card_insert_if)
qed

lemma finite_set_pmf_expectation_sum:
  fixes f :: "'a \<Rightarrow> 'c \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "finite (set_pmf A)"
  shows "measure_pmf.expectation A (\<lambda>x. sum (f x) T) =
    (\<Sum>i\<in>T. measure_pmf.expectation A (\<lambda>x. f x i))"
  apply (intro Bochner_Integration.integral_sum integrable_measure_pmf_finite)
  using assms by auto

lemma (in prob_space) k_universal_prob_unif:
  assumes "k_universal k H D R"
  assumes "w \<in> D" "\<alpha> \<in> R"
  shows "prob {s \<in> space M. H w s = \<alpha>} = 1 / card R"
proof -
  have "uniform_on (H w) R"
    using assms unfolding k_universal_def
    by auto

  from uniform_onD[OF this]
  have "prob
   {\<omega> \<in> space M.  H w \<omega> \<in> {\<alpha>}} =
    real (card (R \<inter> {\<alpha>})) / real (card R)" .

  thus ?thesis
    using assms by auto
qed

(* For h: D \<rightarrow> R, k-universal, S \<subseteq> D.
   E( | {w \<in> S. h w = \<alpha>} | ) = |S| / |R| *)
lemma k_universal_expectation_eq:
  assumes p: "finite (set_pmf p)"
  assumes ind: "prob_space.k_universal p k H D R"
  assumes S: "finite S" "S \<subseteq> D"
  assumes a: "\<alpha> \<in> R"
  shows
    "prob_space.expectation p
      (\<lambda>s. real (card (S \<inter> {w. H w s = \<alpha>}))) =
    real (card S) / card R"
proof -
  have 1: "prob_space (measure_pmf p)"
    by (simp add: prob_space_measure_pmf)
  have 2: "space (measure_pmf p) = UNIV" by auto
  from prob_space.k_universal_prob_unif[OF 1 ind _ a]
  have *: "\<And>w. w \<in> S \<Longrightarrow>
   prob_space.prob p {s. H w s = \<alpha>} = 1 / real (card R)"
    using S(2) by auto

  have "measure_pmf.expectation p
    (\<lambda>s. real (card (S \<inter> {w. H w s = \<alpha>}))) =
    measure_pmf.expectation p
    (\<lambda>s. sum (indicat_real {w. H w s = \<alpha>}) S)"
    unfolding card_inter_sum_indicat_real[OF S(1)]
    by presburger

  moreover have "... =
    (\<Sum>i\<in>S.
       measure_pmf.expectation p
        (indicat_real {s. H i s = \<alpha>}))"
    apply (subst finite_set_pmf_expectation_sum)
    using assms unfolding indicator_def by auto

  moreover have " ... =
    (\<Sum>i\<in> S.
       measure_pmf.prob p {s. H i s = \<alpha>})"
    by auto

  moreover have "... = (\<Sum>i\<in>S. 1 / card R)"
    using * by auto

  ultimately show ?thesis by auto
qed

lemma (in prob_space) two_universal_indep_var:
  assumes "k_universal 2 H D R"
  assumes "w \<in> D" "w' \<in> D" "w \<noteq> w'"
  shows "indep_var
      borel
      (\<lambda>x. indicat_real {w. H w x = \<alpha>} w)
      borel
      (\<lambda>x. indicat_real {w. H w x = \<alpha>} w')"
proof -
  have Y: "(\<lambda>z. (of_bool (z = \<alpha>))::real) \<in> (count_space UNIV) \<rightarrow>\<^sub>M borel"
    by auto

  have "k_wise_indep_vars  2
     (\<lambda>_. count_space UNIV)
     H D"
    using assms
    unfolding k_universal_def
    by auto

  then have "indep_vars (\<lambda>_. count_space UNIV) H {w, w'}"
    unfolding k_wise_indep_vars_def
    by (metis UNIV_bool assms(2) assms(3) card.empty card.insert card_UNIV_bool card_insert_le empty_iff empty_subsetI finite.emptyI finite.insertI insert_subset order.refl singletonD singleton_insert_inj_eq')

  from indep_var_from_indep_vars[OF assms(4) this]
  have "indep_var
    (count_space UNIV) (H w)
    (count_space UNIV) (H w')" .

  from indep_var_compose[OF this Y Y]
  show ?thesis
    unfolding indicator_def
    by (auto simp add: o_def)
qed

(* For h: D \<rightarrow> R, 2-universal, S \<subseteq> D.
   V( | {w \<in> S. h w = \<alpha>} | ) \<le>  E( | {w \<in> S. h w = \<alpha>} | ) *)
lemma two_universal_variance_bound:
  assumes p: "finite (set_pmf p)"
  assumes ind: "prob_space.k_universal (measure_pmf p) 2 H D R"
  assumes S: "finite S" "S \<subseteq> D"
  assumes a: "\<alpha> \<in> R"
  shows
  "measure_pmf.variance p
    (\<lambda>s. real (card (S \<inter> {w. H w s = \<alpha>}))) \<le>
  measure_pmf.expectation p
    (\<lambda>s. real (card (S \<inter> {w. H w s = \<alpha>})))"
proof -
  have vb: "measure_pmf.variance p
        (\<lambda>x. (indicat_real {w. H w x = \<alpha>} i)) \<le>
    measure_pmf.expectation p
        (\<lambda>x. (indicat_real {w. H w x = \<alpha>} i))" for i
  proof -
    have "measure_pmf.variance p
        (\<lambda>x. (indicat_real {w. H w x = \<alpha>} i)) =
     measure_pmf.expectation p
     (\<lambda>x. (indicat_real {w. H w x = \<alpha>} i)\<^sup>2) -
    (measure_pmf.expectation p
      (\<lambda>x. indicat_real {w. H w x = \<alpha>} i))\<^sup>2"
      apply (subst measure_pmf.variance_eq)
      by (auto simp add: p integrable_measure_pmf_finite)
    moreover have "... \<le> measure_pmf.expectation p
     (\<lambda>x. (indicat_real {w. H w x = \<alpha>} i)\<^sup>2)"
      by simp
    moreover have "... = measure_pmf.expectation p
     (\<lambda>x. (indicat_real {w. H w x = \<alpha>} i))"
      by (metis (mono_tags, lifting) indicator_simps(1) indicator_simps(2) power2_eq_1_iff zero_eq_power2)
    ultimately show ?thesis by linarith
  qed

  have "measure_pmf.variance p
    (\<lambda>s. real (card (S \<inter> {w. H w s = \<alpha>}))) =
    measure_pmf.variance p
    (\<lambda>s. sum (indicat_real {w. H w s = \<alpha>}) S)"
    unfolding card_inter_sum_indicat_real[OF S(1)]
    by presburger

  then have "... = (\<Sum>i\<in>S.
       measure_pmf.variance p
        (\<lambda>x. (indicat_real {w. H w x = \<alpha>} i)))"
    apply (subst measure_pmf.var_sum_pairwise_indep)
    using S prob_space_measure_pmf
    by (auto intro!: prob_space.two_universal_indep_var[OF _ ind] simp add: p integrable_measure_pmf_finite)

  moreover have "... \<le> (\<Sum>i\<in>S.
       measure_pmf.expectation p
        (\<lambda>x. (indicat_real {w. H w x = \<alpha>} i)))"
    by (simp add: sum_mono vb)
  moreover have "... = measure_pmf.expectation p
    (\<lambda>s. sum (indicat_real {w. H w s = \<alpha>}) S)"
    apply (subst finite_set_pmf_expectation_sum)
    using assms by auto
  ultimately show ?thesis
    by (simp add: assms(3) card_inter_sum_indicat_real)
qed

lemma (in prob_space) k_universal_mono:
  assumes "k' \<le> k"
  assumes"k_universal k H D R"
  shows"k_universal k' H D R"
  using assms
  unfolding k_universal_def k_wise_indep_vars_def
  by auto

lemma finite_set_pmf_expectation_add:
  assumes "finite (set_pmf S)"
  shows "measure_pmf.expectation S (\<lambda>x. ((f x)::real) + g x) =
    measure_pmf.expectation S f + measure_pmf.expectation S g"
  by (auto intro: Bochner_Integration.integral_add simp add: assms integrable_measure_pmf_finite)

lemma finite_set_pmf_expectation_add_const:
  assumes "finite (set_pmf S)"
  shows "measure_pmf.expectation S (\<lambda>x. ((f x)::real) + g) =
    measure_pmf.expectation S f + g"
proof -
  have "g = measure_pmf.expectation S (\<lambda>x. g)"
    by simp
  thus ?thesis
    by (simp add: assms finite_set_pmf_expectation_add)
qed

lemma finite_set_pmf_expectation_diff:
  assumes "finite (set_pmf S)"
  shows "measure_pmf.expectation S (\<lambda>x. ((f x)::real) - g x) =
    measure_pmf.expectation S f - measure_pmf.expectation S g"
  by (auto intro: Bochner_Integration.integral_diff simp add: assms integrable_measure_pmf_finite)

(* convenient forms of library inequalities *)
lemma spec_paley_zygmund_inequality:
  assumes fin: "finite (set_pmf p)"
  assumes Zpos: "\<And>z. Z z \<ge> 0"
  assumes t: "\<theta> \<le> 1"
  shows "
    (measure_pmf.variance p Z + (1-\<theta>)^2 * (measure_pmf.expectation p Z)^2) *
    measure_pmf.prob p {z. Z z > \<theta> * measure_pmf.expectation p Z} \<ge>
    (1-\<theta>)^2 * (measure_pmf.expectation p Z)^2"
proof -
  have "prob_space (measure_pmf p)" by (auto simp add: prob_space_measure_pmf)

  from prob_space.paley_zygmund_inequality[OF this _ integrable_measure_pmf_finite[OF fin] t]
  show ?thesis
    using Zpos by auto
qed

lemma spec_chebyshev_inequality:
  assumes fin: "finite (set_pmf p)"
  assumes pvar: "measure_pmf.variance p Y > 0"
  assumes k: "k > 0"
  shows "
    measure_pmf.prob p
    {y. (Y y - measure_pmf.expectation p Y)^2 \<ge>
       k^2 * measure_pmf.variance p Y} \<le> 1 / k^2"
proof -
  define f where
    "f x = Y x / sqrt(measure_pmf.variance p Y)" for x
  have 1:
    "measure_pmf.random_variable p borel f"
    by auto
  have *: "(\<lambda>x. (f x)\<^sup>2) = (\<lambda>x. (Y x)\<^sup>2/ measure_pmf.variance p Y)"
    unfolding f_def
    by (simp add: power_divide)
  have 2:
    "integrable p (\<lambda>x. (f x)\<^sup>2)"
    unfolding *
    by (intro integrable_measure_pmf_finite[OF fin])
  from
    measure_pmf.Chebyshev_inequality[OF 1 2 k]
  have ineq1:"measure_pmf.prob p
   {x . k \<le> \<bar>f x - measure_pmf.expectation p f\<bar>}
    \<le> measure_pmf.expectation p
    (\<lambda>x. (f x - measure_pmf.expectation p f)\<^sup>2) / k\<^sup>2" by auto

  have "(\<lambda>x. (f x - measure_pmf.expectation p f)\<^sup>2) =
    (\<lambda>x. ((Y x - measure_pmf.expectation p Y) / sqrt(measure_pmf.variance p Y))\<^sup>2)"
    unfolding f_def
    by (simp add: diff_divide_distrib)

  moreover have "... =  (\<lambda>x. (Y x - measure_pmf.expectation p Y)^2 / (sqrt(measure_pmf.variance p Y))^2)"
    by (simp add: power_divide)
  moreover have "... =  (\<lambda>x. (Y x - measure_pmf.expectation p Y)^2 / measure_pmf.variance p Y)"
    by simp
  ultimately have unfold:"(\<lambda>x. (f x - measure_pmf.expectation p f)\<^sup>2)
                = (\<lambda>x. (Y x - measure_pmf.expectation p Y)^2 / measure_pmf.variance p Y)"
    by auto
  then have "measure_pmf.expectation p (\<lambda>x. (f x - measure_pmf.expectation p f)\<^sup>2) / k\<^sup>2
    =  measure_pmf.expectation p (\<lambda>x. (Y x - measure_pmf.expectation p Y)^2 / measure_pmf.variance p Y) / k\<^sup>2"
    by auto
  moreover have "... = measure_pmf.variance p Y / measure_pmf.variance p Y / k\<^sup>2"
    by simp
  moreover have "... = 1 / k\<^sup>2"
    using pvar by force
  ultimately have eq1:"measure_pmf.expectation p (\<lambda>x. (f x - measure_pmf.expectation p f)\<^sup>2) / k\<^sup>2 = 1 / k\<^sup>2"
    by auto
  have "(\<lambda>x. k \<le> \<bar>f x - measure_pmf.expectation p f\<bar>) = (\<lambda>x. k\<^sup>2 \<le> (f x - measure_pmf.expectation p f)\<^sup>2)"
    by (metis (no_types, opaque_lifting) abs_of_nonneg k less_le real_le_rsqrt real_sqrt_abs sqrt_ge_absD)
  moreover have "... = (\<lambda>x. k\<^sup>2 \<le> ((Y x - measure_pmf.expectation p Y)^2 / measure_pmf.variance p Y))"
    by (metis unfold)
  moreover have "... = (\<lambda>x. (Y x - measure_pmf.expectation p Y)^2 \<ge> k\<^sup>2 * measure_pmf.variance p Y)"
    by (simp add: pos_le_divide_eq pvar)
  ultimately have cond:"(\<lambda>x. k \<le> \<bar>f x - measure_pmf.expectation p f\<bar>)
                 = (\<lambda>x. (Y x - measure_pmf.expectation p Y)^2 \<ge> k\<^sup>2 * measure_pmf.variance p Y)"
    by auto
  show "?thesis" using ineq1 cond eq1
    by auto
qed

end
