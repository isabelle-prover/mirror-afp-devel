(*  Title:   Lemmas_S_Finite_Measure_Monad.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

text \<open>For the terminology of s-finite measures/kernels, we refer to the work by Staton~\cite{staton_2017}.
      For the definition of the s-finite measure monad, we refer to the lecture note by Yang~\cite{HongseokLecture2017}.
      The construction of the s-finite measure monad is based on the detailed pencil-and-paper proof by Tetsuya Sato.
      \<close>

section \<open> Lemmas \<close>
theory Lemmas_S_Finite_Measure_Monad
  imports "HOL-Probability.Probability" "Standard_Borel_Spaces.StandardBorel"
begin

lemma integrable_mono_measure:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable_cong,measurable]:"sets M = sets N" "M \<le> N" "integrable N f"
  shows "integrable M f"
  using assms(3) nn_integral_mono_measure[OF assms(1,2),of "\<lambda>x. ennreal (norm (f x))"]
  by(auto simp: integrable_iff_bounded)

lemma AE_mono_measure:
  assumes "sets M = sets N" "M \<le> N" "AE x in N. P x"
  shows "AE x in M. P x"
  by (metis (no_types, lifting) AE_E Collect_cong assms eventually_ae_filter le_measure le_zero_eq null_setsI sets_eq_imp_space_eq)

lemma finite_measure_return:"finite_measure (return M x)"
  by(auto intro!: finite_measureI) (metis ennreal_top_neq_one ennreal_zero_neq_top indicator_eq_0_iff indicator_eq_1_iff)

lemma nn_integral_return':
  assumes "x \<notin> space M"
  shows "(\<integral>\<^sup>+ x. g x \<partial>return M x) = 0"
proof -
  have "emeasure (return M x) A = 0" for A
    by(cases "A \<in> sets M",insert assms) (auto simp: indicator_def emeasure_notin_sets dest: sets.sets_into_space)
  thus ?thesis
    by(auto simp: nn_integral_def simple_integral_def) (meson SUP_least le_zero_eq)
qed

lemma pair_measure_return: "return M l \<Otimes>\<^sub>M return N r = return (M \<Otimes>\<^sub>M N) (l,r)"
proof(safe intro!: measure_eqI)
  fix A
  assume "A \<in> sets (return M l \<Otimes>\<^sub>M return N r)"
  then have A[measurable]:"A \<in> sets (M \<Otimes>\<^sub>M N)" by simp
  note [measurable_cong] = sets_return[of M] sets_return[of N]
  interpret finite_measure "return N r" by(simp add: finite_measure_return)
  consider "l \<notin> space M" | "r \<notin> space N" | "l \<in> space M" "r \<in> space N" by auto
  then show "emeasure (return M l \<Otimes>\<^sub>M return N r) A = emeasure (return (M \<Otimes>\<^sub>M N) (l, r)) A" (is "?lhs = ?rhs")
    by(cases, insert sets.sets_into_space[OF A]) (auto simp: emeasure_pair_measure nn_integral_return' space_pair_measure nn_integral_return, auto simp: indicator_def)
qed simp_all

lemma null_measure_distr: "distr (null_measure M) N f = null_measure N"
  by(auto intro!: measure_eqI simp: distr_def emeasure_sigma)

lemma distr_id':
  assumes "sets N = sets M"
      and "\<And>x. x \<in> space N \<Longrightarrow> f x = x"
    shows "distr N M f = N"
  by(simp add: distr_cong[OF refl refl,of N f id,simplified,OF assms(2),simplified] distr_id2[OF assms(1)[symmetric]] id_def)

lemma measure_density_times:
  assumes [measurable]:"S \<in> sets M" "X \<in> sets M" "r \<noteq> \<infinity>"
  shows "measure (density M (\<lambda>x. indicator S x * r)) X = enn2real r * measure M (S \<inter> X)"
proof -
  have [simp]:"density M (\<lambda>x. indicator S x * r) = density (density M (indicator S)) (\<lambda>_. r)"
    by(simp add: density_density_eq)
  show ?thesis
    by(simp add: measure_density_const[OF _ assms(3)] measure_restricted)
qed

lemma complete_the_square:
  fixes a b c x :: real
  assumes "a \<noteq> 0"
  shows "a*x\<^sup>2 + b * x + c = a * (x + (b / (2*a)))\<^sup>2 - ((b\<^sup>2 - 4* a * c)/(4*a))"
  using assms by(simp add: comm_semiring_1_class.power2_sum power2_eq_square[of "b / (2 * a)"] ring_class.ring_distribs(1) division_ring_class.diff_divide_distrib power2_eq_square[of b])

lemma complete_the_square2':
  fixes a b c x :: real
  assumes "a \<noteq> 0"
  shows "a*x\<^sup>2 - 2 * b * x + c = a * (x - (b / a))\<^sup>2 - ((b\<^sup>2 - a*c)/a)"
  using complete_the_square[OF assms,where b="-2 * b" and x=x and c=c]
  by(simp add: division_ring_class.diff_divide_distrib assms)

lemma normal_density_mu_x_swap:
   "normal_density \<mu> \<sigma> x = normal_density x \<sigma> \<mu>"
  by(simp add: normal_density_def power2_commute)

lemma normal_density_plus_shift: "normal_density \<mu> \<sigma> (x + y) = normal_density (\<mu> - x) \<sigma> y"
  by(simp add: normal_density_def add.commute diff_diff_eq2)

lemma normal_density_times:
  assumes "\<sigma> > 0" "\<sigma>' > 0"
  shows "normal_density \<mu> \<sigma> x * normal_density \<mu>' \<sigma>' x = (1 / sqrt (2 * pi * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))) * exp (- (\<mu> - \<mu>')\<^sup>2 / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))) * normal_density ((\<mu>*\<sigma>'\<^sup>2 + \<mu>'*\<sigma>\<^sup>2)/(\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) x"
        (is "?lhs = ?rhs")
proof -
  have non0: "2*\<sigma>\<^sup>2 \<noteq> 0" "2*\<sigma>'\<^sup>2 \<noteq> 0" "\<sigma>\<^sup>2 + \<sigma>'\<^sup>2 \<noteq> 0"
    using assms by auto
  have "?lhs = exp (- ((x - \<mu>)\<^sup>2 / (2 * \<sigma>\<^sup>2))) * exp (- ((x - \<mu>')\<^sup>2 / (2 * \<sigma>'\<^sup>2))) / (sqrt (2 * pi * \<sigma>\<^sup>2) * sqrt (2 * pi * \<sigma>'\<^sup>2)) "
    by(simp add: normal_density_def)
  also have "... = exp (- ((x - \<mu>)\<^sup>2 / (2 * \<sigma>\<^sup>2)) - ((x - \<mu>')\<^sup>2 / (2 * \<sigma>'\<^sup>2))) / (sqrt (2 * pi * \<sigma>\<^sup>2) * sqrt (2 * pi * \<sigma>'\<^sup>2))"
    by(simp add: exp_add[of "- ((x - \<mu>)\<^sup>2 / (2 * \<sigma>\<^sup>2))" "- ((x - \<mu>')\<^sup>2 / (2 * \<sigma>'\<^sup>2))",simplified add_uminus_conv_diff])
  also have "... = exp (- (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2 / (2 * (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2) - (\<mu> - \<mu>')\<^sup>2 / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)))  / (sqrt (2 * pi * \<sigma>\<^sup>2) * sqrt (2 * pi * \<sigma>'\<^sup>2))"
  proof -
    have "((x - \<mu>)\<^sup>2 / (2 * \<sigma>\<^sup>2)) + ((x - \<mu>')\<^sup>2 / (2 * \<sigma>'\<^sup>2)) = (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2 / (2 * (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2) + (\<mu> - \<mu>')\<^sup>2 / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))"
         (is "?lhs' = ?rhs'")
    proof -
      have "?lhs' = (2 * ((x - \<mu>)\<^sup>2 * \<sigma>'\<^sup>2) + 2 * ((x - \<mu>')\<^sup>2 * \<sigma>\<^sup>2)) / (4 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2))"
        by(simp add: field_class.add_frac_eq[OF non0(1,2)])
      also have "... = ((x - \<mu>)\<^sup>2 * \<sigma>'\<^sup>2 + (x - \<mu>')\<^sup>2 * \<sigma>\<^sup>2) / (2 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2))"
        by(simp add: power2_eq_square division_ring_class.add_divide_distrib)
      also have "... = ((\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * x\<^sup>2 - 2 * (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) * x  + (\<mu>'\<^sup>2 * \<sigma>\<^sup>2 + \<mu>\<^sup>2 * \<sigma>'\<^sup>2)) / (2 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2))"
        by(simp add: comm_ring_1_class.power2_diff ring_class.left_diff_distrib semiring_class.distrib_right)
       also have "... = ((\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2 - ((\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2)\<^sup>2 - (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * (\<mu>'\<^sup>2 * \<sigma>\<^sup>2 + \<mu>\<^sup>2 * \<sigma>'\<^sup>2)) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) / (2 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2))"
        by(simp only: complete_the_square2'[OF non0(3),of x "(\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2)" "(\<mu>'\<^sup>2 * \<sigma>\<^sup>2 + \<mu>\<^sup>2 * \<sigma>'\<^sup>2)"])
      also have "... = ((\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2) / (2 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2)) - (((\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2)\<^sup>2 - (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * (\<mu>'\<^sup>2 * \<sigma>\<^sup>2 + \<mu>\<^sup>2 * \<sigma>'\<^sup>2)) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) / (2 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2))"
        by(simp add: division_ring_class.diff_divide_distrib)
      also have "... = (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2 / (2 * ((\<sigma> * \<sigma>') / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2) - (((\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2)\<^sup>2 - (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * (\<mu>'\<^sup>2 * \<sigma>\<^sup>2 + \<mu>\<^sup>2 * \<sigma>'\<^sup>2)) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) / (2 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2))"
        by(simp add: monoid_mult_class.power2_eq_square[of "(\<sigma> * \<sigma>') / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)"] ab_semigroup_mult_class.mult.commute[of "\<sigma>\<^sup>2 + \<sigma>'\<^sup>2"] )
          (simp add: monoid_mult_class.power2_eq_square[of \<sigma>] monoid_mult_class.power2_eq_square[of \<sigma>'])
      also have "... =  (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2 / (2 * (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2) - ((\<mu> * \<sigma>'\<^sup>2)\<^sup>2 + (\<mu>' * \<sigma>\<^sup>2)\<^sup>2 + 2 * (\<mu> * \<sigma>'\<^sup>2) * (\<mu>' * \<sigma>\<^sup>2) - (\<sigma>\<^sup>2 * (\<mu>'\<^sup>2 * \<sigma>\<^sup>2) + \<sigma>\<^sup>2 * (\<mu>\<^sup>2 * \<sigma>'\<^sup>2) + (\<sigma>'\<^sup>2 * (\<mu>'\<^sup>2 * \<sigma>\<^sup>2) + \<sigma>'\<^sup>2 * (\<mu>\<^sup>2 * \<sigma>'\<^sup>2)))) / ((\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * (2 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2)))"
        by(simp add: comm_semiring_1_class.power2_sum[of "\<mu> * \<sigma>'\<^sup>2" "\<mu>' * \<sigma>\<^sup>2"] semiring_class.distrib_right[of "\<sigma>\<^sup>2" "\<sigma>'\<^sup>2" "\<mu>'\<^sup>2 * \<sigma>\<^sup>2 + \<mu>\<^sup>2 * \<sigma>'\<^sup>2"] )
          (simp add: semiring_class.distrib_left[of _ "\<mu>'\<^sup>2 * \<sigma>\<^sup>2 " "\<mu>\<^sup>2 * \<sigma>'\<^sup>2"])
      also have "... = (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2 / (2 * (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2) + ((\<sigma>\<^sup>2 * \<sigma>'\<^sup>2)*\<mu>\<^sup>2 + (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2)*\<mu>'\<^sup>2 - (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2) * 2 * (\<mu>*\<mu>')) / ((\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * (2 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2)))"
        by(simp add: monoid_mult_class.power2_eq_square division_ring_class.minus_divide_left)
      also have "... = (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2 / (2 * (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2) + (\<mu>\<^sup>2 + \<mu>'\<^sup>2 - 2 * (\<mu>*\<mu>')) / ((\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * 2)"
        using assms by(simp add: division_ring_class.add_divide_distrib division_ring_class.diff_divide_distrib)
      also have "... = ?rhs'"
        by(simp add: comm_ring_1_class.power2_diff ab_semigroup_mult_class.mult.commute[of 2])
      finally show ?thesis .
    qed
    thus ?thesis
      by simp
  qed
  also have "... = (exp (- (\<mu> - \<mu>')\<^sup>2 / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))) / (sqrt (2 * pi * \<sigma>\<^sup>2) * sqrt (2 * pi * \<sigma>'\<^sup>2))) * sqrt (2 * pi * (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2)  * normal_density ((\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) x"
    by(simp add: exp_add[of "- (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2 / (2 * (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2)" "- (\<mu> - \<mu>')\<^sup>2 / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))",simplified] normal_density_def)
  also have "... = ?rhs" 
  proof -
    have "exp (- (\<mu> - \<mu>')\<^sup>2 / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))) / (sqrt (2 * pi * \<sigma>\<^sup>2) * sqrt (2 * pi * \<sigma>'\<^sup>2)) * sqrt (2 * pi * (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2) = 1 / sqrt (2 * pi * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) * exp (- (\<mu> - \<mu>')\<^sup>2 / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)))"
      using assms by(simp add: real_sqrt_mult)
    thus ?thesis
      by simp
  qed
  finally show ?thesis .
qed

lemma KL_normal_density:
  assumes [arith]: "b > 0" "d > 0"
  shows "KL_divergence (exp 1) (density lborel (normal_density a b)) (density lborel (normal_density c d)) = ln (b / d) + (d\<^sup>2 + (c - a)\<^sup>2) / (2 * b\<^sup>2) - 1 / 2" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<integral>x. normal_density c d x * ln (normal_density c d x / normal_density a b x) \<partial>lborel)"
    by(unfold log_ln,rule lborel.KL_density_density) (use order.strict_implies_not_eq[OF normal_density_pos[of b a]] in auto)
  also have "... = (\<integral>x. normal_density c d x * ln (normal_density c d x) -  normal_density c d x * ln (normal_density a b x) \<partial>lborel)"
    by(simp add: ln_div[OF normal_density_pos[OF assms(2)] normal_density_pos[OF assms(1)]] right_diff_distrib)
  also have "... = (\<integral>x. normal_density c d x * ln (exp (- (x - c)\<^sup>2 / (2 * d\<^sup>2)) / sqrt (2 * pi * d\<^sup>2)) -  normal_density c d x * ln (exp (- (x - a)\<^sup>2 / (2 * b\<^sup>2)) / sqrt (2 * pi * b\<^sup>2)) \<partial>lborel)"
    by(simp add: normal_density_def)
  also have "... = (\<integral>x. normal_density c d x * (- (x - c)\<^sup>2 / (2 * d\<^sup>2)  - ln (sqrt (2 * pi * d\<^sup>2))) - (normal_density c d x * (- (x - a)\<^sup>2 / (2 * b\<^sup>2) - ln (sqrt (2 * pi * b\<^sup>2)))) \<partial>lborel)"
    by(simp add: ln_div)
  also have "... = (\<integral>x. normal_density c d x * (ln (sqrt (2 * pi * b\<^sup>2)) - ln (sqrt (2 * pi * d\<^sup>2))) + (normal_density c d x * ((x - a)\<^sup>2 / (2 * b\<^sup>2)) - normal_density c d x * ((x - c)\<^sup>2 / (2 * d\<^sup>2))) \<partial>lborel)"
    by(auto intro!: Bochner_Integration.integral_cong simp: right_diff_distrib)
  also have "... = (\<integral>x. normal_density c d x * (ln (sqrt (2 * pi * b\<^sup>2)) - ln (sqrt (2 * pi * d\<^sup>2))) + (normal_density c d x * ((x - c)\<^sup>2 / (2 * b\<^sup>2) + (2 * x * (c - a) + a^2 - c^2) / (2 * b\<^sup>2)) - normal_density c d x * ((x - c)\<^sup>2 / (2 * d\<^sup>2))) \<partial>lborel)"
    by(auto intro!: Bochner_Integration.integral_cong simp: add_divide_distrib[symmetric] power2_diff) (simp add: right_diff_distrib)
  also have "... = (\<integral>x. (ln (sqrt (2 * pi * b\<^sup>2)) - ln (sqrt (2 * pi * d\<^sup>2))) * normal_density c d x + ((1 / (2 * b\<^sup>2) * (normal_density c d x * (x - c)\<^sup>2) + (2 * (c - a)) / (2 * b\<^sup>2) * (normal_density c d x * x) +  (a^2 - c^2) / (2 * b\<^sup>2) * (normal_density c d x)) - 1 / (2 * d\<^sup>2) * (normal_density c d x * (x - c)\<^sup>2)) \<partial>lborel)"
    by(auto intro!: Bochner_Integration.integral_cong simp: add_divide_distrib[symmetric] ring_distribs)
  also have "... = (\<integral>x. (ln (sqrt (2 * pi * b\<^sup>2)) - ln (sqrt (2 * pi * d\<^sup>2))) * normal_density c d x \<partial>lborel) + (((\<integral>x. 1 / (2 * b\<^sup>2) * (normal_density c d x * (x - c)\<^sup>2) \<partial>lborel) + (\<integral>x. (2 * (c - a)) / (2 * b\<^sup>2) * (normal_density c d x * x) \<partial>lborel) + (\<integral>x. (a^2 - c^2) / (2 * b\<^sup>2) * (normal_density c d x) \<partial>lborel)) - (\<integral>x. 1 / (2 * d\<^sup>2) * (normal_density c d x * (x - c)\<^sup>2) \<partial>lborel))"
    using integrable_normal_moment_nz_1[OF assms(2)] integrable_normal_moment[OF assms(2),where k=2] by simp
  also have "... = ln (sqrt (2 * pi * b\<^sup>2)) - ln (sqrt (2 * pi * d\<^sup>2)) + 1 / (2 * b\<^sup>2) * d\<^sup>2 + (2 * c - 2 * a) / (2 * b\<^sup>2) * c + (a\<^sup>2 - c\<^sup>2) / (2 * b\<^sup>2) - 1 / (2 * d\<^sup>2) * d\<^sup>2"
    by(simp add: integral_normal_moment_even[OF assms(2),of _ 1,simplified] integral_normal_moment_nz_1[OF assms(2)] del: times_divide_eq_left)
  also have "... = ln (b / d) + 1 / (2 * b\<^sup>2) * d\<^sup>2 + (2 * c - 2 * a) / (2 * b\<^sup>2) * c + (a\<^sup>2 - c\<^sup>2) / (2 * b\<^sup>2) - 1 / (2 * d\<^sup>2) * d\<^sup>2"
    by(simp add: ln_sqrt ln_mult power2_eq_square diff_divide_distrib[symmetric] ln_div)
  also have "... = ?rhs"
    by(auto simp: add_divide_distrib[symmetric] power2_diff left_diff_distrib) (simp add: power2_eq_square)
  finally show ?thesis .
qed

lemma count_space_prod:"count_space (UNIV :: ('a :: countable) set) \<Otimes>\<^sub>M count_space (UNIV :: ('b :: countable) set) = count_space UNIV"
  by(auto simp: pair_measure_countable)

lemma measure_pair_pmf:
  fixes p :: "('a :: countable) pmf" and q :: "('b :: countable) pmf"
  shows "measure_pmf p \<Otimes>\<^sub>M measure_pmf q = measure_pmf (pair_pmf p q)" (is "?lhs = ?rhs")
proof -
  interpret pair_prob_space "measure_pmf p" "measure_pmf q"
    by standard
  have "?lhs = measure_pmf p \<bind> (\<lambda>x. measure_pmf q \<bind> (\<lambda>y. return (measure_pmf p \<Otimes>\<^sub>M measure_pmf q) (x, y)))"
    by(rule pair_measure_eq_bind)
  also have "... = ?rhs"
    by(simp add: measure_pmf_bind pair_pmf_def return_pmf.rep_eq  cong: return_cong[OF sets_pair_measure_cong[OF sets_measure_pmf_count_space[of p] sets_measure_pmf_count_space[of q],simplified count_space_prod]])
  finally show ?thesis .
qed

lemma distr_PiM_distr:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> sigma_finite_measure (distr (M i) (N i) (f i))"
      and "\<And>i. i \<in> I \<Longrightarrow> f i \<in> M i \<rightarrow>\<^sub>M N i"
    shows "distr (\<Pi>\<^sub>M i\<in>I. M i) (\<Pi>\<^sub>M i\<in>I. N i) (\<lambda>xi. \<lambda>i\<in>I. f i (xi i)) = (\<Pi>\<^sub>M i\<in>I. distr (M i) (N i) (f i))"
proof -
  define M' where "M' \<equiv> (\<lambda>i. if i \<in> I then M i else null_measure (M i))"
  have f[measurable]: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> M' i \<rightarrow>\<^sub>M N i" and [measurable_cong]: "\<And>i. sets (M' i) = sets (M i)" and [simp]: "\<And>i. i \<in> I \<Longrightarrow> M' i = M i"
    by(auto simp: M'_def assms)
  interpret product_sigma_finite "\<lambda>i. distr (M' i) (N i) (f i)"
    by(auto simp: product_sigma_finite_def M'_def assms(2)) (auto intro!: finite_measure.sigma_finite_measure finite_measureI simp: null_measure_distr)
  interpret ps: product_sigma_finite M'
    by(auto simp: product_sigma_finite_def M'_def intro!: finite_measure.sigma_finite_measure[of "null_measure _"] finite_measureI sigma_finite_measure_distr[OF assms(2)])
  have "distr (\<Pi>\<^sub>M i\<in>I. M i) (\<Pi>\<^sub>M i\<in>I. N i) (\<lambda>xi. \<lambda>i\<in>I. f i (xi i)) = distr (\<Pi>\<^sub>M i\<in>I. M' i) (\<Pi>\<^sub>M i\<in>I. N i) (\<lambda>xi. \<lambda>i\<in>I. f i (xi i))"
    by(simp cong: PiM_cong)
  also have "... = (\<Pi>\<^sub>M i\<in>I. distr (M' i) (N i) (f i))"
  proof(rule PiM_eqI[OF assms(1)])
    fix A
    assume "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (distr (M' i) (N i) (f i))"
    hence h[measurable]:"\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (N i)"
      by simp
    have [simp]:"(\<lambda>xi. \<lambda>i\<in>I. f i (xi i)) -` (Pi\<^sub>E I A) \<inter> space (Pi\<^sub>M I M') = (\<Pi>\<^sub>E i\<in>I. f i -` A i \<inter> space (M' i))"
      by(auto simp: space_PiM)
    show "emeasure (distr (Pi\<^sub>M I M') (Pi\<^sub>M I N) (\<lambda>xi. \<lambda>i\<in>I. f i (xi i))) (Pi\<^sub>E I A) = (\<Prod>i\<in>I. emeasure (distr (M' i) (N i) (f i)) (A i))"
      by(auto simp: emeasure_distr assms(1) ps.emeasure_PiM[OF assms(1)])
  qed(simp_all cong: sets_PiM_cong)
  also have "... = (\<Pi>\<^sub>M i\<in>I. distr (M i) (N i) (f i))"
    by(auto cong: PiM_cong)
  finally show ?thesis .
qed

lemma distr_PiM_distr_prob:
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)"
      and "\<And>i. i \<in> I \<Longrightarrow> f i \<in> M i \<rightarrow>\<^sub>M N i"
    shows "distr (\<Pi>\<^sub>M i\<in>I. M i) (\<Pi>\<^sub>M i\<in>I. N i) (\<lambda>xi. \<lambda>i\<in>I. f i (xi i)) = (\<Pi>\<^sub>M i\<in>I. distr (M i) (N i) (f i))"
proof -
  define M' where "M' \<equiv> (\<lambda>i. if i \<in> I then M i else return (count_space UNIV) undefined)"
  define N' where "N' \<equiv> (\<lambda>i. if i \<in> I then N i else return (count_space UNIV) undefined)"
  interpret p: product_prob_space "\<lambda>i. distr (M' i) (N' i) (f i)"
    by(auto simp: product_prob_space_def product_prob_space_axioms_def product_sigma_finite_def M'_def prob_space_return N'_def assms intro!: prob_space_imp_sigma_finite prob_space.prob_space_distr)
  interpret p': product_prob_space M'
    by(auto simp: product_prob_space_def product_prob_space_axioms_def product_sigma_finite_def M'_def prob_space_return assms intro!: prob_space_imp_sigma_finite)
  have f[measurable]: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> M' i \<rightarrow>\<^sub>M N' i"
    by(auto simp: assms M'_def N'_def)
  have [simp]: "p.emb I = prod_emb I N'"
    by standard (auto simp: prod_emb_def)
  have "distr (\<Pi>\<^sub>M i\<in>I. M i) (\<Pi>\<^sub>M i\<in>I. N i) (\<lambda>xi. \<lambda>i\<in>I. f i (xi i)) = distr (\<Pi>\<^sub>M i\<in>I. M' i) (\<Pi>\<^sub>M i\<in>I. N' i) (\<lambda>xi. \<lambda>i\<in>I. f i (xi i))"
    by(simp add: M'_def N'_def cong: PiM_cong)
  also have "... =  (\<Pi>\<^sub>M i\<in>I. distr (M' i) (N' i) (f i))"
  proof(rule p.PiM_eq)
    fix J F
    assume h[measurable]: "finite J" "J \<subseteq> I" "\<And>j. j \<in> J \<Longrightarrow> F j \<in> p.M.events j"
    then have [measurable]: "\<And>j. j \<in> J \<Longrightarrow> F j \<in> sets (N' j)" by simp
    show " emeasure (distr (Pi\<^sub>M I M') (Pi\<^sub>M I N') (\<lambda>xi. \<lambda>i\<in>I. f i (xi i))) (p.emb I J (Pi\<^sub>E J F)) = (\<Prod>j\<in>J. emeasure (distr (M' j) (N' j) (f j)) (F j))" (is "?lhs = ?rhs")
    proof -
      have "?lhs = emeasure (Pi\<^sub>M I M') ((\<lambda>xi. \<lambda>i\<in>I. f i (xi i)) -` (prod_emb I N' J (Pi\<^sub>E J F)) \<inter> space (Pi\<^sub>M I M'))"
        by(simp add: emeasure_distr h)
      also have "... = emeasure (Pi\<^sub>M I M') (prod_emb I M' J (\<Pi>\<^sub>E i\<in>J. f i -` (F i) \<inter> space (M' i)))"
      proof -
        have [simp]:"(\<lambda>xi. \<lambda>i\<in>I. f i (xi i)) -` (prod_emb I N' J (Pi\<^sub>E J F)) \<inter> space (Pi\<^sub>M I M') = prod_emb I M' J (\<Pi>\<^sub>E i\<in>J. f i -` (F i) \<inter> space (M' i))"
          using measurable_space[OF f] h(1,2,3)
          by(fastforce simp: space_PiM prod_emb_def PiE_def extensional_def Pi_def M'_def N'_def)
        show ?thesis by simp
      qed
      also have "... = (\<Prod>i\<in>J. emeasure (M' i) (f i -` (F i) \<inter> space (M' i)))"
        by(rule p'.emeasure_PiM_emb,insert h(2)) (auto simp: h(1))
      also have "... = ?rhs"
        using h(2) by(auto simp: emeasure_distr intro!: comm_monoid_mult_class.prod.cong)
      finally show ?thesis .
    qed
  qed (simp cong: sets_PiM_cong)
  also have "... = (\<Pi>\<^sub>M i\<in>I. distr (M i) (N i) (f i))"
    by(simp add: M'_def N'_def cong: distr_cong PiM_cong)
  finally show ?thesis .
qed

end