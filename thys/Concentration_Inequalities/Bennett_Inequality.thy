section \<open>Bennett's Inequality\<close>

text \<open>In this section we verify Bennett's inequality~\cite{bennett1962} and a (weak) version of
Bernstein's inequality as a corollary. Both inequalities give concentration bounds for sums of
independent random variables. The statement and proofs follow a summary paper by
Boucheron et al.~\cite{DBLP:conf/ac/BoucheronLB03}.\<close>

theory Bennett_Inequality
  imports Concentration_Inequalities_Preliminary
begin

context prob_space
begin

(* Restating Chernoff inequality for independent variables *)
lemma indep_vars_Chernoff_ineq_ge:
  assumes I: "finite I"
  assumes ind: "indep_vars (\<lambda> _. borel) X I"
  assumes sge: "s \<ge> 0"
  assumes int: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. exp (s * X i x))"
  shows "prob {x \<in> space M. (\<Sum>i \<in>I. X i x - expectation (X i)) \<ge> t} \<le>
    exp (-s*t) *
    (\<Prod>i\<in>I. expectation (\<lambda>x. exp(s * (X i x - expectation (X i)))))"
proof (cases "s = 0")
  case [simp]: True
  thus ?thesis
    by (simp add: prob_space)
next
  case False
  then have s: "s > 0" using sge by auto

  have [measurable]: "\<And>i. i \<in> I \<Longrightarrow> random_variable borel (X i)"
    using ind unfolding indep_vars_def by blast

  have indep1: "indep_vars (\<lambda>_. borel)
     (\<lambda>i \<omega>. exp (s * (X i \<omega> - expectation (X i)))) I"
    apply (intro indep_vars_compose[OF ind, unfolded o_def])
    by auto

  define S where "S = (\<lambda>x. (\<Sum>i \<in>I. X i x - expectation (X i)))"

  have int1: "\<And>i. i \<in> I \<Longrightarrow>
         integrable M (\<lambda>\<omega>. exp (s * (X i \<omega> - expectation (X i))))"
    by (auto simp add: algebra_simps exp_diff int)

  have eprod: "\<And>x. exp (s * S x) = (\<Prod>i\<in>I. exp(s * (X i x - expectation (X i))))"
     unfolding S_def
     by (simp add: assms(1) exp_sum vector_space_over_itself.scale_sum_right)

  from indep_vars_integrable[OF I indep1 int1]
  have intS: "integrable M (\<lambda>x. exp (s * S x))"
    unfolding eprod by auto

  then have si: "set_integrable M (space M) (\<lambda>x. exp (s * S x))"
    unfolding set_integrable_def
    apply (intro integrable_mult_indicator)
    by auto

  from Chernoff_ineq_ge[OF s si]
  have "prob {x \<in> space M. S x \<ge> t} \<le> exp (- s * t) * (\<integral>x\<in>space M. exp (s * S x)\<partial>M)"
    by auto

  also have "(\<integral>x\<in>space M. exp (s * S x)\<partial>M) = expectation (\<lambda>x. exp(s * S x))"
     unfolding set_integral_space[OF intS] by auto

  also have "... = expectation (\<lambda>x. \<Prod>i\<in>I. exp(s * (X i x - expectation (X i))))"
     unfolding S_def
     by (simp add: assms(1) exp_sum vector_space_over_itself.scale_sum_right)
  also have "... = (\<Prod>i\<in>I. expectation (\<lambda>x. exp(s * (X i x - expectation (X i)))))"
     apply (intro indep_vars_lebesgue_integral[OF I indep1 int1]) .
  finally show ?thesis
    unfolding S_def
    by auto
qed

definition bennett_h::"real \<Rightarrow> real"
  where "bennett_h u = (1 + u) * ln (1 + u) - u"

lemma exp_sub_two_terms_eq:
  fixes x :: real
  shows "exp x - x - 1 = (\<Sum>n. x^(n+2) / fact (n+2))"
    "summable (\<lambda>n. x^(n+2) / fact (n+2))"
proof -
  have "(\<Sum>i<2. inverse (fact i) * x ^ i) = 1 + x"
    by (simp add:numeral_eq_Suc)
  thus "exp x - x - 1 = (\<Sum>n. x^(n+2) / fact (n+2))"
    unfolding exp_def
    apply (subst suminf_split_initial_segment[where k = 2])
    by (auto simp add: summable_exp divide_inverse_commute)
  have "summable (\<lambda>n. x^n / fact n)"
    by (simp add: divide_inverse_commute summable_exp)
  then have "summable (\<lambda>n. x^(Suc (Suc n)) / fact (Suc (Suc n)))"
    apply (subst summable_Suc_iff)
    apply (subst summable_Suc_iff)
    by auto
  thus "summable (\<lambda>n. x^(n+2) / fact (n+2))" by auto
qed

lemma psi_mono:
  defines "f \<equiv> (\<lambda>x. (exp x - x - 1) - x^2 / 2)"
  assumes xy: "a \<le> (b::real)"
  shows "f a \<le> f b"
proof -
  have 1: "(f has_real_derivative (exp x - x - 1)) (at x)" for x
    unfolding f_def
    by (auto intro!: derivative_eq_intros)

  have 2: "\<And>x. x \<in> {a..b} \<Longrightarrow> 0 \<le> exp x - x - 1"
    by (smt (verit) exp_ge_add_one_self)

  from deriv_nonneg_imp_mono[OF 1 2 xy]
  show ?thesis by auto
qed

(* TODO: not sure if this holds for y < 0 too *)
lemma psi_inequality:
  assumes le: "x \<le> (y::real)" "y \<ge> 0"
  shows "y^2 * (exp x - x - 1) \<le> x^2 * (exp y - y - 1)"
proof -

  have x: "exp x - x - 1 = (\<Sum>n. (x^(n+2) / fact (n+2)))"
    "summable (\<lambda>n. x^(n+2) / fact (n+2))"
    using exp_sub_two_terms_eq .

  have y: "exp y - y - 1 = (\<Sum>n. (y^(n+2) / fact (n+2)))"
    "summable (\<lambda>n. y^(n+2) / fact (n+2))"
    using exp_sub_two_terms_eq .

  (* Simplify the expressions in the inequality *)
  have l:"y^2 * (exp x - x - 1) = (\<Sum>n. y^2 * (x^(n+2) / fact (n+2)))"
    using x
    apply (subst suminf_mult)
    by auto
  have ls: "summable (\<lambda>n. y^2 * (x^(n+2) / fact (n+2)))"
    by (intro summable_mult[OF x(2)])

  have r:"x^2 * (exp y - y - 1) = (\<Sum>n. x^2 * (y^(n+2) / fact (n+2)))"
    using y
    apply (subst suminf_mult)
    by auto
  have rs: "summable (\<lambda>n. x^2 * (y^(n+2) / fact (n+2)))"
    by (intro summable_mult[OF y(2)])

  have "\<bar>x\<bar> \<le> \<bar>y\<bar> \<or> \<bar>y\<bar> < \<bar>x\<bar>" by auto
  moreover {
    assume "\<bar>x\<bar> \<le> \<bar>y\<bar>"
    then have "x^ n \<le> y ^n" for n
    by (smt (verit, ccfv_threshold) bot_nat_0.not_eq_extremum le power_0 real_root_less_mono real_root_power_cancel root_abs_power)
    then have "(x^2 * y^2) * x^n \<le> (x^2 * y^2) * y^n" for n
      by (simp add: mult_left_mono)
    then have "y\<^sup>2 * (x ^ (n + 2)) \<le> x\<^sup>2 * (y ^ (n + 2))" for n
      by (metis (full_types) ab_semigroup_mult_class.mult_ac(1) mult.commute power_add)
    then have "y\<^sup>2 * (x ^ (n + 2)) / fact (n+2)\<le> x\<^sup>2 * (y ^ (n + 2)) / fact (n+2)" for n
      by (meson divide_right_mono fact_ge_zero)
    then have "(\<Sum>n. y^2 * (x^(n+2) / fact (n+2))) \<le> (\<Sum>n. x^2 * (y^(n+2) / fact (n+2)))"
      apply (intro suminf_le[OF _ ls rs])
      by auto
    then have "y^2 * (exp x - x - 1) \<le> x^2 * (exp y - y - 1)"
    using l r by presburger
  }
  moreover {
    assume ineq: "\<bar>y\<bar> < \<bar>x\<bar>"

    from psi_mono[OF assms(1)]
    have "(exp x - x - 1) - x^2 /2 \<le> (exp y - y - 1) - y^2/2" .

    then have "y^2 * ((exp x - x - 1) - x^2 /2) \<le> x^2 * ((exp y - y - 1) - y^2/2)"
      by (smt (verit, best) ineq diff_divide_distrib exp_lower_Taylor_quadratic le(1) le(2) mult_nonneg_nonneg one_less_exp_iff power_zero_numeral prob_space.psi_mono prob_space_completion right_diff_distrib zero_le_power2)

    then have "y^2 * (exp x - x - 1) \<le> x^2 * (exp y - y - 1)"
      by (simp add: mult.commute right_diff_distrib)
  }
  ultimately show ?thesis by auto
qed

(* Helper lemma, starting with normalized variables *)
lemma bennett_inequality_1:
  assumes I: "finite I"
  assumes ind: "indep_vars (\<lambda> _. borel) X I"
  assumes intsq: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. (X i x)^2)"
  assumes bnd: "\<And>i. i \<in> I \<Longrightarrow> AE x in M. X i x \<le> 1"
  assumes t: "t \<ge> 0"
  defines "V \<equiv> (\<Sum>i \<in> I. expectation(\<lambda>x. X i x^2))"
  shows "prob {x \<in> space M. (\<Sum>i \<in> I. X i x - expectation (X i)) \<ge> t} \<le>
    exp (-V * bennett_h (t / V))"
proof (cases "V = 0")
  case True
  then show ?thesis
    by auto
next
  case f: False
  have "V \<ge> 0"
    unfolding V_def
    apply (intro sum_nonneg  integral_nonneg_AE)
    by auto
  then have Vpos: "V > 0" using f by auto

  define l :: real where "l = ln(1 + t / V)"
  then have l: "l \<ge> 0"
    using t Vpos by auto
  have rv[measurable]: "\<And>i. i \<in> I \<Longrightarrow> random_variable borel (X i)"
    using ind unfolding indep_vars_def by blast

  define \<psi> where "\<psi> = (\<lambda>x::real. exp(x) - x - 1)"

  have rw: "exp y = 1 + y + \<psi> y" for y
    unfolding \<psi>_def by auto

  have ebnd: "\<And>i. i \<in> I \<Longrightarrow>
         AE x in M. exp (l * X i x) \<le> exp l"
     apply (drule bnd)
     using l by (auto simp add: mult_left_le)

  (* integrability *)
  have int: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. (X i x))"
  using rv intsq square_integrable_imp_integrable by blast

  have intl: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. (l * X i x))"
    using int by blast

  have intexpl: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. exp (l * X i x))"
    apply (intro integrable_const_bound[where B = "exp l"])
    using ebnd by auto

  have intpsi: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. \<psi> (l * X i x))"
    unfolding \<psi>_def
    using intl intexpl by auto

  have **: "\<And>i. i \<in> I \<Longrightarrow>
    expectation (\<lambda>x. \<psi> (l * X i x)) \<le> \<psi> l * expectation (\<lambda>x. (X i x)^2)"
  proof -
    fix i assume i: "i \<in> I"
    then have "AE x in M. l * X i x \<le> l"
      using ebnd by auto
    then have "AE x in M. l^2 * \<psi> (l * X i x) \<le> (l * X i x)^2 * \<psi> l"
      using psi_inequality[OF _ l] unfolding \<psi>_def
      by auto
    then have "AE x in M. l^2 * \<psi> (l * X i x) \<le> l^2 * (\<psi> l * (X i x)^2)"
      by (auto simp add: field_simps)
    then have "AE x in M. \<psi> (l * X i x) \<le> \<psi> l * (X i x)^2 "
      by (smt (verit, best) AE_cong \<psi>_def exp_eq_one_iff mult_cancel_left mult_eq_0_iff mult_left_mono zero_eq_power2 zero_le_power2)
    then have "AE x in M. 0 \<le> \<psi> l * (X i x)^2 - \<psi> (l * X i x) "
      by auto
    then have "expectation (\<lambda>x. \<psi> l * (X i x)^2 + (- \<psi> (l * X i x))) \<ge> 0"
      by (simp add: integral_nonneg_AE)
    also have "expectation (\<lambda>x. \<psi> l * (X i x)^2 + (- \<psi> (l * X i x))) =
        \<psi> l * expectation (\<lambda>x. (X i x)^2) - expectation (\<lambda>x. \<psi> (l * X i x))"
      apply (subst Bochner_Integration.integral_add)
      using intpsi[OF i] intsq[OF i] by auto
    finally show "expectation (\<lambda>x. \<psi> (l * X i x)) \<le> \<psi> l * expectation (\<lambda>x. (X i x)^2)"
      by auto
  qed

  (* Analyzing the expectation *)
  then have *: "\<And>i. i \<in> I \<Longrightarrow>
      expectation (\<lambda>x. exp (l * X i x)) \<le>
      exp (l * expectation (X i)) * exp (\<psi> l * expectation (\<lambda>x. X i x^2))"
  proof -
    fix i
    assume iI: "i \<in> I"
    have "expectation (\<lambda>x. exp (l * X i x)) =
      1 + l * expectation (\<lambda>x. X i x) +
       expectation (\<lambda>x. \<psi> (l * X i x))"
      unfolding rw
      apply (subst Bochner_Integration.integral_add)
      using iI intl intpsi apply auto[2]
      apply (subst Bochner_Integration.integral_add)
      using intl iI prob_space by auto
    also have "... = l * expectation (X i) + 1 + expectation (\<lambda>x. \<psi> (l * X i x))"
      by auto
    also have "... \<le> 1 + l * expectation (X i) + \<psi> l * expectation (\<lambda>x. X i x^2)"
      using **[OF iI] by auto
    also have "... \<le> exp (l * expectation (X i)) * exp (\<psi> l  * expectation (\<lambda>x. X i x^2))"
      by (simp add: is_num_normalize(1) mult_exp_exp)
    finally show "expectation (\<lambda>x. exp (l * X i x)) \<le>
      exp (l * expectation (X i)) * exp (\<psi> l  * expectation (\<lambda>x. X i x^2))" .
  qed

  have "(\<Prod>i\<in>I. expectation (\<lambda>x. exp (l * (X i x)))) \<le>
    (\<Prod>i\<in>I. exp (l * expectation (X i)) * exp (\<psi> l  * expectation (\<lambda>x. X i x^2)))"
    by (auto intro!: prod_mono simp add: *)
  also have "... =
    (\<Prod>i\<in>I. exp (l * expectation (X i))) * (\<Prod>i\<in>I. exp (\<psi> l  * expectation (\<lambda>x. X i x^2)))"
    by (auto simp add: prod.distrib)
  finally have **:
    "(\<Prod>i\<in>I. expectation (\<lambda>x. exp (l * (X i x)))) \<le>
    (\<Prod>i\<in>I. exp (l * expectation (X i))) * exp (\<psi> l * V)"
    by (simp add: V_def I exp_sum sum_distrib_left)

  from indep_vars_Chernoff_ineq_ge[OF I ind l intexpl]
  have "prob {x \<in> space M. (\<Sum>i \<in> I. X i x - expectation (X i)) \<ge> t} \<le>
    exp (- l * t) *
     (\<Prod>i\<in>I. expectation (\<lambda>x. exp (l * (X i x - expectation (X i)))))"
     by auto
  also have "(\<Prod>i\<in>I. expectation (\<lambda>x. exp (l * (X i x - expectation (X i))))) =
    (\<Prod>i\<in>I. expectation (\<lambda>x. exp (l * (X i x))) * exp (- l * expectation (X i)))"
    by (auto intro!: prod.cong simp add: field_simps exp_diff exp_minus_inverse)
  also have "... =
     (\<Prod>i\<in>I. exp (- l * expectation (X i))) * (\<Prod>i\<in>I. expectation (\<lambda>x. exp (l * (X i x))))"
    by (auto simp add: prod.distrib)
  also have "... \<le>
     (\<Prod>i\<in>I. exp (- l * expectation (X i))) * ((\<Prod>i\<in>I. exp (l * expectation (X i))) * exp (\<psi> l * V))"
    apply (intro mult_left_mono[OF **])
    by (meson exp_ge_zero prod_nonneg)
  also have "... = exp (\<psi> l * V)"
    apply (simp add: prod.distrib [symmetric])
    by (smt (verit, ccfv_threshold) exp_minus_inverse prod.not_neutral_contains_not_neutral)
  finally have "
    prob {x \<in> space M. (\<Sum>i \<in> I. X i x - expectation (X i)) \<ge> t} \<le>
    exp (\<psi> l * V - l * t)"
    by (simp add:mult_exp_exp)
  also have "\<psi> l * V - l * t = -V * bennett_h (t / V)"
    unfolding \<psi>_def l_def bennett_h_def
    apply (subst exp_ln)
    subgoal by (smt (verit) Vpos divide_nonneg_nonneg t)
    by (auto simp add: algebra_simps)
  finally show ?thesis .
qed

lemma real_AE_le_sum:
  assumes "\<And>i. i \<in> I \<Longrightarrow> AE x in M. f i x \<le> (g i x::real)"
  shows "AE x in M. (\<Sum>i\<in>I. f i x) \<le> (\<Sum>i\<in>I. g i x)"
proof (cases)
  assume "finite I"
  with AE_finite_allI[OF this assms] have 0:"AE x in M. (\<forall>i\<in>I. f i x \<le> g i x)" by auto
  show ?thesis by (intro eventually_mono[OF 0] sum_mono) auto
qed simp

lemma real_AE_eq_sum:
  assumes "\<And>i. i \<in> I \<Longrightarrow> AE x in M. f i x = (g i x::real)"
  shows "AE x in M. (\<Sum>i\<in>I. f i x) = (\<Sum>i\<in>I. g i x)"
proof -
  have 1: "AE x in M. (\<Sum>i\<in>I. f i x) \<le> (\<Sum>i\<in>I. g i x)"
    apply (intro real_AE_le_sum)
    apply (drule assms)
    by auto
  have 2: "AE x in M. (\<Sum>i\<in>I. g i x) \<le> (\<Sum>i\<in>I. f i x)"
    apply (intro real_AE_le_sum)
    apply (drule assms)
    by auto
  show ?thesis
    using 1 2
    by auto
qed

(* B = 0 case trivial *)
theorem bennett_inequality:
  assumes I: "finite I"
  assumes ind: "indep_vars (\<lambda> _. borel) X I"
  assumes intsq: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. (X i x)^2)"
  assumes bnd: "\<And>i. i \<in> I \<Longrightarrow> AE x in M. X i x \<le> B"
  assumes t: "t \<ge> 0"
  assumes B: "B > 0"
  defines "V \<equiv> (\<Sum>i \<in> I. expectation (\<lambda>x. X i x^2))"
  shows "prob {x \<in> space M. (\<Sum>i \<in> I. X i x - expectation (X i)) \<ge> t} \<le>
    exp (- V / B^2 * bennett_h (t * B / V))"
proof -
  define Y where "Y = (\<lambda>i x. X i x / B)"

  from indep_vars_compose[OF ind, where Y = "\<lambda>i x. x/ B"]
  have 1: "indep_vars (\<lambda>_. borel) Y I"
    unfolding Y_def by (auto simp add: o_def)
  have 2: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. (Y i x)\<^sup>2)"
    unfolding Y_def apply (drule intsq)
    by (auto simp add: field_simps)
  have 3: "\<And>i. i \<in> I \<Longrightarrow> AE x in M. Y i x \<le> 1"
    unfolding Y_def apply (drule bnd)
    using B by auto
  have 4:"0 \<le> t / B" using t B by auto

  have rw1: "(\<Sum>i\<in>I. Y i x - expectation (Y i)) =
    (\<Sum>i\<in>I. X i x - expectation (X i)) / B" for x
    unfolding Y_def
    by (auto simp: diff_divide_distrib sum_divide_distrib)

  have rw2: "expectation (\<lambda>x. (Y i x)\<^sup>2) =
    expectation (\<lambda>x. (X i x)\<^sup>2) / B^2" for i
    unfolding Y_def
    by (simp add: power_divide)

  have rw3:"- (\<Sum>i\<in>I. expectation (\<lambda>x. (X i x)\<^sup>2) / B^2) = - V / B^2"
    unfolding V_def
    by (auto simp add: sum_divide_distrib)

  have "t / B / (\<Sum>i\<in>I. expectation (\<lambda>x. (X i x)\<^sup>2) / B^2) =
    t / B / (V / B^2)"
    unfolding V_def
    by (auto simp add: sum_divide_distrib)
  then have rw4: "t / B / (\<Sum>i\<in>I. expectation (\<lambda>x. (X i x)\<^sup>2) / B^2) =
      t * B / V"
      by (simp add: power2_eq_square)
  have "prob {x \<in> space M. t \<le> (\<Sum>i\<in>I. X i x - expectation (X i))} =
    prob{x \<in> space M. t / B \<le> (\<Sum>i\<in>I. X i x - expectation (X i)) / B}"
    by (smt (verit, best) B Collect_cong divide_cancel_right divide_right_mono)
  also have "... \<le>
    exp (- V / B\<^sup>2 *
          bennett_h (t * B / V))"
    using bennett_inequality_1[OF I 1 2 3 4]
    unfolding rw1 rw2 rw3 rw4 .
  finally show ?thesis .
qed

(* This proof follows https://math.stackexchange.com/a/4066844 *)
lemma bennett_h_bernstein_bound:
  assumes "x \<ge> 0"
  shows "bennett_h x \<ge> x^2 / (2 * (1 + x / 3))"
proof -
  have eq:"x^2 / (2 * (1 + x / 3)) = 3/2 * x - 9/2 * (x / (x+3))"
    using assms
    by (sos "(() & ())")

  define g where "g = (\<lambda>x. bennett_h x - (3/2 * x - 9/2 * (x / (x+3))))"

  define g' where "g' = (\<lambda>x::real.
    ln(1 + x) +  27 / (2 * (x+3)^2) - 3 / 2)"
  define g'' where "g'' = (\<lambda>x::real.
      1 / (1 + x) - 27  / (x+3)^3)"

  have "54 / ((2 * x + 6)^2) = 27 / (2 * (x + 3)\<^sup>2)" (is "?L = ?R") for x :: real
  proof -
    have "?L = 54 / (2^2 * (x + 3)^2)"
      unfolding power_mult_distrib[symmetric] by (simp add:algebra_simps)
    also have "... = ?R" by simp
    finally show ?thesis by simp
  qed

  hence 1: "x \<ge> 0 \<Longrightarrow> (g has_real_derivative (g' x)) (at x)" for x
    unfolding g_def g'_def bennett_h_def by (auto intro!: derivative_eq_intros simp:power2_eq_square)
  have 2: "x \<ge> 0 \<Longrightarrow> (g' has_real_derivative (g'' x)) (at x)" for x
    unfolding g'_def g''_def
    apply (auto intro!: derivative_eq_intros)[1]
    by (sos "(() & ())")

  have gz: "g 0 = 0"
    unfolding g_def bennett_h_def by auto
  have g1z: "g' 0 = 0"
    unfolding g'_def by auto

  have p2: "g'' x  \<ge> 0" if "x \<ge> 0" for x
  proof -
    have "27 * (1+x) \<le> (x+3)^3"
      using that unfolding power3_eq_cube by (auto simp:algebra_simps)
    hence " 27 / (x + 3) ^ 3 \<le> 1 / (1+x)"
      using that by (subst frac_le_eq) (auto intro!:divide_nonpos_pos)
    thus ?thesis unfolding g''_def by simp
  qed

  from deriv_nonneg_imp_mono[OF 2 p2 _]
  have "x \<ge> 0 \<Longrightarrow> g' x \<ge> 0" for x using g1z
    by (metis atLeastAtMost_iff)

  from deriv_nonneg_imp_mono[OF 1 this _]
  have "x \<ge> 0 \<Longrightarrow> g x \<ge> 0" for x using gz
    by (metis atLeastAtMost_iff)

  thus ?thesis
  using assms eq g_def by force
qed

lemma sum_sq_exp_eq_zero_imp_zero:
  assumes "finite I" "i \<in> I"
  assumes intsq: "integrable M (\<lambda>x. (X i x)^2)"
  assumes "(\<Sum>i \<in> I. expectation (\<lambda>x. X i x^2)) = 0"
  shows "AE x in M. X i x = (0::real)"
proof -
  have "(\<forall>i \<in>I. expectation (\<lambda>x. X i x^2) = 0)"
    using assms
    apply (subst sum_nonneg_eq_0_iff[symmetric])
    by auto
  then have "expectation (\<lambda>x. X i x^2) = 0"
    using assms(2) by blast
  thus ?thesis
    using integral_nonneg_eq_0_iff_AE[OF intsq]
    by auto
qed

corollary bernstein_inequality:
  assumes I: "finite I"
  assumes ind: "indep_vars (\<lambda> _. borel) X I"
  assumes intsq: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. (X i x)^2)"
  assumes bnd: "\<And>i. i \<in> I \<Longrightarrow> AE x in M. X i x \<le> B"
  assumes t: "t \<ge> 0"
  assumes B: "B > 0"
  defines "V \<equiv> (\<Sum>i \<in> I. expectation (\<lambda>x. X i x^2))"
  shows "prob {x \<in> space M. (\<Sum>i \<in> I. X i x - expectation (X i)) \<ge> t} \<le>
    exp (- (t^2 / (2 * (V + t * B / 3))))"
proof (cases "V = 0")
  case True
  then have 1:"\<And>i. i \<in> I \<Longrightarrow> AE x in M. X i x = 0"
    unfolding V_def
    using sum_sq_exp_eq_zero_imp_zero
    by (metis I intsq)
  then have 2:"\<And>i. i \<in> I \<Longrightarrow> expectation (X i) = 0"
    using integral_eq_zero_AE by blast

  have "AE x in M. (\<Sum>i \<in> I. X i x - expectation (X i)) = (\<Sum>i \<in> I. 0)"
      apply (intro real_AE_eq_sum)
      using 1 2
      by auto
  then have *: "AE x in M. (\<Sum>i \<in> I. X i x - expectation (X i)) = 0"
    by force

  moreover {
    assume "t > 0"
    then have "prob {x \<in> space M. (\<Sum>i \<in> I. X i x - expectation (X i)) \<ge> t} = 0"
      apply (intro prob_eq_0_AE)
      using * by auto
    then have ?thesis by auto
  }
  ultimately show ?thesis
    apply (cases "t = 0") using t by auto
next
  case f: False
  have "V \<ge> 0"
    unfolding V_def
    apply (intro sum_nonneg  integral_nonneg_AE)
    by auto
  then have V: "V > 0" using f by auto

  have "t * B / V \<ge> 0" using t B V by auto
  from bennett_h_bernstein_bound[OF this]
  have "(t * B / V)\<^sup>2 / (2 * (1 + t * B / V / 3))
    \<le> bennett_h (t * B / V)" .

  then have "(- V / B^2) * bennett_h (t * B / V) \<le>
    (- V / B^2) * ((t * B / V)\<^sup>2 / (2 * (1 + t * B / V / 3)))"
    apply (subst mult_left_mono_neg)
    using B V by auto
  also have "... =
     ((- V / B^2) * (t * B / V)\<^sup>2) / (2 * (1 + t * B / V / 3))"
    by auto
  also have " ((- V / B^2) * (t * B / V)\<^sup>2) = -(t^2) / V"
    using V B by (auto simp add: field_simps power2_eq_square)
  finally have *: "(- V / B^2) * bennett_h (t * B / V) \<le>
     -(t^2)  / (2 * (V + t * B  / 3))"
    using V by (auto simp add: field_simps)

  from bennett_inequality[OF assms(1-6)]
  have "prob {x \<in> space M. (\<Sum>i \<in> I. X i x - expectation (X i)) \<ge> t} \<le>
    exp (- V / B^2 * bennett_h (t * B / V))"
    using V_def by auto
  also have "... \<le> exp (- (t^2/ (2 * (V + t * B  / 3))))"
    using *
    by auto
  finally show ?thesis .
qed

end

end
