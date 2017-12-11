(*
    File:      Zeta_Function.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>The Hurwitz and Riemann $\zeta$ functions\<close>
theory Zeta_Function
imports
  "Euler_MacLaurin.Euler_MacLaurin"
  "Bernoulli.Bernoulli_Zeta"
  "Dirichlet_Series.Dirichlet_Series_Analysis"
begin

subsection \<open>Preliminary facts\<close>

(* TODO Move? *)
lemma powr_add_minus_powr_asymptotics:
  fixes a z :: complex 
  shows "((\<lambda>z. ((1 + z) powr a - 1) / z) \<longlongrightarrow> a) (at 0)"
proof (rule Lim_transform_eventually)
  have "eventually (\<lambda>z::complex. z \<in> ball 0 1 - {0}) (at 0)"
    using eventually_at_ball'[of 1 "0::complex" UNIV] by (simp add: dist_norm)
  thus "eventually (\<lambda>z. (\<Sum>n. (a gchoose (Suc n)) * z ^ n) = ((1 + z) powr a - 1) / z) (at 0)"
  proof eventually_elim
    case (elim z)
    hence "(\<lambda>n. (a gchoose n) * z ^ n) sums (1 + z) powr a"
      by (intro gen_binomial_complex) auto
    hence "(\<lambda>n. (a gchoose (Suc n)) * z ^ (Suc n)) sums ((1 + z) powr a - 1)"
      by (subst sums_Suc_iff) simp_all
    also have "(\<lambda>n. (a gchoose (Suc n)) * z ^ (Suc n)) = (\<lambda>n. z * ((a gchoose (Suc n)) * z ^ n))"
      by (simp add: algebra_simps)
    finally have "(\<lambda>n. (a gchoose (Suc n)) * z ^ n) sums (((1 + z) powr a - 1) / z)"
      by (rule sums_mult_D) (use elim in auto)
    thus ?case by (simp add: sums_iff)
  qed
next
  have "conv_radius (\<lambda>n. a gchoose (n + 1)) = conv_radius (\<lambda>n. a gchoose n)"
    using conv_radius_shift[of "\<lambda>n. a gchoose n" 1] by simp
  hence "continuous_on (cball 0 (1/2)) (\<lambda>z. \<Sum>n. (a gchoose (Suc n)) * (z - 0) ^ n)"
    using conv_radius_gchoose[of a] by (intro powser_continuous_suminf) (simp_all)
  hence "isCont (\<lambda>z. \<Sum>n. (a gchoose (Suc n)) * z ^ n) 0"
    by (auto intro: continuous_on_interior)
  thus "(\<lambda>z. \<Sum>n. (a gchoose Suc n) * z ^ n) \<midarrow>0\<rightarrow> a"
    by (auto simp: isCont_def)
qed

lemma complex_powr_add_minus_powr_asymptotics:
  fixes s :: complex
  assumes a: "a > 0" and s: "Re s < 1"
  shows "filterlim (\<lambda>x. of_real (x + a) powr s - of_real x powr s) (nhds 0) at_top"
proof (rule Lim_transform_eventually)
  show "eventually (\<lambda>x. ((1 + of_real (a / x)) powr s - 1) / of_real (a / x) * 
                            of_real x powr (s - 1) * a = 
                          of_real (x + a) powr s - of_real x powr s) at_top"
    (is "eventually (\<lambda>x. ?f x / ?g x * ?h x * _ = _) _") using eventually_gt_at_top[of a]
  proof eventually_elim
    case (elim x)
    have "?f x / ?g x * ?h x * a = ?f x * (a * ?h x / ?g x)" by simp
    also have "a * ?h x / ?g x = of_real x powr s"
      using elim a by (simp add: powr_diff)
    also have "?f x * \<dots> = of_real (x + a) powr s - of_real x powr s"
      using a elim by (simp add: algebra_simps powr_times_real [symmetric])
    finally show ?case .
  qed

  have "filterlim (\<lambda>x. complex_of_real (a / x)) (nhds (complex_of_real 0)) at_top"
    by (intro tendsto_of_real real_tendsto_divide_at_top[OF tendsto_const] filterlim_ident)
  hence "filterlim (\<lambda>x. complex_of_real (a / x)) (at 0) at_top"
    using a by (intro filterlim_atI) auto
  hence "((\<lambda>x. ?f x / ?g x * ?h x * a) \<longlongrightarrow> s * 0 * a) at_top" using s
    by (intro tendsto_mult filterlim_compose[OF powr_add_minus_powr_asymptotics]
              tendsto_const tendsto_neg_powr_complex_of_real filterlim_ident) auto
  thus "((\<lambda>x. ?f x / ?g x * ?h x * a) \<longlongrightarrow> 0) at_top" by simp
qed
(* END TODO *)

lemma summable_zeta:
  assumes "Re s > 1"
  shows   "summable (\<lambda>n. of_nat (Suc n) powr -s)"
proof -
  have "summable (\<lambda>n. exp (complex_of_real (ln (real (Suc n))) * - s))" (is "summable ?f")
    by (subst summable_Suc_iff, rule summable_complex_powr_iff) (use assms in auto)
  also have "?f = (\<lambda>n. of_nat (Suc n) powr -s)"
    by (simp add: powr_def algebra_simps del: of_nat_Suc)
  finally show ?thesis .
qed

lemma summable_zeta_real:
  assumes "x > 1"
  shows   "summable (\<lambda>n. real (Suc n) powr -x)"
proof -
  have "summable (\<lambda>n. of_nat (Suc n) powr -complex_of_real x)"
    using assms by (intro summable_zeta) simp_all
  also have "(\<lambda>n. of_nat (Suc n) powr -complex_of_real x) = (\<lambda>n. of_real (real (Suc n) powr -x))"
    by (subst powr_Reals_eq) simp_all
  finally show ?thesis
    by (subst (asm) summable_complex_of_real)
qed

lemma summable_hurwitz_zeta:
  assumes "Re s > 1" "a > 0"
  shows   "summable (\<lambda>n. (of_nat n + of_real a) powr -s)"
proof -
  have "summable (\<lambda>n. (of_nat (Suc n) + of_real a) powr -s)"
  proof (rule summable_comparison_test' [OF summable_zeta_real [OF assms(1)]] )
    fix n :: nat
    have "norm ((of_nat (Suc n) + of_real a) powr -s) = (real (Suc n) + a) powr - Re s"
      (is "?N = _") using assms by (simp add: norm_powr_real_powr)
    also have "\<dots> \<le> real (Suc n) powr -Re s"
      using assms by (intro powr_mono2') auto
    finally show "?N \<le> \<dots>" .
  qed
  thus ?thesis by (subst (asm) summable_Suc_iff)
qed

lemma summable_hurwitz_zeta_real:
  assumes "x > 1" "a > 0"
  shows   "summable (\<lambda>n. (real n + a) powr -x)"
proof -
  have "summable (\<lambda>n. (of_nat n + of_real a) powr -complex_of_real x)"
    using assms by (intro summable_hurwitz_zeta) simp_all
  also have "(\<lambda>n. (of_nat n + of_real a) powr -complex_of_real x) = 
               (\<lambda>n. of_real ((real n + a) powr -x))"
    using assms by (subst powr_Reals_eq) simp_all
  finally show ?thesis
    by (subst (asm) summable_complex_of_real)
qed



subsection \<open>Definitions\<close>

text \<open>
  We use the Euler--MacLaurin summation formula to express $\zeta(s,a) - \frac{a^{1-s}}{s-1}$ as
  a polynomial plus some remainder term, which is an integral over a function of 
  order $O(-1-2n-\mathfrak{R}(s))$. It is then clear that this integral converges uniformly
  to an analytic function in $s$ for all $s$ with $\mathfrak{R}(s) > -2n$.
\<close>
definition pre_zeta_aux :: "nat \<Rightarrow> real \<Rightarrow> complex \<Rightarrow> complex" where
  "pre_zeta_aux N a s = a powr - s / 2 +
    (\<Sum>i=1..N. (bernoulli (2 * i) / fact (2 * i)) *\<^sub>R (pochhammer s (2*i - 1) * 
                 of_real a powr (- s - of_nat (2*i - 1)))) +
    EM_remainder (Suc (2*N)) 
      (\<lambda>x. -(pochhammer s (Suc (2*N)) * of_real (x + a) powr (- 1 - 2*N - s))) 0"

text \<open>
  By iterating the above construction long enough, we can extend this to the entire
  complex plane.
\<close>
definition pre_zeta :: "real \<Rightarrow> complex \<Rightarrow> complex" where
  "pre_zeta a s = pre_zeta_aux (nat (1 - \<lceil>Re s / 2\<rceil>)) a s"

text \<open>
  We can then obtain the Hurwitz $\zeta$ function by adding back the pole at 1.
  Note that it is not necessary to trust that this somewhat complicated definition is,
  in fact, the correct one, since we will later show that this Hurwitz zeta function
  fulfils
  \[\zeta(s,a) = \sum_{n=0}^\infty \frac{1}{(n + a)^s}\]
  and is analytic on $\mathbb{C}\setminus \{1\}$, which uniquely defines the function
  due to analytic continuation. It is therefore obvious that any alternative definition
  that is analytic on $\mathbb{C}\setminus \{1\}$ and satisfies the above equation 
  must be equal to our Hurwitz $\zeta$ function.
\<close>
definition hurwitz_zeta :: "real \<Rightarrow> complex \<Rightarrow> complex" where
  "hurwitz_zeta a s = (if s = 1 then 0 else pre_zeta a s + of_real a powr (1 - s) / (s - 1))"

text \<open>
  The Riemann $\zeta$ function is simply the Hurwitz $\zeta$ function with $a = 1$.
\<close>
definition zeta :: "complex \<Rightarrow> complex" where
  "zeta = hurwitz_zeta 1"


text \<open>
  We define the $\zeta$ functions as 0 at their poles. To avoid confusion, these facts
  are not added as simplification rules by default.
\<close>
lemma hurwitz_zeta_1: "hurwitz_zeta c 1 = 0"
  by (simp add: hurwitz_zeta_def)

lemma zeta_1: "zeta 1 = 0"
  by (simp add: zeta_def hurwitz_zeta_1)


context
begin

private lemma holomorphic_pre_zeta_aux':
  assumes "a > 0" "bounded U" "open U" "U \<subseteq> {s. Re s > \<sigma>}" and \<sigma>: "\<sigma> > - 2 * real n"
  shows   "pre_zeta_aux n a holomorphic_on U" unfolding pre_zeta_aux_def
proof (intro holomorphic_intros)
  define C :: real where "C = max 0 (Sup ((\<lambda>s. norm (pochhammer s (Suc (2 * n)))) ` closure U))"
  have "compact (closure U)" 
    using assms by (auto simp: compact_eq_bounded_closed)
  hence "compact ((\<lambda>s. norm (pochhammer s (Suc (2 * n)))) ` closure U)"
    by (rule compact_continuous_image [rotated]) (auto intro!: continuous_intros)
  hence "bounded ((\<lambda>s. norm (pochhammer s (Suc (2 * n)))) ` closure U)"
    by (simp add: compact_eq_bounded_closed)
  hence C: "cmod (pochhammer s (Suc (2 * n))) \<le> C" if "s \<in> U" for s
    using that closure_subset[of U] unfolding C_def 
    by (intro max.coboundedI2 cSup_upper bounded_imp_bdd_above) (auto simp: image_iff)
  have C' [simp]: "C \<ge> 0" by (simp add: C_def)

  let ?g = "\<lambda>(x::real). C * (x + a) powr (- 1 - 2 * of_nat n - \<sigma>)"
  let ?G = "\<lambda>(x::real). C / (- 2 * of_nat n - \<sigma>) * (x + a) powr (- 2 * of_nat n - \<sigma>)"  
  define poch' where "poch' = deriv (\<lambda>z::complex. pochhammer z (Suc (2 * n)))"
  have [derivative_intros]:
    "((\<lambda>z. pochhammer z (Suc (2 * n))) has_field_derivative poch' z) (at z within A)" 
    for z :: complex and A unfolding poch'_def
    by (rule holomorphic_derivI [OF holomorphic_pochhammer [of _ UNIV]]) auto
  have A: "continuous_on A poch'" for A unfolding poch'_def 
    by (rule continuous_on_subset[OF _ subset_UNIV], 
        intro holomorphic_on_imp_continuous_on holomorphic_deriv)
        (auto intro: holomorphic_pochhammer) 
  note [continuous_intros] = continuous_on_compose2[OF this _ subset_UNIV]

  define f' where "f' = (\<lambda>z t. - (poch' z * complex_of_real (t + a) powr (- 1 - 2 * of_nat n - z) -
                          Ln (complex_of_real (t + a)) * complex_of_real (t + a) powr 
                            (- 1 - 2 * of_nat n - z) * pochhammer z (Suc (2 * n))))"

  show "(\<lambda>z. EM_remainder (Suc (2 * n)) (\<lambda>x. - (pochhammer z (Suc (2 * n)) *
                  complex_of_real (x + a) powr (- 1 - 2 * of_nat n - z))) 0) holomorphic_on
    U" unfolding pre_zeta_aux_def
  proof (rule holomorphic_EM_remainder[of _ ?G ?g _ _ f'], goal_cases)
    case (1 x)
    show ?case
      by (insert 1 \<sigma> \<open>a > 0\<close>, rule derivative_eq_intros refl | simp)+
         (auto simp: field_simps powr_diff powr_add powr_minus)
  next
    case (2 z t x)
    note [derivative_intros] = has_field_derivative_powr_right [THEN DERIV_chain2]
    show ?case
      by (insert 2 \<sigma> \<open>a > 0\<close>, (rule derivative_eq_intros refl | (simp add: add_eq_0_iff; fail))+)
         (simp add: f'_def)
  next
    case 3
    hence *: "complex_of_real x + complex_of_real a \<notin> \<real>\<^sub>\<le>\<^sub>0" if "x \<ge> 0" for x
      using nonpos_Reals_of_real_iff[of "x+a", unfolded of_real_add] that \<open>a > 0\<close> by auto
    show ?case using \<open>a > 0\<close> and * unfolding f'_def
      by (auto simp: case_prod_unfold add_eq_0_iff intro!: continuous_intros)
  next
    case (4 b c z e)
    have "- 2 * real n < \<sigma>" by (fact \<sigma>)
    also from 4 assms have "\<sigma> < Re z" by auto
    finally show ?case using assms 4
      by (intro integrable_continuous_real continuous_intros) (auto simp: add_eq_0_iff)
  next
    case (5 t x s)
    thus ?case using \<open>a > 0\<close>
      by (intro integrable_EM_remainder') (auto intro!: continuous_intros simp: add_eq_0_iff)
  next
    case 6
    from \<sigma> have "(\<lambda>y. C / (-2 * real n - \<sigma>) * (a + y) powr (-2 * real n - \<sigma>)) \<longlonglongrightarrow> 0"
      by (intro tendsto_mult_right_zero tendsto_neg_powr
            filterlim_real_sequentially filterlim_tendsto_add_at_top [OF tendsto_const]) auto
    thus ?case unfolding convergent_def by (auto simp: add_ac)
  next
    case 7
    show ?case 
    proof (intro eventually_mono [OF eventually_ge_at_top[of 1]] ballI)
      fix x :: real and s :: complex assume x: "x \<ge> 1" and s: "s \<in> U"
      have "norm (- (pochhammer s (Suc (2 * n)) * of_real (x + a) powr (- 1 - 2 * of_nat n - s))) =
              norm (pochhammer s (Suc (2 * n))) * (x + a) powr (-1 - 2 * of_nat n - Re s)"
        (is "?N = _") using 7 \<open>a > 0\<close> x by (simp add: norm_mult norm_powr_real_powr)
      also have "\<dots> \<le> ?g x"
        using 7 assms x s \<open>a > 0\<close> by (intro mult_mono C powr_mono) auto
      finally show "?N \<le> ?g x" .
    qed
  qed (insert assms, auto)
qed (insert assms, auto)

lemma analytic_pre_zeta_aux:
  assumes "a > 0"
  shows   "pre_zeta_aux n a analytic_on {s. Re s > - 2 * real n}"
  unfolding analytic_on_def
proof
  fix s assume s: "s \<in> {s. Re s > - 2 * real n}"
  define \<sigma> where "\<sigma> = (Re s - 2 * real n) / 2"
  with s have \<sigma>: "\<sigma> > - 2 * real n" 
    by (simp add: \<sigma>_def field_simps)
  from s have s': "s \<in> {s. Re s > \<sigma>}"
    by (auto simp: \<sigma>_def field_simps)

  have "open {s. Re s > \<sigma>}"
    by (rule open_halfspace_Re_gt)
  with s' obtain \<epsilon> where "\<epsilon> > 0" "ball s \<epsilon> \<subseteq> {s. Re s > \<sigma>}"
    unfolding open_contains_ball by blast
  with \<sigma> have "pre_zeta_aux n a holomorphic_on ball s \<epsilon>"
    by (intro holomorphic_pre_zeta_aux' [OF assms, of _ \<sigma>]) auto
  with \<open>\<epsilon> > 0\<close> show "\<exists>e>0. pre_zeta_aux n a holomorphic_on ball s e"
    by blast
qed
end

context
  fixes s :: complex and N :: nat and \<zeta> :: "complex \<Rightarrow> complex" and a :: real
  assumes s: "Re s > 1" and a: "a > 0"
  defines "\<zeta> \<equiv> (\<lambda>s. \<Sum>n. (of_nat n + of_real a) powr -s)"
begin

interpretation \<zeta>: euler_maclaurin_nat'
  "\<lambda>x. of_real (x + a) powr (1 - s) / (1 - s)" "\<lambda>x. of_real (x + a) powr -s" 
  "\<lambda>n x. (-1) ^ n * pochhammer s n * of_real (x + a) powr -(s + n)" 
  0 N "\<zeta> s" "{}"
proof (standard, goal_cases)
  case 2
  show ?case by (simp add: powr_minus field_simps)
next
  case (3 k)
  have "complex_of_real x + complex_of_real a = 0 \<longleftrightarrow> x = -a" for x
    by (simp only: of_real_add [symmetric] of_real_eq_0_iff add_eq_0_iff2)
  with a s show ?case
    by (intro continuous_intros) (auto simp: add_nonneg_nonneg)
next
  case (4 k x)
  with a have "0 < x + a" by simp
  hence *: "complex_of_real x + complex_of_real a \<notin> \<real>\<^sub>\<le>\<^sub>0"
    using nonpos_Reals_of_real_iff[of "x+a", unfolded of_real_add] by auto
  have **: "pochhammer z (Suc n) = - pochhammer z n * (-z - of_nat n :: complex)" for z n
    by (simp add: pochhammer_rec' field_simps)
  show "((\<lambda>x. (- 1) ^ k * pochhammer s k * of_real (x + a) powr - (s + of_nat k)) 
          has_vector_derivative (- 1) ^ Suc k * pochhammer s (Suc k) *
            of_real (x + a) powr - (s + of_nat (Suc k))) (at x)"
    by (insert 4 *, (rule has_vector_derivative_real_field derivative_eq_intros refl | simp)+)
       (auto simp: divide_simps powr_add powr_diff powr_minus **)
next
  case 5
  with s a show ?case 
    by (auto intro!: continuous_intros simp: minus_equation_iff add_eq_0_iff)
next
  case (6 x)
  with a have "0 < x + a" by simp
  hence *: "complex_of_real x + complex_of_real a \<notin> \<real>\<^sub>\<le>\<^sub>0"
    using nonpos_Reals_of_real_iff[of "x+a", unfolded of_real_add] by auto
  show ?case unfolding of_real_add
    by (insert 6 s *, (rule has_vector_derivative_real_field derivative_eq_intros refl | 
          force simp add: minus_equation_iff)+)
next
  case 7
  from s a have "(\<lambda>k. (of_nat k + of_real a) powr -s) sums \<zeta> s"
    unfolding \<zeta>_def by (intro summable_sums summable_hurwitz_zeta) auto
  hence 1: "(\<lambda>b. (\<Sum>k=0..b. (of_nat k + of_real a) powr -s)) \<longlonglongrightarrow> \<zeta> s"
    by (simp add: sums_def')

  {
    fix z assume "Re z < 0"
    hence "((\<lambda>b. (a + real b) powr Re z) \<longlongrightarrow> 0) at_top"
      by (intro tendsto_neg_powr filterlim_tendsto_add_at_top filterlim_real_sequentially) auto    
    also have "(\<lambda>b. (a + real b) powr Re z) = (\<lambda>b. norm ((of_nat b + a) powr z))"
      using a by (subst norm_powr_real_powr) (auto simp: add_ac)
    finally have "((\<lambda>b. (of_nat b + a) powr z) \<longlongrightarrow> 0) at_top" 
      by (subst (asm) tendsto_norm_zero_iff) simp
  } note * = this
  have "(\<lambda>b. (of_nat b + a) powr (1 - s) / (1 - s)) \<longlonglongrightarrow> 0 / (1 - s)"
    using s by (intro tendsto_divide tendsto_const *) auto
  hence 2: "(\<lambda>b. (of_nat b + a) powr (1 - s) / (1 - s)) \<longlonglongrightarrow> 0"
    by simp

  have "(\<lambda>b. (\<Sum>i<2 * N + 1. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R
             ((- 1) ^ i * pochhammer s i * (of_nat b + a) powr -(s + of_nat i))))
          \<longlonglongrightarrow> (\<Sum>i<2 * N + 1. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R 
                   ((- 1) ^ i * pochhammer s i * 0))"
    using s by (intro tendsto_intros *) auto
  hence 3: "(\<lambda>b. (\<Sum>i<2 * N + 1. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R
              ((- 1) ^ i * pochhammer s i * (of_nat b + a) powr -(s + of_nat i)))) \<longlonglongrightarrow> 0" 
    by simp

  from tendsto_diff[OF tendsto_diff[OF 1 2] 3]
  show ?case by simp
qed simp_all

text \<open>
  The pre-$\zeta$ functions agree with the infinite sum that is used to define the $\zeta$
  function for $\mathfrak{R}(s)>1$.
\<close>
lemma pre_zeta_aux_conv_zeta:
  "pre_zeta_aux N a s = \<zeta> s + a powr (1 - s) / (1 - s)"
proof -
  let ?R = "(\<Sum>i=1..N. ((bernoulli (2*i) / fact (2*i)) *\<^sub>R pochhammer s (2*i - 1) * of_real a powr (-s - (2*i-1))))"
  let ?S = "EM_remainder (Suc (2 * N)) (\<lambda>x. - (pochhammer s (Suc (2*N)) *
              of_real (x + a) powr (- 1 - 2 * of_nat N - s))) 0"
  from \<zeta>.euler_maclaurin_strong_nat'[OF le_refl, simplified]
  have "of_real a powr -s = a powr (1 - s) / (1 - s) + \<zeta> s + a powr -s / 2 + (-?R) - ?S"
    unfolding sum_negf [symmetric] by (simp add: scaleR_conv_of_real pre_zeta_aux_def mult_ac)
  thus ?thesis unfolding pre_zeta_aux_def by (simp add: field_simps)
qed

end


text \<open>
  Since all of the partial pre-$\zeta$ functions are analytic and agree in the halfspace with 
  $\mathfrak R(s)>0$, they must agree in their entire domain.
\<close>
lemma pre_zeta_aux_eq:
  assumes "m \<le> n" "a > 0" "Re s > -2 * real m"
  shows   "pre_zeta_aux m a s = pre_zeta_aux n a s"
proof -
  have "pre_zeta_aux n a s - pre_zeta_aux m a s = 0"
  proof (rule analytic_continuation[of "\<lambda>s. pre_zeta_aux n a s - pre_zeta_aux m a s"])
    show "(\<lambda>s. pre_zeta_aux n a s - pre_zeta_aux m a s) holomorphic_on {s. Re s > -2 * real m}"
      using assms by (intro holomorphic_intros analytic_imp_holomorphic 
                        analytic_on_subset[OF analytic_pre_zeta_aux]) auto
  next
    fix s assume "s \<in> {s. Re s > 1}"
    with \<open>a > 0\<close> show "pre_zeta_aux n a s - pre_zeta_aux m a s = 0"
      by (simp add: pre_zeta_aux_conv_zeta)
  next
    have "2 \<in> {s. Re s > 1}" by simp
    also have "\<dots> = interior \<dots>"
      by (intro interior_open [symmetric] open_halfspace_Re_gt)
    finally show "2 islimpt {s. Re s > 1}"
      by (rule interior_limit_point)
  next
    show "connected {s. Re s > -2 * real m}"
      using convex_halfspace_gt[of "-2 * real m" "1::complex"]
      by (intro convex_connected) auto
  qed (insert assms, auto simp: open_halfspace_Re_gt)
  thus ?thesis by simp
qed

lemma pre_zeta_aux_eq':
  assumes "a > 0" "Re s > -2 * real m" "Re s > -2 * real n"
  shows   "pre_zeta_aux m a s = pre_zeta_aux n a s"
proof (cases m n rule: linorder_cases)
  case less
  with assms show ?thesis by (intro pre_zeta_aux_eq) auto
next
  case greater
  with assms show ?thesis by (subst eq_commute, intro pre_zeta_aux_eq) auto
qed auto

lemma pre_zeta_aux_eq_pre_zeta:
  assumes "Re s > -2 * real n" and "a > 0"
  shows   "pre_zeta_aux n a s = pre_zeta a s"
  unfolding pre_zeta_def
proof (intro pre_zeta_aux_eq')
  from assms show "- 2 * real (nat (1 - \<lceil>Re s / 2\<rceil>)) < Re s"
    by linarith
qed (insert assms, simp_all)

text \<open>
  This means that the idea of iterating that construction infinitely does yield
  a well-defined entire function.
\<close>
lemma analytic_pre_zeta: 
  assumes "a > 0"
  shows   "pre_zeta a analytic_on A"
  unfolding analytic_on_def
proof
  fix s assume "s \<in> A"
  let ?B = "{s'. Re s' > of_int \<lfloor>Re s\<rfloor> - 1}"
  have s: "s \<in> ?B" by simp linarith?
  moreover have "open ?B" by (rule open_halfspace_Re_gt)
  ultimately obtain \<epsilon> where \<epsilon>: "\<epsilon> > 0" "ball s \<epsilon> \<subseteq> ?B"
    unfolding open_contains_ball by blast
  define C where "C = ball s \<epsilon>"

  note analytic = analytic_on_subset[OF analytic_pre_zeta_aux]
  have "pre_zeta_aux (nat \<lceil>- Re s\<rceil> + 2) a holomorphic_on C"
  proof (intro analytic_imp_holomorphic analytic subsetI assms, goal_cases)
    case (1 w)
    with \<epsilon> have "w \<in> ?B" by (auto simp: C_def)
    thus ?case by (auto simp: ceiling_minus)
  qed
  also have "?this \<longleftrightarrow> pre_zeta a holomorphic_on C"
  proof (intro holomorphic_cong refl pre_zeta_aux_eq_pre_zeta assms)
    fix w assume "w \<in> C"
    with \<epsilon> have w: "w \<in> ?B" by (auto simp: C_def)
    thus " - 2 * real (nat \<lceil>- Re s\<rceil> + 2) < Re w"
      by (simp add: ceiling_minus)
  qed
  finally show "\<exists>e>0. pre_zeta a holomorphic_on ball s e"
    using \<open>\<epsilon> > 0\<close> unfolding C_def by blast
qed

lemma holomorphic_pre_zeta [holomorphic_intros]:
  "f holomorphic_on A \<Longrightarrow> a > 0 \<Longrightarrow> (\<lambda>z. pre_zeta a (f z)) holomorphic_on A"
  using holomorphic_on_compose [OF _ analytic_imp_holomorphic [OF analytic_pre_zeta], of f]
  by (simp add: o_def)


text \<open>
  It is now obvious that $\zeta$ is holomorphic everywhere except 1, where it has a 
  simple pole with residue 1, which we can simply read off.
\<close>
theorem holomorphic_hurwitz_zeta: 
  assumes "a > 0" "1 \<notin> A"
  shows   "hurwitz_zeta a holomorphic_on A"
proof -
  have "(\<lambda>s. pre_zeta a s + complex_of_real a powr (1 - s) / (s - 1)) holomorphic_on A"
    using assms by (auto intro!: holomorphic_intros)
  also from assms have "?this \<longleftrightarrow> ?thesis"
    by (intro holomorphic_cong) (auto simp: hurwitz_zeta_def)
  finally show ?thesis .
qed

corollary holomorphic_hurwitz_zeta' [holomorphic_intros]:
  assumes "f holomorphic_on A" and "a > 0" and "\<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 1"
  shows   "(\<lambda>x. hurwitz_zeta a (f x)) holomorphic_on A"
proof -
  have "hurwitz_zeta a \<circ> f holomorphic_on A" using assms
    by (intro holomorphic_on_compose_gen[of _ _ _ "f ` A"] holomorphic_hurwitz_zeta assms) auto
  thus ?thesis by (simp add: o_def)
qed

theorem holomorphic_zeta: "1 \<notin> A\<Longrightarrow> zeta holomorphic_on A"
  unfolding zeta_def by (auto intro: holomorphic_intros)

corollary holomorphic_zeta' [holomorphic_intros]:
  assumes "f holomorphic_on A" and "\<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 1"
  shows   "(\<lambda>x. zeta (f x)) holomorphic_on A"
  using assms unfolding zeta_def by (auto intro: holomorphic_intros)

corollary analytic_hurwitz_zeta: 
  assumes "a > 0" "1 \<notin> A"
  shows   "hurwitz_zeta a analytic_on A"
proof -
  from assms(1) have "hurwitz_zeta a holomorphic_on -{1}"
    by (rule holomorphic_hurwitz_zeta) auto
  also have "?this \<longleftrightarrow> hurwitz_zeta a analytic_on -{1}"
    by (intro analytic_on_open [symmetric]) auto
  finally show ?thesis by (rule analytic_on_subset) (insert assms, auto)
qed

corollary analytic_zeta: "1 \<notin> A \<Longrightarrow> zeta analytic_on A"
  unfolding zeta_def by (rule analytic_hurwitz_zeta) auto

corollary continuous_on_hurwitz_zeta:
  "a > 0 \<Longrightarrow> 1 \<notin> A \<Longrightarrow> continuous_on A (hurwitz_zeta a)"
  by (intro holomorphic_on_imp_continuous_on holomorphic_intros) auto

corollary continuous_on_hurwitz_zeta' [continuous_intros]:
  "continuous_on A f \<Longrightarrow> a > 0 \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 1) \<Longrightarrow> 
     continuous_on A (\<lambda>x. hurwitz_zeta a (f x))"
  using continuous_on_compose2 [OF continuous_on_hurwitz_zeta, of a "f ` A" A f]
  by (auto simp: image_iff)

corollary continuous_on_zeta: "1 \<notin> A \<Longrightarrow> continuous_on A zeta"
  by (intro holomorphic_on_imp_continuous_on holomorphic_intros) auto

corollary continuous_on_zeta' [continuous_intros]:
  "continuous_on A f \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 1) \<Longrightarrow> 
     continuous_on A (\<lambda>x. zeta (f x))"
  using continuous_on_compose2 [OF continuous_on_zeta, of "f ` A" A f]
  by (auto simp: image_iff)

corollary continuous_hurwitz_zeta [continuous_intros]:
  "a > 0 \<Longrightarrow> s \<noteq> 1 \<Longrightarrow> continuous (at s within A) (hurwitz_zeta a)"
  by (rule continuous_within_subset[of _ UNIV])
     (insert continuous_on_hurwitz_zeta[of a "-{1}"], 
      auto simp: continuous_on_eq_continuous_at open_Compl)

corollary continuous_hurwitz_zeta' [continuous_intros]:
  "a > 0 \<Longrightarrow> f s \<noteq> 1 \<Longrightarrow> continuous (at s within A) f \<Longrightarrow>
     continuous (at s within A) (\<lambda>s. hurwitz_zeta a (f s))"
  using continuous_within_compose3[OF continuous_hurwitz_zeta, of a f s A] by auto

corollary continuous_zeta [continuous_intros]:
  "s \<noteq> 1 \<Longrightarrow> continuous (at s within A) zeta"
  unfolding zeta_def by (intro continuous_intros) auto

corollary continuous_zeta' [continuous_intros]:
  "f s \<noteq> 1 \<Longrightarrow> continuous (at s within A) f \<Longrightarrow> continuous (at s within A) (\<lambda>s. zeta (f s))"
  unfolding zeta_def by (intro continuous_intros) auto

corollary field_differentiable_at_zeta:
  assumes "s \<noteq> 1"
  shows "zeta field_differentiable at s"
proof -
  have "zeta holomorphic_on (- {1})" using holomorphic_zeta by force
  moreover have "open (-{1} :: complex set)" by (intro open_Compl) auto
  ultimately show ?thesis using assms
    by (auto simp add: holomorphic_on_open open_halfspace_Re_gt open_Diff field_differentiable_def)
qed

theorem is_pole_hurwitz_zeta:
  assumes "a > 0"
  shows   "is_pole (hurwitz_zeta a) 1"
proof -
  from assms have "continuous_on UNIV (pre_zeta a)"
    by (intro holomorphic_on_imp_continuous_on analytic_imp_holomorphic analytic_pre_zeta)
  hence "isCont (pre_zeta a) 1"
    by (auto simp: continuous_on_eq_continuous_at)
  hence *: "pre_zeta a \<midarrow>1\<rightarrow> pre_zeta a 1"
    by (simp add: isCont_def)
  from assms have "isCont (\<lambda>s. complex_of_real a powr (1 - s)) 1"
    by (intro isCont_powr_complex) auto
  with assms have **: "(\<lambda>s. complex_of_real a powr (1 - s)) \<midarrow>1\<rightarrow> 1" 
    by (simp add: isCont_def)
  have "(\<lambda>s::complex. s - 1) \<midarrow>1\<rightarrow> 1 - 1" by (intro tendsto_intros)
  hence "filterlim (\<lambda>s::complex. s - 1) (at 0) (at 1)"
    by (auto simp: filterlim_at eventually_at_filter)
  hence ***: "filterlim (\<lambda>s :: complex. a powr (1 - s) / (s - 1)) at_infinity (at 1)"
    by (intro filterlim_divide_at_infinity [OF **]) auto
  have "is_pole (\<lambda>s. pre_zeta a s + complex_of_real a powr (1 - s) / (s - 1)) 1"
    unfolding is_pole_def hurwitz_zeta_def by (rule tendsto_add_filterlim_at_infinity * ***)+
  also have "?this \<longleftrightarrow> ?thesis" unfolding is_pole_def
    by (intro filterlim_cong refl) (auto simp: eventually_at_filter hurwitz_zeta_def)
  finally show ?thesis .
qed

corollary is_pole_zeta: "is_pole zeta 1"
  unfolding zeta_def by (rule is_pole_hurwitz_zeta) auto

theorem porder_hurwitz_zeta: 
  assumes "a > 0"
  shows   "porder (hurwitz_zeta a) 1 = 1"
proof (rule porder_eqI)
  fix w :: complex assume "w \<in> UNIV - {1}"
  thus "hurwitz_zeta a w = (pre_zeta a w * (w - 1) + a powr (1 - w)) / (w - 1) ^ 1"
    by (simp add: hurwitz_zeta_def field_simps)
qed (insert assms, auto intro!: holomorphic_intros)

corollary porder_zeta: "porder zeta 1 = 1"
  unfolding zeta_def by (rule porder_hurwitz_zeta) auto

theorem residue_hurwitz_zeta: 
  assumes "a > 0"
  shows   "residue (hurwitz_zeta a) 1 = 1"
proof -
  note holo = analytic_imp_holomorphic[OF analytic_pre_zeta]
  have "residue (hurwitz_zeta a) 1 = residue (\<lambda>z. pre_zeta a z + a powr (1 - z) / (z - 1)) 1"
    by (intro residue_cong) (auto simp: eventually_at_filter hurwitz_zeta_def)
  also have "\<dots> = residue (\<lambda>z. a powr (1 - z) / (z - 1)) 1" using assms
    by (subst residue_add [of UNIV])
       (auto intro!: holomorphic_intros holo intro: residue_holo[of UNIV, OF _ _ holo])
  also have "\<dots> = complex_of_real a powr (1 - 1)"
    using assms by (intro residue_simple [of UNIV]) (auto intro!: holomorphic_intros)
  also from assms have "\<dots> = 1" by simp
  finally show ?thesis .
qed

corollary residue_zeta: "residue zeta 1 = 1"
  unfolding zeta_def by (rule residue_hurwitz_zeta) auto

theorem
  assumes "a > 0" "Re s > 1"
  shows hurwitz_zeta_conv_suminf: "hurwitz_zeta a s = (\<Sum>n. (of_nat n + of_real a) powr -s)"
  and   sums_hurwitz_zeta: "(\<lambda>n. (of_nat n + of_real a) powr -s) sums hurwitz_zeta a s"
proof -
  from assms have [simp]: "s \<noteq> 1" by auto
  from assms have "hurwitz_zeta a s = pre_zeta_aux 0 a s + of_real a powr (1 - s) / (s - 1)"
    by (simp add: hurwitz_zeta_def pre_zeta_def)
  also from assms have "pre_zeta_aux 0 a s = (\<Sum>n. (of_nat n + of_real a) powr -s) + 
                          of_real a powr (1 - s) / (1 - s)"
    by (intro pre_zeta_aux_conv_zeta)
  also have "\<dots> + a powr (1 - s) / (s - 1) = 
               (\<Sum>n. (of_nat n + of_real a) powr -s) + a powr (1 - s) * (1 / (1 - s) + 1 / (s - 1))"
    by (simp add: algebra_simps)
  also have "1 / (1 - s) + 1 / (s - 1) = 0" 
    by (simp add: divide_simps)
  finally show "hurwitz_zeta a s = (\<Sum>n. (of_nat n + of_real a) powr -s)" by simp
  moreover have "(\<lambda>n. (of_nat n + of_real a) powr -s) sums (\<Sum>n. (of_nat n + of_real a) powr -s)"
    by (intro summable_sums summable_hurwitz_zeta assms)
  ultimately show "(\<lambda>n. (of_nat n + of_real a) powr -s) sums hurwitz_zeta a s" 
    by simp
qed

corollary
  assumes "Re s > 1"
  shows zeta_conv_suminf: "zeta s = (\<Sum>n. of_nat (Suc n) powr -s)"
  and   sums_zeta: "(\<lambda>n. of_nat (Suc n) powr -s) sums zeta s"
  using hurwitz_zeta_conv_suminf[of 1 s] sums_hurwitz_zeta[of 1 s] assms 
  by (simp_all add: zeta_def add_ac)

corollary
  assumes "n > 1"
  shows zeta_nat_conv_suminf: "zeta (of_nat n) = (\<Sum>k. 1 / of_nat (Suc k) ^ n)"
  and   sums_zeta_nat: "(\<lambda>k. 1 / of_nat (Suc k) ^ n) sums zeta (of_nat n)"
proof -
  have "(\<lambda>k. of_nat (Suc k) powr -of_nat n) sums zeta (of_nat n)"
    using assms by (intro sums_zeta) auto
  also have "(\<lambda>k. of_nat (Suc k) powr -of_nat n) = (\<lambda>k. 1 / of_nat (Suc k) ^ n :: complex)"
    by (simp add: powr_minus divide_simps del: of_nat_Suc)
  finally show "(\<lambda>k. 1 / of_nat (Suc k) ^ n) sums zeta (of_nat n)" .
  thus "zeta (of_nat n) = (\<Sum>k. 1 / of_nat (Suc k) ^ n)" by (simp add: sums_iff)
qed

lemma pre_zeta_aux_cnj [simp]: 
  assumes "a > 0"
  shows   "pre_zeta_aux n a (cnj z) = cnj (pre_zeta_aux n a z)"
proof -
  have "cnj (pre_zeta_aux n a z) = 
          of_real a powr -cnj z / 2 + (\<Sum>x=1..n. (bernoulli (2 * x) / fact (2 * x)) *\<^sub>R
            a powr (-cnj z - (2*x-1)) * pochhammer (cnj z) (2*x-1)) + EM_remainder (2*n+1)
          (\<lambda>x. -(pochhammer (cnj z) (Suc (2 * n)) * 
                  cnj (of_real (x + a) powr (-1 - 2 * of_nat n - z)))) 0"
    (is "_ = _ + ?A + ?B") unfolding pre_zeta_aux_def complex_cnj_add using assms
    by (subst EM_remainder_cnj [symmetric]) 
       (auto intro!: continuous_intros simp: cnj_powr add_eq_0_iff mult_ac)
  also have "?B = EM_remainder (2*n+1)
        (\<lambda>x. -(pochhammer (cnj z) (Suc (2 * n)) * of_real (x + a) powr (-1 - 2 * of_nat n - cnj z))) 0"
    using assms by (intro EM_remainder_cong) (auto simp: cnj_powr)
  also have "of_real a powr -cnj z / 2 + ?A + \<dots> = pre_zeta_aux n a (cnj z)"
    by (simp add: pre_zeta_aux_def mult_ac)
  finally show ?thesis ..
qed

lemma pre_zeta_cnj [simp]: "a > 0 \<Longrightarrow> pre_zeta a (cnj z) = cnj (pre_zeta a z)"
  by (simp add: pre_zeta_def)

theorem hurwitz_zeta_cnj [simp]: "a > 0 \<Longrightarrow> hurwitz_zeta a (cnj z) = cnj (hurwitz_zeta a z)"
proof -
  assume "a > 0"
  moreover have "cnj z = 1 \<longleftrightarrow> z = 1" by (simp add: complex_eq_iff)
  ultimately show ?thesis by (auto simp: hurwitz_zeta_def cnj_powr)
qed

theorem zeta_cnj [simp]: "zeta (cnj z) = cnj (zeta z)"
  by (simp add: zeta_def)

corollary hurwitz_zeta_real: "a > 0 \<Longrightarrow> hurwitz_zeta a (of_real x) \<in> \<real>"
  using hurwitz_zeta_cnj [of a "of_real x"] by (simp add: Reals_cnj_iff del: zeta_cnj)

corollary zeta_real: "zeta (of_real x) \<in> \<real>"
  unfolding zeta_def by (rule hurwitz_zeta_real) auto


subsection \<open>Connection to Dirichlet series\<close>

lemma eval_fds_zeta: "Re s > 1 \<Longrightarrow> eval_fds fds_zeta s = zeta s"
  using sums_zeta [of s] by (intro eval_fds_eqI) (auto simp: powr_minus divide_simps)

theorem euler_product_zeta:
  assumes "Re s > 1"
  shows   "(\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - 1 / of_nat p powr s) else 1) \<longlonglongrightarrow> zeta s"
  using euler_product_fds_zeta[of s] assms unfolding nat_power_complex_def 
  by (simp add: eval_fds_zeta)

corollary euler_product_zeta':
  assumes "Re s > 1"
  shows   "(\<lambda>n. \<Prod>p | prime p \<and> p \<le> n. inverse (1 - 1 / of_nat p powr s)) \<longlonglongrightarrow> zeta s"
proof -
  note euler_product_zeta [OF assms]
  also have "(\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - 1 / of_nat p powr s) else 1) =
               (\<lambda>n. \<Prod>p | prime p \<and> p \<le> n. inverse (1 - 1 / of_nat p powr s))"
    by (intro ext prod.mono_neutral_cong_right refl) auto
  finally show ?thesis .
qed

theorem zeta_Re_gt_1_nonzero: "Re s > 1 \<Longrightarrow> zeta s \<noteq> 0"
  using eval_fds_zeta_nonzero[of s] by (simp add: eval_fds_zeta)

theorem tendsto_zeta_Re_going_to_at_top: "(zeta \<longlongrightarrow> 1) (Re going_to at_top)"
proof (rule Lim_transform_eventually)
  have "eventually (\<lambda>x::real. x > 1) at_top"
    by (rule eventually_gt_at_top)
  hence "eventually (\<lambda>s. Re s > 1) (Re going_to at_top)"
    by blast
  thus "eventually (\<lambda>z. eval_fds fds_zeta z = zeta z) (Re going_to at_top)"
    by eventually_elim (simp add: eval_fds_zeta)
next
  have "conv_abscissa (fds_zeta :: complex fds) \<le> 1"
  proof (rule conv_abscissa_leI)
    fix c' assume "ereal c' > 1"
    thus "\<exists>s. s \<bullet> 1 = c' \<and> fds_converges fds_zeta (s::complex)"
      by (auto intro!: exI[of _ "of_real c'"])
  qed
  hence "(eval_fds fds_zeta \<longlongrightarrow> fds_nth fds_zeta 1) (Re going_to at_top)"
    by (intro tendsto_eval_fds_Re_going_to_at_top') auto
  thus "(eval_fds fds_zeta \<longlongrightarrow> 1) (Re going_to at_top)" by simp
qed

lemma conv_abscissa_zeta [simp]: "conv_abscissa (fds_zeta :: complex fds) = 1"
  and abs_conv_abscissa_zeta [simp]: "abs_conv_abscissa (fds_zeta :: complex fds) = 1"
proof -
  let ?z = "fds_zeta :: complex fds"
  have A: "conv_abscissa ?z \<ge> 1"
  proof (intro conv_abscissa_geI)
    fix c' assume "ereal c' < 1"
    hence "\<not>summable (\<lambda>n. real n powr -c')"
      by (subst summable_real_powr_iff) auto
    hence "\<not>summable (\<lambda>n. of_real (real n powr -c') :: complex)"
      by (subst summable_of_real_iff)
    also have "summable (\<lambda>n. of_real (real n powr -c') :: complex) \<longleftrightarrow> 
                 fds_converges fds_zeta (of_real c' :: complex)"
      unfolding fds_converges_def
      by (intro summable_cong eventually_mono [OF eventually_gt_at_top[of 0]])
         (simp add: fds_nth_zeta powr_Reals_eq powr_minus divide_simps)
    finally show "\<exists>s::complex. s \<bullet> 1 = c' \<and> \<not>fds_converges fds_zeta s"
      by (intro exI[of _ "of_real c'"]) auto
  qed

  have B: "abs_conv_abscissa ?z \<le> 1"
  proof (intro abs_conv_abscissa_leI)
    fix c' assume "1 < ereal c'"
    thus "\<exists>s::complex. s \<bullet> 1 = c' \<and> fds_abs_converges fds_zeta s"
      by (intro exI[of _ "of_real c'"]) auto
  qed

  have "conv_abscissa ?z \<le> abs_conv_abscissa ?z"
    by (rule conv_le_abs_conv_abscissa)
  also note B
  finally show "conv_abscissa ?z = 1" using A by (intro antisym)

  note A
  also have "conv_abscissa ?z \<le> abs_conv_abscissa ?z"
    by (rule conv_le_abs_conv_abscissa)
  finally show "abs_conv_abscissa ?z = 1" using B by (intro antisym)
qed

theorem deriv_zeta_sums:
  assumes s: "Re s > 1"
  shows "(\<lambda>n. -of_real (ln (real (Suc n))) / of_nat (Suc n) powr s) sums deriv zeta s"
proof -
  from s have "fds_converges (fds_deriv fds_zeta) s"
    by (intro fds_converges_deriv) simp_all
  with s have "(\<lambda>n. -of_real (ln (real (Suc n))) / of_nat (Suc n) powr s) sums
                  deriv (eval_fds fds_zeta) s"
    unfolding fds_converges_altdef
    by (simp add: fds_nth_deriv scaleR_conv_of_real eval_fds_deriv eval_fds_zeta)
  also from s have "eventually (\<lambda>s. s \<in> {s. Re s > 1}) (nhds s)"
    by (intro eventually_nhds_in_open) (auto simp: open_halfspace_Re_gt)
  hence "eventually (\<lambda>s. eval_fds fds_zeta s = zeta s) (nhds s)"
    by eventually_elim (auto simp: eval_fds_zeta)
  hence "deriv (eval_fds fds_zeta) s = deriv zeta s"
    by (intro deriv_cong_ev refl)
  finally show ?thesis .
qed

theorem inverse_zeta_sums:
  assumes s: "Re s > 1"
  shows   "(\<lambda>n. moebius_mu (Suc n) / of_nat (Suc n) powr s) sums inverse (zeta s)"
proof -
  have "fds_converges (fds moebius_mu) s"
    using assms by (auto intro!: fds_abs_converges_moebius_mu)
  hence "(\<lambda>n. moebius_mu (Suc n) / of_nat (Suc n) powr s) sums eval_fds (fds moebius_mu) s"
    by (simp add: fds_converges_altdef)
  also have "fds moebius_mu = inverse (fds_zeta :: complex fds)"
    by (rule fds_moebius_inverse_zeta)
  also from s have "eval_fds \<dots> s = inverse (zeta s)"
    by (subst eval_fds_inverse)
       (auto simp: fds_moebius_inverse_zeta [symmetric] eval_fds_zeta 
             intro!: fds_abs_converges_moebius_mu)
  finally show ?thesis .
qed

lemma zeta_conv_hurwitz_zeta_multiplication:
  fixes k :: nat and s :: complex
  assumes "k > 0" "s \<noteq> 1"
  shows   "k powr s * zeta s = (\<Sum>n=1..k. hurwitz_zeta (n / k) s)" (is "?lhs s = ?rhs s")
proof (rule analytic_continuation_open[where ?f = ?lhs and ?g = ?rhs])
  show "connected (-{1::complex})" by (rule connected_punctured_universe) auto
  show "{s. Re s > 1} \<noteq> {}" by (auto intro!: exI[of _ 2])
next
  fix s assume s: "s \<in> {s. Re s > 1}"
  show "?lhs s = ?rhs s"
  proof (rule sums_unique2)
    have "(\<lambda>m. \<Sum>n=1..k. (of_nat m + of_real (real n / real k)) powr -s) sums 
            (\<Sum>n=1..k. hurwitz_zeta (real n / real k) s)"
      using assms s by (intro sums_sum sums_hurwitz_zeta) auto
    also have "(\<lambda>m. \<Sum>n=1..k. (of_nat m + of_real (real n / real k)) powr -s) =
                 (\<lambda>m. of_nat k powr s * (\<Sum>n=1..k. of_nat (m * k + n) powr -s))"
      unfolding sum_distrib_left
    proof (intro ext sum.cong, goal_cases)
      case (2 m n)
      hence "m * k + n > 0" by (intro add_nonneg_pos) auto
      hence "of_nat 0 \<noteq> (of_nat (m * k + n) :: complex)" by (simp only: of_nat_eq_iff)
      also have "of_nat (m * k + n) = of_nat m * of_nat k + (of_nat n :: complex)" by simp
      finally have nz: "\<dots> \<noteq> 0" by auto
      
      have "of_nat m + of_real (real n / real k) = 
              (inverse (of_nat k) * of_nat (m * k + n) :: complex)"
        using assms by (simp add: field_simps)
      also from nz have "\<dots> powr -s = of_nat k powr s * of_nat (m * k + n) powr -s"
        by (subst powr_times_real) (auto simp: add_eq_0_iff powr_def exp_minus Ln_inverse)
      finally show ?case .
    qed auto
    finally show "\<dots> sums (\<Sum>n=1..k. hurwitz_zeta (real n / real k) s)" .
  next
    have "(\<lambda>m. of_nat (Suc m) powr -s) sums zeta s"
      using s by (intro sums_zeta assms) auto
    hence "(\<lambda>m. \<Sum>n=m*k..<m*k+k. of_nat (Suc n) powr - s) sums zeta s"
      using \<open>k > 0\<close> by (rule sums_group)
    also have "(\<lambda>m. \<Sum>n=m*k..<m*k+k. of_nat (Suc n) powr - s) = 
                 (\<lambda>m. \<Sum>n=1..k. of_nat (m * k + n) powr -s)"
    proof (rule ext, goal_cases)
      case (1 m)
      show ?case using assms
        by (intro ext sum.reindex_bij_witness[of _ "\<lambda>n. m * k + n - 1" "\<lambda>n. Suc n - m * k"]) auto
    qed
    finally show "(\<lambda>m. of_nat k powr s * (\<Sum>n=1..k. of_nat (m * k + n) powr -s)) sums
                    (of_nat k powr s * zeta s)" by (rule sums_mult)
  qed
qed (insert assms, auto intro!: holomorphic_intros simp: finite_imp_closed open_halfspace_Re_gt)

lemma hurwitz_zeta_one_half_left:
  assumes "s \<noteq> 1"
  shows   "hurwitz_zeta (1 / 2) s = (2 powr s - 1) * zeta s"
  using zeta_conv_hurwitz_zeta_multiplication[of 2 s] assms
  by (simp add: eval_nat_numeral zeta_def field_simps)


text \<open>
  The following gives an extension of the $\zeta$ functions to the critical strip.
\<close>
lemma hurwitz_zeta_critical_strip:
  fixes s :: complex and a :: real
  defines "S \<equiv> (\<lambda>n. \<Sum>i<n. (of_nat i + a) powr - s)"
  defines "I' \<equiv> (\<lambda>n. of_nat n powr (1 - s) / (1 - s))"
  assumes "Re s > 0" "s \<noteq> 1" and "a > 0"
  shows   "(\<lambda>n. S n - I' n) \<longlonglongrightarrow> hurwitz_zeta a s"
proof -
  from assms have [simp]: "s \<noteq> 1" by auto
  let ?f = "\<lambda>x. of_real (x + a) powr -s"
  let ?fs = "\<lambda>n x. (-1) ^ n * pochhammer s n * of_real (x + a) powr (-s - of_nat n)"
  have minus_commute: "-a - b = -b - a" for a b :: complex by (simp add: algebra_simps)
  define I where "I = (\<lambda>n. (of_nat n + a) powr (1 - s) / (1 - s))"
  define R where "R = (\<lambda>n. EM_remainder' 1 (?fs 1) (real 0) (real n))"
  define R_lim where "R_lim = EM_remainder 1 (?fs 1) 0"
  define C where "C = - (a powr -s / 2)"
  define D where "D = (\<lambda>n. (1/2) * (of_real (a + real n) powr - s))"
  define D' where "D' = (\<lambda>n. of_real (a + real n) powr - s)"
  define C' where "C' = a powr (1 - s) / (1 - s)"
  define C'' where "C'' = of_real a powr - s"
  {
    fix n :: nat assume n: "n > 0"
    have "((\<lambda>x. of_real (x + a) powr -s) has_integral (of_real (real n + a) powr (1-s) / (1 - s) - 
            of_real (0 + a) powr (1 - s) / (1 - s))) {0..real n}" using n assms 
      by (intro fundamental_theorem_of_calculus)
         (auto intro!: continuous_intros has_vector_derivative_real_field derivative_eq_intros
               simp: complex_nonpos_Reals_iff)
    hence I: "((\<lambda>x. of_real (x + a) powr -s) has_integral (I n - C')) {0..n}"
      by (auto simp: divide_simps C'_def I_def)
    have "(\<Sum>i\<in>{0<..n}. ?f (real i)) - integral {real 0..real n} ?f =
            (\<Sum>k<1. (bernoulli' (Suc k) / fact (Suc k)) *\<^sub>R (?fs k (real n) - ?fs k (real 0))) + R n" 
      using n assms unfolding R_def
      by (intro euler_maclaurin_strong_raw_nat[where Y = "{0}"])
         (auto intro!: continuous_intros derivative_eq_intros has_vector_derivative_real_field
               simp: pochhammer_rec' algebra_simps complex_nonpos_Reals_iff add_eq_0_iff)
    also have "(\<Sum>k<1. (bernoulli' (Suc k) / fact (Suc k)) *\<^sub>R (?fs k (real n) - ?fs k (real 0))) = 
                  ((n + a) powr - s - a powr - s) / 2"
      by (simp add: lessThan_nat_numeral scaleR_conv_of_real numeral_2_eq_2 [symmetric])
    also have "\<dots> = C + D n" by (simp add: C_def D_def field_simps)
    also have "integral {real 0..real n} (\<lambda>x. complex_of_real (x + a) powr - s) = I n - C'"
      using I by (simp add: has_integral_iff)
    also have "(\<Sum>i\<in>{0<..n}. of_real (real i + a) powr - s) = 
                 (\<Sum>i=0..n. of_real (real i + a) powr - s) - of_real a powr -s"
      using assms by (subst sum_head) auto
    also have "(\<Sum>i=0..n. of_real (real i + a) powr - s) = S n + of_real (real n + a) powr -s"
      unfolding S_def by (subst sum_last_plus) (auto simp: atLeast0LessThan)
    finally have "C - C' + C'' - D' n + D n + R n + (I n - I' n) = S n - I' n"
      by (simp add: algebra_simps S_def D'_def C''_def)
  }
  hence ev: "eventually (\<lambda>n. C - C' + C'' - D' n + D n + R n + (I n - I' n) = S n - I' n) at_top"
    by (intro eventually_mono[OF eventually_gt_at_top[of 0]]) auto

  have [simp]: "-1 - s = -s - 1" by simp
  {
    let ?C = "norm (pochhammer s 1)"
    have "R \<longlonglongrightarrow> R_lim" unfolding R_def R_lim_def of_nat_0
    proof (subst of_int_0 [symmetric], rule tendsto_EM_remainder)
      show "eventually (\<lambda>x. norm (?fs 1 x) \<le> ?C * (x + a) powr (-Re s - 1)) at_top"
        using eventually_ge_at_top[of 0]
        by eventually_elim (insert assms, auto simp: norm_mult norm_powr_real_powr)
    next
      fix x assume x: "x \<ge> real_of_int 0"
      have [simp]: "-numeral n - (x :: real) = -x - numeral n" for x n by (simp add: algebra_simps)
      show "((\<lambda>x. ?C / (-Re s) * (x + a) powr (-Re s)) has_real_derivative 
              ?C * (x + a) powr (- Re s - 1)) (at x within {real_of_int 0..})"
        using assms x by (auto intro!: derivative_eq_intros)
    next
      have "(\<lambda>y. ?C / (- Re s) * (a + real y) powr (- Re s)) \<longlonglongrightarrow> 0"
        by (intro tendsto_mult_right_zero tendsto_neg_powr filterlim_real_sequentially
                  filterlim_tendsto_add_at_top[OF tendsto_const]) (use assms in auto)
      thus "convergent (\<lambda>y. ?C / (- Re s) * (real y + a) powr (- Re s))"
        by (auto simp: add_ac convergent_def)
    qed (intro integrable_EM_remainder' continuous_intros, insert assms, auto simp: add_eq_0_iff)
  }
  moreover have "(\<lambda>n. I n - I' n) \<longlonglongrightarrow> 0"
  proof -
    have "(\<lambda>n. (complex_of_real (real n + a) powr (1 - s) - 
                 of_real (real n) powr (1 - s)) / (1 - s)) \<longlonglongrightarrow> 0 / (1 - s)" 
      using assms(3-5) by (intro filterlim_compose[OF _ filterlim_real_sequentially]
                             tendsto_divide complex_powr_add_minus_powr_asymptotics) auto
    thus "(\<lambda>n. I n - I' n) \<longlonglongrightarrow> 0" by (simp add: I_def I'_def divide_simps)
  qed
  ultimately have "(\<lambda>n. C - C' + C'' - D' n + D n + R n + (I n - I' n)) 
                     \<longlonglongrightarrow> C - C' + C'' - 0 + 0 + R_lim + 0"
    unfolding D_def D'_def using assms
    by (intro tendsto_add tendsto_diff tendsto_const tendsto_mult_right_zero
              tendsto_neg_powr_complex_of_real filterlim_tendsto_add_at_top 
              filterlim_real_sequentially) auto
  also have "C - C' + C'' - 0 + 0 + R_lim + 0 = 
               (a powr - s / 2) + a powr (1 - s) / (s - 1) + R_lim"
    by (simp add: C_def C'_def C''_def field_simps)
  also have "\<dots> = hurwitz_zeta a s"
    using assms by (simp add: hurwitz_zeta_def pre_zeta_def pre_zeta_aux_def
                              R_lim_def scaleR_conv_of_real)
  finally have "(\<lambda>n. C - C' + C'' - D' n + D n + R n + (I n - I' n)) \<longlonglongrightarrow> hurwitz_zeta a s" .
  from ev and this show ?thesis
    by (rule Lim_transform_eventually)
qed

lemma zeta_critical_strip:
  fixes s :: complex and a :: real
  defines "S \<equiv> (\<lambda>n. \<Sum>i=1..n. (of_nat i) powr - s)"
  defines "I \<equiv> (\<lambda>n. of_nat n powr (1 - s) / (1 - s))"
  assumes s: "Re s > 0" "s \<noteq> 1"
  shows   "(\<lambda>n. S n - I n) \<longlonglongrightarrow> zeta s"
proof -
  from hurwitz_zeta_critical_strip[OF s zero_less_one]
    have "(\<lambda>n. (\<Sum>i<n. complex_of_real (Suc i) powr - s) -
            of_nat n powr (1 - s) / (1 - s)) \<longlonglongrightarrow> hurwitz_zeta 1 s" by (simp add: add_ac)
  also have "(\<lambda>n. (\<Sum>i<n. complex_of_real (Suc i) powr -s)) = (\<lambda>n. (\<Sum>i=1..n. of_nat i powr -s))"
    by (intro ext sum.reindex_bij_witness[of _ "\<lambda>x. x - 1" Suc]) auto
  finally show ?thesis by (simp add: zeta_def S_def I_def)
qed


subsection \<open>The non-vanishing of $\zeta$ for $\mathfrak{R}(s) = 1$\<close>

text \<open>
  This fact was originally done by John Harrison in HOL Light and ported to Isabelle by
  Larry Paulson, then cleaned up and converted to the Isabelle definition of the zeta function
  by Manuel Eberl.
\<close>
lemma zeta_bound_calc:
  fixes r::real
  assumes "0<r" "r<1" "-1\<le>t" "t \<le> 1"
  shows "\<bar>1 - r\<bar>^3 * ((1 + r\<^sup>2 - 2 * (r * t))\<^sup>2 * (1 + r\<^sup>2 - 2 * (r * (2 * t\<^sup>2 - 1)))) \<le> 1"
proof -
  have le1: "c * a\<^sup>2 * b \<le> 1"
            if  "0 \<le> a" "0 \<le> b" "0 \<le> c" "c * (2 * a + b)^3 / 27 \<le> 1" for a b c::real
  proof -
    have "c * (a\<^sup>2 * b) \<le> c * ((2 * a + b)^3 / 27)"
    proof (rule mult_left_mono)
      have "0 \<le> (8 / 27 * a + 1 / 27 * b) * (a - b)\<^sup>2"
        using that by (simp add: zero_le_mult_iff)
      then show "a\<^sup>2 * b \<le> (2 * a + b)^3 / 27"
       by (auto simp: field_simps power_eq_if)
    qed (use that in auto)
    with that show ?thesis
      by linarith
  qed
  have le_a_ln: "0 \<le> 1 + r\<^sup>2 - 2 * (r * u)" if "u \<le> 1" for u
  proof -
    have "0 \<le> (1 - r)\<^sup>2"
      by simp
    also have "\<dots> = 1 + r\<^sup>2 - 2*r"
      by (simp add: power_eq_if algebra_simps)
    also have "\<dots> \<le> 1 + r\<^sup>2 - 2 * (r * u)"
      using that assms by simp
    finally show "0 \<le> 1 + r\<^sup>2 - 2 * (r * u)" .
  qed
  have "\<bar>1 - r\<bar>^3 * ((1 + r\<^sup>2 - 2 * (r * t))\<^sup>2 * (1 + r\<^sup>2 - 2 * (r * (2 * t\<^sup>2 - 1)))) =
        (1 - r)^3 * (1 + r\<^sup>2 - 2 * (r * t))\<^sup>2 * (1 + r\<^sup>2 - 2 * (r * (2 * t\<^sup>2 - 1)))"
    using assms by simp
  also have "\<dots> \<le> 1"
  proof (rule le1)
    show "0 \<le> 1 + r\<^sup>2 - 2 * (r * t)"
      by (metis assms(4) le_a_ln)
    show "0 \<le> 1 + r\<^sup>2 - 2 * (r * (2 * t\<^sup>2 - 1))"
      by (rule le_a_ln) (insert assms, simp add: abs_square_le_1)
    show "0 \<le> (1 - r)^3"
      using assms by auto
    have "((1 - r) * (2 * (1 + r\<^sup>2 - 2 * (r * t)) + (1 + r\<^sup>2 - 2 * (r * (2 * t\<^sup>2 - 1)))))^3 \<le> 3^3"
    proof (rule power_mono_odd)
      have "(1 - r) * (2 * (1 + r\<^sup>2 - 2 * (r * t)) + (1 + r\<^sup>2 - 2 * (r * (2 * t\<^sup>2 - 1)))) =
            (1 - r) * ((3 + 3 * r\<^sup>2) - 2 * r * (2 * t\<^sup>2 + 2 * t - 1))"
        by (auto simp: algebra_simps)
      also have "\<dots> \<le> (1 - r) * ((3 + 3 * r\<^sup>2) + 3 * r)"
      proof (rule mult_left_mono, simp)
        have "0 \<le> (1 + 2*t)^2"
          by (auto simp: algebra_simps)
        with assms have "- (2 * (2 * t\<^sup>2 + 2 * t - 1)) \<le> 3"
          unfolding power2_eq_square by (auto simp: algebra_simps)
        then have "- (2 * (2 * t\<^sup>2 + 2 * t - 1)) * r \<le> 3 * r"
          using assms real_mult_le_cancel_iff1 by blast
        then show "- (2 * r * (2 * t\<^sup>2 + 2 * t - 1)) \<le> 3 * r"
          by (simp add: algebra_simps)
      qed (use assms in auto)
      also have "\<dots> \<le> 3"
        using assms by (auto simp: algebra_simps power_eq_if)
      finally show "(1 - r) * (2 * (1 + r\<^sup>2 - 2 * (r * t)) + (1 + r\<^sup>2 - 2 * (r * (2 * t\<^sup>2 - 1)))) \<le> 3" .
    qed auto
    then
    show "(1 - r)^3 * (2 * (1 + r\<^sup>2 - 2 * (r * t)) + (1 + r\<^sup>2 - 2 * (r * (2 * t\<^sup>2 - 1))))^3 / 27 \<le> 1"
      by (simp add: power_mult_distrib)
  qed
  finally show ?thesis .
qed


lemma of_nat_nz [simp]: "1 + of_nat n \<noteq> (0::'a::real_algebra_1)"
                        "numeral x + of_nat n \<noteq> (0::'a::real_algebra_1)"
proof -
  have "1 + of_nat n = (of_nat (Suc n) :: 'a)" by simp
  also have "\<dots> \<noteq> of_nat 0" by (subst of_nat_eq_iff) auto
  finally show "1 + of_nat n \<noteq> (0::'a)" by simp
  have "numeral x + of_nat n = (of_nat (numeral x + n) :: 'a)" by simp
  also have "\<dots> \<noteq> of_nat 0" by (subst of_nat_eq_iff) auto
  finally show "numeral x + of_nat n \<noteq> (0::'a)" by simp
qed

lemma powr_of_nat_ne_1:
  assumes "Re s > 0" and "n \<ge> 2"
  shows   "of_nat n powr s \<noteq> 1"
proof -
  from assms have "real n powr 0 < real n powr Re s"
    by (intro powr_less_mono) auto
  also have "real n powr Re s = norm (of_nat n powr s)"
    by (simp add: norm_powr_real_powr)
  finally show ?thesis using assms by auto
qed

lemma zeta_multiple_bound:
  assumes "x \<in> \<real>" "y \<in> \<real>" and x: "1 < Re x"
    shows "1 \<le> norm (zeta x^3 * zeta(x + \<i> * y) ^ 4 * zeta(x + 2 * \<i> * y)^2)"  (is "1 \<le> norm ?g")
proof -
  let ?f = "\<lambda>n. (\<Prod>p \<in> {p. prime p \<and> p \<le> n}. inverse(1 - 1 / (of_nat p powr x)))^3 *
        (\<Prod>p \<in> {p. prime p \<and> p \<le> n}. inverse(1 - 1 / (of_nat p powr (x + \<i> * y)))) ^ 4 *
        (\<Prod>p \<in> {p. prime p \<and> p \<le> n}. inverse(1 - 1 / (of_nat p powr (x + 2 * \<i> * y))))\<^sup>2"
  show ?thesis
  proof (rule Lim_norm_lbound)
    show "?f \<longlonglongrightarrow> ?g"
      by (intro tendsto_mult tendsto_power euler_product_zeta' assms)
         (insert assms, auto simp: Reals_def)
    have "1 \<le> cmod (?f n)" for n
    proof -
      have "cmod ((1 - inverse (of_nat p powr x))^3 *
                  (1 - inverse (of_nat p powr (x + \<i> * y))) ^ 4 *
                  (1 - inverse (of_nat p powr (x + 2 * \<i> * y)))\<^sup>2) \<le> 1"
           if "prime p" "p \<le> n" for p
      proof -
        have "p \<ge> 2"
          by (simp add: prime_ge_2_nat that)
        let ?r = "exp (-(Re x * ln (real p)))"
        let ?t = "cos (Re y * ln (real p))"
        have r01: "0 < ?r" "?r < 1"
          using \<open>p \<ge> 2\<close> assms by (auto simp: zero_less_mult_iff)
        have 422: "z ^ 4 = (z\<^sup>2)\<^sup>2" for z::real by auto
        have rcs: "(1 - r * c)\<^sup>2 + (r * s)\<^sup>2 = 1 + r\<^sup>2 * (s\<^sup>2 + c\<^sup>2) - 2 * r * c" for r c s::real
          by (auto simp: algebra_simps power_eq_if)
        have "cmod ((1 - inverse (of_nat p powr x))^3 *
                    (1 - inverse (of_nat p powr (x + \<i> * y))) ^ 4 *
                    (1 - inverse (of_nat p powr (x + 2 * \<i> * y)))\<^sup>2) =
              cmod ((1 - inverse (of_nat p powr x))^3 *
                    ((1 - inverse (of_nat p powr x) * inverse (of_nat p powr (\<i> * y))) ^ 4 *
                    (1 - inverse (of_nat p powr x) * inverse (of_nat p powr (2 * (\<i> * y))))\<^sup>2))"
          by (simp add: powr_add mult.assoc)
        also have "\<dots> = cmod ((1 - inverse (of_nat p powr x))^3 *
                           ((1 - inverse (of_nat p powr x) * inverse (of_nat p powr (\<i> * y))) ^ 4 *
                            (1 - inverse (of_nat p powr x) * inverse ((of_nat p powr (\<i> * y))\<^sup>2))\<^sup>2))"
          by (simp add: semiring_numeral_class.mult_2 [symmetric] powr_add [symmetric] power_eq_if)
        also have "\<dots> = cmod ((1 - exp (- (x * complex_of_real (ln (real p)))))^3 *
                               ((1 - exp (- (x * of_real (ln (real p)))) * 
                                exp (- (\<i> * y * of_real (ln (real p))))) ^ 4 *
                                (1 - exp (- (x * of_real (ln (real p)))) * 
                                exp (- (2 * (\<i> * y * of_real (ln (real p))))))\<^sup>2))"
          using \<open>p \<ge> 2\<close> by (simp add: powr_def Ln_of_nat exp_minus [symmetric]
                                      exp_of_nat_mult [symmetric])
        also have "\<dots> = cmod ((1 - exp (- (x * complex_of_real (ln (real p)))))^3 *
                               ((1 - exp (- (x * of_real (ln (real p)))) * 
                               exp (\<i> * (-y * of_real (ln (real p))))) ^ 4 *
                               (1 - exp (- (x * of_real (ln (real p)))) * 
                               exp (\<i> * (2 * -y * of_real (ln (real p)))))\<^sup>2))"
          by (simp add: algebra_simps)
        also have "\<dots> = cmod ((1 - exp (- (x * of_real (ln (real p)))))^3 *
                               ((1 - exp (- (x * of_real (ln (real p)))) * 
                               (cos (- y * of_real (ln (real p))) + 
                                \<i> * sin (- y * of_real (ln (real p))))) ^ 4 *
                               (1 - exp (- (x * of_real (ln (real p)))) * 
                               (cos (2 * - y * of_real (ln (real p))) +
                                \<i> * sin (2 * - y * of_real (ln (real p)))))\<^sup>2))"
          by (simp only: exp_Euler)
        also have "\<dots> = cmod (of_real(1 - ?r)^3 *
                               ((1 - ?r * (cos (- (Re y) * ln (real p)) +
                                            \<i> * sin (- (Re y) * ln (real p)))) ^ 4 *
                               (1 - ?r * (of_real (cos (2 * - (Re y) * ln (real p))) + 
                                         \<i> * of_real (sin (2 * - (Re y) * ln (real p)))))\<^sup>2))"
          using assms by (auto simp: exp_of_real [symmetric] cos_of_real [symmetric] 
                                     sin_of_real [symmetric] Reals_def)
        also have "\<dots> = \<bar>1 - ?r\<bar>^3 * ((1 + ?r\<^sup>2 - 2 * (?r * ?t))\<^sup>2 * 
                          (1 + ?r\<^sup>2 - 2 * (?r * (2 * ?t\<^sup>2 - 1))))"
          unfolding norm_mult norm_power cmod_power2 422 norm_of_real
          by (simp add: rcs) (simp_all add: mult.assoc cos_double_cos)
        also have "\<dots> \<le> 1"
          by (auto intro: zeta_bound_calc [OF r01])
        finally show ?thesis .
      qed
      then have "inverse (cmod (?f n)) \<le> 1"
        unfolding prod_power_distrib prod.distrib [symmetric] norm_inverse [symmetric]
                  prod_inversef [symmetric] power_inverse o_def
        by (auto simp: prod_norm [symmetric] divide_simps intro: prod_le_1)
      moreover have "cmod (?f n) > 0"
        using assms by (simp add: powr_of_nat_ne_1 prime_ge_2_nat complex_is_Real_iff)
      ultimately have "1 \<le> inverse (inverse (cmod (?f n)))"
        using inverse_positive_iff_positive one_le_inverse_iff by blast
      then show ?thesis by simp
    qed
    then show "\<forall>\<^sub>F n in sequentially. 1 \<le> cmod (?f n)"
      by (rule eventually_sequentiallyI [of 0])
  qed auto
qed

lemma tendsto_pre_zeta [tendsto_intros]:
  assumes "a > 0"
  shows   "(pre_zeta a \<longlongrightarrow> pre_zeta a s) (at s within A)"
proof -
  from assms have "continuous_on UNIV (pre_zeta a)"
    by (intro holomorphic_on_imp_continuous_on holomorphic_intros)
  hence "pre_zeta a \<midarrow>s\<rightarrow> pre_zeta a s" by (auto simp: continuous_on_def)
  thus ?thesis by (rule filterlim_mono) (auto intro!: at_le)
qed

lemma zeta_nonzero_aux: "((\<lambda>s. zeta s^3 * (s - 1) ^ 4) \<longlongrightarrow> 0) (at 1 within {s \<in> \<real>. 1 < Re s})"
  (is "filterlim _ _ ?F")
proof (rule Lim_transform_eventually)
  let ?f = "pre_zeta 1"
  have "eventually (\<lambda>s. s \<noteq> 1) ?F" by (auto simp: eventually_at_filter)
  thus "eventually (\<lambda>s. (\<Sum>k\<le>3. (3 choose k) * ?f s ^ k * (s - 1) ^ Suc k) =
                            zeta s ^ 3 * (s - 1) ^ 4) ?F"
  proof eventually_elim
    case (elim s)
    let ?t = "inverse (s - 1)" and ?u = "s - 1"
    from elim have "zeta s = ?f s + ?t"
      by (simp add: zeta_def hurwitz_zeta_def divide_simps)
    also have "\<dots> ^ 3 = (\<Sum>k\<le>3. (3 choose k) * ?f s ^ k * ?t ^ (3 - k))"
      by (simp add: algebra_simps eval_nat_numeral)
    also have "\<dots> * ?u ^ 4 = (\<Sum>k\<le>3. (3 choose k) * ?f s ^ k * (?u ^ 4 * ?t ^ (3 - k)))"
      by (subst sum_distrib_right) (simp_all add: algebra_simps)
    also have "\<dots> = (\<Sum>k\<le>3. (3 choose k) * ?f s ^ k * ?u ^ Suc k)"
      by (intro sum.cong) (auto simp: divide_simps power_diff eval_nat_numeral)
    finally show ?case ..
  qed
qed (auto intro!: tendsto_eq_intros)

theorem zeta_nonzero:
  assumes "1 \<le> Re s" and "s \<noteq> 1"
    shows "zeta s \<noteq> 0"
proof
  assume contr: "zeta s = 0"
  let ?y = "Im s"
  have "?thesis" if Re1: "Re s = 1"
  proof (cases "?y = 0")
    case True then show ?thesis
      using Re1 assms by (auto simp: complex_eq_iff)
  next
    case False
    let ?D = "deriv (\<lambda>x. zeta(x + \<i> * ?y)) 1"
    let ?F = "at 1 within {s \<in> \<real>. 1 < Re s}"
    have 1: "1 islimpt {s. s \<in> \<real> \<and> 1 < Re s}" unfolding islimpt_approachable_le
    proof safe
      fix \<epsilon> :: real assume "\<epsilon> > 0"
      thus "\<exists>x'\<in>{s \<in> \<real>. 1 < Re s}. x' \<noteq> 1 \<and> dist x' 1 \<le> \<epsilon>"
        by (intro bexI[of _ "of_real (1 + \<epsilon>)"]) (auto simp: dist_norm)
    qed
    show ?thesis
    proof (rule notE [OF _ Lim_norm_lbound])
      show "((\<lambda>x. zeta x^3 * zeta (x + \<i> * ?y) ^ 4 * (zeta (x + 2*\<i>*?y))\<^sup>2) \<longlongrightarrow>
             ((0 * ?D ^ 4) * zeta(1 + 2*\<i>*?y)^2)) ?F"
      proof (rule tendsto_mult)
        show "((\<lambda>x. zeta x^3 * zeta (x + \<i> * ?y) ^ 4) \<longlongrightarrow> 0 * ?D ^ 4)
              ?F"
        proof (rule Lim_transform_eventually)
          show " \<forall>\<^sub>F x in at 1 within {s \<in> \<real>. 1 < Re s}.
                    zeta x^3 * (x - 1) ^ 4 * (zeta (x + \<i> * ?y) / (x - 1)) ^ 4 =
                    zeta x^3 * zeta (x + \<i> * ?y) ^ 4"
            by (force simp: eventually_at divide_simps intro!: zero_less_one)
          have "((\<lambda>x. zeta (x + \<i> * ?y)) has_field_derivative ?D) ?F" using False
            by (intro holomorphic_derivI[where ?S = "-{1 - \<i> * Im s}"])
               (auto intro!: holomorphic_intros simp: complex_eq_iff)
          then have *: "((\<lambda>y. (zeta (y + \<i> * ?y) - zeta (1 + \<i> * ?y)) / (y - 1)) \<longlongrightarrow> ?D) ?F"
            by (simp add: has_field_derivative_iff)
          from Re1 have s_eq: "s = 1 + \<i> * Im s" by (auto simp: complex_eq_iff)
          have *: "((\<lambda>x. zeta (x + \<i> * ?y) / (x - 1)) \<longlongrightarrow> ?D) ?F"
            by (rule Lim_transform [OF *])
               (auto simp: Lim_within norm_divide divide_simps complex_eq dist_complex_def 
                           s_eq [symmetric] contr intro!: exI[of _ 1])
          have zeta_lim0: "((\<lambda>x. zeta x^3 * (x - 1) ^ 4) \<longlongrightarrow> 0) ?F" by (rule zeta_nonzero_aux)
          show "((\<lambda>x. zeta x^3 * (x - 1) ^ 4 * (zeta (x + \<i>*?y) / (x - 1)) ^ 4) \<longlongrightarrow> 0 * ?D ^ 4) ?F"
            by (intro tendsto_mult [OF zeta_lim0] tendsto_power *)
        qed
        have "continuous ?F (\<lambda>x. (zeta (x + 2*\<i>*?y))\<^sup>2)" using \<open>Im s \<noteq> 0\<close>
          by (intro continuous_intros continuous_within_compose2 
                   [where f = "\<lambda>x. x + 2*\<i>*?y" and g = zeta]) auto
        then show "((\<lambda>x. (zeta (x + 2*\<i>*?y))\<^sup>2) \<longlongrightarrow> (zeta (1 + 2*\<i>*?y))\<^sup>2) ?F"
          by (force simp: continuous_within)
      qed
      show "\<forall>\<^sub>F x in ?F. 1 \<le> cmod (zeta x^3 * zeta (x + \<i> * ?y) ^ 4 * (zeta (x + 2*\<i>*?y))\<^sup>2)"
        by (force simp: eventually_at intro!: zeta_multiple_bound zero_less_one)
    qed (use 1 trivial_limit_within 1 in auto)
  qed
  then show False using assms contr zeta_Re_gt_1_nonzero[of s]
    by (cases "Re s > 1") auto
qed


subsection \<open>Special values of the $\zeta$ functions\<close>

theorem hurwitz_zeta_neg_of_nat: 
  assumes "a > 0"
  shows   "hurwitz_zeta a (-of_nat n) = -bernpoly (Suc n) a / of_nat (Suc n)"
proof -
  have "-of_nat n \<noteq> (1::complex)" by (simp add: complex_eq_iff)
  hence "hurwitz_zeta a (-of_nat n) = 
           pre_zeta a (-of_nat n) + a powr real (Suc n) / (-of_nat (Suc n))"
    unfolding zeta_def hurwitz_zeta_def using assms by (simp add: powr_of_real [symmetric])
  also have "a powr real (Suc n) / (-of_nat (Suc n)) = - (a powr real (Suc n) / of_nat (Suc n))"
    by (simp add: divide_simps del: of_nat_Suc)
  also have "a powr real (Suc n) = a ^ Suc n"
    using assms by (intro powr_realpow)
  also have "pre_zeta a (-of_nat n) = pre_zeta_aux (Suc n) a (- of_nat n)"
    using assms by (intro pre_zeta_aux_eq_pre_zeta [symmetric]) auto
  also have "\<dots> = of_real a powr of_nat n / 2 +
                    (\<Sum>i = 1..Suc n. (bernoulli (2 * i) / fact (2 * i)) *\<^sub>R
                       (pochhammer (- of_nat n) (2 * i - 1) *
                       of_real a powr (of_nat n - of_nat (2 * i - 1)))) +
                    EM_remainder (Suc (2 * Suc n)) (\<lambda>x. - (pochhammer (- of_nat n)
                      (2*n+3) * of_real (x + a) powr (- of_nat n - 3))) 0"
    (is "_ = ?B + sum (\<lambda>n. ?f (2 * n)) _ + _") 
    unfolding pre_zeta_aux_def by (simp add: add_ac eval_nat_numeral)
  also have "?B = of_real (a ^ n) / 2" 
    using assms by (subst powr_Reals_eq) (auto simp: powr_realpow)
  also have "pochhammer (-of_nat n :: complex) (2*n+3) = 0"
    by (subst pochhammer_eq_0_iff) auto
  finally have "hurwitz_zeta a (-of_nat n) = 
                  - (a ^ Suc n / of_nat (Suc n)) + (a ^ n / 2 + sum (\<lambda>n. ?f (2 * n)) {1..Suc n})"
    by simp

  also have "sum (\<lambda>n. ?f (2 * n)) {1..Suc n} = sum ?f (op * 2 ` {1..Suc n})"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>i. i div 2" "\<lambda>i. 2*i"]) auto
  also have "\<dots> = (\<Sum>i=2..2*n+2. ?f i)"
  proof (intro sum.mono_neutral_left ballI, goal_cases)
    case (3 i)
    hence "odd i" "i \<noteq> 1" by (auto elim!: evenE)
    thus ?case by (simp add: bernoulli_odd_eq_0)
  qed auto
  also have "\<dots> = (\<Sum>i=2..Suc n. ?f i)"
  proof (intro sum.mono_neutral_right ballI, goal_cases)
    case (3 i)
    hence "pochhammer (-of_nat n :: complex) (i - 1) = 0"
      by (subst pochhammer_eq_0_iff) auto
    thus ?case by simp
  qed auto
  also have "\<dots> = (\<Sum>i=Suc 1..Suc n. -of_real (real (Suc n choose i) * bernoulli i * 
                     a ^ (Suc n - i)) / of_nat (Suc n))"
    (is "sum ?lhs _ = sum ?f _")
  proof (intro sum.cong, goal_cases)
    case (2 i)
    hence "of_nat n - of_nat (i - 1) = (of_nat (Suc n - i) :: complex)"
      by (auto simp: of_nat_diff)
    also have "of_real a powr \<dots> = of_real (a ^ (Suc n - i))"
      using 2 assms by (subst powr_nat) auto
    finally have A: "of_real a powr (of_nat n - of_nat (i - 1)) = \<dots>" .
    have "pochhammer (-of_nat n) (i - 1) = complex_of_real (pochhammer (-real n) (i - 1))"
      by (simp add: pochhammer_of_real [symmetric])
    also have "pochhammer (-real n) (i - 1) = pochhammer (-of_nat (Suc n)) i / (-1 - real n)"
      using 2 by (subst (2) pochhammer_rec_if) auto
    also have "-1 - real n = -real (Suc n)" by simp
    finally have B: "pochhammer (-of_nat n) (i - 1) = 
                    -complex_of_real (pochhammer (-real (Suc n)) i / real (Suc n))"
      by (simp del: of_nat_Suc)
    have "?lhs i = -complex_of_real (bernoulli i * pochhammer (-real (Suc n)) i / fact i * 
                      a ^ (Suc n - i)) / of_nat (Suc n)"
      by (simp only: A B) (simp add: scaleR_conv_of_real)
    also have "bernoulli i * pochhammer (-real (Suc n)) i / fact i =
                 (real (Suc n) gchoose i) * bernoulli i" using 2
      by (subst gbinomial_pochhammer) (auto simp: minus_one_power_iff bernoulli_odd_eq_0)
    also have "real (Suc n) gchoose i = Suc n choose i"
      by (subst binomial_gbinomial) auto
    finally show ?case by simp
  qed auto
  also have "a ^ n / 2 + sum ?f {Suc 1..Suc n} = sum ?f {1..Suc n}"
    by (subst (2) sum_head_Suc) (simp_all add: scaleR_conv_of_real del: of_nat_Suc)
  also have "-(a ^ Suc n / of_nat (Suc n)) + sum ?f {1..Suc n} = sum ?f {0..Suc n}"
    by (subst (2) sum_head_Suc) (simp_all add: scaleR_conv_of_real)
  also have "\<dots> = - bernpoly (Suc n) a / of_nat (Suc n)"
    unfolding sum_negf sum_divide_distrib [symmetric] by (simp add: bernpoly_def atLeast0AtMost)
  finally show ?thesis .
qed

theorem zeta_neg_of_nat: 
  "zeta (-of_nat n) = -of_real (bernoulli' (Suc n)) / of_nat (Suc n)"
  unfolding zeta_def by (simp add: hurwitz_zeta_neg_of_nat bernpoly_1')

corollary zeta_trivial_zero:
  assumes "even n" "n \<noteq> 0"
  shows   "zeta (-of_nat n) = 0"
  using zeta_neg_of_nat[of n] assms by (simp add: bernoulli'_odd_eq_0)

theorem zeta_even_nat: 
  "zeta (2 * of_nat n) = 
     of_real ((-1) ^ Suc n * bernoulli (2 * n) * (2 * pi) ^ (2 * n) / (2 * fact (2 * n)))"
proof (cases "n = 0")
  case False
  hence "(\<lambda>k. 1 / of_nat (Suc k) ^ (2 * n)) sums zeta (of_nat (2 * n))"
    by (intro sums_zeta_nat) auto
  from sums_unique2 [OF this nat_even_power_sums_complex] False show ?thesis by simp
qed (insert zeta_neg_of_nat[of 0], simp_all)

corollary zeta_even_numeral: 
  "zeta (numeral (Num.Bit0 n)) = of_real
     ((- 1) ^ Suc (numeral n) * bernoulli (numeral (num.Bit0 n)) *
     (2 * pi) ^ numeral (num.Bit0 n) / (2 * fact (numeral (num.Bit0 n))))" (is "_ = ?rhs")
proof -
  have *: "(2 * numeral n :: nat) = numeral (Num.Bit0 n)"
    by (subst numeral.numeral_Bit0, subst mult_2, rule refl)
  have "numeral (Num.Bit0 n) = (2 * numeral n :: complex)"
    by (subst numeral.numeral_Bit0, subst mult_2, rule refl)
  also have "\<dots> = 2 * of_nat (numeral n)" by (simp only: of_nat_numeral of_nat_mult)
  also have "zeta \<dots> = ?rhs" by (subst zeta_even_nat) (simp only: *)
  finally show ?thesis .
qed

corollary zeta_neg_even_numeral [simp]: "zeta (-numeral (Num.Bit0 n)) = 0"
proof -
  have "-numeral (Num.Bit0 n) = (-of_nat (numeral (Num.Bit0 n)) :: complex)"
    by simp
  also have "zeta \<dots> = 0"
  proof (rule zeta_trivial_zero)
    have "numeral (Num.Bit0 n) = (2 * numeral n :: nat)"
      by (subst numeral.numeral_Bit0, subst mult_2, rule refl)
    also have "even \<dots>" by (rule dvd_triv_left)
    finally show "even (numeral (Num.Bit0 n) :: nat)" .
  qed auto
  finally show ?thesis .
qed

corollary zeta_neg_numeral:
  "zeta (-numeral n) = 
     -of_real (bernoulli' (numeral (Num.inc n)) / numeral (Num.inc n))"
proof -
  have "-numeral n = (- of_nat (numeral n) :: complex)" 
    by simp
  also have "zeta \<dots> = -of_real (bernoulli' (numeral (Num.inc n)) / numeral (Num.inc n))"
    by (subst zeta_neg_of_nat) (simp add: numeral_inc)
  finally show ?thesis .
qed

corollary zeta_0 [simp]: "zeta 0 = - 1 / 2"
  using zeta_neg_of_nat[of 0] by simp

corollary zeta_neg1: "zeta (-1) = - 1 / 12"
  using zeta_neg_of_nat[of 1] by (simp add: eval_bernoulli)

corollary zeta_neg3: "zeta (-3) = 1 / 120"
  by (simp add: zeta_neg_numeral)

corollary zeta_neg5: "zeta (-5) = - 1 / 252"
  by (simp add: zeta_neg_numeral)

corollary zeta_2: "zeta 2 = pi ^ 2 / 6"
  by (simp add: zeta_even_numeral)

corollary zeta_4: "zeta 4 = pi ^ 4 / 90"
  by (simp add: zeta_even_numeral fact_num_eq_if)

corollary zeta_6: "zeta 6 = pi ^ 6 / 945"
  by (simp add: zeta_even_numeral fact_num_eq_if)

corollary zeta_8: "zeta 8 = pi ^ 8 / 9450"
  by (simp add: zeta_even_numeral fact_num_eq_if)


subsection \<open>Integral relation between $\Gamma$ and $\zeta$ function\<close>

lemma
  assumes z: "Re z > 0" and a: "a > 0"
  shows   Gamma_hurwitz_zeta_aux_integral: 
            "Gamma z / (of_nat n + of_real a) powr z = 
               (\<integral>s\<in>{0<..}. (s powr (z - 1) / exp ((n+a) * s)) \<partial>lebesgue)"
    and   Gamma_hurwitz_zeta_aux_integrable:
            "set_integrable lebesgue {0<..} (\<lambda>s. s powr (z - 1) / exp ((n+a) * s))"
proof -
  note integrable = absolutely_integrable_Gamma_integral' [OF z]
  let ?INT = "set_lebesgue_integral lebesgue {0<..} :: (real \<Rightarrow> complex) \<Rightarrow> complex"
  let ?INT' = "set_lebesgue_integral lebesgue {0<..} :: (real \<Rightarrow> real) \<Rightarrow> real"

  have meas1: "set_borel_measurable lebesgue {0<..} 
                 (\<lambda>x. of_real x powr (z - 1) / of_real (exp ((n+a) * x)))"
    by (intro measurable_completion, subst measurable_lborel2, 
        intro borel_measurable_continuous_on_indicator) (auto intro!: continuous_intros)
  show integrable1: "set_integrable lebesgue {0<..} 
                       (\<lambda>s. s powr (z - 1) / exp ((n+a) * s))"
    using assms by (intro absolutely_integrable_Gamma_integral) auto
  from assms have pos: "0 < real n + a" by (simp add: add_nonneg_pos)
  hence "complex_of_real 0 \<noteq> of_real (real n + a)" by (simp only: of_real_eq_iff)
  also have "complex_of_real (real n + a) = of_nat n + of_real a" by simp
  finally have nz: "\<dots> \<noteq> 0" by auto

  have "((\<lambda>t. complex_of_real t powr (z - 1) / of_real (exp t)) has_integral Gamma z) {0<..}"
    by (rule Gamma_integral_complex') fact+
  hence "Gamma z = ?INT (\<lambda>t. t powr (z - 1) / of_real (exp t))"
    using set_lebesgue_integral_eq_integral(2) [OF integrable] 
    by (simp add: has_integral_iff exp_of_real)
  also have "lebesgue = density (distr lebesgue lebesgue (\<lambda>t. (real n+a) * t)) 
                          (\<lambda>x. ennreal (real n+a))"
    using lebesgue_real_scale[of "real n + a"] pos by auto
  also have "set_lebesgue_integral \<dots> {0<..} (\<lambda>t. of_real t powr (z - 1) / of_real (exp t)) = 
               set_lebesgue_integral (distr lebesgue lebesgue (\<lambda>t. (real n + a) * t)) {0<..}
                 (\<lambda>t. (real n + a) * t powr (z - 1) / exp t)" using integrable pos
    by (subst integral_density) (simp_all add: exp_of_real algebra_simps scaleR_conv_of_real)
  also have "\<dots> = ?INT (\<lambda>s. (n + a) * (of_real (n+a) * of_real s) powr (z - 1) / 
                    of_real (exp ((n+a) * s)))"
  proof (subst integral_distr)
    show "op * (real n + a) \<in> lebesgue \<rightarrow>\<^sub>M lebesgue"
      using lebesgue_measurable_scaling[of "real n + a", where ?'a = real]
      unfolding real_scaleR_def .
  next
    have "(\<lambda>x. (n+a) * (indicator {0<..} x *\<^sub>R (of_real x powr (z - 1) / of_real (exp x)))) 
             \<in> lebesgue \<rightarrow>\<^sub>M borel" using integrable by (intro borel_measurable_times) simp_all
    thus "set_borel_measurable lebesgue {0<..} 
            (\<lambda>x. of_real (n+a) * of_real x powr (z - 1) / of_real (exp x))" by simp
  qed (intro Bochner_Integration.integral_cong refl, insert pos, 
       auto simp: indicator_def zero_less_mult_iff)
  also have "\<dots> = ?INT (\<lambda>s. ((n+a) powr z) * (s powr (z - 1) / exp ((n+a) * s)))" using pos
    by (intro set_lebesgue_integral_cong refl allI impI, simp, subst powr_times_real)
       (auto simp: powr_diff)
  also have "\<dots> = (n + a) powr z * ?INT (\<lambda>s. s powr (z - 1) / exp ((n+a) * s))"
    by (subst integral_mult_right_zero [symmetric]) simp_all
  finally show "Gamma z / (of_nat n + of_real a) powr z = 
                  ?INT (\<lambda>s. s powr (z - 1) / exp ((n+a) * s))" 
    using nz by (auto simp add: field_simps)
qed

lemma
  assumes x: "x > 0" and "a > 0"
  shows   Gamma_hurwitz_zeta_aux_integral_real: 
            "Gamma x / (real n + a) powr x = 
               set_lebesgue_integral lebesgue {0<..} 
               (\<lambda>s. s powr (x - 1) / exp ((real n + a) * s))"
    and   Gamma_hurwitz_zeta_aux_integrable_real:
            "set_integrable lebesgue {0<..} (\<lambda>s. s powr (x - 1) / exp ((real n + a) * s))"
proof -
  show "set_integrable lebesgue {0<..} (\<lambda>s. s powr (x - 1) / exp ((real n + a) * s))"
    using absolutely_integrable_Gamma_integral[of "of_real x" "real n + a"]
  proof (rule Bochner_Integration.integrable_bound, goal_cases)
    case 3
    have "set_integrable lebesgue {0<..} (\<lambda>xa. complex_of_real xa powr (of_real x - 1) / 
              of_real (exp ((n + a) * xa)))"
      using assms by (intro Gamma_hurwitz_zeta_aux_integrable) auto
    also have "?this \<longleftrightarrow> integrable lebesgue
                 (\<lambda>s. complex_of_real (indicator {0<..} s *\<^sub>R (s powr (x - 1) / (exp ((n+a) * s)))))"
      by (intro Bochner_Integration.integrable_cong refl) (auto simp: powr_Reals_eq indicator_def)
    finally have "set_integrable lebesgue {0<..} (\<lambda>s. s powr (x - 1) / exp ((n+a) * s))"
      by (subst (asm) complex_of_real_integrable_eq)
    thus ?case by simp
  qed (insert assms, auto intro!: AE_I2 simp: indicator_def norm_divide norm_powr_real_powr)
  from Gamma_hurwitz_zeta_aux_integral[of "of_real x" a n] and assms
    have "of_real (Gamma x / (real n + a) powr x) = set_lebesgue_integral lebesgue {0<..} 
            (\<lambda>s. complex_of_real s powr (of_real x - 1) / of_real (exp ((n+a) * s)))" (is "_ = ?I")
      by (auto simp: Gamma_complex_of_real powr_Reals_eq)
  also have "?I = lebesgue_integral lebesgue
                    (\<lambda>s. of_real (indicator {0<..} s *\<^sub>R (s powr (x - 1) / exp ((n+a) * s))))"
    using assms by (intro Bochner_Integration.integral_cong refl) 
                   (auto simp: indicator_def powr_Reals_eq)
  also have "\<dots> = of_real (set_lebesgue_integral lebesgue {0<..} 
                    (\<lambda>s. s powr (x - 1) / exp ((n+a) * s)))"
    by (rule Bochner_Integration.integral_complex_of_real)
  finally show "Gamma x / (real n + a) powr x = set_lebesgue_integral lebesgue {0<..} 
                  (\<lambda>s. s powr (x - 1) / exp ((real n + a) * s))"
    by (subst (asm) of_real_eq_iff)
qed

theorem
  assumes "Re z > 1" and "a > (0::real)"
  shows   Gamma_times_hurwitz_zeta_integral: "Gamma z * hurwitz_zeta a z =
            (\<integral>x\<in>{0<..}. (of_real x powr (z - 1) * of_real (exp (-a*x) / (1 - exp (-x)))) \<partial>lebesgue)"
    and   Gamma_times_hurwitz_zeta_integrable:
            "set_integrable lebesgue {0<..} 
               (\<lambda>x. of_real x powr (z - 1) * of_real (exp (-a*x) / (1 - exp (-x))))"
proof -
  from assms have z: "Re z > 0" by simp
  let ?INT = "set_lebesgue_integral lebesgue {0<..} :: (real \<Rightarrow> complex) \<Rightarrow> complex"
  let ?INT' = "set_lebesgue_integral lebesgue {0<..} :: (real \<Rightarrow> real) \<Rightarrow> real"

  have 1: "complex_set_integrable lebesgue {0<..} 
            (\<lambda>x. of_real x powr (z - 1) / of_real (exp ((real n + a) * x)))" for n
      by (rule Gamma_hurwitz_zeta_aux_integrable) (use assms in simp_all)
  have 2: "summable (\<lambda>n. norm (indicator {0<..} s *\<^sub>R (of_real s powr (z - 1) / 
             of_real (exp ((n + a) * s)))))" for s
  proof (cases "s > 0")
    case True
    hence "summable (\<lambda>n. norm (of_real s powr (z - 1)) * exp (-a * s) * exp (-s) ^ n)"
      using assms by (intro summable_mult summable_geometric) simp_all
    with True show ?thesis
      by (simp add: norm_mult norm_divide exp_add exp_diff
                    exp_minus field_simps exp_of_nat_mult [symmetric])
  qed simp_all
  have 3: "summable (\<lambda>n. \<integral>x. norm (indicator {0<..} x *\<^sub>R (complex_of_real x powr (z - 1) /
                            complex_of_real (exp ((n + a) * x)))) \<partial>lebesgue)"
  proof -
    have "summable (\<lambda>n. Gamma (Re z) * (real n + a) powr -Re z)"
      using assms by (intro summable_mult summable_hurwitz_zeta_real) simp_all
    also have "?this \<longleftrightarrow> summable (\<lambda>n. ?INT' (\<lambda>s. norm (of_real s powr (z - 1) / 
                                       of_real (exp ((n+a) * s)))))"
    proof (intro summable_cong always_eventually allI, goal_cases)
      case (1 n)
      have "Gamma (Re z) * (real n + a) powr -Re z = Gamma (Re z) / (real n + a) powr Re z"
        by (subst powr_minus) (simp_all add: field_simps)
      also from assms have "\<dots> = (\<integral>x\<in>{0<..}. (x powr (Re z-1) / exp ((n+a) * x)) \<partial>lebesgue)"
        by (subst Gamma_hurwitz_zeta_aux_integral_real) simp_all
      also have "\<dots> = (\<integral>xa\<in>{0<..}. norm (of_real xa powr (z-1) / of_real (exp ((n+a) * xa)))
                         \<partial>lebesgue)"
        by (intro Bochner_Integration.integral_cong refl)
           (auto simp: indicator_def norm_divide norm_powr_real_powr)
      finally show ?case .
    qed
    finally show ?thesis by simp
  qed

  have sum_eq: "(\<Sum>n. indicator {0<..} s *\<^sub>R (of_real s powr (z - 1) / of_real (exp ((n+a) * s)))) = 
                   indicator {0<..} s *\<^sub>R (of_real s powr (z - 1) * 
                     of_real (exp (-a * s) / (1 - exp (-s))))" for s
  proof (cases "s > 0")
    case True
    hence "(\<Sum>n. indicator {0..} s *\<^sub>R (of_real s powr (z - 1) / of_real (exp ((n+a) * s)))) =
             (\<Sum>n. of_real s powr (z - 1) * of_real (exp (-a * s)) * of_real (exp (-s)) ^ n)"
      by (intro suminf_cong) 
         (auto simp: exp_add exp_minus exp_of_nat_mult [symmetric] field_simps of_real_exp)
    also have "(\<Sum>n. of_real s powr (z - 1) * of_real (exp (-a * s)) * of_real (exp (-s)) ^ n) =
                 of_real s powr (z - 1) * of_real (exp (-a * s)) * (\<Sum>n. of_real (exp (-s)) ^ n)"
      using True by (intro suminf_mult summable_geometric) simp_all
    also have "(\<Sum>n. complex_of_real (exp (-s)) ^ n) = 1 / (1 - of_real (exp (-s)))"
      using True by (intro suminf_geometric) auto
    also have "of_real s powr (z - 1) * of_real (exp (-a * s)) * \<dots> = 
                 of_real s powr (z - 1) * of_real (exp (-a * s) / (1 - exp (-s)))" using \<open>a > 0\<close>
      by (auto simp add: divide_simps exp_minus)
    finally show ?thesis using True by simp
  qed simp_all

  show "set_integrable lebesgue {0<..} 
          (\<lambda>x. of_real x powr (z - 1) * of_real (exp (-a*x) / (1 - exp (-x))))"
    unfolding sum_eq [symmetric] by (intro integrable_suminf[OF _ AE_I2] 1 2 3)

  have "(\<lambda>n. ?INT (\<lambda>s. s powr (z - 1) / exp ((n+a) * s))) sums lebesgue_integral lebesgue
            (\<lambda>s. \<Sum>n. indicator {0<..} s *\<^sub>R (s powr (z - 1) / exp ((n+a) * s)))" (is "?A sums ?B")
    by (rule sums_integral[OF 1 AE_I2[OF 2] 3])
  also have "?A = (\<lambda>n. Gamma z * (n + a) powr -z)"
    using assms by (subst Gamma_hurwitz_zeta_aux_integral [symmetric]) 
                   (simp_all add: powr_minus divide_simps)
  also have "?B = ?INT (\<lambda>s. of_real s powr (z - 1) * of_real (exp (-a * s) / (1 - exp (-s))))"
    unfolding sum_eq ..
  finally have "(\<lambda>n. Gamma z * (of_nat n + of_real a) powr -z) sums
                  ?INT (\<lambda>x. of_real x powr (z - 1) * of_real (exp (-a * x) / (1 - exp (-x))))" 
    by simp
  moreover have "(\<lambda>n. Gamma z * (of_nat n + of_real a) powr -z) sums (Gamma z * hurwitz_zeta a z)"
    using assms by (intro sums_mult sums_hurwitz_zeta) simp_all
  ultimately show "Gamma z * hurwitz_zeta a z = 
                     (\<integral>x\<in>{0<..}. (of_real x powr (z - 1) * 
                        of_real (exp (-a * x) / (1 - exp (-x)))) \<partial>lebesgue)"
    by (rule sums_unique2 [symmetric])
qed

corollary
  assumes "Re z > 1"
  shows   Gamma_times_zeta_integral: "Gamma z * zeta z =
            (\<integral>x\<in>{0<..}. (of_real x powr (z - 1) / of_real (exp x - 1)) \<partial>lebesgue)" (is ?th1)
    and   Gamma_times_zeta_integrable:
            "set_integrable lebesgue {0<..} 
               (\<lambda>x. of_real x powr (z - 1) / of_real (exp x - 1))" (is ?th2)
proof -
  have *: "(\<lambda>x. indicator {0<..} x *\<^sub>R (of_real x powr (z - 1) * 
                of_real (exp (-x) / (1 - exp (-x))))) =
             (\<lambda>x. indicator {0<..} x *\<^sub>R (of_real x powr (z - 1) / of_real (exp x - 1)))"
    by (intro ext) (simp add: field_simps exp_minus indicator_def)
  from Gamma_times_hurwitz_zeta_integral [OF assms zero_less_one] and *
    show ?th1 by (simp add: zeta_def)
  from Gamma_times_hurwitz_zeta_integrable [OF assms zero_less_one] and *
    show ?th2 by (simp add: zeta_def)
qed

corollary hurwitz_zeta_integral_Gamma_def:
  assumes "Re z > 1" "a > 0"
  shows   "hurwitz_zeta a z = 
             rGamma z * (\<integral>x\<in>{0<..}. (of_real x powr (z - 1) * 
               of_real (exp (-a * x) / (1 - exp (-x)))) \<partial>lebesgue)"
proof -
  from assms have "Gamma z \<noteq> 0" 
    by (subst Gamma_eq_zero_iff) (auto elim!: nonpos_Ints_cases)
  with Gamma_times_hurwitz_zeta_integral [OF assms] show ?thesis
    by (simp add: rGamma_inverse_Gamma field_simps)
qed

corollary zeta_integral_Gamma_def:
  assumes "Re z > 1"
  shows   "zeta z =
             rGamma z * (\<integral>x\<in>{0<..}. (of_real x powr (z - 1) / of_real (exp x - 1)) \<partial>lebesgue)"
proof -
  from assms have "Gamma z \<noteq> 0" 
    by (subst Gamma_eq_zero_iff) (auto elim!: nonpos_Ints_cases)
  with Gamma_times_zeta_integral [OF assms] show ?thesis
    by (simp add: rGamma_inverse_Gamma field_simps)
qed


text \<open>
  We can now also do an analytic proof of the infinitude of primes.
\<close>
lemma primes_infinite_analytic: "infinite {p :: nat. prime p}"
proof
  -- \<open>Suppose the set of primes were finite.\<close>
  define P :: "nat set" where "P = {p. prime p}"
  assume fin: "finite P"

  -- \<open>Then the Euler product form of the $\zeta$ function ranges over a finite set,
      and since each factor is holomorphic in the positive real half-space, 
      the product is, too.\<close>
  define zeta' :: "complex \<Rightarrow> complex" 
    where "zeta' = (\<lambda>s. (\<Prod>p\<in>P. inverse (1 - 1 / of_nat p powr s)))"
  have holo: "zeta' holomorphic_on A" if "A \<subseteq> {s. Re s > 0}" for A
  proof -
    {
      fix p :: nat and s :: complex assume p: "p \<in> P" and s: "s \<in> A"
      from p have p': "real p > 1" 
        by (subst of_nat_1 [symmetric], subst of_nat_less_iff) (simp add: prime_gt_Suc_0_nat P_def)
      have "norm (of_nat p powr s) = real p powr Re s"
        by (simp add: norm_powr_real_powr)
      also have "\<dots> > real p powr 0" using p p' s that
        by (subst powr_less_cancel_iff) (auto simp: prime_gt_1_nat)
      finally have "of_nat p powr s \<noteq> 1" using p by (auto simp: P_def)
    }
    thus ?thesis by (auto simp: zeta'_def P_def intro!: holomorphic_intros)
  qed

  -- \<open>Since the Euler product expansion of $\zeta(s)$ is valid for all $s$ with
      real value at least 1, and both $\zeta(s)$ and the Euler product must 
      be equal in the positive real half-space punctured at 1 by analytic
      continuation.\<close>
  have eq: "zeta s = zeta' s" if "Re s > 0" "s \<noteq> 1" for s
  proof (rule analytic_continuation_open[of "{s. Re s > 1}" "{s. Re s > 0} - {1}" zeta zeta'])
    fix s assume s: "s \<in> {s. Re s > 1}"
    let ?f = "(\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - 1 / of_nat p powr s) else 1)"
    have "eventually (\<lambda>n. ?f n = zeta' s) sequentially"
      using eventually_ge_at_top[of "Max P"]
    proof eventually_elim
      case (elim n)
      have "P \<noteq> {}" by (auto simp: P_def intro!: exI[of _ 2])
      with elim have "P \<subseteq> {..n}" using fin by auto
      thus ?case unfolding zeta'_def
        by (intro prod.mono_neutral_cong_right) (auto simp: P_def)
    qed
    moreover from s have "?f \<longlonglongrightarrow> zeta s" by (intro euler_product_zeta) auto
    ultimately have "(\<lambda>_. zeta' s) \<longlonglongrightarrow> zeta s"
      by (rule Lim_transform_eventually)
    thus "zeta s = zeta' s" by (simp add: LIMSEQ_const_iff)
  qed (auto intro!: exI[of _ 2] open_halfspace_Re_gt connected_open_delete convex_halfspace_Re_gt 
         holomorphic_intros holo that intro: convex_connected)

  -- \<open>However, since the Euler product is holomorphic on the entire positive real
      half-space, it cannot have a pole at 1, while $\zeta(s)$ does have a pole
      at 1. Since they are equal in the punctured neighbourhood of 1, this is
      a contradiction.\<close>
  have ev: "eventually (\<lambda>s. s \<in> {s. Re s > 0} - {1}) (at 1)"
    by (auto simp: eventually_at_filter intro!: open_halfspace_Re_gt
               eventually_mono[OF eventually_nhds_in_open[of "{s. Re s > 0}"]])
  have "\<not>is_pole zeta' 1"
    by (rule not_is_pole_holomorphic [of "{s. Re s > 0}"]) (auto intro!: holo open_halfspace_Re_gt)
  also have "is_pole zeta' 1 \<longleftrightarrow> is_pole zeta 1" unfolding is_pole_def
    by (intro filterlim_cong refl eventually_mono [OF ev] eq [symmetric]) auto
  finally show False using is_pole_zeta by contradiction
qed

end
