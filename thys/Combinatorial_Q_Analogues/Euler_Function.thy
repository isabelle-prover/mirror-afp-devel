section \<open>Euler's function\<close>
theory Euler_Function
  imports Q_Pochhammer_Infinite "Lambert_Series.Lambert_Series"
begin

subsection \<open>Definition and basic properties\<close>

text \<open>
  Euler's $\phi$ function is closely related to the Dedekind $\eta$ function and the Jacobi
  $\vartheta$ nullwert functions. The $q$-Pochhammer symbol gives us a simple and convenient
  way to define it.
\<close>
definition euler_phi :: "'a :: {real_normed_field, banach, heine_borel} \<Rightarrow> 'a" where
  "euler_phi q = qpochhammer_inf q q"

lemma euler_phi_0 [simp]: "euler_phi 0 = 1"
  by (simp add: euler_phi_def)

lemma euler_phi_of_real: "\<bar>x\<bar> < 1 \<Longrightarrow> euler_phi (of_real x) = of_real (euler_phi x)"
  unfolding euler_phi_def by (simp add: qpochhammer_inf_of_real)

lemma abs_convergent_euler_phi:
  assumes "(q :: 'a :: real_normed_div_algebra) \<in> ball 0 1"
  shows   "abs_convergent_prod (\<lambda>n. 1 - q ^ Suc n)"
proof (rule summable_imp_abs_convergent_prod)
  show "summable (\<lambda>n. norm (1 - q ^ Suc n - 1))"
    using assms by (subst summable_Suc_iff) (auto simp: norm_power)
qed

lemma convergent_euler_phi:
  assumes "(q :: 'a :: {real_normed_field, banach}) \<in> ball 0 1"
  shows   "convergent_prod (\<lambda>n. 1 - q ^ Suc n)"
  using abs_convergent_euler_phi[OF assms] abs_convergent_prod_imp_convergent_prod by blast

lemma has_prod_euler_phi:
  "norm q < 1 \<Longrightarrow> (\<lambda>n. 1 - q ^ Suc n) has_prod euler_phi q"
  using has_prod_qpochhammer_inf[of q q] by (simp add: euler_phi_def)

lemma euler_phi_nonzero [simp]:
  assumes x: "x \<in> ball 0 1"
  shows   "euler_phi x \<noteq> 0"
  using assms by (simp add: euler_phi_def qpochhammer_inf_nonzero)

lemma euler_phi_pos_real: 
  assumes x: "\<bar>x::real\<bar> < 1"
  shows   "euler_phi x > 0"
proof (rule has_prod_pos[OF has_prod_euler_phi[of x]])
  fix n :: nat
  have "\<bar>x ^ Suc n\<bar> = \<bar>x\<bar> ^ Suc n"
    by (simp only: power_abs)
  also have "\<dots> < 1 ^ Suc n"
    by (intro power_strict_mono) (use x in auto)
  finally show "1 - x ^ Suc n > 0"
    unfolding power_one by linarith
qed (use x in auto)

lemma holomorphic_euler_phi [holomorphic_intros]:
  assumes [holomorphic_intros]: "f holomorphic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) < 1"
  shows   "(\<lambda>z. euler_phi (f z)) holomorphic_on A"
proof -
  have *: "euler_phi holomorphic_on ball 0 1"
    unfolding euler_phi_def by (intro holomorphic_intros) auto
  show ?thesis
    by (rule holomorphic_on_compose_gen[OF assms(1) *, unfolded o_def]) (use assms(2) in auto)
qed

lemma analytic_euler_phi [analytic_intros]:
  assumes [analytic_intros]: "f analytic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) < 1"
  shows   "(\<lambda>z. euler_phi (f z)) analytic_on A"
  using assms(2) by (auto intro!: analytic_intros simp: euler_phi_def)

lemma meromorphic_on_euler_phi [meromorphic_intros]:
  "f analytic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> norm (f z) < 1) \<Longrightarrow> (\<lambda>z. euler_phi (f z)) meromorphic_on A"
  unfolding euler_phi_def by (intro meromorphic_intros)

lemma continuous_on_euler_phi [continuous_intros]:
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> norm (f z) < 1"
  shows   "continuous_on A (\<lambda>z. euler_phi (f z))"
  using assms unfolding euler_phi_def by (intro continuous_intros) auto

lemma continuous_euler_phi [continuous_intros]:
  fixes a q :: "'b :: t2_space \<Rightarrow> 'a :: {real_normed_field, banach, heine_borel}"
  assumes "continuous (at x within A) f" "norm (f x) < 1"
  shows   "continuous (at x within A) (\<lambda>x. euler_phi (f x))"
  unfolding euler_phi_def by (intro continuous_intros assms)

lemma tendsto_euler_phi [tendsto_intros]:
  assumes [tendsto_intros]: "(f \<longlongrightarrow> c) F" and "norm c < 1"
  shows   "((\<lambda>x. euler_phi (f x)) \<longlongrightarrow> euler_phi c) F"
  unfolding euler_phi_def using assms by (auto intro!: tendsto_intros)

lemma uniform_limit_euler_phi:
  fixes A :: "complex set"
  assumes A: "compact A" "A \<subseteq> ball 0 1"
  shows "uniform_limit A (\<lambda>n q. \<Prod>k<n. 1 - q ^ Suc k) euler_phi sequentially"
proof -
  have "uniform_limit (A \<times> A)
          (\<lambda>n (a, q). \<Prod>k<n. 1 - a * q ^ k) (\<lambda>(a, q). qpochhammer_inf a q) sequentially"
    by (rule uniform_limit_qpochhammer_inf) (use A in \<open>auto intro!: compact_Times\<close>)
  hence "uniform_limit A (\<lambda>n q. case (q, q) of (a, q) \<Rightarrow> \<Prod>k<n. 1 - a * q ^ k) 
           (\<lambda>q. case (q,q) of (a,q) \<Rightarrow> qpochhammer_inf a q) sequentially"
    by (rule uniform_limit_compose) auto
  thus ?thesis
    by (simp add: euler_phi_def [abs_def])
qed


subsection \<open>Connection to Lambert series\<close>

text \<open>
  The Lambert series $\sum_{k=1}^\infty \frac{1}{k}\frac{q^k}{1-q^k}$ is a logarithm of
  $\frac{1}{\phi(q)}$:
\<close>
lemma euler_phi_conv_lambert_complex':
  fixes q :: complex
  assumes q: "norm q < 1"
  shows "euler_phi q = exp (-lambert (\<lambda>n. 1 / of_nat n) q)"
proof (rule has_prod_unique2)
  show "(\<lambda>n. 1 - q ^ Suc n) has_prod euler_phi q"
    by (rule has_prod_euler_phi) (use q in auto)
  show "(\<lambda>n. 1 - q ^ Suc n) has_prod exp (-lambert (\<lambda>n. 1 / of_nat n) q)"
    by (rule euler_phi_conv_lambert_complex) (use q in auto)
qed

lemma euler_phi_conv_lambert_real':
  fixes q :: real
  assumes q: "\<bar>q\<bar> < 1"
  shows "euler_phi q = exp (-lambert (\<lambda>n. 1 / real n) q)"
proof (rule has_prod_unique2)
  show "(\<lambda>n. 1 - q ^ Suc n) has_prod euler_phi q"
    by (rule has_prod_euler_phi) (use q in auto)
  show "(\<lambda>n. 1 - q ^ Suc n) has_prod exp (-lambert (\<lambda>n. 1 / real n) q)"
    by (rule euler_phi_conv_lambert_real) (use q in auto)
qed  

text \<open>
  As an application of this, we obtain the useful inequality $\phi(q) \geq -\frac{\pi^2 q}{6(1-q)}$
  for real $q\in (0,1)$.
\<close>
theorem ln_euler_phi_ge:
  fixes x :: real
  assumes x: "x \<in> {0<..<1}"
  shows "ln (euler_phi x) \<ge> -pi\<^sup>2 / 6 * x / (1 - x)"
proof -
  have lt1: "x ^ Suc n < 1" for n
    by (subst power_less_one_iff) (use x in auto)
  define t where "t = (1 - x) / x"

  have "-ln (euler_phi x) = lambert (\<lambda>n. 1 / real n) x"
    by (subst euler_phi_conv_lambert_real') (use x in auto)
  also have "lambert (\<lambda>n. 1 / real n) x \<le> pi ^ 2 / (6 * t)"
  proof (rule sums_le)
    show "(\<lambda>n. 1 / real (Suc n) * x ^ Suc n / (1 - x ^ Suc n)) sums lambert (\<lambda>n. 1 / real n) x"
      by (rule sums_lambert)
         (use lambert_conv_radius_power_int[of "-1", where ?'a = real] x 
          in  \<open>auto simp: field_simps\<close>)
  next
    have "(\<lambda>n. (x / (1 - x)) * (1 / real (Suc n) ^ 2)) sums ((x / (1 - x)) * (pi ^ 2 / 6))"
      by (intro sums_mult) (use inverse_squares_sums in auto)
    thus "(\<lambda>n. 1 / real (Suc n) ^ 2 * x / (1 - x)) sums (pi ^ 2 / (6 * t))"
      by (simp add: t_def field_simps)
  next
    fix n :: nat
    define f where "f = (\<lambda>a. a * x powr a / (1 - x powr a))"
    have *: "f (Suc n) \<le> f 1"
    proof (rule DERIV_nonpos_imp_nonincreasing[of _ _ f])
      show "real (Suc n) \<ge> 1"
        by simp
    next
      fix a assume "1 \<le> a" "a \<le> real (Suc n)"
      define f' where "f' = x powr a * (1 - x powr a + ln x * a) / (1 - x powr a) ^ 2"
      have lt1: "x powr a < 1"
        by (subst powr01_less_one) (use x \<open>a \<ge> 1\<close> in auto)
      have "(f has_real_derivative f') (at a)"
        unfolding f_def f'_def using lt1
        by (auto intro!: derivative_eq_intros simp: field_simps power2_eq_square)
      moreover have "1 + ln x * a \<le> x powr a"
        using exp_ge_add_one_self[of "ln x * a"] x by (simp add: powr_def mult_ac)
      hence "f' \<le> 0"
        unfolding f'_def using x lt1
        by (intro divide_nonpos_pos zero_less_power mult_nonneg_nonpos) auto
      ultimately show "\<exists>y. (f has_real_derivative y) (at a) \<and> y \<le> 0"
        by blast
    qed
    have "1 / real (Suc n) * x ^ Suc n / (1 - x ^ Suc n) = 1 / real (Suc n) ^ 2 * f (real (Suc n))"
      using x by (simp add: f_def power2_eq_square powr_realpow del: of_nat_Suc power_Suc)
    also have "\<dots> \<le> 1 / real (Suc n) ^ 2 * f 1"
      by (intro mult_left_mono *) (auto simp del: of_nat_Suc)
    also have "\<dots> = 1 / real (Suc n) ^ 2 * x / (1 - x)"
      using x by (simp add: f_def)
    finally show "1 / real (Suc n) * x ^ Suc n / (1 - x ^ Suc n) \<le> 
                    1 / real (Suc n) ^ 2 * x / (1 - x)" .
  qed
  also have "pi\<^sup>2 / (6 * t) = pi\<^sup>2 / 6 * x / (1 - x)"
    unfolding t_def using x by (simp add: divide_simps)
  finally show ?thesis
    using x by (simp add: t_def divide_simps)
qed


subsection \<open>Logarithmic derivative\<close>

text \<open>
  The logarithmic derivative of $\phi$ is given by the following Lambert-style series:
  \[\frac{\phi'(q)}{\phi(q)} = \sum_{k=0}^\infty (k+1) \frac{q^k}{q^{k+1}-1}\]
\<close>
lemma sums_logderiv_euler_phi:
  fixes q :: complex
  assumes q: "norm q < 1"
  shows   "(\<lambda>k. of_nat (Suc k) * q ^ k / (q ^ Suc k - 1)) sums (deriv euler_phi q / euler_phi q)"
proof -
  from q obtain r where r: "norm q < r" "r < 1"
    using dense by blast

  have "(\<lambda>k. deriv (\<lambda>q. 1 - q ^ Suc k) q / (1 - q ^ Suc k)) sums (deriv euler_phi q / euler_phi q)"
  proof (rule logderiv_prodinf_complex_uniform_limit)
    show "open (ball 0 r :: complex set)" "q \<in> ball 0 r"
      using q r by auto
  next
    have "uniform_limit (cball 0 r :: complex set) (\<lambda>n x. \<Prod>k<n. 1 - x ^ Suc k) euler_phi sequentially"
      by (rule uniform_limit_euler_phi) (use r in auto)
    thus "uniform_limit (ball 0 r :: complex set) (\<lambda>n x. \<Prod>k<n. 1 - x ^ Suc k) euler_phi sequentially"
      by (rule uniform_limit_on_subset) auto
  qed (use q in \<open>auto intro!: holomorphic_intros\<close>)
  also have "(\<lambda>k. deriv (\<lambda>q. 1 - q ^ Suc k) q / (1 - q ^ Suc k)) =
               (\<lambda>k. of_nat (Suc k) * q ^ k / (q ^ Suc k - 1))"
  proof
    fix k :: nat
    have "deriv (\<lambda>q. 1 - q ^ Suc k) q = -(of_nat (k+1) * q ^ k)"
      by (auto intro!: DERIV_imp_deriv derivative_eq_intros simp del: power_Suc)
    thus "deriv (\<lambda>q. 1 - q ^ Suc k) q / (1 - q ^ Suc k) = of_nat (Suc k) * q ^ k / (q ^ Suc k - 1)"
      by (simp add: divide_simps del: power_Suc) (auto simp: algebra_simps)?
  qed
  finally show ?thesis .
qed

lemma deriv_euler_phi_aux:
  fixes q :: complex
  assumes q: "norm q < 1"
  shows   "q * deriv euler_phi q = -lambert of_nat q * euler_phi q"
proof -
  have "(\<lambda>k. of_nat (Suc k) * q ^ Suc k / (1 - q ^ (Suc k))) sums lambert of_nat q"
    by (rule sums_lambert)
       (use q lambert_conv_radius_power_of_nat[of 1, where ?'a = complex] in auto)
  hence "(\<lambda>k. -(of_nat (Suc k) * q ^ Suc k / (1 - q ^ (Suc k)))) sums 
           (-lambert of_nat q)"
    by (intro sums_minus)
  also have "(\<lambda>k. -(of_nat (Suc k) * q ^ Suc k / (1 - q ^ (Suc k)))) =
             (\<lambda>k. q * (of_nat (Suc k) * q ^ k / (q ^ (Suc k) - 1)))"
    using q by (auto simp: fun_eq_iff divide_simps) (auto simp: algebra_simps)?
  finally have "(\<lambda>k. q * (of_nat (Suc k) * q ^ k / (q ^ (Suc k) - 1))) sums (-lambert of_nat q)" .

  moreover have "(\<lambda>k. q * (of_nat (Suc k) * q ^ k / (q ^ Suc k - 1))) sums 
                   (q * (deriv euler_phi q / euler_phi q))"
    by (intro sums_mult sums_logderiv_euler_phi) (fact q)
  ultimately have "-lambert of_nat q = q * (deriv euler_phi q / euler_phi q)"
    using sums_unique2 by blast
  thus ?thesis
    using q by (simp add: field_simps)
qed

theorem deriv_euler_phi:
  fixes q :: complex
  assumes q: "norm q < 1" "q \<noteq> 0"
  shows   "deriv euler_phi q = -lambert of_nat q * euler_phi q / q"
  using deriv_euler_phi_aux[of q] assms by (simp add: field_simps)

end