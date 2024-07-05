theory PNT_Remainder_Library
imports
  "PNT_Notation"
begin
unbundle pnt_notation
section \<open>Auxiliary library for prime number theorem\<close>

subsection \<open>Zeta function\<close>

lemma pre_zeta_1_bound:
  assumes "0 < Re s"
  shows "\<parallel>pre_zeta 1 s\<parallel> \<le> \<parallel>s\<parallel> / Re s"
proof -
  have "\<parallel>pre_zeta 1 s\<parallel> \<le> \<parallel>s\<parallel> / (Re s * 1 powr Re s)"
    by (rule pre_zeta_bound') (use assms in auto)
  also have "\<dots> = \<parallel>s\<parallel> / Re s" by auto
  finally show ?thesis .
qed

lemma zeta_pole_eq:
  assumes "s \<noteq> 1"
  shows "zeta s = pre_zeta 1 s + 1 / (s - 1)"
proof -
  have "zeta s - 1 / (s - 1) = pre_zeta 1 s" by (intro zeta_minus_pole_eq assms)
  thus ?thesis by (simp add: field_simps)
qed

definition zeta' where "zeta' s \<equiv> pre_zeta 1 s * (s - 1) + 1"

lemma zeta'_analytic:
  "zeta' analytic_on UNIV"
  unfolding zeta'_def by (intro analytic_intros) auto

lemma zeta'_analytic_on [analytic_intros]:
  "zeta' analytic_on A" using zeta'_analytic analytic_on_subset by auto

lemma zeta'_holomorphic_on [holomorphic_intros]:
  "zeta' holomorphic_on A" using zeta'_analytic_on by (intro analytic_imp_holomorphic)

lemma zeta_eq_zeta':
  "zeta s = zeta' s / (s - 1)"
proof (cases "s = 1")
  case True thus ?thesis using zeta_1 unfolding zeta'_def by auto
next
  case False with zeta_pole_eq [OF this]
  show ?thesis unfolding zeta'_def by (auto simp add: field_simps)
qed

lemma zeta'_1 [simp]: "zeta' 1 = 1" unfolding zeta'_def by auto

lemma zeta_eq_zero_iff_zeta':
  shows "s \<noteq> 1 \<Longrightarrow> zeta' s = 0 \<longleftrightarrow> zeta s = 0"
  using zeta_eq_zeta' [of s] by auto

lemma zeta'_eq_zero_iff:
  shows "zeta' s = 0 \<longleftrightarrow> zeta s = 0 \<and> s \<noteq> 1"
  by (cases "s = 1", use zeta_eq_zero_iff_zeta' in auto)

lemma zeta_eq_zero_iff:
  shows "zeta s = 0 \<longleftrightarrow> zeta' s = 0 \<or> s = 1"
  by (subst zeta'_eq_zero_iff, use zeta_1 in auto)

subsection \<open>Logarithm derivatives\<close>

definition "logderiv f x \<equiv> deriv f x / f x"
definition log_differentiable
  (infixr "(log'_differentiable)" 50)
where
  "f log_differentiable x \<equiv> (f field_differentiable (at x)) \<and> f x \<noteq> 0"

lemma logderiv_prod':
  fixes f :: "'n \<Rightarrow> 'f \<Rightarrow> 'f :: real_normed_field"
  assumes fin: "finite I"
    and lder: "\<And>i. i \<in> I \<Longrightarrow> f i log_differentiable a"
  shows "logderiv (\<lambda>x. \<Prod>i\<in>I. f i x) a = (\<Sum>i\<in>I. logderiv (f i) a)" (is ?P)
    and "(\<lambda>x. \<Prod>i\<in>I. f i x) log_differentiable a" (is ?Q)
proof -
  let ?a = "\<lambda>i. deriv (f i) a"
  let ?b = "\<lambda>i. \<Prod>j\<in>I - {i}. f j a"
  let ?c = "\<lambda>i. f i a"
  let ?d = "\<Prod>i\<in>I. ?c i"
  have der: "\<And>i. i \<in> I \<Longrightarrow> f i field_differentiable (at a)"
    and nz: "\<And>i. i \<in> I \<Longrightarrow> f i a \<noteq> 0"
    using lder unfolding log_differentiable_def by auto
  have 1: "(*) x = (\<lambda>y. y * x)" for x :: 'f by auto
  have "((\<lambda>x. \<Prod>i\<in>I. f i x) has_derivative
    (\<lambda>y. \<Sum>i\<in>I. ?a i * y *?b i)) (at a within UNIV)"
    by (rule has_derivative_prod, fold has_field_derivative_def)
       (rule field_differentiable_derivI, elim der)
  hence 2: "DERIV (\<lambda>x. \<Prod>i\<in>I. f i x) a :> (\<Sum>i\<in>I. ?a i * ?b i)"
    unfolding has_field_derivative_def
    by (simp add: sum_distrib_left [symmetric] mult_ac)
       (subst 1, blast)
  have prod_nz: "(\<Prod>i\<in>I. ?c i) \<noteq> 0"
    using prod_zero_iff nz fin by auto
  have mult_cong: "b = c \<Longrightarrow> a * b = a * c" for a b c :: real by auto
  have "logderiv (\<lambda>x. \<Prod>i\<in>I. f i x) a = deriv (\<lambda>x. \<Prod>i\<in>I. f i x) a / ?d"
    unfolding logderiv_def by auto
  also have "\<dots> = (\<Sum>i\<in>I. ?a i * ?b i) / ?d"
    using 2 DERIV_imp_deriv by auto
  also have "\<dots> = (\<Sum>i\<in>I. ?a i * (?b i / ?d))"
    by (auto simp add: sum_divide_distrib)
  also have "\<dots> = (\<Sum>i\<in>I. logderiv (f i) a)"
  proof -
    have "\<And>a b c :: 'f. a \<noteq> 0 \<Longrightarrow> a = b * c \<Longrightarrow> c / a = inverse b"
      by (auto simp add: field_simps)
    moreover have "?d = ?c i * ?b i" if "i \<in> I" for i
      by (intro prod.remove that fin)
    ultimately have "?b i / ?d = inverse (?c i)" if "i \<in> I" for i
      using prod_nz that by auto
    thus ?thesis unfolding logderiv_def using 2
      by (auto simp add: divide_inverse intro: sum.cong)
  qed
  finally show ?P .
  show ?Q by (auto
    simp: log_differentiable_def field_differentiable_def
    intro!: 2 prod_nz)
qed

lemma logderiv_prod:
  fixes f :: "'n \<Rightarrow> 'f \<Rightarrow> 'f :: real_normed_field"
  assumes lder: "\<And>i. i \<in> I \<Longrightarrow> f i log_differentiable a"
  shows "logderiv (\<lambda>x. \<Prod>i\<in>I. f i x) a = (\<Sum>i\<in>I. logderiv (f i) a)" (is ?P)
    and "(\<lambda>x. \<Prod>i\<in>I. f i x) log_differentiable a" (is ?Q)
proof -
  consider "finite I" | "infinite I" by auto
  hence "?P \<and> ?Q"
  proof cases
    assume fin: "finite I"
    show ?thesis by (auto intro: logderiv_prod' lder fin)
  next
    assume nfin: "infinite I"
    show ?thesis using nfin
      unfolding logderiv_def log_differentiable_def by auto
  qed
  thus ?P ?Q by auto
qed

lemma logderiv_mult:
  assumes "f log_differentiable a"
    and "g log_differentiable a"
  shows "logderiv (\<lambda>z. f z * g z) a = logderiv f a + logderiv g a" (is ?P)
    and "(\<lambda>z. f z * g z) log_differentiable a" (is ?Q)
proof -
  have "logderiv (\<lambda>z. f z * g z) a
      = logderiv (\<lambda>z. \<Prod>i\<in>{0, 1}. ([f, g]!i) z) a" by auto
  also have "\<dots> = (\<Sum>i\<in>{0, 1}. logderiv ([f, g]!i) a)"
    by (rule logderiv_prod(1), use assms in auto)
  also have "\<dots> = logderiv f a + logderiv g a"
    by auto
  finally show ?P .
  have "(\<lambda>z. \<Prod>i\<in>{0, 1}. ([f, g]!i) z) log_differentiable a"
    by (rule logderiv_prod(2), use assms in auto)
  thus ?Q by auto
qed

lemma logderiv_cong_ev:
  assumes "\<forall>\<^sub>F x in nhds x. f x = g x"
    and "x = y"
  shows "logderiv f x = logderiv g y"
proof -
  have "deriv f x = deriv g y" using assms by (rule deriv_cong_ev)
  moreover have "f x = g y" using assms by (auto intro: eventually_nhds_x_imp_x)
  ultimately show ?thesis unfolding logderiv_def by auto
qed

lemma logderiv_linear:
  assumes "z \<noteq> a"
  shows "logderiv (\<lambda>w. w - a) z = 1 / (z - a)"
    and "(\<lambda>w. w - z) log_differentiable a"
unfolding logderiv_def log_differentiable_def
  using assms by (auto simp add: derivative_intros)

lemma deriv_shift:
  assumes "f field_differentiable at (a + x)"
  shows "deriv (\<lambda>t. f (a + t)) x = deriv f (a + x)"
proof -
  have "deriv (f \<circ> (\<lambda>t. a + t)) x = deriv f (a + x)"
    by (subst deriv_chain) (auto intro: assms)
  thus ?thesis unfolding comp_def by auto
qed

lemma logderiv_shift:
  assumes "f field_differentiable at (a + x)"
  shows "logderiv (\<lambda>t. f (a + t)) x = logderiv f (a + x)"
  unfolding logderiv_def by (subst deriv_shift) (auto intro: assms)

lemma logderiv_inverse:
  assumes "x \<noteq> 0"
  shows "logderiv (\<lambda>x. 1 / x) x = - 1 / x"
proof -
  have "deriv (\<lambda>x. 1 / x) x = (deriv (\<lambda>x. 1) x * x - 1 * deriv (\<lambda>x. x) x) / x\<^sup>2"
    by (rule deriv_divide) (use assms in auto)
  hence "deriv (\<lambda>x. 1 / x) x = - 1 / x\<^sup>2" by auto
  thus ?thesis unfolding logderiv_def power2_eq_square using assms by auto
qed

lemma logderiv_zeta_eq_zeta':
  assumes "s \<noteq> 1" "zeta s \<noteq> 0"
  shows "logderiv zeta s = logderiv zeta' s - 1 / (s - 1)"
proof -
  have "logderiv zeta s = logderiv (\<lambda>s. zeta' s * (1 / (s - 1))) s"
    using zeta_eq_zeta' by auto metis
  also have "\<dots> = logderiv zeta' s + logderiv (\<lambda>s. 1 / (s - 1)) s"
  proof -
    have "zeta' s \<noteq> 0" using assms zeta_eq_zero_iff_zeta' by auto
    hence "zeta' log_differentiable s"
      unfolding log_differentiable_def
      by (intro conjI analytic_on_imp_differentiable_at)
         (rule zeta'_analytic, auto)
    moreover have "(\<lambda>z. 1 / (z - 1)) log_differentiable s"
      unfolding log_differentiable_def using assms(1)
      by (intro derivative_intros conjI, auto)
    ultimately show ?thesis using assms by (intro logderiv_mult(1))
  qed
  also have "logderiv (\<lambda>s. 1 / (- 1 + s)) s = logderiv (\<lambda>s. 1 / s) (- 1 + s)"
    by (rule logderiv_shift) (insert assms(1), auto intro: derivative_intros)
  moreover have "\<dots> = - 1 / (- 1 + s)"
    by (rule logderiv_inverse) (use assms(1) in auto)
  ultimately show ?thesis by auto
qed

lemma analytic_logderiv [analytic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 0"
  shows "(\<lambda>s. logderiv f s) analytic_on A"
  using assms unfolding logderiv_def by (intro analytic_intros)

subsection \<open>Lemmas of integration and integrability\<close>

lemma powr_has_integral:
  fixes a b w :: real
  assumes Hab: "a \<le> b" and Hw: "w > 0 \<and> w \<noteq> 1"
  shows "((\<lambda>x. w powr x) has_integral w powr b / ln w - w powr a / ln w) {a..b}"
proof (rule fundamental_theorem_of_calculus)
  show "a \<le> b" using assms by auto
next
  fix x assume "x \<in> {a..b}"
  have "((\<lambda>x. exp (x * ln w)) has_vector_derivative exp (x * ln w) * (1 * ln w)) (at x within {a..b})"
    by (subst has_real_derivative_iff_has_vector_derivative [symmetric])
       (rule derivative_intros DERIV_cmult_right)+
  hence "((powr) w has_vector_derivative w powr x * ln w) (at x within {a..b})"
    unfolding powr_def using Hw by (simp add: DERIV_fun_exp)
  moreover have "ln w \<noteq> 0" using Hw by auto
  ultimately show "((\<lambda>x. w powr x / ln w) has_vector_derivative w powr x) (at x within {a..b})"
    by (auto intro: derivative_eq_intros)
qed

lemma powr_integrable:
  fixes a b w :: real
  assumes Hab: "a \<le> b" and Hw: "w > 0 \<and> w \<noteq> 1"
  shows "(\<lambda>x. w powr x) integrable_on {a..b}"
by (rule has_integral_integrable, rule powr_has_integral)
   (use assms in auto)

lemma powr_integral_bound_gt_1:
  fixes a b w :: real
  assumes Hab: "a \<le> b" and Hw: "w > 1"
  shows "integral {a..b} (\<lambda>x. w powr x) \<le> w powr b / \<bar>ln w\<bar>"
proof -
  have "integral {a..b} (\<lambda>x. w powr x) = w powr b / ln w - w powr a / ln w"
    by (intro integral_unique powr_has_integral) (use assms in auto)
  also have "\<dots> \<le> w powr b / \<bar>ln w\<bar>" using Hw by auto
  finally show ?thesis .
qed

lemma powr_integral_bound_lt_1:
  fixes a b w :: real
  assumes Hab: "a \<le> b" and Hw: "0 < w \<and> w < 1"
  shows "integral {a..b} (\<lambda>x. w powr x) \<le> w powr a / \<bar>ln w\<bar>"
proof -
  have "integral {a..b} (\<lambda>x. w powr x) = w powr b / ln w - w powr a / ln w"
    by (intro integral_unique powr_has_integral) (use assms in auto)
  also have "\<dots> \<le> w powr a / \<bar>ln w\<bar>" using Hw by (auto simp add: field_simps)
  finally show ?thesis .
qed

lemma set_integrableI_bounded:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "A \<in> sets M
  \<Longrightarrow> (\<lambda>x. indicator A x *\<^sub>R f x) \<in> borel_measurable M
  \<Longrightarrow> emeasure M A < \<infinity>
  \<Longrightarrow> (AE x in M. x \<in> A \<longrightarrow> norm (f x) \<le> B)
  \<Longrightarrow> set_integrable M A f"
unfolding set_integrable_def
  by (rule integrableI_bounded_set[where A=A]) auto

lemma integrable_cut':
  fixes a b c :: real and f :: "real \<Rightarrow> real"
  assumes "a \<le> b" "b \<le> c"
  and Hf: "\<And>x. a \<le> x \<Longrightarrow> f integrable_on {a..x}"
  shows "f integrable_on {b..c}"
proof -
  have "a \<le> c" using assms by linarith
  hence "f integrable_on {a..c}" by (rule Hf)
  thus ?thesis by
    (rule integrable_subinterval_real)
    (subst subset_iff, (subst atLeastAtMost_iff)+,
    blast intro: \<open>a \<le> b\<close> order_trans [of a b])
qed

lemma integration_by_part':
  fixes a b :: real
    and f g :: "real \<Rightarrow> 'a :: {real_normed_field, banach}"
    and f' g' :: "real \<Rightarrow> 'a"
  assumes "a \<le> b"
    and "\<And>x. x \<in> {a..b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
    and "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
    and int: "(\<lambda>x. f x * g' x) integrable_on {a..b}"
  shows "((\<lambda>x. f' x * g x) has_integral
    f b * g b - f a * g a - integral{a..b} (\<lambda>x. f x * g' x)) {a..b}"
proof -
  define prod where "prod \<equiv> (*) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  define y where "y \<equiv> f b * g b - f a * g a - integral{a..b} (\<lambda>x. f x * g' x)"
  have 0: "bounded_bilinear prod" unfolding prod_def
    by (rule bounded_bilinear_mult)
  have 1: "((\<lambda>x. f x * g' x) has_integral f b * g b - f a * g a - y) {a..b}"
  using y_def and int and integrable_integral by auto
  note 2 = integration_by_parts
    [where y = y and prod = prod, OF 0, unfolded prod_def]
  have "continuous_on {a..b} f" "continuous_on {a..b} g"
    by (auto intro: has_vector_derivative_continuous
                    has_vector_derivative_at_within assms
             simp: continuous_on_eq_continuous_within)
  with assms and 1 show ?thesis by (fold y_def, intro 2) auto
qed

lemma integral_bigo:
  fixes a :: real and f g :: "real \<Rightarrow> real"
  assumes f_bound: "f \<in> O(g)"
    and Hf:  "\<And>x. a \<le> x \<Longrightarrow> f integrable_on {a..x}"
    and Hf': "\<And>x. a \<le> x \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar>) integrable_on {a..x}"
    and Hg': "\<And>x. a \<le> x \<Longrightarrow> (\<lambda>x. \<bar>g x\<bar>) integrable_on {a..x}"
  shows "(\<lambda>x. integral{a..x} f) \<in> O(\<lambda>x. 1 + integral{a..x} (\<lambda>x. \<bar>g x\<bar>))"
proof -
  from \<open>f \<in> O(g)\<close> obtain c where
    "\<forall>\<^sub>F x in at_top. \<bar>f x\<bar> \<le> c * \<bar>g x\<bar>" and Hc: "c \<ge> 0"
    unfolding bigo_def by auto
  then obtain N' :: real where asymp: "\<And>n. n \<ge> N' \<Longrightarrow> \<bar>f n\<bar> \<le> c * \<bar>g n\<bar>"
    by (subst (asm) eventually_at_top_linorder) (blast)
  define N where "N \<equiv> max a N'"
  define I where "I \<equiv> \<bar>integral {a..N} f\<bar>"
  define c' where "c' \<equiv> max I c"
  have "\<And>x. N \<le> x \<Longrightarrow> \<bar>integral {a..x} f\<bar>
      \<le> c' * \<bar>1 + integral {a..x} (\<lambda>x. \<bar>g x\<bar>)\<bar>"
  proof -
    fix x :: real
    assume 1: "N \<le> x"
    define J where "J \<equiv> integral {a..x} (\<lambda>x. \<bar>g x\<bar>)"
    have 2: "a \<le> N" unfolding N_def by linarith
    hence 3: "a \<le> x" using 1 by linarith
    have nnegs: "0 \<le> I" "0 \<le> J"
      unfolding I_def J_def using 1 2 Hg' by (auto intro!: integral_nonneg)
    hence abs_eq: "\<bar>I\<bar> = I" "\<bar>J\<bar> = J"
      using nnegs by simp+
    have "int\<bar>f\<bar>": "(\<lambda>x. \<bar>f x\<bar>) integrable_on {N..x}"
      using 2 1 Hf' by (rule integrable_cut')
    have "intf": "f integrable_on {N..x}"
      using 2 1 Hf by (rule integrable_cut')
    have "\<And>x. a \<le> x \<Longrightarrow> (\<lambda>x. c * \<bar>g x\<bar>) integrable_on {a..x}"
      by (blast intro: Hg' integrable_cmul [OF Hg', simplified])
    hence "intc\<bar>g\<bar>": "(\<lambda>x. c * \<bar>g x\<bar>) integrable_on {N..x}"
      using 2 1 by (blast intro: integrable_cut')
    have "\<bar>integral {a..x} f\<bar> \<le> I + \<bar>integral {N..x} f\<bar>"
      unfolding I_def
      by (subst Henstock_Kurzweil_Integration.integral_combine
          [OF 2 1 Hf [of x], THEN sym])
         (rule 3, rule abs_triangle_ineq)
    also have "\<dots> \<le> I + integral {N..x} (\<lambda>x. \<bar>f x\<bar>)"
    proof -
      note integral_norm_bound_integral [OF "intf" "int\<bar>f\<bar>"]
      then have "\<bar>integral {N..x} f\<bar> \<le> integral {N..x} (\<lambda>x. \<bar>f x\<bar>)" by auto
      then show ?thesis by linarith
    qed
    also have "\<dots> \<le> I + c * integral {N..x} (\<lambda>x. \<bar>g x\<bar>)"
    proof -
      have 1: "N' \<le> N" unfolding N_def by linarith
      hence "\<And>y :: real. N \<le> y \<Longrightarrow> \<bar>f y\<bar> \<le> c * \<bar>g y\<bar>"
      proof -
        fix y :: real
        assume "N \<le> y"
        thus "\<bar>f y\<bar> \<le> c * \<bar>g y\<bar>"
          by (rule asymp [OF order_trans [OF 1]])
      qed
      hence "integral {N..x} (\<lambda>x. \<bar>f x\<bar>) \<le> integral {N..x} (\<lambda>x. c * \<bar>g x\<bar>)"
        by (rule integral_le [OF "int\<bar>f\<bar>" "intc\<bar>g\<bar>"]) simp
      thus ?thesis by simp
    qed
    also have "\<dots> \<le> I + c * integral {a..x} (\<lambda>x. \<bar>g x\<bar>)"
    proof -
      note Henstock_Kurzweil_Integration.integral_combine [OF 2 1 Hg' [OF 3]]
      moreover have "0 \<le> integral {a..N} (\<lambda>x. \<bar>g x\<bar>)"
        by (metis abs_ge_zero Hg' 2 integral_nonneg)
      ultimately show ?thesis
        using Hc by (simp add: landau_omega.R_mult_left_mono)
    qed
    also have "\<dots> \<le> c' + c' * integral {a..x} (\<lambda>x. \<bar>g x\<bar>)"
      unfolding c'_def using Hc
      by (auto intro!: add_mono mult_mono integral_nonneg Hg' 3)
    finally show "\<bar>integral {a..x} f\<bar>
      \<le> c' * \<bar>1 + integral {a..x} (\<lambda>x. \<bar>g x\<bar>)\<bar>"
      by (simp add: integral_nonneg Hg' 3 field_simps)
  qed
  note 0 = this
  show ?thesis proof (rule eventually_mono [THEN bigoI])
    show "\<forall>\<^sub>Fx in at_top. N \<le> x" by simp
    show "\<And>x. N \<le> x \<Longrightarrow>
      \<parallel>integral {a..x} f\<parallel> \<le> c' * \<parallel>1 + integral {a..x} (\<lambda>x. \<bar>g x\<bar>)\<parallel>"
      by (auto intro: 0)
  qed
qed

lemma integral_linepath_same_Re:
  assumes Ha: "Re a = Re b"
    and Hb: "Im a < Im b"
    and Hf: "(f has_contour_integral x) (linepath a b)"
  shows "((\<lambda>t. f (Complex (Re a) t) * \<i>) has_integral x) {Im a..Im b}"
proof -
  define path where "path \<equiv> linepath a b"
  define c d e g where "c \<equiv> Re a" and "d \<equiv> Im a" and "e \<equiv> Im b" and "g \<equiv> e - d"
  hence [simp]: "a = Complex c d" "b = Complex c e" by auto (subst Ha, auto)
  have hg: "0 < g" unfolding g_def using Hb by auto
  have [simp]: "a *\<^sub>R z = a * z" for a and z :: complex by (rule complex_eqI) auto
  have "((\<lambda>t. f (path t) * (b - a)) has_integral x) {0..1}"
    unfolding path_def by (subst has_contour_integral_linepath [symmetric]) (intro Hf)
  moreover have "path t = Complex c (g *\<^sub>R t + d)" for t
    unfolding path_def linepath_def g_def
    by (auto simp add: field_simps legacy_Complex_simps)
  moreover have "b - a = g * \<i>"
    unfolding g_def by (auto simp add: legacy_Complex_simps)
  ultimately have
    "((\<lambda>t. f (Complex c (g *\<^sub>R t + d)) * (g * \<i>)) has_integral g * x /\<^sub>R g ^ DIM(real))
     (cbox ((d - d) /\<^sub>R g) ((e - d) /\<^sub>R g))"
    by (subst (6) g_def) (auto simp add: field_simps)
  hence "((\<lambda>t. f (Complex c t) * \<i> * g) has_integral x * g) {d..e}"
    by (subst (asm) has_integral_affinity_iff)
       (auto simp add: field_simps hg)
  hence "((\<lambda>t. f (Complex c t) * \<i> * g * (1 / g)) has_integral x * g * (1 / g)) {d..e}"
    by (rule has_integral_mult_left)
  thus ?thesis using hg by auto
qed

subsection \<open>Lemmas on asymptotics\<close>

lemma eventually_at_top_linorderI':
  fixes c :: "'a :: {no_top, linorder}"
  assumes h: "\<And>x. c < x \<Longrightarrow> P x"
  shows "eventually P at_top"
proof (rule eventually_mono)
  show "\<forall>\<^sub>F x in at_top. c < x" by (rule eventually_gt_at_top)
  from h show "\<And>x. c < x \<Longrightarrow> P x" .
qed

lemma eventually_le_imp_bigo:
  assumes "\<forall>\<^sub>F x in F. \<parallel>f x\<parallel> \<le> g x"
  shows "f \<in> O[F](g)"
proof -
  from assms have "\<forall>\<^sub>F x in F. \<parallel>f x\<parallel> \<le> 1 * \<parallel>g x\<parallel>" by eventually_elim auto
  thus ?thesis by (rule bigoI)
qed

lemma eventually_le_imp_bigo':
  assumes "\<forall>\<^sub>F x in F. \<parallel>f x\<parallel> \<le> g x"
  shows "(\<lambda>x. \<parallel>f x\<parallel>) \<in> O[F](g)"
proof -
  from assms have "\<forall>\<^sub>F x in F. \<parallel>\<parallel>f x\<parallel>\<parallel> \<le> 1 * \<parallel>g x\<parallel>"
    by eventually_elim auto
  thus ?thesis by (rule bigoI)
qed

lemma le_imp_bigo:
  assumes "\<And>x. \<parallel>f x\<parallel> \<le> g x"
  shows "f \<in> O[F](g)"
  by (intro eventually_le_imp_bigo eventuallyI assms)

lemma le_imp_bigo':
  assumes "\<And>x. \<parallel>f x\<parallel> \<le> g x"
  shows "(\<lambda>x. \<parallel>f x\<parallel>) \<in> O[F](g)"
  by (intro eventually_le_imp_bigo' eventuallyI assms)

lemma exp_bigo:
  fixes f g :: "real \<Rightarrow> real"
  assumes "\<forall>\<^sub>F x in at_top. f x \<le> g x"
  shows "(\<lambda>x. exp (f x)) \<in> O(\<lambda>x. exp (g x))"
proof -
  from assms have "\<forall>\<^sub>F x in at_top. exp (f x) \<le> exp (g x)" by simp
  hence "\<forall>\<^sub>F x in at_top. \<parallel>exp (f x)\<parallel> \<le> 1 * \<parallel>exp (g x)\<parallel>" by simp
  thus ?thesis by blast
qed

lemma ev_le_imp_exp_bigo:
  fixes f g :: "real \<Rightarrow> real"
  assumes hf: "\<forall>\<^sub>F x in at_top. 0 < f x"
    and hg: "\<forall>\<^sub>F x in at_top. 0 < g x"
    and le: "\<forall>\<^sub>F x in at_top. ln (f x) \<le> ln (g x)"
  shows "f \<in> O(g)"
proof -
  have "\<forall>\<^sub>F x in at_top. exp (ln (f x)) \<le> exp (ln (g x))"
    using le by simp
  hence "\<forall>\<^sub>F x in at_top. \<parallel>f x\<parallel> \<le> 1 * \<parallel>g x\<parallel>"
    using hf hg by eventually_elim auto
  thus ?thesis by (intro bigoI)
qed

lemma smallo_ln_diverge_1:
  fixes f :: "real \<Rightarrow> real"
  assumes f_ln: "f \<in> o(ln)"
  shows "LIM x at_top. x * exp (- f x) :> at_top"
proof -
  have "(\<lambda>x. ln x - f x) \<sim>[at_top] (\<lambda>x. ln x)"
    using assms by (simp add: asymp_equiv_altdef)
  moreover have "filterlim (\<lambda>x. ln x :: real) at_top at_top"
    by real_asymp
  ultimately have "filterlim (\<lambda>x. ln x - f x) at_top at_top"
    using asymp_equiv_at_top_transfer asymp_equiv_sym by blast
  hence "filterlim (\<lambda>x. exp (ln x - f x)) at_top at_top"
    by (rule filterlim_compose[OF exp_at_top])
  moreover have "\<forall>\<^sub>F x in at_top. exp (ln x - f x) = x * exp (- f x)"
    using eventually_gt_at_top[of 0]
    by eventually_elim (auto simp: exp_diff exp_minus field_simps)
  ultimately show ?thesis
    using filterlim_cong by fast
qed

lemma ln_ln_asymp_pos: "\<forall>\<^sub>F x :: real in at_top. 0 < ln (ln x)" by real_asymp
lemma ln_asymp_pos: "\<forall>\<^sub>F x :: real in at_top. 0 < ln x" by real_asymp
lemma x_asymp_pos: "\<forall>\<^sub>F x :: real in at_top. 0 < x" by auto

subsection \<open>Lemmas of \<open>floor\<close>, \<open>ceil\<close> and \<open>nat_powr\<close>\<close>

lemma nat_le_self: "0 \<le> x \<Longrightarrow> nat (int x) \<le> x" by auto
lemma floor_le: "\<And>x :: real. \<lfloor>x\<rfloor> \<le> x" by auto
lemma ceil_ge: "\<And>x :: real. x \<le> \<lceil>x\<rceil>" by auto

lemma nat_lt_real_iff:
  "(n :: nat) < (a :: real) = (n < nat \<lceil>a\<rceil>)"
proof -
  have "n < a = (of_int n < a)" by auto
  also have "\<dots> = (n < \<lceil>a\<rceil>)" by (rule less_ceiling_iff [symmetric])
  also have "\<dots> = (n < nat \<lceil>a\<rceil>)" by auto
  finally show ?thesis .
qed

lemma nat_le_real_iff:
  "(n :: nat) \<le> (a :: real) = (n < nat (\<lfloor>a\<rfloor> + 1))"
proof -
  have "n \<le> a = (of_int n \<le> a)" by auto
  also have "\<dots> = (n \<le> \<lfloor>a\<rfloor>)" by (rule le_floor_iff [symmetric])
  also have "\<dots> = (n < \<lfloor>a\<rfloor> + 1)" by auto
  also have "\<dots> = (n < nat (\<lfloor>a\<rfloor> + 1))" by auto
  finally show ?thesis .
qed

lemma of_real_nat_power: "n nat_powr (of_real x :: complex) = of_real (n nat_powr x)" for n x
  by (subst of_real_of_nat_eq [symmetric])
     (subst powr_of_real, auto)

lemma norm_nat_power: "\<parallel>n nat_powr (s :: complex)\<parallel> = n powr (Re s)"
  unfolding powr_def by auto

subsection \<open>Elementary estimation of \<open>exp\<close> and \<open>ln\<close>\<close>

lemma ln_when_ge_3:
  "1 < ln x" if "3 \<le> x" for x :: real
proof (rule ccontr)
  assume "\<not> 1 < ln x"
  hence "exp (ln x) \<le> exp 1" by auto
  hence "x \<le> exp 1" using that by auto
  thus False using e_less_272 that by auto
qed

lemma exp_lemma_1:
  fixes x :: real
  assumes "1 \<le> x"
  shows "1 + exp x \<le> exp (2 * x)"
proof -
  let ?y = "exp x"
  have "ln 2 \<le> x" using assms ln_2_less_1 by auto
  hence "exp (ln 2) \<le> ?y" by (subst exp_le_cancel_iff)
  hence "(3 / 2)\<^sup>2 \<le> (?y - 1 / 2)\<^sup>2" by auto
  hence "0 \<le> - 5 / 4 + (?y - 1 / 2)\<^sup>2" by (simp add: power2_eq_square)
  also have "\<dots> = ?y\<^sup>2 - ?y - 1" by (simp add: power2_eq_square field_simps)
  finally show ?thesis by (simp add: exp_double)
qed

lemma ln_bound_1:
  fixes t :: real
  assumes Ht: "0 \<le> t"
  shows "ln (14 + 4 * t) \<le> 4 * ln (t + 2)"
proof -
  have "ln (14 + 4 * t) \<le> ln (14 / 2 * (t + 2))" using Ht by auto
  also have "\<dots> = ln 7 + ln (t + 2)" using Ht by (subst ln_mult) auto
  also have "\<dots> \<le> 3 * ln (t + 2) + ln (t + 2)" proof -
    have "(14 :: real) \<le> 2 powr 4" by auto
    hence "exp (ln (14 :: real)) \<le> exp (4 * ln 2)"
      unfolding powr_def by (subst exp_ln) auto
    hence "ln (14 :: real) \<le> 4 * ln 2" by (subst (asm) exp_le_cancel_iff)
    hence "ln (14 / 2 :: real) \<le> 3 * ln 2" by (subst ln_div) auto
    also have "\<dots> \<le> 3 * ln (t + 2)" using Ht by auto
    finally show ?thesis by auto
  qed
  also have "\<dots> = 4 * ln (t + 2)" by auto
  finally show ?thesis by (auto simp add: field_simps)
qed

subsection \<open>Miscellaneous lemmas\<close>

abbreviation "fds_zeta_complex :: complex fds \<equiv> fds_zeta"

lemma powr_mono_lt_1_cancel:
  fixes x a b :: real
  assumes Hx: "0 < x \<and> x < 1"
  shows "(x powr a \<le> x powr b) = (b \<le> a)"
proof -
  have "(x powr a \<le> x powr b) = ((x powr -1) powr -a \<le> (x powr -1) powr -b)" by (simp add: powr_powr)
  also have "\<dots> = (-a \<le> -b)" using Hx by (intro powr_le_cancel_iff) (auto simp add: powr_neg_one)
  also have "\<dots> = (b \<le> a)" by auto
  finally show ?thesis .
qed

abbreviation "mangoldt_real :: _ \<Rightarrow> real \<equiv> mangoldt"
abbreviation "mangoldt_complex :: _ \<Rightarrow> complex \<equiv> mangoldt"

lemma norm_fds_mangoldt_complex:
  "\<And>n. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel> = mangoldt_real n" by (simp add: fds_nth_fds)

lemma suminf_norm_bound:
  fixes f :: "nat \<Rightarrow> 'a :: banach"
  assumes "summable g"
    and "\<And>n. \<parallel>f n\<parallel> \<le> g n"
  shows "\<parallel>suminf f\<parallel> \<le> (\<Sum>n. g n)"
proof -
  have *: "summable (\<lambda>n. \<parallel>f n\<parallel>)"
    by (rule summable_comparison_test' [where g = g])
       (use assms in auto)
  hence "\<parallel>suminf f\<parallel> \<le> (\<Sum>n. \<parallel>f n\<parallel>)" by (rule summable_norm)
  also have "(\<Sum>n. \<parallel>f n\<parallel>) \<le> (\<Sum>n. g n)"
    by (rule suminf_le) (use assms * in auto)
  finally show ?thesis .
qed

lemma C\<^sub>1_gt_zero: "0 < C\<^sub>1" unfolding PNT_const_C\<^sub>1_def by auto

unbundle no_pnt_notation
end