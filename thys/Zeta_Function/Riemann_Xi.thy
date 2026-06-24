(*
    File:    Riemann_Xi.thy
    Author:  Manuel Eberl, University of Innsbruck
*)
section \<open>The Riemann $\xi$ function\<close>
theory Riemann_Xi
  imports "Zeta_Function.Zeta_Laurent_Expansion"
begin

text \<open>
  The Riemann $\xi$ function is a variant of the Riemann $\zeta$ function that is useful in
  the study of the non-trivial zeros of $\zeta$: unlike $\zeta$, it is entire, and its zeros are
  exactly the non-trivial zeros of $\zeta$ (with the same multiplicity). It also satisfies the
  particularly simple functional equation $\xi(1-s) = \xi(s)$.
\<close>

subsection \<open>Definition, zeros, and holomorphicity\<close>

text \<open>
  $\xi$ is defined as
    \[\xi(s) = \tfrac{1}{2} s(s-1) \pi^{-s/2} \Gamma\left(\tfrac{s}{2}\right) \zeta(s)\ .\]
  However, there is a subtlety hidden in this: $\zeta$ has a pole at $s = 1$ and $\Gamma(s/2)$ has
  a pole whenever $s$ is an even non-negative integer. Therefore, $\xi$ is in fact really the
  analytic continuation of the above expression and only equal to it when $s$ is not one of these
  points.
\<close>
definition riemann_xi :: "complex \<Rightarrow> complex" where
  "riemann_xi = remove_sings (\<lambda>s. 1/2 * s * (s - 1) * of_real pi powr (-s/2) * Gamma (s/2) * zeta s)"

lemma riemann_xi_conv_zeta:
  assumes "s / 2 \<notin> \<int>\<^sub>\<le>\<^sub>0" "s \<noteq> 1"
  shows   "riemann_xi s = 1/2 * s * (s - 1) * of_real pi powr (-s/2) * Gamma (s/2) * zeta s"
proof -
  define f where "f = (\<lambda>s. 1/2 * s * (s - 1) * of_real pi powr (-s/2) * Gamma (s/2) * zeta s)"
  have "f analytic_on {s}" using pi_gt_zero assms
    by (auto simp: f_def intro!: analytic_intros simp del: pi_gt_zero)
  hence "remove_sings f s = f s"
    by (rule remove_sings_at_analytic)
  thus ?thesis
    by (simp add: f_def riemann_xi_def)
qed

text \<open>
  Next, we show that the zeros of $\xi$ are exactly the non-trivial zeros of $\zeta$ 
  (with the same multiplicity). This is done simply by analysing the zeros and poles of the
  factors used in defining $\xi$ and noticing that they cancel except for the non-trivial zeros
  of $\zeta$.

  Since we consider poles to be zeros of negative multiplicity, this also directly shows that
  $\xi$ has no poles (as $\zeta$ has no poles in the critical strip).
\<close>
theorem has_zorder_riemann_xi:
  "has_zorder riemann_xi s (if Re s \<in> {0<..<1} then zorder zeta s else 0)"
proof -
  define n where "n = (if s = 1 then 1 else if s \<noteq> 0 \<and> s / 2 \<in> \<int>\<^sub>\<le>\<^sub>0 then -1 else 0 :: int)"
  have 1: "(1/2::complex) \<noteq> 0"
    by auto
  have 2: "has_zorder (\<lambda>z. complex_of_real pi powr (-z / 2)) s 0" using pi_gt_zero
    by (intro analytic_imp_has_zorder_0) (auto intro!: analytic_intros simp del: pi_gt_zero)
  have 3: "has_zorder (\<lambda>z. Gamma (z / 2)) s (if s/2 \<in> \<int>\<^sub>\<le>\<^sub>0 then -1 else 0)"
    using has_zorder_compose_scale[OF has_zorder_Gamma[OF refl], of "1/2" s] by simp
  have [simp]: "zorder zeta 0 = 0"
    by (rule zorder_eq_0I) (auto intro!: analytic_intros)
  have 4: "Re s \<notin> {0<..<1}" if "s / 2 \<in> \<int>\<^sub>\<le>\<^sub>0"
    using that by (auto elim!: nonpos_Ints_cases')
  have 5: "zorder zeta s = 0" if "Re s \<notin> {0<..<1}" "s \<noteq> 1" "s / 2 \<notin> \<int>\<^sub>\<le>\<^sub>0"
  proof (rule zorder_eq_0I)
    show "zeta s \<noteq> 0"
      using that by (auto dest!: zeta_zeroD)
  qed (auto intro!: analytic_intros simp: \<open>s \<noteq> 1\<close>)

  have has_zorder: "has_zorder riemann_xi s (zorder zeta s + n)"
    unfolding riemann_xi_def n_def by (rule zorder_intros refl 1 2 3 has_zorder_zeta)+ auto
  also have "zorder zeta s + n = (if Re s \<in> {0<..<1} then zorder zeta s else 0)"
    using 4 5 by (auto simp: n_def zorder_zeta_1 zorder_zeta_trivial_zero)
  finally show ?thesis .
qed

text \<open>
  It follows that $\xi$ is entire.
\<close>
corollary analytic_on_riemann_xi: "riemann_xi analytic_on A"
proof (intro nicely_meromorphic_without_singularities ballI)
  define f where "f = (\<lambda>s. 1/2 * s * (s - 1) * complex_of_real pi powr (-s/2) * Gamma (s/2) * zeta s)"
  have "(\<lambda>w. complex_of_real pi powr - (w / 2)) meromorphic_on A" using pi_gt_zero
    by (auto intro!: analytic_on_imp_meromorphic_on analytic_intros simp del: pi_gt_zero)
  hence mero_f: "f meromorphic_on A"
    unfolding f_def by (auto intro!: meromorphic_intros analytic_intros)
  thus "riemann_xi nicely_meromorphic_on A"
    unfolding riemann_xi_def f_def by (rule remove_sings_nicely_meromorphic)
next
  show "\<not>is_pole riemann_xi s" if s: "s \<in> A" for s
  proof -
    define n where "n = (if Re s \<in> {0<..<1} then zorder zeta s else 0)"
    have has_zorder: "has_zorder riemann_xi s n"
      unfolding n_def by (rule has_zorder_riemann_xi)
    have "zorder zeta s \<ge> 0" if "s \<noteq> 1"
    proof (rule zorder_ge_0)
      have "has_zorder zeta s (zorder zeta s)"
        by (rule has_zorder_zeta)
      thus "\<exists>\<^sub>F z in at s. zeta z \<noteq> 0"
        by (auto dest!: has_zorder_imp_eventually_nonzero intro!: eventually_frequently)
    qed (use \<open>s \<noteq> 1\<close> in \<open>auto intro!: analytic_intros\<close>)
    hence "n \<ge> 0"
      by (cases "s = 1") (auto simp: n_def)
    thus "\<not>is_pole riemann_xi s"
      using has_zorder_imp_is_pole_iff[OF has_zorder] by auto
  qed
qed

lemma analytic_on_riemann_xi' [analytic_intros]:
  "f analytic_on A \<Longrightarrow> (\<lambda>z. riemann_xi (f z)) analytic_on A"
  using analytic_on_compose[OF _ analytic_on_riemann_xi, of f A] by (simp add: o_def)

lemma holomorphic_on_riemann_xi' [holomorphic_intros]:
  "f holomorphic_on A \<Longrightarrow> (\<lambda>z. riemann_xi (f z)) holomorphic_on A"
  using holomorphic_on_compose[OF _ analytic_imp_holomorphic[OF analytic_on_riemann_xi], of f A] 
  by (simp add: o_def)

lemma riemann_xi_eq_0_iff: "riemann_xi s = 0 \<longleftrightarrow> Re s \<in> {0<..<1} \<and> zeta s = 0"
proof -
  have "riemann_xi s = 0 \<longleftrightarrow> (if Re s \<in> {0<..<1} then zorder zeta s else 0) > 0"
    using has_zorder_riemann_xi 
    by (rule has_zorder_analytic_imp_isolated_zero_iff) (auto intro!: analytic_intros)
  also have "\<dots> \<longleftrightarrow> Re s \<in> {0<..<1} \<and> zorder zeta s > 0"
    by auto
  also have "\<dots> \<longleftrightarrow> Re s \<in> {0<..<1} \<and> zeta s = 0"
    by (intro conj_cong has_zorder_analytic_imp_isolated_zero_iff [OF has_zorder_zeta , symmetric])
       (auto intro!: analytic_intros)
  finally show ?thesis .
qed


subsection \<open>Functional equation\<close>

text \<open>
  Lastly, we show that $\xi$ satisfies the particularly simple functional equation
  $\xi(1-s) = \xi(s)$. This is done by proving the statement for $s\notin\mathbb{Z}$ and then
  using analytic continuation.

  The proof is some tedious but straightforward algebra, using the reflection identities for
  $\zeta$ and $\Gamma$ as well as the Legendre duplication identity for $\Gamma$.
\<close>
theorem riemann_xi_reflect: "riemann_xi (1 - s) = riemann_xi s"
proof (rule analytic_continuation_open[where f = "\<lambda>s. riemann_xi (1 - s)"])
  show "-\<int> \<subseteq> (UNIV :: complex set)"
    by auto
  have "1/2 \<in> (-\<int> :: complex set)"
    by auto
  thus "-\<int> \<noteq> ({}  :: complex set)"
    by blast
next
  fix s :: complex assume s: "s \<in> -\<int>"
  from s have s1: "s / 2 \<notin> \<int>\<^sub>\<le>\<^sub>0"
    by (auto elim!: nonpos_Ints_cases')
  have s2: "(1 - s) / 2 \<notin> \<int>\<^sub>\<le>\<^sub>0"
  proof
    assume "(1 - s) / 2 \<in> \<int>\<^sub>\<le>\<^sub>0"
    then obtain n where "(1 - s) / 2 = -of_nat n"
      by (auto elim!: nonpos_Ints_cases')
    hence "s = of_int (2 * int n + 1)"
      by (auto simp: algebra_simps)
    also have "\<dots> \<in> \<int>"
      by auto
    finally show False
      using s by auto
  qed
  have s3: "1 - s / 2 \<notin> \<int>\<^sub>\<le>\<^sub>0"
  proof
    assume "1 - s / 2 \<in> \<int>\<^sub>\<le>\<^sub>0"
    then obtain n where "1 - s / 2 = -of_nat n"
      by (auto elim!: nonpos_Ints_cases')
    hence "s = of_int (2 * (int n + 1))"
      by (auto simp: algebra_simps)
    also have "\<dots> \<in> \<int>"
      by auto
    finally show False
      using s by auto
  qed
  have [simp]: "Gamma s \<noteq> 0"
    by (rule Gamma_nonzero) (use s in auto)
  have sin_nz: "sin (s * complex_of_real pi) \<noteq> 0"
    by (subst sin_eq_0) (use s in auto)
  have nz: "Gamma (1 - s / 2) \<noteq> 0" "Gamma (s/2) \<noteq> 0"
    using s1 s2 s3 by (auto intro!: Gamma_nonzero)

  have "riemann_xi (1 - s) = -((1 - s) * s * of_real pi powr ((s - 1) / 2) * 
          Gamma ((1 - s) / 2) * zeta (1 - s) / 2)"
    using s2 s by (subst riemann_xi_conv_zeta) auto
  also have "rGamma s * zeta (1 - s) = 2 * of_real (2 * pi) powr -s * cos (s * of_real pi / 2) * zeta s"
    by (rule zeta_reflect) (use s in auto)
  hence "zeta (1 - s) = 2 * Gamma s * of_real (2 * pi) powr -s * cos (s * of_real pi / 2) * zeta s"
    using s by (simp add: rGamma_inverse_Gamma field_simps)
  also have "(1 - s) * s * of_real pi powr ((s - 1) / 2) * Gamma ((1 - s) / 2) * \<dots> =
               2 * (1 - s) * s * (2 powr (-s) * Gamma s * Gamma ((1-s)/2)) * 
               (of_real pi powr ((s-1)/2) * of_real pi powr (-s)) * 
               cos (s * of_real pi / 2) * zeta s"
    by (simp add: powr_times_real_left)
  also have "of_real pi powr ((s-1)/2) * of_real pi powr (-s) = of_real pi powr ((s-1)/2 - s)"
    by (subst powr_add [symmetric]) auto
  also have "(s-1)/2 - s = -s/2 - 1/2"
    by (simp add: field_simps)
  also have "of_real pi powr \<dots> = of_real pi powr (-s/2) / of_real (sqrt pi)"
    by (auto simp: powr_diff simp flip: csqrt_conv_powr)
  also have "2 powr (-s) * Gamma s * Gamma ((1 - s) / 2) = rGamma (1 - s / 2) *
                    of_real (sqrt pi * pi) / sin (complex_of_real pi * s)"
  proof -
    have "Gamma ((1 - s) / 2) * Gamma ((1 - s) / 2 + 1 / 2) =
            exp ((1 - 2 * ((1 - s) / 2)) * complex_of_real (ln 2)) *
              complex_of_real (sqrt pi) * Gamma (2 * ((1 - s) / 2))"
      by (rule Gamma_legendre_duplication[of "(1-s)/2"])
         (use s1 s2 s3 in \<open>auto simp: diff_divide_distrib\<close>)
    hence "Gamma ((1 - s) / 2) * Gamma (1 - s / 2) = 2 powr s * of_real (sqrt pi) * Gamma (1 - s)"
      by (simp add: diff_divide_distrib powr_def flip: Ln_of_real)
    also have "Gamma (1 - s) = of_real pi * rGamma s / sin (complex_of_real pi * s)"
      using Gamma_reflection_complex[of s] sin_nz by (auto simp: rGamma_inverse_Gamma field_simps)
    finally show ?thesis
      using sin_nz nz by (simp add: rGamma_inverse_Gamma field_simps powr_minus)
  qed
  also have "rGamma (1 - s / 2) = Gamma (s/2) * sin (of_real pi / 2 * s) / of_real pi"
    using rGamma_reflection_complex[of "s/2"] nz by (auto simp: rGamma_inverse_Gamma field_simps)
  also have "-(2 * (1 - s) * s * (\<dots> * of_real (sqrt pi * pi) / sin (of_real pi * s)) *
               (of_real pi powr (- s / 2) / of_real (sqrt pi)) * cos (s * of_real pi / 2) * zeta s / 2) =
             1/2 * s * (s-1) * pi powr (-s/2) * Gamma (s/2) * 
               (2 * sin (pi/2 * s) * cos (pi/2 * s) / sin (pi * s)) * zeta s"
    using sin_nz by (simp add: field_simps)
  also have "2 * sin (pi/2 * s) * cos (pi/2 * s) = sin (pi * s)"
    by (subst sin_double [symmetric]) auto
  also have "sin (pi * s) / sin (pi * s) = 1"
    using sin_nz by (simp add: mult_ac)
  also have "1/2 * s * (s-1) * pi powr (-s/2) * Gamma (s/2) * 1 * zeta s = riemann_xi s"
    by (subst riemann_xi_conv_zeta) (use s1 s in auto)
  finally show "riemann_xi (1 - s) = riemann_xi s" .
qed (auto intro!: holomorphic_intros)


subsection \<open>Special values\<close>

text \<open>
  By looking at the Laurent series expansion of $\zeta(s)$ at $s = 1$, we can determine the
  value of $\xi(1)$ to be $\frac{1}{2}$.
\<close>
lemma riemann_xi_1 [simp]: "riemann_xi 1 = 1/2"
proof -
  define f where "f = (\<lambda>s. 1/2 * s * (s - 1) * of_real pi powr (-s/2) * Gamma (s/2) * zeta s)"
  have "(\<lambda>s. s * zeta (1 + s)) has_laurent_expansion (fls_X * fls_zeta_1)"
    by (intro laurent_expansion_intros)
  also have "fls_X * fls_zeta_1 = fps_to_fls (1 + fps_X * fps_pre_zeta_1)"
    by (simp add: fls_zeta_1_def field_simps fls_X_times_conv_shift fls_times_fps_to_fls)
  finally have *: "(\<lambda>s. (1 + s - 1) * zeta (1 + s)) has_laurent_expansion 
                     fps_to_fls (1 + fps_X * fps_pre_zeta_1)" by simp

  have "(\<lambda>s. (s - 1) * zeta s) \<midarrow>1 \<rightarrow> 1"
    using has_laurent_expansion_imp_tendsto[OF * fls_subdegree_fls_to_fps_gt0] by simp
  hence "(\<lambda>s. 1/2 * s * of_real pi powr (-s/2) * Gamma (s/2) * ((s-1) * zeta s)) \<midarrow>1\<rightarrow>
           (1/2 * 1 * of_real pi powr (-1/2) * Gamma (1/2) * 1)"
    using pi_gt_zero by (intro tendsto_intros) (auto simp del: pi_gt_zero)
  hence "f \<midarrow>1\<rightarrow> 1/2"
    by (simp add: f_def mult_ac Gamma_one_half_complex powr_minus flip: csqrt_conv_powr)
  hence "remove_sings f 1 = 1/2"
    by (rule remove_sings_eqI)
  thus ?thesis
    by (simp add: f_def riemann_xi_def)
qed

text \<open>
  The value of $\xi(0)$ must then be the same by symmetry.
\<close>
lemma riemann_xi_0 [simp]: "riemann_xi 0 = 1/2"
  using riemann_xi_reflect[of 1] by simp

text \<open>
  Next, we look at the situation for positive even integers. Like with the $\zeta$ function, 
  $\xi(2n)$ for $n>0$ has a closed form in the form of a rational multiple of $\pi^n$,
  namely:
  \[\xi(2n) = (-1)^{n+1} (n-\tfrac{1}{2}) B(2n) \frac{n!}{(2n)!} (4\pi)^n\]
  By symmetry, the same holds for odd negative integers.
\<close>
lemma riemann_xi_even_nat:
  assumes "n > 0"
  shows "riemann_xi (2 * of_nat n) =
           (-1) ^ (n+1) * (of_nat n - 1 / 2)  * (4*pi)^n * bernoulli (2 * n) * fact n / fact (2 * n)"
proof -
  have "2 * of_nat n \<noteq> (1::complex)"
  proof
    assume "2 * of_nat n = (1::complex)"
    hence "of_nat (2 * n) = (of_nat 1 :: complex)"
      by simp
    thus False
      unfolding of_nat_eq_iff by simp
  qed
  hence "riemann_xi (of_nat (2*n)) = of_nat n * (2 * of_nat n - 1) * of_real pi powr -of_nat n *
           Gamma (of_nat n) * zeta (2 * of_nat n)"
    using assms by (subst riemann_xi_conv_zeta) (auto simp: of_nat_in_nonpos_Ints_iff)
  also have "\<dots> = (-1)^(n+1)* (of_nat n - 1 / 2) * (of_nat n * Gamma (of_nat n)) * 2 ^ (2*n) *
                    of_real (bernoulli (2 * n) * pi ^ (2 * n)) / (of_real pi ^ n * fact (2 * n))"
    by (subst zeta_even_nat) (auto simp: divide_simps powr_minus)
  also have "of_nat n * Gamma (of_nat n) = fact n" using assms
    by (subst Gamma_plus1 [symmetric])
       (auto simp flip: Gamma_fact simp: add_ac of_nat_in_nonpos_Ints_iff)
  also have "pi ^ (2 * n) = pi ^ n * pi ^ n"
    by (subst mult.commute, subst power_mult) (simp_all add: power2_eq_square)
  also have "2 ^ (2 * n) = (4::complex) ^ n"
    by (simp add: power_mult)
  finally show ?thesis
    by simp
qed

lemma riemann_xi_neg_odd_int:
  assumes "n > 0"
  shows "riemann_xi (-2 * of_nat n + 1) =
           (-1) ^ (n+1) * (of_nat n - 1 / 2)  * (4*pi)^n * bernoulli (2 * n) * fact n / fact (2 * n)"
  using riemann_xi_reflect[of "2 * of_nat n"] riemann_xi_even_nat[of n] assms by simp

lemma riemann_xi_2: "riemann_xi 2 = pi / 6"
  using riemann_xi_even_nat[of 1] by simp

lemma riemann_xi_neg1: "riemann_xi (-1) = pi / 6"
  using riemann_xi_neg_odd_int[of 1] by simp


subsection \<open>Conjugation and behaviour on the real line\<close>

text \<open>
  $\xi$ commutes with conjugation:
\<close>
lemma riemann_xi_cnj: "riemann_xi (cnj s) = cnj (riemann_xi s)"
proof -
  have *: "riemann_xi (cnj s) = cnj (riemann_xi s)"
    if "Re s > 0" for s
  proof (cases "s = 1")
    case False
    have 1: "s / 2 \<notin> \<int>\<^sub>\<le>\<^sub>0" and 2: "cnj s / 2 \<notin> \<int>\<^sub>\<le>\<^sub>0"
      using that by (auto elim!: nonpos_Ints_cases' simp: complex_eq_iff)
    from 1 2 show ?thesis
      by (subst (1 2) riemann_xi_conv_zeta) (use that False in \<open>auto simp: cnj_Gamma cnj_powr\<close>)
  qed auto

  show ?thesis
  proof (cases "Re s > 0")
    case True
    thus ?thesis by (simp add: *)
  next
    case False
    hence "riemann_xi (cnj (1 - s)) = cnj (riemann_xi (1 - s))"
      by (intro *) auto
    thus ?thesis
      by (simp add: riemann_xi_reflect)
  qed
qed

text \<open>
  Consequently, $\xi(t)$ is real for real $t$.
\<close>
lemma riemann_xi_in_Reals: "z \<in> \<real> \<Longrightarrow> riemann_xi z \<in> \<real>"
  using riemann_xi_cnj by (metis Reals_cnj_iff)

text \<open>
  In combination with the functional equation, it also follows that $\xi(\frac{1}{2} + it)$ is real
  for real $t$. The function $s\mapsto \xi(\frac{1}{2} + is)$ is often denoted as $\Xi(s)$.
  We do not introduce a separate definition here.
\<close>
lemma riemann_xi_critical_line_in_Reals: "riemann_xi (Complex (1/2) t) \<in> \<real>"
  using riemann_xi_reflect[of "Complex (1/2) t"] riemann_xi_cnj[of "Complex (1/2) t"]
  by (simp add: Complex_eq Reals_cnj_iff)

end