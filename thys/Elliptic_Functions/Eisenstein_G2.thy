subsection \<open>The transformation law for $G_2$\<close>
theory Eisenstein_G2
  imports Dedekind_Eta
begin            

text \<open>
  In his book, Apostol derives the inversion law for $G_2$ in the exercises to Chapter~3 and
  remarks that it leads to a proof of the inversion law for $\eta$. Since we already have a nice
  and short proof for the inversion law for $\eta$, we instead go the other direction.
  We differentiate the inversion law for $\eta$ and easily obtain the corresponding law for $G_2$
\<close>
theorem Eisenstein_G2_minus_one_over:
  assumes t: "Im t > 0"
  shows   "Eisenstein_G 2 (-(1/t)) = t\<^sup>2 * Eisenstein_G 2 t - 2 * pi * \<i> * t"
proof -
  write dedekind_eta ("\<eta>")
  from assms have "t \<noteq> 0"
    by auto
  note [derivative_intros] = has_field_derivative_dedekind_eta
  have "deriv (\<lambda>t. \<eta> (-(1/t))) t = 
          \<i> * Eisenstein_G 2 (-(1 / t)) * \<eta> (-(1 / t)) / (4 * pi * t^2)"
    by (rule DERIV_imp_deriv) (use t in \<open>auto intro!: derivative_eq_intros simp: power2_eq_square\<close>)
  also have "\<eta> (-(1 / t)) = csqrt (- (\<i> * t)) * \<eta> t"
    by (subst dedekind_eta_minus_one_over) (use t in auto)
  finally have "\<i> * \<eta> t * csqrt (-\<i>*t) / (4 * pi * t\<^sup>2) * Eisenstein_G 2 (-(1 / t)) =
                 deriv (\<lambda>t. \<eta> (-(1/t))) t"
    by simp

  also have "deriv (\<lambda>t. \<eta> (-(1/t))) t = deriv (\<lambda>t. csqrt (-(\<i>*t)) * \<eta> t) t"
  proof (intro deriv_cong_ev refl)
    have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (nhds t)"
      by (rule eventually_nhds_in_open) (use t in \<open>auto simp: open_halfspace_Im_gt\<close>)
    thus "\<forall>\<^sub>F x in nhds t. \<eta> (- (1 / x)) = csqrt (- (\<i> * x)) * \<eta> x"
      by eventually_elim (subst dedekind_eta_minus_one_over, auto)
  qed
  also have "deriv (\<lambda>t. csqrt (- (\<i> * t)) * \<eta> t) t = 
               \<i> * \<eta> t * (Eisenstein_G 2 t * csqrt (-\<i>*t) / (4 * pi) - 1 / (2 * csqrt (-\<i>*t)))"
    by (rule DERIV_imp_deriv)
       (use t in \<open>auto intro!: derivative_eq_intros simp: complex_nonpos_Reals_iff field_simps\<close>)
  also have "1 / (2 * csqrt (-\<i>*t)) = csqrt (-\<i>*t) / (2 * (-\<i> * t))"
  proof -
    have *: "-\<i> * t = csqrt (-\<i> * t) ^ 2"
      by simp
    show ?thesis
      by (subst (3) *, unfold power2_eq_square) (use \<open>t \<noteq> 0\<close> in \<open>auto simp: field_simps\<close>)
  qed
  also have "\<i> * \<eta> t * (Eisenstein_G 2 t * csqrt (-\<i>*t) / (4 * pi) - \<dots>) =
             \<i> * \<eta> t * csqrt (-\<i> * t) / (4 * pi) * (Eisenstein_G 2 t + 2 * pi / (\<i>*t))"
    by (simp add: field_simps)
  also have "\<dots> = \<i> * \<eta> t * csqrt (-\<i> * t) / (4 * pi * t\<^sup>2) * (t\<^sup>2 * Eisenstein_G 2 t - 2 * \<i> * pi * t)"
    using \<open>t \<noteq> 0\<close> by (simp add: field_simps power2_eq_square)
  finally show "Eisenstein_G 2 (-(1 / t)) = t\<^sup>2 * Eisenstein_G 2 t - 2 * pi * \<i> * t"
    by (subst (asm) mult_cancel_left) (use t in auto)
qed

lemma Eisenstein_E2_minus_one_over:
  assumes t: "Im t > 0"
  shows   "Eisenstein_E 2 (-(1/t)) = t\<^sup>2 * Eisenstein_E 2 t - 6 * \<i> / pi * t"
  using assms
  by (simp add: Eisenstein_E_def Eisenstein_G2_minus_one_over[OF t] 
                zeta_2 power2_eq_square field_simps)

text \<open>
  In a similar fashion to the $\eta$ function, we can prove the general modular 
  transformation law for $G_2$:
\<close>
theorem Eisenstein_G2_apply_modgrp:
  assumes "Im z > 0"
  shows   "Eisenstein_G 2 (apply_modgrp f z) = 
             modgrp_factor f z ^ 2 * Eisenstein_G 2 z -
             2 * \<i> * pi * modgrp_c f * modgrp_factor f z"
  using assms
proof (induction f arbitrary: z rule: modgrp_induct_S_shift')
  case id
  thus ?case by simp
next
  case (shift f n z)
  have "Eisenstein_G 2 (apply_modgrp (f * shift_modgrp n) z) = 
          Eisenstein_G 2 (apply_modgrp f (z + of_int n))"
    using shift.prems by (subst apply_modgrp_mult) auto
  also have "\<dots> = (modgrp_factor f (z + of_int n))\<^sup>2 * Eisenstein_G 2 (z + of_int n) -
                  2 * \<i> * of_real pi * of_int (modgrp_c f) * modgrp_factor f (z + of_int n)"
    using shift.prems by (subst shift.IH) auto
  also have "Eisenstein_G 2 (z + of_int n) = Eisenstein_G 2 z"
    by (rule Eisenstein_G_plus_int)
  finally show ?case
    by simp
next
  case (S f z)
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  define a b c d where "a = modgrp_a f" "b = modgrp_b f" "c = modgrp_c f" "d = modgrp_d f"
  have det: "a * d - b * c = 1"
    using modgrp_abcd_det[of f] by (simp add: a_b_c_d_def)

  from S.prems have [simp]: "z \<noteq> 0"
    by auto
  show ?case
  proof (cases "is_singular_modgrp f")
    case False
    hence f: "f = shift_modgrp b"
      unfolding a_b_c_d_def by (rule not_singular_modgrpD)
    have *: "f * S_modgrp = modgrp b (-1) 1 0"
      unfolding f shift_modgrp_code S_modgrp_code times_modgrp_code by simp
    have [simp]: "modgrp_a (f * S_modgrp) = b"
                 "modgrp_b (f * S_modgrp) = -1"
                 "modgrp_c (f * S_modgrp) = 1"
                 "modgrp_d (f * S_modgrp) = 0"
      by (simp_all add: * modgrp_a_code modgrp_b_code modgrp_c_code modgrp_d_code)

    have "Eisenstein_G 2 (apply_modgrp (f * S_modgrp) z) = Eisenstein_G 2 (-1 / z + of_int b)"
      using S.prems by (subst apply_modgrp_mult) (auto simp: f algebra_simps)
    also have "\<dots> = Eisenstein_G 2 (-(1 / z))"
      by (subst Eisenstein_G_plus_int) auto
    also have "\<dots> = z\<^sup>2 * Eisenstein_G 2 z - 2 * pi * \<i> * z"
      by (subst Eisenstein_G2_minus_one_over) (use S.prems in auto)
    also have "\<dots> = (modgrp_factor (f * S_modgrp) z)\<^sup>2 * Eisenstein_G 2 z -
                    2 * \<i> * pi * complex_of_int (modgrp_c (f * S_modgrp)) * modgrp_factor (f * S_modgrp) z"
      by (simp add: modgrp_factor_def)
    finally show ?thesis .
  next
    case sing: True
    hence "c > 0"
      unfolding a_b_c_d_def by (meson is_singular_modgrp_altdef modgrp_cd_signs)
    have "Im (1 / z) < 0"
      using S.prems Im_one_over_neg_iff by blast
    have Arg_z: "Arg z \<in> {0<..<pi}"
      using S.prems by (simp add: Arg_lt_pi)
    have Arg_z': "Arg (-\<i> * z) = -pi/2 + Arg z"
      using Arg_z by (subst Arg_times) auto
    have [simp]: "Arg (-z) = Arg z - pi"
      using Arg_z by (subst Arg_minus) auto

    show ?thesis
    proof (cases d "0 :: int" rule: linorder_cases)
      case equal
      hence *: "\<not>is_singular_modgrp (f * S_modgrp)"
        unfolding a_b_c_d_def
        by transfer (auto simp: modgrp_rel_def split: if_splits)
      define n where "n = modgrp_b (f * S_modgrp)"
      have **: "f * S_modgrp = shift_modgrp n"
        unfolding n_def using * by (rule not_singular_modgrpD)
      show ?thesis using S.prems
        by (simp add: ** Eisenstein_G_plus_int)
    next
      case greater
      have "modgrp a b c d * S_modgrp = modgrp b (-a) d (-c)"
        unfolding shift_modgrp_code S_modgrp_code times_modgrp_code det by simp
      hence *: "f * S_modgrp = modgrp b (-a) d (-c)"
        by (simp add: a_b_c_d_def)
      have [simp]: "modgrp_a (f * S_modgrp) = b" "modgrp_b (f * S_modgrp) = -a"
                   "modgrp_c (f * S_modgrp) = d" "modgrp_d (f * S_modgrp) = -c"
        unfolding * modgrp_a_code modgrp_b_code modgrp_c_code modgrp_d_code
        using greater det by auto
      define F where "F = modgrp_factor (f * S_modgrp) z"

      have "Eisenstein_G 2 (apply_modgrp (f * S_modgrp) z) = 
              Eisenstein_G 2 (apply_modgrp f (- (1 / z)))"
        using S.prems by (subst apply_modgrp_mult) auto
      also have "\<dots> = (modgrp_factor f (- (1 / z)))\<^sup>2 * Eisenstein_G 2 (-(1 / z)) -
                      2 * \<i> * complex_of_real pi * c * modgrp_factor f (- (1 / z))"
        using S.prems by (subst S.IH) (auto simp flip: a_b_c_d_def)
      also have "modgrp_factor f (- (1 / z)) = F / z"
        unfolding F_def modgrp_factor_def by (simp add: a_b_c_d_def field_simps)
      also have "Eisenstein_G 2 (-(1 / z)) = z\<^sup>2 * Eisenstein_G 2 z - 2 * pi * \<i> * z"
        by (subst Eisenstein_G2_minus_one_over) (use S.prems in auto)
      also have "(F / z)\<^sup>2 * (z\<^sup>2 * Eisenstein_G 2 z - of_real (2 * pi) * \<i> * z) =
                 F ^ 2 * Eisenstein_G 2 z - 2 * pi * \<i> * F ^ 2 / z"
        using S.prems by (simp add: field_simps power2_eq_square modgrp_factor_def F_def)
      also have "F\<^sup>2 * Eisenstein_G 2 z - of_real (2 * pi) * \<i> * F\<^sup>2 / z -
                   2 * \<i> * of_real pi * of_int c * (F / z) =
                 F\<^sup>2 * Eisenstein_G 2 z - 2 * pi * \<i> * ((F\<^sup>2 + of_int c * F) / z)"
        by (simp add: field_simps)
      also have "(F\<^sup>2 + of_int c * F) / z = of_int (modgrp_c (f * S_modgrp)) * F"
        by (simp add: F_def modgrp_factor_def field_simps power2_eq_square flip: modgrp_c_def)
      finally show ?thesis
        unfolding F_def by simp
    next
      case less
      have "modgrp a b c d * S_modgrp = modgrp b (-a) d (-c)"
        unfolding shift_modgrp_code S_modgrp_code times_modgrp_code det by simp
      hence *: "f * S_modgrp = modgrp b (-a) d (-c)"
        by (simp add: a_b_c_d_def)
      have [simp]: "modgrp_a (f * S_modgrp) = -b" "modgrp_b (f * S_modgrp) = a"
                   "modgrp_c (f * S_modgrp) = -d" "modgrp_d (f * S_modgrp) = c"
        unfolding * modgrp_a_code modgrp_b_code modgrp_c_code modgrp_d_code
        using less det by auto
      define F where "F = modgrp_factor (f * S_modgrp) z"

      have "Eisenstein_G 2 (apply_modgrp (f * S_modgrp) z) = 
              Eisenstein_G 2 (apply_modgrp f (- (1 / z)))"
        using S.prems by (subst apply_modgrp_mult) auto
      also have "\<dots> = (modgrp_factor f (- (1 / z)))\<^sup>2 * Eisenstein_G 2 (-(1 / z)) -
                      2 * \<i> * complex_of_real pi * c * modgrp_factor f (- (1 / z))"
        using S.prems by (subst S.IH) (auto simp flip: a_b_c_d_def)
      also have "modgrp_factor f (- (1 / z)) = -F / z"
        unfolding F_def modgrp_factor_def by (simp add: a_b_c_d_def field_simps)
      also have "Eisenstein_G 2 (-(1 / z)) = z\<^sup>2 * Eisenstein_G 2 z - 2 * pi * \<i> * z"
        by (subst Eisenstein_G2_minus_one_over) (use S.prems in auto)
      also have "(-F / z)\<^sup>2 * (z\<^sup>2 * Eisenstein_G 2 z - of_real (2 * pi) * \<i> * z) =
                 F ^ 2 * Eisenstein_G 2 z - 2 * pi * \<i> * F ^ 2 / z"
        using S.prems by (simp add: field_simps power2_eq_square modgrp_factor_def F_def)
      also have "F\<^sup>2 * Eisenstein_G 2 z - of_real (2 * pi) * \<i> * F\<^sup>2 / z -
                   2 * \<i> * of_real pi * of_int c * (-F / z) =
                 F\<^sup>2 * Eisenstein_G 2 z - 2 * pi * \<i> * ((F\<^sup>2 - of_int c * F) / z)"
        by (simp add: field_simps)
      also have "(F\<^sup>2 - of_int c * F) / z = of_int (modgrp_c (f * S_modgrp)) * F"
        by (simp add: F_def modgrp_factor_def field_simps power2_eq_square flip: modgrp_c_def)
      finally show ?thesis
        unfolding F_def by simp
    qed
  qed
qed

lemma Eisenstein_E2_apply_modgrp:
  assumes "Im z > 0"
  shows   "Eisenstein_E 2 (apply_modgrp f z) = 
             modgrp_factor f z ^ 2 * Eisenstein_E 2 z - 6 * \<i> / pi * modgrp_c f * modgrp_factor f z"
  unfolding Eisenstein_E_def
  by (simp add: Eisenstein_G2_apply_modgrp[OF assms] power2_eq_square zeta_2 field_simps)


text \<open>
  We can now also easily derive the values $G_2(i) = \pi$ and $G_2(\rho) = \frac{2\pi}{\sqrt{3}}$
  using the same technique we used earlier for general $G_k$ with $k\geq 3$.
\<close>
lemma Eisenstein_G2_ii: "Eisenstein_G 2 \<i> = of_real pi"
  using Eisenstein_G2_minus_one_over[of "\<i>"] by simp

lemma Eisenstein_E2_ii: "Eisenstein_E 2 \<i> = 3 / of_real pi"
  by (simp add: Eisenstein_G2_ii Eisenstein_E_def zeta_2 power2_eq_square)

lemma Eisenstein_G2_rho: "Eisenstein_G 2 modfun_rho = of_real (2 / sqrt 3 * pi)"
proof -
  have "Eisenstein_G 2 (- (1 / modfun_rho)) = modfun_rho\<^sup>2 * Eisenstein_G 2 modfun_rho -
          complex_of_real (2 * pi) * \<i> * modfun_rho"
    using Eisenstein_G2_minus_one_over[of modfun_rho] by simp
  also have "- (1 / modfun_rho) = modfun_rho + 1"
    by (auto simp: modfun_rho_altdef field_simps simp flip: of_real_mult)
  also have "modfun_rho ^ 2 = -(modfun_rho + 1)"
    by (auto simp: modfun_rho_altdef field_simps power2_eq_square simp flip: of_real_mult)
  also have "Eisenstein_G 2 (modfun_rho + 1) = Eisenstein_G 2 modfun_rho"
    using Eisenstein_G_plus_int[of 2 "modfun_rho" 1] by simp
  finally have *: "(modfun_rho + 2) * Eisenstein_G 2 modfun_rho = -2 * \<i> * pi * modfun_rho"
    unfolding of_real_mult of_real_numeral by Groebner_Basis.algebra

  have "modfun_rho + 2 \<noteq> 0"
    by (auto simp: modfun_rho_altdef complex_eq_iff)
  hence "Eisenstein_G 2 modfun_rho = (-2 * \<i> * pi * modfun_rho) / (modfun_rho + 2)"
    by (subst * [symmetric]) auto
  also have "(-2 * \<i> * pi * modfun_rho) / (modfun_rho + 2) = of_real (2 / sqrt 3 * pi)"
    by (auto simp: complex_eq_iff modfun_rho_altdef Re_divide Im_divide field_simps)
  finally show ?thesis .
qed

lemma Eisenstein_E2_rho: "Eisenstein_E 2 modfun_rho = of_real (2 * sqrt 3 / pi)"
  by (simp add: Eisenstein_G2_rho Eisenstein_E_def zeta_2 power2_eq_square field_simps
           flip: of_real_mult[of "sqrt 3" "sqrt 3"])

end