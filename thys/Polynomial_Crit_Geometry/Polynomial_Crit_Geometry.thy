(*
  File:      Polynomial_Crit_Geometry/Polynomial_Crit_Geometry.thy
  Authors:   Manuel Eberl, University of Innsbruck
*)
theory Polynomial_Crit_Geometry
imports
  "HOL-Computational_Algebra.Computational_Algebra" 
  "HOL-Analysis.Analysis" (* for "convex" *)
  Polynomial_Crit_Geometry_Library
begin

text_raw \<open>\newpage\<close>

section \<open>The Gauß--Lucas Theorem\<close>

text \<open>
\begin{figure}\begin{center}\gausslucasexample\end{center}
\caption{Example for the Gauß--Lucas Theorem: The roots (\blackdot) and 
critical points (\whitedot) of $x^7 - 2 x^6 + x^5 +  x^4 - (1+i) x^3 -15i x^2 -4(1-i) x - 7$.\\
The critical points all lie inside the convex hull of the roots (\bluesquare).}\end{figure}
\<close>

text \<open>
  The following result is known as the \<^emph>\<open>Gauß--Lucas Theorem\<close>: 
  The critical points of a non-constant complex polynomial lie inside
  the convex hull of its roots.

  The proof is relatively straightforward by writing the polynomial in the form
  \[p(x) = \prod_{i=1}^n (x - x_i)^{a_i}\ ,\]
  from which we get the derivative
  \[p'(x) = p(x)\cdot \sum_{i=1}^n \frac{a_i}{x - x_i}\ .\]

  With some more calculations, one can then see that every root $x$ of $p'$ 
  can be written as
  \[x = \sum_{i=1}^n \frac{u_i}{U}\cdot x_i\]
  where $u_i = \frac{a_i}{|x-x_i|^2}$ and $U = \sum_{i=1}^n u_i$.
\<close>
theorem pderiv_roots_in_convex_hull:
  fixes p :: "complex poly"
  assumes "degree p \<noteq> 0"
  shows   "{z. poly (pderiv p) z = 0} \<subseteq> convex hull {z. poly p z = 0}"
proof safe
  fix z :: complex
  assume "poly (pderiv p) z = 0"
  show "z \<in> convex hull {z. poly p z = 0}"
  proof (cases "poly p z = 0")
    case True
    thus ?thesis by (simp add: hull_inc)
  next
    case False
    hence [simp]: "p \<noteq> 0" by auto
    define \<alpha> where "\<alpha> = lead_coeff p"
    have p_eq: "p = smult \<alpha> (\<Prod>z | poly p z = 0. [:- z, 1:] ^ order z p)"
      unfolding \<alpha>_def by (rule alg_closed_imp_factorization') fact
    have poly_p: "poly p = (\<lambda>w. \<alpha> * (\<Prod>z | poly p z = 0. (w - z) ^ order z p))"
      by (subst p_eq) (simp add: poly_prod fun_eq_iff)
  
    define S where "S = (\<Sum>w | poly p w = 0. of_nat (order w p) / (z - w))"
    define u :: "complex \<Rightarrow> real" where "u = (\<lambda>w. of_nat (order w p) / norm (z - w) ^ 2)"
    define U where "U = (\<Sum>w | poly p w = 0. u w)"
    have u_pos: "u w > 0" if "poly p w = 0" for w
      using that False by (auto simp: u_def order_pos_iff intro!: divide_pos_pos)
    hence "U > 0" unfolding U_def
      using assms fundamental_theorem_of_algebra[of p] False
      by (intro sum_pos poly_roots_finite) (auto simp: constant_degree)
  
    note [derivative_intros del] = has_field_derivative_prod
    note [derivative_intros] = has_field_derivative_prod'
    have "(poly p has_field_derivative poly p z * 
            (\<Sum>w | poly p w = 0. of_nat (order w p) * 
               (z - w) ^ (order w p - 1) / (z - w) ^ order w p) ) (at z)"
      (is "(_ has_field_derivative _ * ?S') _") using False
      by (subst (1 2) poly_p)
         (auto intro!: derivative_eq_intros simp: order_pos_iff mult_ac power_diff S_def)
    also have "?S' = S" unfolding S_def
    proof (intro sum.cong refl, goal_cases)
      case (1 w)
      with False have "w \<noteq> z" and "order w p > 0"
        by (auto simp: order_pos_iff)
      thus ?case by (simp add: power_diff)
    qed
    finally have "(poly p has_field_derivative poly p z * S) (at z)" .
    hence "poly (pderiv p) z = poly p z * S"
      by (rule sym[OF DERIV_unique]) (auto intro: poly_DERIV)
    with \<open>poly (pderiv p) z = 0\<close> and \<open>poly p z \<noteq> 0\<close> have "S = 0" by simp
  
    also have "S = (\<Sum>w | poly p w = 0. of_nat (order w p) * cnj z / norm (z - w) ^ 2 - 
                                        of_nat (order w p) * cnj w / norm (z - w) ^ 2)"
      unfolding S_def by (intro sum.cong refl, subst complex_div_cnj)
                         (auto simp: diff_divide_distrib ring_distribs)
    also have "\<dots> = cnj z * (\<Sum>w | poly p w = 0. u w) - (\<Sum>w | poly p w = 0. u w * cnj w)"
      by (simp add: sum_subtractf sum_distrib_left mult_ac u_def)
    finally have "cnj z * (\<Sum>w | poly p w = 0. of_real (u w)) = 
                    (\<Sum>w | poly p w = 0. of_real (u w) * cnj w)" by simp
    from arg_cong[OF this, of cnj]
    have "z * of_real U = (\<Sum>w | poly p w = 0. of_real (u w) * w)"
      unfolding complex_cnj_mult by (simp add: U_def)
    hence "z = (\<Sum>w | poly p w = 0. of_real (u w) * w) / of_real U"
      using \<open>U > 0\<close> by (simp add: divide_simps)
    also have "\<dots> = (\<Sum>w | poly p w = 0. (u w / U) *\<^sub>R w)"
      by (subst sum_divide_distrib) (auto simp: scaleR_conv_of_real)
    finally have z_eq: "z = (\<Sum>w | poly p w = 0. (u w / U) *\<^sub>R w)" .
  
    show "z \<in> convex hull {z. poly p z = 0}"
    proof (subst z_eq, rule convex_sum)
      have "(\<Sum>i\<in>{w. poly p w = 0}. u i / U) = U / U"
        by (subst (2) U_def) (simp add: sum_divide_distrib)
      also have "\<dots> = 1" using \<open>U > 0\<close> by simp
      finally show "(\<Sum>i\<in>{w. poly p w = 0}. u i / U) = 1" .
    qed (insert \<open>U > 0\<close> u_pos,
         auto simp: hull_inc intro!: divide_nonneg_pos less_imp_le poly_roots_finite)
  qed
qed

text_raw \<open>\newpage\<close>


section \<open>Jensen's Theorem\<close>

text \<open>
\begin{figure}\begin{center}\jensenexample\end{center}
\caption{Example for Jensen's Theorem: The roots (\blackdot) and critical points (\whitedot) of the polynomial $x^7 - 3x^6 + 2x^5 + 8x^4 + 10x^3 - 10x + 1$.\\
It can be seen that all the non-real critical points lie inside a Jensen disc (\bluecircle), whereas there can be real critical points that do \emph{not} lie inside a Jensen disc.
}\end{figure}
\<close>

text \<open>
  For each root \<open>w\<close> of a real polynomial \<open>p\<close>, the Jensen disc of \<open>w\<close> is the smallest disc
  containing both $w$ and $\overline{w}$, i.e.\ the disc with centre $\text{Re}(w)$ and radius
  $|\text{Im}(w)|$.

  We now show that if \<open>p\<close> is a real polynomial, every non-real critical point of \<open>p\<close> lies
  inside a Jensen disc of one of its non-real roots.
\<close>
definition jensen_disc :: "complex \<Rightarrow> complex set" where
  "jensen_disc w = cball (of_real (Re w)) \<bar>Im w\<bar>"

theorem pderiv_root_in_jensen_disc:
  fixes p :: "complex poly"
  assumes "set (coeffs p) \<subseteq> \<real>" and "degree p \<noteq> 0"
  assumes "poly (pderiv p) z = 0" and "z \<notin> \<real>"
  shows   "\<exists>w. w \<notin> \<real> \<and> poly p w = 0 \<and> z \<in> jensen_disc w"
proof (rule ccontr)
  have real_coeffs: "coeff p n \<in> \<real>" for n
    using assms(1) by (metis Reals_0 coeff_0 coeff_in_coeffs le_degree subsetD)
  define d where "d = (\<lambda>x. dist z (Re x) ^ 2 - Im x ^ 2)"

  assume *: "\<not>(\<exists>w. w \<notin> \<real> \<and> poly p w = 0 \<and> z \<in> jensen_disc w)"
  have d_pos: "d w > 0" if "poly p w = 0" "w \<notin> \<real>" for w
  proof -
    have "dist z (Re w) > \<bar>Im w\<bar>"
      using * that unfolding d_def jensen_disc_def by (auto simp: dist_commute)
    hence "dist z (Re w) ^ 2 > \<bar>Im w\<bar> ^ 2"
      by (intro power_strict_mono) auto
    thus ?thesis
      by (simp add: d_def)
  qed

  have "poly p z \<noteq> 0"
    using d_pos[of z] assms by (auto simp: d_def dist_norm cmod_power2)
  hence [simp]: "p \<noteq> 0" by auto
  define \<alpha> where "\<alpha> = lead_coeff p"
  have [simp]: "\<alpha> \<noteq> 0"
    using assms(4) by (auto simp: \<alpha>_def)
  obtain A where p_eq: "p = smult \<alpha> (\<Prod>x\<in>#A. [:-x, 1:])"
    unfolding \<alpha>_def using alg_closed_imp_factorization[of p] by auto 
  have poly_p: "poly p = (\<lambda>w. \<alpha> * (\<Prod>z\<in>#A. w - z))"
    by (subst p_eq) (simp add: poly_prod_mset fun_eq_iff)
  have [simp]: "poly p z = 0 \<longleftrightarrow> z \<in># A" for z
    by (auto simp: poly_p \<alpha>_def)

  define Apos where "Apos = filter_mset (\<lambda>w. Im w > 0) A"
  define Aneg where "Aneg = filter_mset (\<lambda>w. Im w < 0) A"
  define A0 where "A0 = filter_mset (\<lambda>w. Im w = 0) A"
  have "A = Apos + Aneg + A0"
    unfolding Apos_def Aneg_def A0_def by (induction A) auto

  have count_A: "count A w = order w p" for w
  proof -
    have "0 \<notin># {#[:- x, 1:]. x \<in># A#}"
      by auto
    hence "order w p = (\<Sum>x\<in>#A. order w [:- x, 1:])"
      by (simp add: p_eq order_smult order_prod_mset multiset.map_comp o_def)
    also have "\<dots> = (\<Sum>x\<in>#A. if w = x then 1 else 0)"
      by (simp add: order_linear_factor)
    also have "\<dots> = count A w"
      by (induction A) auto
    finally show ?thesis ..
  qed

  have "Aneg = image_mset cnj Apos"
  proof (rule multiset_eqI)
    fix x :: complex
    have "order (cnj x) (map_poly cnj p) = order x p"
      by (subst order_map_poly_cnj) auto
    also have "map_poly cnj p = p"
      using assms(1) by (metis Reals_cnj_iff map_poly_idI' subsetD)
    finally have [simp]: "order (cnj x) p = order x p" .

    have "count (image_mset cnj Apos) (cnj (cnj x)) = count Apos (cnj x)"
      by (subst count_image_mset_inj) (auto simp: inj_on_def)
    also have "\<dots> = count Aneg x"
      by (simp add: Apos_def Aneg_def count_A)
    finally show "count Aneg x = count (image_mset cnj Apos) x"
      by simp
  qed

  have [simp]: "cnj x \<in># A \<longleftrightarrow> x \<in># A" for x
  proof -
    have "cnj x \<in># A \<longleftrightarrow> poly p (cnj x) = 0"
      by simp
    also have "poly p (cnj x) = cnj (poly (map_poly cnj p) x)"
      by simp
    also have "map_poly cnj p = p"
      using real_coeffs by (intro poly_eqI) (auto simp: coeff_map_poly Reals_cnj_iff)
    finally show ?thesis
      by simp
  qed    

  define N where "N = (\<lambda>x. norm ((z - x) * (z - cnj x)))"
  have N_pos: "N x > 0" if "x \<in># A" for x
    using that \<open>poly p z \<noteq> 0\<close> by (auto simp: N_def)
  have N_nonneg: "N x \<ge> 0" and [simp]: "N x \<noteq> 0" if "x \<in># A" for x
    using N_pos[OF that] by simp_all

  text \<open>
    We show that \<^prop>\<open>(\<Sum>x\<in>#A. 1 / (z - x)) = 0\<close> (which is relatively obvious) and then 
    that the imaginary part of this sum is positive, which is a contradiction.
  \<close>
  define S where "S = (\<Sum>x\<in>#A. 1 / (z - x))"
  note [derivative_intros del] = has_field_derivative_prod_mset
  note [derivative_intros] = has_field_derivative_prod_mset'
  have "(poly p has_field_derivative poly p z * S) (at z)"
    using \<open>poly p z \<noteq> 0\<close> unfolding S_def
    by (subst (1 2) poly_p)
       (auto intro!: derivative_eq_intros simp: order_pos_iff mult_ac
          power_diff multiset.map_comp o_def)
    hence "poly (pderiv p) z = poly p z * S"
    by (rule sym[OF DERIV_unique]) (auto intro: poly_DERIV)
  with \<open>poly (pderiv p) z = 0\<close> and \<open>poly p z \<noteq> 0\<close> have "S = 0" by simp

  text \<open>
    For determining \<^term>\<open>Im S\<close>, we decompose the sum into real roots and pairs of
    conjugate and merge the sum of each pair of conjugate roots.
  \<close>
  have "Im S = (\<Sum>x\<in>#Apos. Im (1 / (z - x))) + (\<Sum>x\<in>#Aneg. Im (1 / (z - x))) + (\<Sum>x\<in>#A0. Im (1 / (z - x)))"
    by (simp add: S_def \<open>A = Apos + Aneg + A0\<close> Im_sum_mset')
  also have "Aneg = image_mset cnj Apos"
    by fact
  also have "(\<Sum>x\<in>#\<dots>. Im (1 / (z - x))) = (\<Sum>x\<in>#Apos. Im (1 / (z - cnj x)))"
    by (simp add: multiset.map_comp o_def)
  also have "(\<Sum>x\<in>#Apos. Im (1 / (z - x))) + (\<Sum>x\<in>#Apos. Im (1 / (z - cnj x))) =
             (\<Sum>x\<in>#Apos. Im (1 / (z - x) + 1 / (z - cnj x)))"
    by (subst sum_mset.distrib [symmetric]) simp_all
  also have "image_mset (\<lambda>x. Im (1 / (z - x) + 1 / (z - cnj x))) Apos =
             image_mset (\<lambda>x. - 2 * Im z * d x / N x ^ 2) Apos"
  proof (intro image_mset_cong, goal_cases)
    case (1 x)
    have "1 / (z - x) + 1 / (z - cnj x) = (2 * z - (x + cnj x)) * inverse ((z - x) * (z - cnj x))"
      using \<open>poly p z \<noteq> 0\<close> 1
      by (auto simp: divide_simps Apos_def complex_is_Real_iff simp flip: Reals_cnj_iff)
    also have "x + cnj x = 2 * Re x"
      by (subst complex_add_cnj) auto
    also have "inverse ((z - x) * (z - cnj x)) = (cnj z - cnj x) * (cnj z - x) / N x ^ 2"
      by (subst inverse_complex_altdef) (simp_all add: N_def)
    also have "Im ((2 * z - complex_of_real (2 * Re x)) * ((cnj z - cnj x) * (cnj z - x) / N x ^ 2)) =
               (-2 * Im z * (Im z ^ 2 - Im x ^ 2 + (Re x - Re z) ^ 2)) / N x ^ 2"
      by (simp add: algebra_simps power2_eq_square)
    also have "Im z ^ 2 - Im x ^ 2 + (Re x - Re z) ^ 2 = d x"
      unfolding dist_norm cmod_power2 d_def by (simp add: power2_eq_square algebra_simps)
    finally show ?case .
  qed
  also have "sum_mset \<dots> = -Im z * (\<Sum>x\<in>#Apos.  2 * d x / N x ^ 2)"
    by (subst sum_mset_distrib_left) (simp_all add: multiset.map_comp o_def mult_ac)
  also have "image_mset (\<lambda>x. Im (1 / (z - x))) A0 = image_mset (\<lambda>x. -Im z / N x) A0"
  proof (intro image_mset_cong, goal_cases)
    case (1 x)
    have [simp]: "Im x = 0"
      using 1 by (auto simp: A0_def)
    have [simp]: "cnj x = x"
      by (auto simp: complex_eq_iff)
    show "Im (1 / (z - x)) = -Im z / N x"
      by (simp add: Im_divide N_def cmod_power2 norm_power flip: power2_eq_square)
  qed
  also have "sum_mset \<dots> = -Im z * (\<Sum>x\<in>#A0. 1 / N x)"
    by (simp add: sum_mset_distrib_left multiset.map_comp o_def)
  also have "-Im z * (\<Sum>x\<in>#Apos.  2 * d x / N x ^ 2) + \<dots> =
             -Im z * ((\<Sum>x\<in>#Apos.  2 * d x / N x ^ 2) + (\<Sum>x\<in>#A0. 1 / N x))"
    by algebra
  also have "Im S = 0"
    using \<open>S = 0\<close> by simp
  finally have "((\<Sum>x\<in>#Apos. 2 * d x / N x ^ 2) + (\<Sum>x\<in>#A0. 1 / N x)) = 0"
    using \<open>z \<notin> \<real>\<close> by (simp add: complex_is_Real_iff)

  moreover have "((\<Sum>x\<in>#Apos.  2 * d x / N x ^ 2) + (\<Sum>x\<in>#A0. 1 / N x)) > 0"
  proof -
    have "A \<noteq> {#}"
      using \<open>degree p \<noteq> 0\<close> p_eq by fastforce
    hence "Apos \<noteq> {#} \<or> A0 \<noteq> {#}"
      using \<open>Aneg = image_mset cnj Apos\<close> \<open>A = Apos + Aneg + A0\<close> by auto
    thus ?thesis
    proof 
      assume "Apos \<noteq> {#}"
      hence "(\<Sum>x\<in>#Apos.  2 * d x / N x ^ 2) > 0"
        by (intro sum_mset_pos)
           (auto intro!: mult_pos_pos divide_pos_pos d_pos simp: Apos_def complex_is_Real_iff)
      thus ?thesis
        by (intro add_pos_nonneg sum_mset_nonneg) (auto intro!: N_nonneg simp: A0_def)
    next
      assume "A0 \<noteq> {#}"
      hence "(\<Sum>x\<in>#A0. 1 / N x) > 0"
        by (intro sum_mset_pos) (auto intro!: divide_pos_pos N_pos simp: A0_def)
      thus ?thesis
        by (intro add_nonneg_pos sum_mset_nonneg)
           (auto intro!: N_pos less_imp_le[OF d_pos] mult_nonneg_nonneg divide_nonneg_pos
                 simp: Apos_def complex_is_Real_iff)
    qed
  qed

  ultimately show False
    by simp
qed

end
