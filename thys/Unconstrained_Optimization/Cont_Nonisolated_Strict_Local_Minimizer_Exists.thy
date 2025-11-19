section \<open>Pathological Example: Non-Isolated Strict Local Minima\<close>

theory Cont_Nonisolated_Strict_Local_Minimizer_Exists
  imports Second_Derivative_Test "HOL-Library.Quadratic_Discriminant"
begin

text \<open>
\paragraph{Idea of the example.}
We construct a continuous function
\[
  f(x)=
  \begin{cases}
    x^{4}\!\bigl(\cos(1/x)+2\bigr), & x\neq 0,\\[4pt]
    0, & x = 0
  \end{cases}
\]
\begin{figure}[htbp]
  \centering
  \includegraphics[width=0.8\textwidth]{Plot.png}
\end{figure}

whose oscillations \emph{speed up} as \(x\to 0\) because of the \(\cos(1/x)\) term.  
Multiplying by \(x^{4}\) makes the function and its first derivative
vanish at the origin, ensuring that \(x=0\) is a strict local minimizer,
while the shifted cosine creates infinitely many additional strict local
minimizers that accumulate at \(0\).  
Hence the minimizer at \(0\) is \emph{strict} but \emph{not isolated}.
\<close>

theorem Exists_Continuous_Func_with_non_isolated_strict_local_minimizer:
  "\<exists>f::real \<Rightarrow> real. continuous_on \<real> f \<and> 
     (\<exists>x_star. strict_local_minimizer f x_star \<and> \<not> isolated_local_minimizer f x_star)"
proof -
  obtain f where f_def: "f = (\<lambda>(x::real). if x \<noteq> 0 then x^4 * (cos (1 / x) + 2) else 0)"
    by simp

  have deriv_f: "\<And>x::real. deriv f x = (if x = 0 then 0 else x\<^sup>2 * sin (1 / x) + 
                                             4 * x^3 * cos (1 / x) + 8 * x^3)
                     \<and> (\<lambda>x. f x) differentiable_on UNIV
                     \<and> deriv (deriv f) x = (if x = 0 then 0 else 6*x * sin (1 / x) + 
                                            (12*x\<^sup>2 - 1)* cos (1 / x) + 24*x\<^sup>2)
                     \<and> (deriv f) differentiable_on UNIV"
  proof (safe)
    \<comment> \<open>First we compute the derivative away from \(0\), then we compute it at \(0\).\<close>
    have deriv_f_at_nonzero:
      "\<And>x. x \<noteq> 0 \<longrightarrow> deriv f x = (x\<^sup>2 * sin (1 / x) + 4*x^3 * cos (1 / x) + 8*x^3)
           \<and> f field_differentiable at x"
    proof (safe)
      fix x :: real
      assume x_type: "x \<noteq> 0"
      
      have cos_inverse_diff: "(\<lambda>w. cos (1 / w)) field_differentiable at x"
      proof -
        have f1: "(\<lambda>w. 1 / w) field_differentiable at x"
          by (simp add: field_differentiable_divide x_type)
        have "(\<lambda>z. cos z) field_differentiable at (1 / x)"
          by (simp add: field_differentiable_within_cos)
        then show ?thesis
          by (metis DERIV_chain2 f1 field_differentiable_def)
      qed
      then have "(\<lambda>x. cos (1 / x) + 2) field_differentiable at x"
        by (simp add: Derivative.field_differentiable_add)
      then have f2: "(\<lambda>x. x^4 * (cos (1 / x) + 2)) field_differentiable at x"
        by (subst field_differentiable_mult, simp add: field_differentiable_power, simp_all)
  
      have deriv_2nd_part: "deriv (\<lambda>w. (\<lambda>x. cos (1 / x) + 2) w) x = (sin (1 / x)) / x\<^sup>2"
      proof -
        have "deriv (\<lambda>w. (\<lambda>x. cos (1 / x) + 2) w) x =
              (deriv (\<lambda>w. (\<lambda>x. cos (1 / x)) w) x + deriv (\<lambda>w. (\<lambda>x. 2) w) x)"
          by (rule deriv_add, simp add: cos_inverse_diff, simp)
        also have "... = (sin (1 / x)) / x\<^sup>2"
        proof -
          have f1: "DERIV (\<lambda>z. cos z) (1 / x) :> -sin (1 / x)"
            by simp
          have f2: "DERIV (\<lambda>w. 1 / w) x :> -1 / x\<^sup>2"
            using DERIV_inverse_func x_type by blast
          from f1 f2 have "DERIV ((\<lambda>z. cos z) \<circ> (\<lambda>w. 1 / w)) x :> (-sin (1 / x)) * (-1 / x\<^sup>2)"
              by (rule DERIV_chain)
          then show ?thesis
            by (simp add: DERIV_imp_deriv o_def)
        qed
        finally show ?thesis.
      qed
  
      show "deriv f x = x\<^sup>2 * sin (1 / x) + 4*x^3 * cos (1 / x) + 8*x^3"
      proof -
        have "deriv f x = deriv (\<lambda>x. x^4 * (cos (1 / x) + 2)) x"
          by (metis (no_types, lifting) f_def mult_eq_0_iff power_zero_numeral)
        also have "... = x^4 * deriv (\<lambda>x. cos (1 / x) + 2) x +
                        deriv (\<lambda>x. x^4) x * (cos (1 / x) + 2)"
          by (rule deriv_mult, simp add: field_differentiable_power, 
              simp add: Derivative.field_differentiable_add cos_inverse_diff)
        also have "... = x^4 * (sin (1 / x)) / x\<^sup>2 +
                        deriv (\<lambda>x. x^4) x * (cos (1 / x) + 2)"
          by (simp add: deriv_2nd_part)
        also have "... = x^4 * (sin (1 / x)) / x\<^sup>2 + (4*x^3) * (cos (1 / x) + 2)"
          by (subst power_rule, simp)
        also have "... = x\<^sup>2 * (sin (1 / x)) + (4*x^3) * (cos (1 / x) + 2)"
          by (simp add: power2_eq_square power4_eq_xxxx)
        also have "... = x\<^sup>2 * sin (1 / x) + 4*x^3 * cos (1 / x) + 8*x^3"
          by (simp add: Rings.ring_distribs(2) mult.commute)
        finally show ?thesis.
      qed
      from x_type f_def f2 show "f field_differentiable at x"
        by (subst field_differentiable_transfer_on_ball[where f = "\<lambda> x. (x^4 * (cos (1 / x) + 2))"
              and \<epsilon> = "\<bar>x\<bar>"], simp_all)          
    qed
  
    have deriv_f_at_0: "deriv f 0 = 0 \<and> f field_differentiable at 0"
    proof -
     \<comment> \<open>By the definition of deriv, we need to show the limit of the difference quotient is \(0\).\<close>
      have dq_limit: "((\<lambda>h. (f (0 + h) - f 0) / h) \<longlongrightarrow> 0) (at 0)"
      proof
        fix \<epsilon> :: real
        assume \<epsilon>_pos: "0 < \<epsilon>"
        \<comment> \<open>Choose \(\delta > 0\) to make \(\lvert\text{difference quotient}\rvert < \varepsilon\).\<close>
        obtain \<delta> where \<delta>_def: "\<delta> = (\<epsilon> / 3) powr (1 / 3)"  
          by simp
        \<comment> \<open>A reasonable \(\delta\) based on the growth of \(\lvert h^3\rvert\).\<close>
        have \<delta>_pos: "\<delta> > 0"
          using \<epsilon>_pos by (simp add: \<delta>_def)
        have "\<exists>\<delta>>0. \<forall>h. 0 < \<bar>h\<bar> \<and> \<bar>h\<bar> < \<delta> \<longrightarrow> \<bar>(f (0 + h) - f 0) / h - 0\<bar> < \<epsilon>"
        proof (intro exI[where x=\<delta>], intro conjI insert \<delta>_pos, clarify)
          fix h :: real
          assume h_pos: "0 < \<bar>h\<bar>" 
          assume h_lt_\<delta>: "\<bar>h\<bar> < \<delta>"
  
          have "\<bar>(f (0 + h) - f 0) / h - 0\<bar> = \<bar>f h / h\<bar>"
            by (simp add: f_def)
          also have "... = \<bar>h^4 * (cos (1 / h) + 2) / h\<bar>"
            using f_def by presburger
          also have "... = \<bar>h^3 * (cos (1 / h) + 2)\<bar>"
            by (simp add: power3_eq_cube power4_eq_xxxx vector_space_over_itself.scale_scale)
          also have "... \<le> \<bar>h^3\<bar> * \<bar>cos (1 / h) + 2\<bar>"
            by (metis abs_mult order.refl)
          also have "... \<le> \<bar>h^3\<bar> * (\<bar>cos (1 / h)\<bar> + \<bar>2\<bar>)"
            by (simp add: mult_left_mono)
          also have "... \<le> \<bar>h^3\<bar> * (1 + 2)"
            by (simp add: mult_left_mono)
          also have "... = 3 * \<bar>h^3\<bar>"
            by simp
          also have "... < 3 * \<delta>^3"
            using power_strict_mono[of "\<bar>h\<bar>" \<delta> 3] by (simp add: h_lt_\<delta> power_abs)
          also have "... = 3 * (\<epsilon> / 3)"
            by (metis \<delta>_def \<epsilon>_pos div_self less_le more_arith_simps(5)
                      mult_eq_0_iff pos_le_divide_eq powr_numeral powr_one_gt_zero_iff
                      powr_powr times_divide_eq_left verit_comp_simplify(19) zero_neq_numeral)
          also have "... = \<epsilon>"
            by simp
          finally show "\<bar>(f (0 + h) - f 0) / h - 0\<bar> < \<epsilon>".
        qed
        then show "\<exists>d>0.\<forall>x\<in>UNIV. 0 < dist x 0 \<and> dist x 0 < d \<longrightarrow> dist ((f (0 + x) - f 0) / x) 0 \<le> \<epsilon>"
          by (metis arithmetic_simps(57) dist_real_def less_le)
      qed
      then show ?thesis
        using DERIV_def DERIV_imp_deriv field_differentiable_def by blast
    qed
  
    show deriv_f: "\<And>x. deriv f x = 
      (if x = 0 then 0 else x\<^sup>2 * sin (1 / x) + 4 * x^3 * cos (1 / x) + 8 * x^3)"
      using deriv_f_at_0 deriv_f_at_nonzero by presburger
  
    show f_is_differentiable: "(\<lambda>x. f x) differentiable_on UNIV"
      by (metis deriv_f_at_0 deriv_f_at_nonzero differentiable_on_def 
          field_differentiable_imp_differentiable)
       
    have snd_deriv_f_at_nonzero:
      "\<And>x. x \<noteq> 0 \<longrightarrow> deriv (deriv f) x = (6*x * sin (1 / x) + (12*x\<^sup>2 - 1)* cos (1 / x) + 24*x\<^sup>2)
           \<and> (deriv f) field_differentiable at x"
    proof (safe)
      fix x :: real
      assume x_type: "x \<noteq> 0"
      
      have fst_term_diff: "(\<lambda>w. w\<^sup>2 * sin (1 / w)) field_differentiable at x"
      proof -
        have f1: "(\<lambda>w. w\<^sup>2) field_differentiable at x"
          by (simp add: field_differentiable_power)
        have "(\<lambda>w. sin (1 / w)) field_differentiable at x"
          by (metis DERIV_chain2 DERIV_inverse_func field_differentiable_at_sin
                    field_differentiable_def x_type)
        then show ?thesis
          by (simp add: f1 field_differentiable_mult)
      qed
  
      have fst_term_deriv: "deriv (\<lambda>w. w^2 * sin (1 / w)) x = 2 * x * sin (1 / x) - cos (1 / x)"
      proof -
        have "deriv (\<lambda>x. x^2 * sin (1 / x)) x =
              x^2 * deriv (\<lambda>x. sin (1 / x)) x + deriv (\<lambda>x. x^2) x * sin (1 / x)"
          by (rule deriv_mult, simp add: field_differentiable_power,
              metis DERIV_chain2 DERIV_inverse_func field_differentiable_at_sin
                    field_differentiable_def x_type)
        moreover have "deriv (\<lambda>x. x^2) x = 2 * x"
          using power_rule by auto
        moreover have "deriv (\<lambda>x. sin (1 / x)) x = -cos (1 / x) / x^2"
        proof -
          have f1: "DERIV (\<lambda>z. sin z) (1 / x) :> cos (1 / x)"
            by simp
          have f2: "DERIV (\<lambda>x. 1 / x) x :> -1 / x^2"
            using DERIV_inverse_func x_type by blast
          from f1 f2 have "DERIV ((\<lambda>z. sin z) \<circ> (\<lambda>x. 1 / x)) x :> cos (1 / x) * (-1 / x^2)"
            by (rule DERIV_chain)
          then show ?thesis
            by (simp add: DERIV_imp_deriv o_def)
        qed
        ultimately show ?thesis
          by (simp add: x_type)
      qed
  
      have snd_term_diff: "(\<lambda>x. 4 * x^3 * cos (1 / x)) field_differentiable at x"
      proof -
        have t1: "(\<lambda>x. 4 * x^3) field_differentiable at x"
          by (simp add: field_differentiable_power field_differentiable_mult)
        have t2: "(\<lambda>x. cos (1 / x)) field_differentiable at x"
          by (metis DERIV_chain2 DERIV_inverse_func field_differentiable_at_cos
                    field_differentiable_def x_type)
        show ?thesis
          by (simp add: t1 t2 field_differentiable_mult)
      qed
      have snd_term_diff': "(\<lambda>w. 4 * w ^ 3 * cos (1 / w) + 8 * w ^ 3) field_differentiable at x"
      proof -
        have t3: "(\<lambda>x. 8 * x^3) field_differentiable at x"
          by (simp add: field_differentiable_mult field_differentiable_power)
        show ?thesis
          by (simp add: Derivative.field_differentiable_add t3 snd_term_diff)
      qed
  
      have snd_term_deriv:
        "deriv (\<lambda>x. 4 * x^3 * cos (1 / x) + 8 * x^3) x =
         12 * x^2 * cos (1 / x) + 4 * x * sin (1 / x) + 24 * x^2"
      proof -
        have "deriv (\<lambda>x. 4 * x^3 * cos (1 / x) + 8 * x^3) x =
              deriv (\<lambda>x. 4 * x^3 * cos (1 / x)) x + deriv (\<lambda>x. 8 * x^3) x"
          by (rule deriv_add, simp add: snd_term_diff,
              simp add: field_differentiable_mult field_differentiable_power)
        also have "... = (4*x^3) * (deriv (\<lambda>x. cos (1 / x)) x) +
                          ((12 * x^2) * (cos (1 / x))) + deriv (\<lambda>x. 8 * x^3) x"
        proof -
          have "deriv (\<lambda>x. 4 * x^3 * cos (1 / x)) x =
                (4*x^3) * (deriv (\<lambda>x. cos (1 / x)) x) +
                (deriv (\<lambda>x. 4 * x^3) x) * (cos (1 / x))"
            by (rule deriv_mult, simp add: field_differentiable_mult field_differentiable_power,
                metis DERIV_fun_cos DERIV_inverse_func field_differentiable_def x_type)
          then have "deriv (\<lambda>x. 4 * x^3) x = 12 * x^2"
          proof -
            have "deriv (\<lambda>x. 4 * x^3) x = 4 * deriv (\<lambda>x. x^3) x"
              by (rule deriv_cmult, simp add: field_differentiable_power)
            then show ?thesis
              by (simp add: power_rule)
          qed
          then show ?thesis
            using \<open>deriv (\<lambda>x. 4 * x^3 * cos (1 / x)) x = (4*x^3) * (deriv (\<lambda>x. cos (1 / x)) x) +
                                                     (deriv (\<lambda>x. 4 * x^3) x) * (cos (1 / x))\<close>
            by auto
        qed
        also have "... = (4*x^3) * (deriv (\<lambda>x. cos (1 / x)) x) +
                          ((12 * x^2) * (cos (1 / x))) + 24 * x^2"
        proof -
          have "deriv (\<lambda>x. 8 * x^3) x = 24 * x^2"
          proof -
            have "deriv (\<lambda>x. 8 * x^3) x = 8 * deriv (\<lambda>x. x^3) x"
              by (rule deriv_cmult, simp add: field_differentiable_power)
            then show ?thesis
              by (simp add: power_rule)
          qed
          then show ?thesis
            by auto
        qed
        also have "... = (4*x^3) * sin (1 / x) / x^2 + ((12 * x^2) * (cos (1 / x))) + 24 * x^2"
        proof -
          have "deriv (\<lambda>x. cos (1 / x)) x = sin (1 / x) / x^2"
          proof -
            have f1: "DERIV (\<lambda>z. cos z) (1 / x) :> -sin (1 / x)"
              by simp
            have f2: "DERIV (\<lambda>x. 1 / x) x :> -1 / x^2"
              using DERIV_inverse_func x_type by blast
            from f1 f2 have "DERIV ((\<lambda>z. cos z) \<circ> (\<lambda>x. 1 / x)) x :> (-sin (1 / x)) * (-1 / x^2)"
              by (rule DERIV_chain)
            then show ?thesis
              by (simp add: DERIV_imp_deriv o_def)
          qed
          then show ?thesis
            by auto
        qed
        also have "... = ((12 * x^2) * (cos (1 / x))) + (4*x^3) * sin (1 / x) / x^2 + 24 * x^2"
          by linarith
        also have "... = (12 * x^2) * (cos (1 / x)) + 4*x * sin (1 / x) + 24 * x^2"
        proof -
          have "(4*x^3) * sin (1 / x) / x^2 = 4*x * sin (1 / x)"
            by (simp add: power2_eq_square power3_eq_cube)
          then show ?thesis
            by presburger
        qed
        finally show ?thesis.
      qed
  
      show "deriv (deriv f) x = (6*x * sin (1 / x) + (12*x\<^sup>2 - 1)* cos (1 / x) + 24*x\<^sup>2)"
      proof -
        have "deriv (deriv f) x = deriv (\<lambda>x. x\<^sup>2 * sin (1 / x) + 4 * x^3 * cos (1 / x) + 8 * x^3) x"
          by (metis (no_types, opaque_lifting) deriv_f mult_cancel_left2 mult_cancel_right2 
              power_zero_numeral pth_7(2))
        also have "... = deriv (\<lambda>x. x\<^sup>2 * sin (1 / x) + (4 * x^3 * cos (1 / x) + 8 * x^3)) x"
          by (meson Groups.add_ac(1))
        also have "... = deriv (\<lambda>x. x^2 * sin (1 / x)) x +
                         deriv (\<lambda>x. 4 * x^3 * cos (1 / x) + 8 * x^3) x"
          by (rule deriv_add, simp add: fst_term_diff, simp add: snd_term_diff')
        also have "... = 2 * x * sin (1 / x) - cos (1 / x) +
                          deriv (\<lambda>x. 4 * x^3 * cos (1 / x) + 8 * x^3) x"
          by (simp add: fst_term_deriv)
        also have "... = 2 * x * sin (1 / x) - cos (1 / x) +
                        12 * x^2 * cos (1 / x) + 4 * x * sin (1 / x) + 24 * x^2"
          by (simp add: snd_term_deriv)
        also have "... = 2 * x * sin (1 / x) + 4 * x * sin (1 / x) +
                          12 * x^2 * cos (1 / x) - cos (1 / x) + 24 * x^2"
          by simp
        also have "... = (6*x * sin (1 / x) + (12*x\<^sup>2 - 1)* cos (1 / x) + 24*x\<^sup>2)"
          by (smt (verit, best) cos_add cos_zero mult_diff_mult sin_zero)
        finally show ?thesis.
      qed
  
      show "(deriv f) field_differentiable at x"
      proof (rule field_differentiable_transfer_on_ball
          [where f = "\<lambda> x. (x\<^sup>2 * sin (1 / x) + 4 * x^3 * cos (1 / x) + 8 * x^3)" and \<epsilon> = "\<bar>x\<bar>"])
        show " 0 < \<bar>x\<bar>"
          by (simp add: x_type)
        show "\<forall>y. y \<in> ball x \<bar>x\<bar> \<longrightarrow> y\<^sup>2 * sin (1 / y) + 4 * y ^ 3 * cos (1 / y) + 8 * y ^ 3 = 
          deriv f y"
          by (simp add: deriv_f)
        show "(\<lambda>x. x\<^sup>2 * sin (1 / x) + 4 * x ^ 3 * cos (1 / x) + 8 * x ^ 3)field_differentiable at x"
          by (simp add: Derivative.field_differentiable_add fst_term_diff is_num_normalize(1) 
              snd_term_diff')
      qed
    qed
  
    have deriv2_f_at_0:
      "deriv (deriv f) 0 = 0 \<and> (deriv f) field_differentiable at 0"
    proof -
      \<comment> \<open>By the definition of deriv, we need to show the limit of the difference quotient of \(f'\) is \(0\).\<close>
      have dq_limit: "((\<lambda>h. (deriv f (0 + h) - deriv f 0) / h) \<longlongrightarrow> 0) (at 0)"
      proof
        fix \<epsilon> :: real
        assume \<epsilon>_pos: "0 < \<epsilon>"
        have "\<exists>\<delta>>0. \<forall>h. 0 < \<bar>h\<bar> \<and> \<bar>h\<bar> < \<delta> \<longrightarrow> \<bar>(deriv f (0 + h) - deriv f 0) / h - 0\<bar> < \<epsilon>"
        proof (cases "\<epsilon> < 1/6")
          assume eps_lt_inv6: "\<epsilon> < 1/6"
          \<comment> \<open>Choose \(\delta > 0\) to ensure \(\lvert\text{difference quotient}\rvert < \varepsilon\).\<close>
          obtain \<delta> where \<delta>_def: "\<delta> = \<epsilon> / 2"
            by blast
          have \<delta>_pos: "\<delta> > 0"
            using \<epsilon>_pos by (simp add: \<delta>_def)
          show "\<exists>\<delta>>0. \<forall>h. 0 < \<bar>h\<bar> \<and> \<bar>h\<bar> < \<delta> \<longrightarrow> \<bar>(deriv f (0 + h) - deriv f 0) / h - 0\<bar> < \<epsilon>"
          proof (intro exI[where x=\<delta>], intro conjI insert \<delta>_pos, clarify)
            fix h :: real
            assume h_pos: "0 < \<bar>h\<bar>"
            assume h_lt_\<delta>: "\<bar>h\<bar> < \<delta>"
            
            have h_bound1: "\<bar>h\<bar> < \<epsilon> / 2"
              using h_lt_\<delta> by (simp add: \<delta>_def)
            have h_bound2: "12 * \<bar>h^2\<bar> < \<epsilon> / 2"
            proof -
              have "\<bar>h\<bar> < \<epsilon> / 2" using h_bound1 by blast
              then have "\<bar>h^2\<bar> < (\<epsilon> / 2)^2"
                by (metis abs_ge_zero abs_power2 power2_abs power_strict_mono zero_less_numeral)
              then have "12 * \<bar>h^2\<bar> < 12 * (\<epsilon> / 2)^2"
                by (simp add: mult_strict_left_mono)
              also have "... = 12 * (\<epsilon>^2 / 4)"
                by (simp add: power2_eq_square)
              also have "... = 3 * \<epsilon>^2"
                by simp
              also have "... < \<epsilon>/2"
              proof -
                have "\<epsilon> * 6 < 1"
                  by (meson eps_lt_inv6 less_divide_eq_numeral1(1))
                then show ?thesis
                  by (simp add: \<epsilon>_pos power2_eq_square)
              qed
              finally show ?thesis.
            qed
            have "\<bar>(deriv f (0 + h) - deriv f 0) / h - 0\<bar> = \<bar>deriv f h / h\<bar>"
              by (simp add: deriv_f_at_0)
            also have "... = \<bar>(h\<^sup>2 * sin (1 / h) + 4*h^3 * cos (1 / h) + 8*h^3) / h\<bar>"
              using deriv_f by presburger
            also have "... = \<bar>(h\<^sup>2 * sin (1 / h) / h) + (4*h^3 * cos (1 / h)) / h + (8*h^3) / h\<bar>"
              by (simp add: add_divide_distrib)
            also have "... = \<bar>h * sin (1 / h) + (4*h^2 * cos (1 / h)) + 8 * h^2\<bar>"
              by (simp add: more_arith_simps(11) power2_eq_square power3_eq_cube)
            also have "... \<le> \<bar>h * sin (1 / h)\<bar> + \<bar>4*h^2 * cos (1 / h)\<bar> + \<bar>8 * h^2\<bar>"
              by linarith
            also have "... \<le> \<bar>h\<bar> * \<bar>sin (1 / h)\<bar> + 4 * \<bar>h^2\<bar> * \<bar>cos (1 / h)\<bar> + 8 * \<bar>h^2\<bar>"
              by (simp add: abs_mult)
            also have "... \<le> \<bar>h\<bar> + 4 * \<bar>h^2\<bar> + 8 * \<bar>h^2\<bar>"
            proof -
              have i1: "\<bar>h\<bar> * \<bar>sin (1 / h)\<bar> \<le> \<bar>h\<bar>"
                using h_pos by fastforce
              have "\<bar>h\<bar> * \<bar>cos (1 / h)\<bar> \<le> \<bar>h\<bar>"
                by (simp add: mult_left_le)
              then show ?thesis
                by (smt (verit) cos_ge_minus_one cos_le_one i1 mult_left_le)
            qed
            also have "... = \<bar>h\<bar> + 12 * \<bar>h^2\<bar>"
              by simp
            also have "... < \<epsilon>"
              using h_bound1 h_bound2 by auto
            finally show "\<bar>(deriv f (0 + h) - deriv f 0) / h - 0\<bar> < \<epsilon>".
          qed
        next
          assume "\<not> \<epsilon> < 1/6"
          then have "\<epsilon> \<ge> 1/6" by linarith
          then have eps_half: "\<epsilon> / 2 \<ge> 1/12" by linarith
          obtain \<delta> where \<delta>_def: "\<delta> = (1::real)/12" by blast
          have \<delta>_pos: "\<delta> > 0" using \<epsilon>_pos by (simp add: \<delta>_def)
          show "\<exists>\<delta>>0. \<forall>h. 0 < \<bar>h\<bar> \<and> \<bar>h\<bar> < \<delta> \<longrightarrow> \<bar>(deriv f (0 + h) - deriv f 0) / h - 0\<bar> < \<epsilon>"
          proof (intro exI[where x=\<delta>], intro conjI insert \<delta>_pos, clarify)
            fix h :: real
            assume h_pos: "0 < \<bar>h\<bar>"
            assume h_lt_\<delta>: "\<bar>h\<bar> < \<delta>"
            have h_bound1: "\<bar>h\<bar> < \<epsilon> / 2"
            proof -
              have "\<bar>h\<bar> < \<delta>" using h_lt_\<delta> by blast
              also have "... = (1::real)/12" by (simp add: \<delta>_def)
              also have "... \<le> \<epsilon> / 2" using eps_half by blast
              finally show ?thesis.
            qed
            have h_bound2: "12 * \<bar>h\<bar>^2 < \<epsilon> / 2"
            proof -
              from h_bound1 have "\<bar>h\<bar>^2 < (1/12)^2"
                by (metis \<delta>_def abs_ge_zero h_lt_\<delta> power_strict_mono zero_less_numeral)
              hence "12 * \<bar>h\<bar>^2 < 12 * (1/12)^2"
                by (rule mult_strict_left_mono, simp_all)
              also have "... = 1/12" by (simp add: power_one_over)
              also have "... \<le> \<epsilon> / 2" using eps_half by blast
              finally show ?thesis.
            qed
            have "\<bar>(deriv f (0 + h) - deriv f 0) / h - 0\<bar> = \<bar>deriv f h / h\<bar>"
              by (simp add: deriv_f_at_0)
            also have "... = \<bar>(h\<^sup>2 * sin (1 / h) + 4*h^3 * cos (1 / h) + 8*h^3) / h\<bar>"
              using deriv_f by presburger
            also have "... = \<bar>(h\<^sup>2 * sin (1 / h) / h) + (4*h^3 * cos (1 / h)) / h + (8*h^3) / h\<bar>"
              by (simp add: add_divide_distrib)
            also have "... = \<bar>h * sin (1 / h) + (4*h^2 * cos (1 / h)) + 8 * h^2\<bar>"
              by (simp add: more_arith_simps(11) power2_eq_square power3_eq_cube)
            also have "... \<le> \<bar>h * sin (1 / h)\<bar> + \<bar>4*h^2 * cos (1 / h)\<bar> + \<bar>8 * h^2\<bar>"
              by linarith
            also have "... \<le> \<bar>h\<bar> * \<bar>sin (1 / h)\<bar> + 4 * \<bar>h^2\<bar> * \<bar>cos (1 / h)\<bar> + 8 * \<bar>h^2\<bar>"
              by (simp add: abs_mult)
            also have "... \<le> \<bar>h\<bar> + 4 * \<bar>h^2\<bar> + 8 * \<bar>h^2\<bar>"
            proof -
              have i1: "\<bar>h\<bar> * \<bar>sin (1 / h)\<bar> \<le> \<bar>h\<bar>" 
                using h_pos by fastforce
              have "\<bar>h\<bar> * \<bar>cos (1 / h)\<bar> \<le> \<bar>h\<bar>" 
                by (simp add: mult_left_le)
              then show ?thesis 
                by (smt (verit) cos_ge_minus_one cos_le_one i1 mult_left_le)
            qed
            also have "... = \<bar>h\<bar> + 12 * \<bar>h^2\<bar>" 
              by simp
            also have "... < \<epsilon>" 
              using h_bound1 h_bound2 by auto
            finally show "\<bar>(deriv f (0 + h) - deriv f 0) / h - 0\<bar> < \<epsilon>".
          qed
        qed
        then show "\<exists>d>0. \<forall>x\<in>UNIV. 0 < dist x 0 \<and> dist x 0 < d \<longrightarrow>
                          dist ((deriv f (0 + x) - deriv f 0) / x) 0 \<le> \<epsilon>"
          by (metis cancel_comm_monoid_add_class.diff_zero dist_real_def le_less)
      qed
      then show ?thesis
        using DERIV_def DERIV_imp_deriv field_differentiable_def by blast
    qed
  
    show "\<And>x. deriv (deriv f) x = (if x = 0 then 0 else 6 * x * sin (1 / x)
                                       + (12 * x\<^sup>2 - 1) * cos (1 / x)
                                       + 24 * x\<^sup>2)"
      using snd_deriv_f_at_nonzero deriv2_f_at_0 by presburger
  
    show "(deriv f) differentiable_on UNIV"
      by (metis deriv2_f_at_0 differentiable_on_def
                field_differentiable_imp_differentiable snd_deriv_f_at_nonzero)
  qed
  then have f_cont: "continuous_on \<real> f"
    by (meson continuous_on_subset differentiable_imp_continuous_on top.extremum)
  have f'_cont: "continuous_on \<real> (deriv f)"
    by (meson continuous_on_subset deriv_f differentiable_imp_continuous_on top.extremum)

  obtain U where U_def: "U = {x :: real. -1 < x \<and> x < 1}"
    by blast
  then have open_neighborhood_of_zero: "open U \<and> 0 \<in> U"
    using lemma_interval_lt by (subst open_dist, subst dist_real_def,fastforce)

  have strict_local_minimizer_at_0: "strict_local_minimizer f 0"
    unfolding strict_local_minimizer_def  strict_local_minimizer_on_def
  proof (intro exI[where x=U],(subst sym[OF conj_assoc],rule conjI), rule open_neighborhood_of_zero)
    show "\<forall> x \<in> U - {0}. f 0 < f x"
    proof 
      fix x 
      assume x_type: "x \<in> U - {0}"
      then have x_nonzero: "x \<noteq> 0"
        by blast
      have "cos(1/x) + 2 \<ge> 1"
        by (smt (verit) cos_ge_minus_one)
      then have "x^4 * (cos(1/x) + 2) \<ge> x^4 * 1"
        by (rule mult_left_mono, force)
      then have "f x \<ge> x^4"
        by (simp add: f_def x_nonzero)
      then have "f x > 0"
        by (smt (verit, del_insts) mult_le_0_iff power4_eq_xxxx x_nonzero zero_le_mult_iff)
      then show "f 0 < f x"
        using f_def by force
    qed
  qed
  then have zero_min: "local_minimizer f 0"
    by (simp add: strict_local_minimizer_imp_local_minimizer)
  have "(\<exists>x_seq::nat \<Rightarrow> real. (\<forall>n. local_minimizer f (x_seq n) \<and> x_seq n \<noteq> 0) \<and> 
                                                     ((x_seq \<longlongrightarrow> 0) at_top))"
  proof - 
    obtain left_seq :: "nat \<Rightarrow> real" where left_seq_def: "\<forall>n \<in> \<nat>. n \<noteq> 0 \<longrightarrow> 
           left_seq n = inverse ((5 * pi / 4) + 2 * real n * pi)"
      by force 
    obtain right_seq :: "nat \<Rightarrow> real" where right_seq_def: "\<forall>n \<in> \<nat>. n \<noteq> 0 \<longrightarrow> 
           right_seq n = inverse  (pi + 2 * real n * pi)"  
      by force

    have zero_lt_left_seq_lt_right_seq_both_pos: "\<forall>n \<in> \<nat>. n \<noteq> 0 \<longrightarrow> 
                                                  0 < left_seq n \<and> left_seq n < right_seq n"
    proof clarify
      fix n::nat
      assume n_pos: "0 < n"
      then have inv_left: "inverse (left_seq n) = (5 * pi / 4) + 2 * real n * pi"
        by (metis bot_nat_0.not_eq_extremum id_apply inverse_inverse_eq left_seq_def of_nat_eq_id 
            of_nat_in_Nats)

      have inv_right: "inverse (right_seq n) = pi + 2 * real n * pi"
        by (metis bot_nat_0.not_eq_extremum id_apply inverse_inverse_eq n_pos of_nat_eq_id 
            of_nat_in_Nats right_seq_def)

      have denom_ineq: "(pi + 2 * real n * pi) < ((5 * pi / 4) + 2 * real n * pi)"
      proof -
        have "(5 * pi / 4) + 2 * real n * pi = 2 * real n * pi + (5 * pi / 4)"
          by simp
        have "((5 * pi / 4) + 2 * real n * pi) - (pi + 2 * real n * pi) =
                  (5 * pi / 4) + 2 * real n * pi - pi - 2 * real n * pi"
          by simp
        also have "... = (5 * pi / 4) - pi"
          by simp
        also have "... = (5 * pi / 4) - (4 * pi / 4)"
          by simp
        also have "... = (5 - 4) * pi / 4"
          by simp
        also have "... = pi / 4"
          by simp
        then show ?thesis
          by simp
      qed
      then have "left_seq n < right_seq n"
        by (smt (verit) inv_left inv_right inverse_positive_iff_positive le_imp_inverse_le 
            mult_nonneg_nonneg of_nat_less_0_iff pi_gt3)
      then show "0 < left_seq n \<and> left_seq n < right_seq n"
        by (smt (verit, best) denom_ineq inv_left inverse_positive_iff_positive mult_nonneg_nonneg 
            of_nat_less_0_iff pi_gt3)
    qed
    have first_and_second_order_conditions: "\<forall>n. n \<noteq> 0 \<longrightarrow> 
  (\<exists> y \<in> {left_seq n .. right_seq n}. (y^2 * sin (1 / y) + 4 * y^3 * cos (1 / y) + 8 * y^3) = 0 \<and>                                                      
  (6*y * sin (1 / y) + (12*y\<^sup>2 - 1)* cos (1 / y) + 24*y\<^sup>2) > 0) \<and>
  ((left_seq n)^2 * sin (1 /(left_seq n)) + 4 * (left_seq n)^3 * cos (1 / (left_seq n)) + 
                                      8 * (left_seq n)^3) < 0 \<and>
  ((right_seq n)^2 * sin (1 /(right_seq n)) + 4 * (right_seq n)^3 * cos (1 / (right_seq n)) 
                                    + 8 * (right_seq n)^3) > 0"
    proof(clarify)
      fix n:: nat
      assume n_pos: "0 < n"
      then have n_ge_1: "1 \<le> n"
        by simp
      show "(\<exists>y\<in>{left_seq n..right_seq n}. y\<^sup>2 * sin (1 / y) + 4 * y ^ 3 * cos (1 / y) + 8 * y ^ 3 = 0 \<and> 0 < 6 * y * sin (1 / y) + (12 * y\<^sup>2 - 1) * cos (1 / y) + 24 * y\<^sup>2) \<and>
              (left_seq n)\<^sup>2 * sin (1 / left_seq n) + 4 * left_seq n ^ 3 * cos (1 / left_seq n) + 8 * left_seq n ^ 3 < 0 \<and>
              0 < (right_seq n)\<^sup>2 * sin (1 / right_seq n) + 4 * right_seq n ^ 3 * cos (1 / right_seq n) + 8 * right_seq n ^ 3"
      proof safe
        show left_seq_less_zero: "(\<lambda>x. x^2 * sin (1 / x) + 4 * x^3 * cos (1 / x) + 8 * x^3) (left_seq n) < 0"
        proof - 
          obtain x where x_def: "x = left_seq n"
            by blast    
          \<comment> \<open>Rewrite \(1/x\) in terms of \(\tfrac{5\pi}{4} + 2n\pi\).\<close>

          then have inv_x_eqs: "inverse x = inverse (inverse ((5 * pi / 4) + 2 * real n * pi))"
            by (metis bot_nat_0.not_eq_extremum id_apply left_seq_def n_pos of_nat_eq_id of_nat_in_Nats)
          then have x_inv: "1/x =  (5 * pi / 4) + 2 * real n * pi"
            by (simp add: inverse_eq_divide)
           
          \<comment> \<open>Evaluate \(\sin(1/x)\) and \(\cos(1/x)\).\<close>
          have sin_inv_x: "sin (1 / x) = - (sqrt 2 / 2)"
          proof - 
            have "sin (1 / x) = sin ((5 * pi / 4) + 2 * real n * pi)"
              using x_inv by presburger       
            also have "... = sin (5 * pi / 4)"
              by (simp add: sin_add)
            also have "... = - (sqrt 2 / 2)"
              using sin_5pi_div_4 by blast
            finally show "sin (1 / x) = - (sqrt 2 / 2)".
          qed
                        
          have cos_inv_x: "cos (1 / x) = - (sqrt 2 / 2)"
          proof - 
            have cos_val: "cos (1 / x) = cos ((5 * pi / 4) + 2 * real n * pi)"
              using x_inv by presburger
            also have "... = cos (5 * pi / 4)"
              by (simp add: cos_add)
            also have "... = - (sqrt 2 / 2)"
              using cos_5pi_div_4 by linarith
            finally show "cos (1 / x) = - (sqrt 2 / 2)".
          qed
        
          \<comment> \<open>Substitute these into the expression.\<close>
          have expr: "x^2 * sin (1 / x) + 4 * x^3 * cos (1 / x) + 8 * x^3 
                         = - (sqrt 2 / 2) * x^2  + (8 - 2 * sqrt 2) * x^3"
          proof - 
            have "x^2 * sin (1 / x) + 4 * x^3 * cos (1 / x) + 8 * x^3
                      = (x^2 * - (sqrt 2 / 2)) + 4 * x^3 * (-(sqrt 2 / 2)) + 8 * x^3"
              by (simp add: cos_inv_x sin_inv_x)
      
            also have "... = x^2 * - (sqrt 2 / 2) + (-2 * sqrt 2) * x^3 + 8 * x^3"
              by simp
            also have "... =   - (sqrt 2 / 2) * x^2 + (8 - 2 * sqrt 2) * x^3"
            proof -
              have "- (sqrt 2 / 2) + (x ^ 3 * (sqrt 2 * - 2) + x ^ 3 * 8) = 
                    - (sqrt 2 / 2) + x ^ 3 * (sqrt 2 * - 2 + 8)"
                by (metis (no_types) nat_distrib(2))
              then show ?thesis
                by (simp add: Groups.mult_ac(2))
            qed
            finally show rewrite_expr:
              "x^2 * sin (1 / x) + 4 * x^3 * cos (1 / x) + 8 * x^3
               = - (sqrt 2 / 2) * x^2  + (8 - 2 * sqrt 2) * x^3".
          qed
  
          \<comment> \<open>Factor out \(x^3\), and rewrite \(x^3\) as \(\bigl(\frac{5\pi}{4} + 2n\pi\bigr)^{-1}\).\<close>

          have deriv_right_seq_eval: "sin (1 / x) * x^2 + 4 * x^3 * cos (1 / x) + 8 * x^3 = 
              (- (sqrt 2 / 2)*((5 * pi / 4) + 2 * real n * pi)  + (8 - 2 * sqrt 2)) * x^3"
          proof - 
            have "sin (1 / x) * x^2 + 4 * x^3 * cos (1 / x) + 8 * x^3  =  
              - (sqrt 2 / 2)*inverse x * x^3 + (8 - 2 * sqrt 2) * x^3"
              by (smt (verit, del_insts) Groups.mult_ac(2) cos_inv_x cos_zero divide_eq_0_iff expr 
                  left_inverse more_arith_simps(11) one_power2 power2_eq_square power3_eq_cube 
                  power_minus sin_inv_x sin_zero)
            also have "... = (- (sqrt 2 / 2)*inverse x  + (8 - 2 * sqrt 2)) * x^3"
              by (metis (no_types) distrib_right)
            also have "... = (- (sqrt 2 / 2)*((5 * pi / 4) + 2 * real n * pi)  + 
                                                          (8 - 2 * sqrt 2)) * x^3"
              by (simp add: inv_x_eqs) 
            finally show ?thesis.
          qed

          \<comment> \<open>Combine into a single fraction and show negativity.\<close>
          have first_term_eval: "x^3 > 0"
            by (smt (verit) mult_nonneg_nonneg of_nat_0_le_iff pi_gt3 x_inv zero_compare_simps(7) 
                zero_less_power)
          have neg_term: "(-(sqrt 2 / 2)*((5 * pi / 4) + 2 * real n * pi)  + (8 - 2 * sqrt 2))  < 0"   
            proof -
              have n_ge1: "n \<ge> 1"
                using n_ge_1 by auto 
              have lower_bound: "2 * real n * pi \<ge> 2 * pi"
                using n_ge1 by (simp add: mult_left_mono)
              then have mult_bound: "- (sqrt 2 / 2) * ((5 * pi / 4) + 2 * real n * pi)
                                   \<le> - (sqrt 2 / 2) * (5 * pi / 4 + 2 * pi)"
                by (simp add: mult_left_mono)
              moreover have "(- (sqrt 2 / 2) * (5 * pi / 4 + 2 * pi) + (8 - 2 * sqrt 2)) < 0"
              proof -
                have "5 * pi / 4 + 2 * pi = 13 * pi / 4" 
                  by simp
                then have simpification: "(- (sqrt 2 / 2) * (5 * pi / 4 + 2 * pi) + (8 - 2 * sqrt 2))
                     =     (64 - 16 * sqrt 2 - 13 * pi * sqrt 2) / 8"
                  by (simp add: field_simps)
                have sufficies_to_show_numerator_neg:"((64 - 16 * sqrt 2 - 13 * pi * sqrt 2) / 8 < 0) 
                    = (64 - 16 * sqrt 2 - 13 * pi * sqrt 2 < 0)"
                  by simp
                have "sqrt 2 * (16 + 13 * pi) > 64"
                proof -
                  have pi_gt_3: "pi > 3"
                    by (simp add: pi_gt3)
                  hence "16 + 13 * pi > 16 + 13 * 3" 
                    by (simp add: mult_strict_left_mono)
                  hence "16 + 13 * pi > 55"
                    by simp
                  then have "sqrt 2 * (16 + 13 * pi) > sqrt 2 * 55" 
                    by (simp add: mult_strict_left_mono)
                  moreover have "sqrt 2 * 55 > 64"
                  proof -
                    have "(sqrt 2 * 55)^2 = 2 * 55^2" 
                      by (simp add: power_mult_distrib)
                    also have "... = 2 * (55*55)"
                      by auto 
                    also have "... = 6050" 
                      by simp
                    also have "... > 64*64"
                      by eval                   
                    moreover have "sqrt 2 * 55 > 0" 
                      by simp
                    ultimately show "sqrt 2 * 55 > 64" 
                      using power_mono_iff
                      by (metis less_le power2_eq_square zero_less_numeral)
                  qed
                  ultimately show ?thesis
                    by linarith
                qed
                then have "64 - 16 * sqrt 2 - 13 * pi * sqrt 2 < 0"
                  by (simp add: Groups.mult_ac(2) distrib_left)
                then show ?thesis
                  using simpification sufficies_to_show_numerator_neg by presburger
              qed
              then show ?thesis
                using mult_bound by linarith
            qed
            then show "(left_seq n)\<^sup>2 * sin (1 / left_seq n) +  
                  4 * left_seq n ^ 3 * cos (1 / left_seq n) + 8 * left_seq n ^ 3 < 0"
              by (metis deriv_right_seq_eval first_term_eval mult.commute x_def 
                  zero_compare_simps(10))
          qed        
          show right_seq_greater_zero:"(\<lambda>x. x^2 * sin (1 / x) + 4 * x^3 * cos (1 / x) + 8 * x^3) 
                                                                              (right_seq n) > 0"
        proof - 
          obtain x where x_def: "x  = right_seq n"
            by blast
          then have inv_x_eqs: "inverse x = inverse (inverse (pi + 2 * real n * pi))"
            by (metis id_apply n_pos of_nat_eq_id of_nat_in_Nats of_nat_less_0_iff right_seq_def)
          have x_inv: "1 / x = pi + 2 * real n * pi"
            unfolding right_seq_def by (metis inv_x_eqs inverse_eq_divide inverse_inverse_eq)
        
          have sin_inv_x: "sin (1 / x) = 0"
            by (metis add.inverse_neutral sin_2npi sin_periodic_pi2 x_inv)

          have cos_inv_x: "cos (1 / x) = -1"
            using cos_2npi cos_periodic_pi2 x_inv by presburger

          have f_x: "x^2 * sin (1 / x) + 4 * x^3 * cos (1 / x) + 8 * x^3 = 4 * x^3"
            by (simp add: cos_inv_x sin_inv_x)
                    
          have x_pos: "x > 0"
            unfolding right_seq_def
            by (smt (verit) mult_nonneg_nonneg of_nat_less_0_iff pi_gt_zero x_inv zero_less_divide_iff)    
          then show "0 < (right_seq n)\<^sup>2 * sin (1 / right_seq n) + 4 * right_seq n ^ 3 * cos (1 / right_seq n) + 8 * right_seq n ^ 3"
            using cos_inv_x sin_inv_x x_def by fastforce
        qed

        show "\<exists>y\<in>{left_seq n..right_seq n}. y\<^sup>2 * sin (1 / y) + 4 * y ^ 3 * cos (1 / y) + 8 * y ^ 3 =
                                0 \<and> 0 < 6 * y * sin (1 / y) + (12 * y\<^sup>2 - 1) * cos (1 / y) + 24 * y\<^sup>2"
        proof - 
          have existence_of_minimizing_sequence: "\<exists>y\<in>{left_seq n..right_seq n}. y\<^sup>2 * sin (1 / y) + 4 * y ^ 3 * cos (1 / y) + 8 * y ^ 3 = 0"
          proof -       
            have "\<exists>x\<ge>left_seq n. x \<le> right_seq n \<and> (\<lambda>x. x^2 * sin (1 / x) + 4 * x^3 * cos (1 / x) + 8 * x^3) x = 0"
            proof(rule IVT')
              show "(left_seq n)\<^sup>2 * sin (1 / left_seq n) + 4 * left_seq n ^ 3 * cos (1 / left_seq n) + 8 * left_seq n ^ 3 \<le> 0"
                using left_seq_less_zero by auto
              show "0 \<le> (right_seq n)\<^sup>2 * sin (1 / right_seq n) + 4 * right_seq n ^ 3 * cos (1 / right_seq n) + 8 * right_seq n ^ 3"
                using right_seq_greater_zero by linarith        
              show "left_seq n \<le> right_seq n"
                by (metis id_apply leD linorder_linear n_pos of_nat_eq_id of_nat_in_Nats zero_lt_left_seq_lt_right_seq_both_pos)
              show "continuous_on {left_seq n..right_seq n} (\<lambda>x. x\<^sup>2 * sin (1 / x) + 4 * x ^ 3 * cos (1 / x) + 8 * x ^ 3)"
              proof - \<comment> \<open>We prove continuity by establishing it is differentiable.\<close>
                \<comment> \<open>First, note that \(\mathit{left\_seq}_n\) is positive, so the interval does not contain \(0\).\<close>      
                have left_seq_pos: "left_seq n > 0"
                  by (metis bot_nat_0.extremum_strict id_apply n_pos of_nat_eq_id of_nat_in_Nats zero_lt_left_seq_lt_right_seq_both_pos)
  
                \<comment> \<open>Transfer global differentiability to local differentiability of \(\mathrm{deriv}\,f\).\<close>
    
                have "\<And>x. x \<in> {left_seq n..right_seq n} \<longrightarrow> (\<lambda>x. x\<^sup>2 * sin (1 / x) + 4 * x ^ 3 * cos (1 / x) + 8 * x ^ 3) field_differentiable at x"
                proof clarify
                  fix x::real
                  assume x_type: "x \<in> {left_seq n..right_seq n}"
                  show "(\<lambda>x. x\<^sup>2 * sin (1 / x) + 4 * x ^ 3 * cos (1 / x) + 8 * x ^ 3) field_differentiable at x"
                  proof(rule field_differentiable_transfer_on_ball[where f = "deriv f" and \<epsilon> = "x"])
                    show "0 < x"
                      using left_seq_pos x_type by auto
                    show "\<forall>y. y \<in> ball x x \<longrightarrow> deriv f y = y\<^sup>2 * sin (1 / y) + 4 * y ^ 3 * cos (1 / y) + 8 * y ^ 3"
                      by (simp add: deriv_f)
                    show "deriv f field_differentiable at x"
                      by (meson UNIV_I deriv_f differentiable_on_def field_differentiable_def real_differentiableE)
                  qed
                qed   
                then have "(\<lambda>x. x\<^sup>2 * sin (1 / x) + 4 * x ^ 3 * cos (1 / x) + 8 * x ^ 3) differentiable_on {left_seq n..right_seq n}"
                  by (meson differentiable_at_imp_differentiable_on field_differentiable_imp_differentiable)
                then show ?thesis
                  using differentiable_imp_continuous_on by blast
              qed
            qed    
            then show "\<exists>y\<in>{left_seq n..right_seq n}. y\<^sup>2 * sin (1 / y) + 4 * y ^ 3 * cos (1 / y) + 8 * y ^ 3 = 0"
              by presburger
          qed
          then obtain min_n where min_n_def: "min_n  \<in>{left_seq n..right_seq n} \<and> min_n\<^sup>2 * sin (1 / min_n) + 4 * min_n ^ 3 * cos (1 / min_n) + 8 * min_n ^ 3 = 0"
            by blast
          have "\<And>y. y \<in> {left_seq n .. right_seq n} \<longrightarrow> 0 < 6 * y * sin (1 / y) + (12 * y\<^sup>2 - 1) * cos (1 / y) + 24 * y\<^sup>2"
          proof (clarify)
            fix y :: real
            assume y_int: "y \<in> {left_seq n .. right_seq n}"
            \<comment> \<open>Since \(\mathit{left\_seq}_n > 0\), every \(y\) in the interval is positive.\<close>
            then have y_pos: "y > 0"
              by (metis atLeastAtMost_iff bot_nat_0.extremum id_apply linorder_not_less n_pos 
                  of_nat_eq_id of_nat_in_Nats order_less_le_trans zero_lt_left_seq_lt_right_seq_both_pos)   
            have "\<exists> x_nc :: real \<Rightarrow> real. \<forall> c \<in> {0..pi/4}. x_nc c = inverse (pi + c + 2*pi*real n)"
              by auto
            then obtain x_nc :: "real \<Rightarrow> real" where x_nc_def: "\<forall> c \<in> {0..pi/4}. x_nc c = inverse (pi + c + 2*pi*real n)"
              by auto
             have "\<exists> x_nc :: real \<Rightarrow> real. \<forall> c \<in> {0..pi/4}. x_nc c = inverse (pi + c + 2*pi*real n)"
              by auto
            then obtain x_nc :: "real \<Rightarrow> real" where x_nc_def: "\<forall> c \<in> {0..pi/4}. x_nc c = inverse (pi + c + 2*pi*real n)"
              by auto
            have continuous_on_subinterval: "continuous_on {0..pi/4} x_nc"
            proof -
              have cont_denom: "continuous_on {0..pi/4} (\<lambda>c. pi + c + 2*pi*real n)"
              proof -
                have "continuous_on {0..pi/4} (\<lambda>c. c)"
                  using continuous_on_id by blast 
                moreover have "continuous_on {0..pi/4} (\<lambda>c. pi + 2*pi*real n)"
                  using continuous_on_const by blast
                ultimately show ?thesis
                  by (simp add: continuous_on_add)
              qed
              then have "continuous_on {0..pi/4} (\<lambda>x. inverse ((\<lambda>c. pi + c + 2*pi*real n) x))"
                by(rule continuous_on_inverse,
                   smt (verit) add_mono_thms_linordered_field(4) atLeastAtMost_iff
                     of_nat_less_0_iff pi_neq_zero pi_not_less_zero zero_compare_simps(4))           
              then show ?thesis
                using continuous_on_cong x_nc_def by fastforce 
            qed
  
            have minimizer_dom: "\<exists>x. 0 \<le> x \<and> x \<le> pi/4 \<and> x_nc x = y"
            proof(rule IVT2')
              show "x_nc (pi / 4) \<le> y"
              proof - 
                have "x_nc (pi / 4) = inverse ( pi  +  pi / 4 + 2 * real n * pi)"
                  by (metis (no_types, opaque_lifting) atLeastAtMost_iff divide_eq_imp 
                      divide_real_def linorder_not_less mult.left_commute mult.right_neutral 
                      mult_le_0_iff nle_le of_nat_0_le_iff of_nat_numeral pi_gt_zero x_nc_def 
                      zero_neq_numeral)
                also have "... = inverse ((5 * pi / 4) + 2 * real n * pi)"
                  by simp
                also have "... = left_seq n"
                  by (metis bot_nat_0.not_eq_extremum id_apply left_seq_def n_pos of_nat_eq_id of_nat_in_Nats)
                also have "... \<le> y"
                  using y_int by presburger
                finally show ?thesis.
              qed
              show "y \<le> x_nc 0"
              proof - 
                have "y \<le> right_seq n"
                  using y_int by presburger
                also have "... = inverse  (pi + 2 * real n * pi)"
                  by (metis bot_nat_0.not_eq_extremum id_apply n_pos of_nat_eq_id of_nat_in_Nats right_seq_def)
                also have "... = x_nc 0"
                  using x_nc_def by auto
                finally show ?thesis.
              qed
              show "0 \<le> pi / 4"
                by simp
              show "continuous_on {0..pi / 4} x_nc"
                using continuous_on_subinterval by simp
            qed
            then have minimizer_dom': "\<exists>c \<in> {0..pi/4}. y = x_nc c"
              using atLeastAtMost_iff by blast
   
            \<comment> \<open>We will show that \(f''(x_{nc}(c)) > 0\) for all \(c \in [0,1]\), 
            then use the fact that \(\mathit{left\_seq}_n \le x_{nc}(c) \le \mathit{right\_seq}_n\) 
            together with the IVT to establish the existence of \(c \in [0,\tfrac{\pi}{4}]\) 
            such that \(x_{nc}(c) = y\), and then conclude that \(f''(y) > 0\).\<close>

            have snd_deriv_positive_in_neighborhood: "\<forall>c \<in> {0..pi/4}. left_seq n \<le> x_nc c \<and> x_nc c \<le> right_seq n \<and> deriv (deriv f) (x_nc c) > 0"
            proof (safe)
              fix c :: real
              assume c_type: "c \<in> {0..pi/4}"
              then have c_bounds: "0 \<le> c \<and> c \<le> pi/4"
                by simp
              
              have x_nc_eqs: "x_nc c = inverse (pi + c + 2*pi*real n)"
                using c_bounds inverse_eq_divide pi_half_le_two x_nc_def by auto      
              show "left_seq n \<le> x_nc c"
              proof - 
                have f1: "left_seq n = inverse ((5 * pi / 4) + 2 * real n * pi)"
                  by (metis bot_nat_0.not_eq_extremum id_apply left_seq_def n_pos of_nat_eq_id of_nat_in_Nats)              
                from c_bounds have "1/ ((5 * pi / 4) + 2 * real n * pi) \<le> 1/ (pi + c + 2*pi*real n)"
                  by(subst frac_le, simp_all, simp add: add_sign_intros(1))
                then show ?thesis
                  by (simp add: f1 x_nc_eqs inverse_eq_divide)
              qed
  
              then have x_nc_pos: "x_nc c > 0"
                by (metis id_apply n_pos of_nat_eq_id of_nat_in_Nats order_less_le_trans zero_lt_left_seq_lt_right_seq_both_pos zero_order(5))
  
              show "x_nc c \<le> right_seq n"
              proof -
                have f1: "right_seq n = inverse (pi + 2 * real n * pi)"
                  by (metis bot_nat_0.not_eq_extremum id_apply n_pos of_nat_eq_id of_nat_in_Nats right_seq_def)
                from c_bounds have "1/ (pi + c + 2*pi*real n) \<le> 1 /(pi + 2 * real n * pi)"
                  by(subst frac_le, simp_all, smt (verit, del_insts) m2pi_less_pi mult_sign_intros(1) of_nat_less_0_iff)
                then show ?thesis
                  by (simp add: f1 x_nc_eqs inverse_eq_divide)   
              qed
  
              \<comment> \<open>Bounds on \(\sin(c)\) and \(\cos(c)\).\<close>
              have "pi + c + 2*pi*real n \<ge> 3*pi"
              proof -
                have "pi + c + 2*pi*real n \<ge> pi + 0 + 2*pi*real 1"
                  by (smt (verit, best) Num.of_nat_simps(2) c_bounds mult_left_mono n_ge_1 
                      pi_not_less_zero real_of_nat_ge_one_iff)
                then show ?thesis
                  by linarith
              qed
              then have x_nc_bound: "x_nc c \<le> inverse(3*pi)"
                by (smt (verit) le_imp_inverse_le pi_gt_zero x_nc_eqs)     
              then have cos_coef_bound: "(1- 12 * (x_nc c)\<^sup>2) \<ge> (1- 12 * (inverse(3*pi))\<^sup>2)"
                using x_nc_pos by force
  
              have sin_bound: "0 \<le> sin c \<and> sin c \<le> sqrt(2)/2"
              proof safe
                show "0 \<le> sin c"
                  using c_bounds sin_ge_zero by auto
                show "sin c \<le> sqrt(2)/2"
                  by (smt (verit, best) c_bounds frac_le pi_not_less_zero sin_45 sin_mono_less_eq)
              qed
              have cos_bound: "sqrt(2)/2 \<le> cos c \<and> cos c \<le> 1"
              proof safe
                show "sqrt 2 / 2 \<le> cos c"
                  by (smt (verit) c_bounds cos_45 cos_monotone_0_pi_le machin pi_machin)  
                show "cos c \<le> 1"
                  by simp
              qed
  
              show "0 < deriv (deriv f) (x_nc c)"
              proof - 
                \<comment> \<open>Lower bound of \(f''(x_{nc})\).\<close>
                have snd_deriv_at_x_nc: "deriv (deriv f) (x_nc c) = (1- 12 * (x_nc c)\<^sup>2) * cos c - 6 * (x_nc c) * sin c + 24 * (x_nc c)\<^sup>2"
                proof-  
                  have f1: "sin (1 / (x_nc c)) = -sin c"
                  proof - 
                    have "sin (1 / (x_nc c)) = sin (pi + c + 2*pi*real n)"
                      by (simp add: inverse_eq_divide x_nc_eqs)
                    also have "... = sin (pi + c)"
                      by (metis Groups.mult_ac(2) id_apply of_real_eq_id sin.plus_of_nat)
                    also have "... = -sin c"
                      by simp
                    finally show ?thesis.
                  qed
                  have f2: "cos (1 / (x_nc c)) = -cos c"
                  proof - 
                    have "cos (1 / (x_nc c)) = cos (pi + c + 2*pi*real n)"
                      by (simp add: inverse_eq_divide x_nc_eqs)
                    also have "... = cos (pi + c)"
                      by (metis Groups.mult_ac(2) id_apply of_real_eq_id cos.plus_of_nat)
                    also have "... = -cos c"
                      by simp
                    finally show ?thesis.
                  qed
    
                  have "deriv (deriv f) (x_nc c) = (12*(x_nc c)\<^sup>2 - 1)* cos (1 / (x_nc c)) + 6*(x_nc c) * sin (1 / (x_nc c)) + 24*(x_nc c)\<^sup>2"
                    using deriv_f x_nc_pos by auto
                  also have "... = (1- 12 * (x_nc c)\<^sup>2) * cos c - 6 * (x_nc c) * sin c + 24 * (x_nc c)\<^sup>2"
                    by (smt (verit) f1 f2 minus_mult_commute more_arith_simps(8))
                  finally show ?thesis.
                qed
                have snd_deriv_bound: "deriv (deriv f) (x_nc c) \<ge> (1 - 12 * (x_nc c)\<^sup>2 - 6 * (x_nc c)) * (sqrt 2 / 2)"
                proof -                 
                  have "deriv (deriv f) (x_nc c) \<ge> (1- 12 * (x_nc c)\<^sup>2) * cos c - 6 * (x_nc c) * (sqrt(2)/2) + 24 * (x_nc c)\<^sup>2"
                    using snd_deriv_at_x_nc sin_bound x_nc_pos by auto
                  also have "... \<ge> (1 - 12 * (x_nc c)\<^sup>2 - 6 * (x_nc c)) * (sqrt 2 / 2)"
                    by (smt (verit, best) calculation cos_bound divide_pos_pos one_power2 real_le_rsqrt right_diff_distrib' sum_le_prod1 vector_space_over_itself.scale_left_diff_distrib zero_compare_simps(12))
                  then show ?thesis.
                qed
  
                show "0 < deriv (deriv f) (x_nc c)"
                proof - 
                  obtain h :: "real \<Rightarrow> real" where h_def: "h = (\<lambda>x.  - 12 * x\<^sup>2 - 6 * x + 1)"
                    by auto      
                  have diff_h: "\<forall>x. h field_differentiable at x"
                    unfolding h_def
                  proof clarify
                    fix x::real
                    have d1: "(\<lambda>x.  - 12 * x\<^sup>2) field_differentiable at x"
                      by(rule field_differentiable_mult, simp, simp add: field_differentiable_power)
                    have d2: "(\<lambda>x.  - 6 * x) field_differentiable at x"
                      by(rule field_differentiable_mult, simp, simp add: field_differentiable_power)
                    from d1 d2 show "(\<lambda>x.  - 12 * x\<^sup>2 - 6 * x + 1) field_differentiable at x"
                      by(subst field_differentiable_add, simp add: Derivative.field_differentiable_diff, simp_all)
                  qed
    
                  have h_roots: "\<forall>x. h x = 0 \<longleftrightarrow> x = (-6 + sqrt 84) / 24 \<or> x = (-6 - sqrt 84) / 24"
                  proof(clarify)
                    fix x ::real
                    have roots: "(12 * x\<^sup>2 + 6 * x + (-1) = 0) = (x = (- 6 + sqrt (6\<^sup>2 - 4 * 12 * (-1))) / (2 * 12) \<or> x = (- 6 - sqrt (6\<^sup>2 - 4 * 12 * (-1))) / (2 * 12))"                                   
                      using discrim_def by(subst discriminant_iff, eval, force)                                                            
                    then show "(h x = 0) = (x = (- 6 + sqrt 84) / 24 \<or> x = (- 6 - sqrt 84) / 24)"
                        using h_def by auto
                  qed  
  
                  have right_root_positive: "(- 6 + sqrt 84) / 24 > 0"                  
                  proof - 
                    have "- 6 + sqrt 84 > - 6 + sqrt 64"
                      by (smt (verit) real_sqrt_less_mono)
                    then show "(- 6 + sqrt 84) / 24 > 0"
                      by simp
                  qed
                  then have left_root_neg: "0 > (- 6 - sqrt 84) / 24"
                    by fastforce
                  have h_pos_on_interval: "\<forall> x \<in> {0..<(-6 + sqrt 84) / 24}. h x > 0"
                  proof(rule ccontr)
                    assume "\<not> (\<forall>x\<in>{0..<(- 6 + sqrt 84) / 24}. 0 < h x)"
                    then obtain z where z_def: "z \<in> {0..<(- 6 + sqrt 84) / 24} \<and> 0 \<ge> h z"
                      by fastforce
                    then have z_not_root: "z \<noteq> (- 6 + sqrt 84) / 24 \<and> z \<noteq> (- 6 - sqrt 84) / 24"
                      using z_def by force                                  
                    show False
                    proof(cases "h z = 0")
                      show "h z = 0 \<Longrightarrow> False"
                        using h_roots z_not_root by blast
                    next
                      assume "h z \<noteq> 0"
                      then have hz_neg: "h z < 0"
                        using z_def by auto                    
                      have "\<exists>x. 0 \<le> x \<and> x \<le> z \<and> h x = 0"
                      proof(rule IVT2')
                        show "h z \<le> 0"
                          by (simp add: z_def)
                        show "0 \<le> h 0"
                          by (simp add: h_def)
                        show "0 \<le> z"
                          using z_def by fastforce
                        show "continuous_on {0..z} h"
                          by (meson continuous_at_imp_continuous_on diff_h field_differentiable_imp_continuous_at)
                      qed
                      then show False
                        by (metis atLeastLessThan_iff h_roots left_root_neg not_less z_def)
                    qed
                  qed
                   
                  have "(-6 + sqrt 84) / 24 > 1 / (3 * pi)"
                  proof -
                    have i1: "64 / pi^2 < 8"
                    proof -
                      have "pi*pi > 3*3"
                        by (meson pi_gt3 mult_strict_mono pi_gt_zero verit_comp_simplify(7))
                      then have "pi^2 > 9"
                        by (simp add: power2_eq_square)       
                      then have "64/pi^2 < 64/8"
                        by (smt (verit) frac_less2)
                      also have "... = 8"
                        by eval
                      finally show ?thesis.
                    qed
                      
                    have i2: "96/pi < 32"                    
                    proof - 
                      have "96/pi < 96/3"
                        by (meson frac_less2 order.refl pi_gt3 verit_comp_simplify(19))
                      also have "... = 32"
                        by eval
                      finally show ?thesis.
                    qed
    
                    have "(8/pi + 6)\<^sup>2 < 84"
                    proof - 
                      have "((8::real)/pi + 6)\<^sup>2 = (8/pi)\<^sup>2 + 2*(8/pi)*6 + 6\<^sup>2"
                        by (simp add: power2_sum)
                      also have "... = 8\<^sup>2/pi\<^sup>2 + 2*(8/pi)*6 + 6\<^sup>2"
                        by (simp add: power_divide)
                      also have "... = 64/pi\<^sup>2 +96/pi + 36"
                        by simp
                      also have "... < 84"
                        using i1 i2 by linarith
                      finally show ?thesis.
                    qed
                    then have lt_sqrt84: "8/pi + 6 < sqrt(84)"
                      using real_less_rsqrt by presburger
                    have lt_3pi_sqrt84: "24 + 18*pi < 3 * pi  * sqrt (84)"
                    proof - 
                      have "24 + 18*pi = 3*8 + 3*6*pi"
                        by simp
                      also have "... = 3*pi*(8/pi) + 3*pi*6"
                        by simp
                      also have "... = 3*pi*((8/pi)+6)"
                        by (simp add: distrib_left)
                      also have "... < 3 * pi * sqrt(84)"
                        by (simp add: lt_sqrt84)
                      finally show ?thesis.
                    qed
                    have "(-6+sqrt(84))*(3*pi) > 24"
                    proof - 
                      have "(-6+sqrt(84))*(3*pi) = -6*(3*pi) + sqrt(84)*(3*pi)"
                        by (meson ring_class.ring_distribs(2))
                      also have "... =  -18*pi + 3*pi * sqrt(84)"
                        by simp
                      also have "... > 24"
                        using lt_3pi_sqrt84 by auto
                      finally show ?thesis.
                    qed
                    then have "(-6+sqrt(84))*(3*pi) / 24 > 1"
                      by simp
                    then show "(-6+sqrt(84)) / 24 > 1 / (3*pi)"
                      by (metis pi_gt_zero pos_divide_less_eq times_divide_eq_left zero_compare_simps(6) zero_less_numeral)
                  qed
                  then have "x_nc c < (-6+sqrt(84)) / 24"
                    by (metis dual_order.strict_trans2 inverse_eq_divide x_nc_bound)
                  then have h_x_nc_pos: "h (x_nc c) > 0"
                    by (simp add: h_pos_on_interval less_eq_real_def x_nc_pos)
  
                  have "deriv (deriv f) (x_nc c) \<ge> (sqrt(2)/2) * h (x_nc c)"
                    by (metis Groups.mult_ac(2) snd_deriv_bound diff_add_eq h_def mult_minus_left uminus_add_conv_diff)
                  then show ?thesis
                    by (smt (verit) h_x_nc_pos half_gt_zero_iff mult_pos_pos real_sqrt_gt_0_iff)
                qed
              qed
            qed
                     
            then show "0 < 6 * y * sin (1 / y) + (12 * y\<^sup>2 - 1) * cos (1 / y) + 24 * y\<^sup>2"
              by (smt (verit, best) deriv_f minimizer_dom')
          qed
            then show "\<exists>y\<in>{left_seq n..right_seq n}. y\<^sup>2 * sin (1 / y) + 4 * y ^ 3 * cos (1 / y) + 8 * y ^ 3 = 0 \<and> 0 < 6 * y * sin (1 / y) + (12 * y\<^sup>2 - 1) * cos (1 / y) + 24 * y\<^sup>2"
              using min_n_def by blast
        qed
      qed
    qed

    have optimality_conditions: "\<forall>n. n \<noteq> 0 \<longrightarrow> (\<exists> y \<in> {left_seq n .. right_seq n}. (deriv f) y = 0 \<and> deriv (deriv f) y  > 0)"
    proof clarify
      fix n::nat
      assume "0 < n"
      then obtain min_n where min_n_def:  "min_n \<in>{left_seq n..right_seq n} 
                                   \<and> min_n\<^sup>2 * sin (1 / min_n) + 4 * min_n ^ 3 * cos (1 / min_n) + 8 * min_n ^ 3 = 0
                                   \<and> 0 < 6 * min_n * sin (1 / min_n) + (12 * min_n\<^sup>2 - 1) * cos (1 / min_n) + 24 * min_n\<^sup>2"
        using first_and_second_order_conditions bot_nat_0.not_eq_extremum by presburger
      have fst_order_condition: "deriv f min_n = 0"
        using deriv_f min_n_def by presburger
      have snd_order_condition: "deriv (deriv f) min_n > 0"
        using deriv_f min_n_def by fastforce
      show "\<exists>y\<in>{left_seq n..right_seq n}. deriv f y = 0 \<and> 0 < deriv (deriv f) y"
        using fst_order_condition min_n_def snd_order_condition by blast
    qed

    have seq_of_local_minizers_exists: "\<forall>n. n \<noteq> 0 \<longrightarrow> (\<exists> y \<in> {left_seq n .. right_seq n}. local_minimizer f y)"
    proof(clarify)
      fix n::nat
      assume n_pos: "0 < n"
      then obtain y where y_def: "(y \<in> {left_seq n .. right_seq n} \<and> (deriv f) y = 0 \<and> deriv (deriv f) y  > 0)"
        using gr_implies_not0 optimality_conditions by presburger
      have right_seq_def2: "right_seq n = inverse (pi + 2 * real n * pi)"
        by (metis id_apply less_not_refl n_pos of_nat_eq_id of_nat_in_Nats right_seq_def)
                  
      have "y \<in> {left_seq n..right_seq n} \<and> local_minimizer f y"
      proof(subst second_derivative_test[where a = "left_seq n", where b = "right_seq n"])  
        show proper_interval: "left_seq n < right_seq n"
          by (metis (no_types) id_apply n_pos of_nat_eq_id of_nat_in_Nats rel_simps(70) zero_lt_left_seq_lt_right_seq_both_pos)
        show "C_k_on 2 f {left_seq n <..<right_seq n}"
        proof(rule C_k_on_subset[where U = "{0<..<(1::real)}"])
          show f_contin_diff_on_right: "C_k_on 2 f {0<..<(1::real)}"
          proof(rule C2_on_open_U_def2)
            show "open {0<..<(1::real)}"
              using lemma_interval by(subst open_dist, subst dist_real_def, simp add: abs_minus_commute lemma_interval_lt)
            show "f differentiable_on {0<..<(1::real)}"
              by (meson deriv_f differentiable_on_subset top.extremum)
            show "deriv f differentiable_on {0<..<(1::real)}"
              by (meson deriv_f differentiable_on_subset top.extremum)
            show "continuous_on {0<..<(1::real)} (deriv (deriv f))"
            proof - 
              have "\<forall>x \<in> {0<..<1}. deriv (deriv f) x = 6*x * sin(1/x) + (12*x^2 - 1)*cos(1/x) + 24*x^2"
                by (simp add: deriv_f)
              moreover have "continuous_on {0<..<(1::real)} (\<lambda>x. 6*x * sin(1/x) + (12*x^2 - 1)*cos(1/x) + 24*x^2)"               
              proof - 
                have "{0<..<(1::real)} \<subseteq> {x :: real. x>0}"
                  by fastforce
                moreover have "continuous_on {x :: real. x>0} (\<lambda>x. 6*x * sin(1/x) + (12*x^2 - 1)*cos(1/x) + 24*x^2)"               
                  by (auto intro!: continuous_intros)
                ultimately show ?thesis
                  using  continuous_on_subset by blast
              qed
              ultimately show "continuous_on {0<..<1} (deriv (deriv f))"
                using continuous_on_cong by fastforce
            qed
          qed

          show "open {left_seq n<..<right_seq n} \<and> {left_seq n<..<right_seq n} \<subset> {0<..<1}"
          proof -
            have "0 < left_seq n"
              by (metis id_apply n_pos of_nat_eq_id of_nat_in_Nats order.asym zero_lt_left_seq_lt_right_seq_both_pos)
            moreover have "right_seq n < 1"
              using right_seq_def2
              by (smt (verit, ccfv_SIG) inverse_1 inverse_le_imp_le mult_sign_intros(5) n_pos of_nat_0_less_iff pi_gt3)
            ultimately show ?thesis
              using proper_interval by fastforce
          qed
        qed

        show "y \<in> {left_seq n<..<right_seq n}"
        proof - 
          have "y \<in> {left_seq n..right_seq n}"
            using y_def by blast
          moreover have "y \<noteq> left_seq n"
          proof(rule ccontr)
            assume "\<not> y \<noteq> left_seq n"
            then have "deriv f y \<noteq> 0"           
              using deriv_f first_and_second_order_conditions
              by (metis n_pos rel_simps(70) y_def)
            then show False
              by (simp add: y_def)
          qed
          moreover have "y \<noteq> right_seq n"
          proof(rule ccontr)
            assume "\<not> y \<noteq> right_seq n"
            then have "deriv f y \<noteq> 0"              
              using deriv_f first_and_second_order_conditions
              by (metis n_pos rel_simps(70) y_def)
            then show False
              by (simp add: y_def)
          qed
          ultimately show "y \<in> {left_seq n<..<right_seq n}"
            by auto
        qed
        show "deriv f y = 0" and "0 < deriv (deriv f) y" 
          using y_def by auto
        show "y \<in> {left_seq n..right_seq n} \<and> True"
          using y_def by blast
      qed
      then show "\<exists>y\<in>{left_seq n..right_seq n}. local_minimizer f y"
        by blast
    qed
    show "\<exists>x_seq. (\<forall>n. local_minimizer f (x_seq n) \<and> x_seq n \<noteq> 0) \<and> x_seq \<longlonglongrightarrow> 0"
    proof -
      define x_seq where
        "x_seq n = (SOME y. y \<in> {left_seq (n+1)..right_seq (n+1)} \<and> local_minimizer f y)" for n
      have x_seq_prop: "\<forall>n. x_seq n \<in> {left_seq (n+1)..right_seq (n+1)} \<and> local_minimizer f (x_seq n)"
        by (metis (mono_tags, lifting) seq_of_local_minizers_exists someI_ex verit_eq_simplify(7) x_seq_def zero_eq_add_iff_both_eq_0)
      
      from x_seq_prop have bounds: "\<forall>n. left_seq (n+1) \<le> x_seq n \<and> x_seq n \<le> right_seq (n+1)"
        by auto
 
      have nonzero: "\<forall>n. x_seq n \<noteq> 0"
        by (metis Suc_eq_plus1 bounds id_apply nat.simps(3) not_less of_nat_eq_id of_nat_in_Nats zero_lt_left_seq_lt_right_seq_both_pos)
    
      have left_seq_converges: "left_seq \<longlonglongrightarrow> 0"
      proof (rule LIMSEQ_I)
        fix \<epsilon> :: real
        assume \<epsilon>_pos: "0 < \<epsilon>"
        then obtain N where N_def: "(N::nat) = \<lceil>1 / (2 * pi * \<epsilon>)\<rceil> + 1"
          by (metis add_mono_thms_linordered_field(5) arithmetic_simps(50) divide_pos_pos 
              mult_sign_intros(5) pi_gt_zero pos_int_cases semiring_norm(172) 
              zero_less_ceiling zero_less_numeral)
        then have N_gt_0: "N > 0"
          by (smt (verit) \<epsilon>_pos divide_pos_pos gr0I int_ops(1) m2pi_less_pi mult_sign_intros(5) zero_less_ceiling)
                   
        have "\<forall>n \<ge> N. \<bar>left_seq n\<bar> < \<epsilon>"
        proof clarify
          fix n :: nat 
          assume n_ge: "n \<ge> N"                   
          have left_seq_eqs: "left_seq n = inverse ((5 * pi / 4) + 2 * pi * real n)"
            unfolding left_seq_def
            by (metis N_gt_0 id_apply left_seq_def linorder_not_less mult.commute n_ge of_nat_eq_id of_nat_in_Nats vector_space_over_itself.scale_scale)
          show "\<bar>left_seq n\<bar> < \<epsilon>"
          proof - 
            have "\<bar>left_seq n\<bar> = 1 / ((5 * pi / 4) + 2 * pi * real n)"
              by (simp add: left_seq_eqs inverse_eq_divide)              
            also have "... \<le>  1 / (2 * pi * real N)"
              by (smt (verit, best) N_gt_0 divide_nonneg_nonneg frac_le m2pi_less_pi mult_left_mono mult_sign_intros(5) n_ge of_nat_0_less_iff of_nat_mono)
            also have "... <  1 / (2 * pi * (\<lceil>1 / (2 * pi * \<epsilon>)\<rceil>))"
              by (smt (verit, best) N_def \<epsilon>_pos ceiling_correct divide_pos_pos frac_less2 m2pi_less_pi mult_less_cancel_left_pos mult_sign_intros(5) of_int_1 of_int_add of_int_of_nat_eq)
            also have "... \<le> 1 / (2 * pi * (1 / (2 * pi * \<epsilon>)))"
              by (smt (verit, ccfv_SIG) \<epsilon>_pos ceiling_correct frac_le mult_left_mono mult_sign_intros(5) pi_gt_zero zero_less_divide_iff)
            also have "... = \<epsilon>"
              by simp
            finally show ?thesis.
          qed
        qed
        then show "\<exists>N. \<forall>n\<ge>N. \<parallel>left_seq n - 0\<parallel> < \<epsilon>"
          by (metis cancel_comm_monoid_add_class.diff_zero real_norm_def)
      qed
      have right_seq_converges: "right_seq \<longlonglongrightarrow> 0"
      proof (rule LIMSEQ_I)
        fix \<epsilon>::real
        assume eps_pos: "0 < \<epsilon>"
        then obtain N where N_def: "(N::nat) = \<lceil>1 / (2 * pi * \<epsilon>)\<rceil> + 1"
          by (metis add_mono_thms_linordered_field(5) arithmetic_simps(50) divide_pos_pos 
                    mult_sign_intros(5) pi_gt_zero pos_int_cases semiring_norm(172)
                    zero_less_ceiling zero_less_numeral)
        hence N_gt_0: "N > 0"
          by (smt (verit) eps_pos divide_pos_pos gr0I int_ops(1) m2pi_less_pi mult_sign_intros(5) 
                    zero_less_ceiling)
      
        have "\<forall>n\<ge>N. \<bar>right_seq n\<bar> < \<epsilon>"
        proof clarify
          fix n :: nat
          assume n_ge: "n \<ge> N"
          have right_seq_eqs: "right_seq n = inverse (pi + 2 * pi * real n)"
            unfolding right_seq_def
            by (metis N_gt_0 id_apply linorder_not_less mult.commute mult.left_commute n_ge of_nat_eq_id of_nat_in_Nats right_seq_def)            
          show "\<bar>right_seq n\<bar> < \<epsilon>"
          proof -
            have "\<bar>right_seq n\<bar> = 1 / (pi + 2 * pi * real n)"
              by (simp add: right_seq_eqs inverse_eq_divide)
            also have "... \<le> 1 / (2 * pi * real N)"
              by (smt (verit, best) N_gt_0 divide_nonneg_nonneg frac_le m2pi_less_pi 
                        mult_left_mono mult_sign_intros(5) n_ge of_nat_0_less_iff of_nat_mono)
            also have "... < 1 / (2 * pi * (\<lceil>1 / (2 * pi * \<epsilon>)\<rceil>))"
              by (smt (verit, best) N_def eps_pos ceiling_correct divide_pos_pos frac_less2 m2pi_less_pi 
                        mult_less_cancel_left_pos mult_sign_intros(5) of_int_1 of_int_add of_int_of_nat_eq)
            also have "... \<le> 1 / (2 * pi * (1 / (2 * pi * \<epsilon>)))"
              by (smt (verit, ccfv_SIG) eps_pos ceiling_correct frac_le mult_left_mono 
                        mult_sign_intros(5) pi_gt_zero zero_less_divide_iff)
            also have "... = \<epsilon>"
              by simp
            finally show ?thesis
              by blast
          qed
        qed
        then show "\<exists>no. \<forall>n\<ge>no. \<parallel>right_seq n - 0\<parallel> < \<epsilon>"
          by (metis cancel_comm_monoid_add_class.diff_zero real_norm_def)
      qed
      have x_seq_converges: "x_seq \<longlonglongrightarrow> 0"
      proof (rule LIMSEQ_I)
        fix \<epsilon> :: real
        assume \<epsilon>_pos: "0 < \<epsilon>"
      
        obtain N\<^sub>0 where N\<^sub>0: "\<forall>n\<ge>N\<^sub>0. \<parallel>left_seq (n+1) - 0\<parallel> < \<epsilon>"
          using left_seq_converges
          by (meson LIMSEQ_iff \<epsilon>_pos le_diff_conv) 
      
        obtain N\<^sub>1 where N\<^sub>1: "\<forall>n\<ge>N\<^sub>1. \<parallel>right_seq (n+1) - 0\<parallel> < \<epsilon>"
          using right_seq_converges
          by (meson LIMSEQ_iff \<epsilon>_pos le_diff_conv) 
      
        obtain N where "N = max N\<^sub>0 N\<^sub>1"
          by simp
        hence N_def: "N \<ge> N\<^sub>0 \<and> N \<ge> N\<^sub>1"
          by simp
      
        show "\<exists>N. \<forall>n\<ge>N. \<parallel>x_seq n - 0\<parallel> < \<epsilon>"
        proof (intro exI[where x=N] exI allI impI)
          fix n :: nat
          assume N_leq_n: "N \<le> n"
          
          from bounds have "left_seq (n+1) \<le> x_seq n \<and> x_seq n \<le> right_seq (n+1)"
            by auto
          hence "\<parallel>x_seq n\<parallel> \<le> \<parallel>left_seq (n+1)\<parallel> \<or> \<parallel>x_seq n\<parallel> \<le> \<parallel>right_seq (n+1)\<parallel>"
            by force
          moreover have "\<parallel>left_seq (n+1)\<parallel> < \<epsilon> \<and> \<parallel>right_seq (n+1)\<parallel> < \<epsilon>"
            using N\<^sub>0 N\<^sub>1 N_leq_n N_def by auto           
          ultimately show "\<parallel>x_seq n - 0\<parallel> < \<epsilon>"
            by auto
        qed
      qed
      then show ?thesis
        using nonzero x_seq_prop by blast
    qed
  qed
  then show ?thesis
    using zero_min f_cont not_isolated_minimizer_def strict_local_minimizer_at_0 by auto
qed

end