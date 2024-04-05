section \<open>Catalan numbers\<close>

theory Catalan_Auxiliary_Integral
imports "HOL-Analysis.Analysis" "HOL-Real_Asymp.Real_Asymp"
begin

subsection \<open>Auxiliary integral\<close>

text \<open>
  First, we will prove the integral $$\int\limits_0^4 \sqrt{\frac{4-x}{x}}\,\textrm{d}x = 2\pi$$
  which occurs in the proof for the integral formula for the Catalan numbers.
\<close>

context
begin

text \<open>
  We prove the integral by explicitly constructing the indefinite integral.
\<close>
lemma catalan_aux_integral:
  "((\<lambda>x::real. sqrt ((4 - x) / x)) has_integral 2 * pi) {0..4}"
proof -
  define F where "F \<equiv> \<lambda>x. sqrt (4/x - 1) * x - 2 * arctan ((sqrt (4/x - 1) * (x - 2)) / (x - 4))"
    \<comment> \<open>The nice part of the indefinite integral. The endpoints are removable singularities.\<close>
    
  define G where "G \<equiv> \<lambda>x. if x = 4 then pi else if x = 0 then -pi else F x"
    \<comment> \<open>The actual indefinite integral including the endpoints.\<close>

  \<comment> \<open>We now prove that the indefinite integral indeed tends to @{term "pi"} resp. @{term "-pi"} 
      at the edges of the integration interval.\<close>
  have "(F \<longlongrightarrow> -pi) (at_right 0)"
    unfolding F_def by real_asymp
  (* TODO: Why can real_asymp not show the thing below? *)
  hence G_0: "(G \<longlongrightarrow> -pi) (at_right 0)" unfolding G_def
    by (rule Lim_transform_eventually) (auto intro!: eventually_at_rightI[of 0 1])  

  have "(F \<longlongrightarrow> pi) (at_left 4)"
    unfolding F_def by real_asymp
  hence G_4: "(G \<longlongrightarrow> pi) (at_left 4)" unfolding G_def
    by (rule Lim_transform_eventually) (auto intro!: eventually_at_leftI[of 1])
  
  \<comment> \<open>The derivative of @{term G} is indeed the integrand in the interior of 
      the integration interval.\<close>
  have deriv_G: "(G has_field_derivative sqrt ((4 - x) / x)) (at x)" if x: "x \<in> {0<..<4}" for x
  proof -
    from x have "eventually (\<lambda>y. y \<in> {0<..<4}) (nhds x)"
      by (intro eventually_nhds_in_open) simp_all
    hence eq: "eventually (\<lambda>x. F x = G x) (nhds x)" by eventually_elim (simp add: G_def)
    
    define T where "T \<equiv> \<lambda>x::real. 4 / (sqrt (4/x - 1) * (x - 4) * x^2)"
    have *: "((\<lambda>x. (sqrt (4/x - 1) * (x - 2)) / (x - 4)) has_field_derivative T x) (at x)"
      by (insert x, rule derivative_eq_intros refl | simp)+
         (simp add: divide_simps T_def, simp add: field_simps power2_eq_square)
    have "((\<lambda>x. 2 * arctan ((sqrt (4/x - 1) * (x - 2)) / (x - 4))) has_field_derivative 
             2 * T x / (1 + (sqrt (4 / x - 1) * (x - 2) / (x - 4))\<^sup>2)) (at x)"
      by (rule * derivative_eq_intros refl | simp)+ (simp add: field_simps)
    also from x have "(sqrt (4 / x - 1) * (x - 2) / (x - 4))\<^sup>2 = (4/x - 1) * (x-2)^2 / (x - 4)^2"
      by (simp add: power_mult_distrib power_divide)
    also from x have "1 + \<dots> = -4 / ((x - 4) * x)" 
      by (simp add: divide_simps power2_eq_square mult_ac) (simp add: algebra_simps)?
    also from x have "2 * T x / \<dots> = - (2 / (x * sqrt (4 / x - 1)))"
      by (simp add: T_def power2_eq_square)
    finally have *: "((\<lambda>x. 2 * arctan (sqrt (4 / x - 1) * (x - 2) / (x - 4))) has_real_derivative
                        - (2 / (x * sqrt (4 / x - 1)))) (at x)" .
    have "(F has_field_derivative sqrt (4 / x - 1)) (at x)" unfolding F_def
      by (insert x, (rule * derivative_eq_intros refl | simp)+) (simp add: field_simps)
    thus ?thesis by (subst (asm) DERIV_cong_ev[OF refl eq refl]) (insert x, simp add: field_simps)
  qed
  
  \<comment> \<open>It is now obvious that @{term G} is continuous over the entire integration interval.\<close>
  have cont_G: "continuous_on {0..4} G" unfolding continuous_on
  proof safe
    fix x :: real assume "x \<in> {0..4}"
    then consider "x = 0" | "x = 4" | "x \<in> {0<..<4}" by force
    thus "(G \<longlongrightarrow> G x) (at x within {0..4})"
    proof cases
      assume "x = 0"
      have *: "at (0::real) within {0..4} \<le> at_right 0" unfolding at_within_def
        by (rule inf_mono) auto
      from G_0 have "(G \<longlongrightarrow> -pi) (at x within {0..4})" 
        by (rule filterlim_mono) (simp_all add: * \<open>x = 0\<close>)
      also have "-pi = G x" by (simp add: G_def \<open>x = 0\<close>)
      finally show ?thesis .
    next
      assume "x = 4"
      have *: "at (4::real) within {0..4} \<le> at_left 4" unfolding at_within_def
        by (rule inf_mono) auto
      from G_4 have "(G \<longlongrightarrow> pi) (at x within {0..4})" 
        by (rule filterlim_mono) (simp_all add: * \<open>x = 4\<close>)
      also have "pi = G x" by (simp add: G_def \<open>x = 4\<close>)
      finally show ?thesis .
    next
      assume "x \<in> {0<..<4}"
      from deriv_G[OF this] have "isCont G x" by (rule DERIV_isCont)
      thus ?thesis unfolding isCont_def by (rule filterlim_mono) (auto simp: at_le)
    qed
  qed
  
  \<comment> \<open>Finally, we can apply the Fundamental Theorem of Calculus.\<close>
  have "((\<lambda>x. sqrt ((4 - x) / x)) has_integral G 4 - G 0) {0..4}"
    using cont_G deriv_G
    by (intro fundamental_theorem_of_calculus_interior)
       (auto simp: has_real_derivative_iff_has_vector_derivative)
  also have "G 4 - G 0 = 2 * pi" by (simp add: G_def)
  finally show ?thesis .
qed

end

end
