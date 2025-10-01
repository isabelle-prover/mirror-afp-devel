theory Pi_to_M3_rat
  imports Pi_Relations J3_Relations M3_Polynomial
begin


subsection \<open>Relation between $M_3$ and $\Pi$\<close>

ML\<open>
Theory.setup (
  Method.setup \<^binding>\<open>unfold_auto\<close> (Attrib.thms >>
    (fn thms => fn ctxt =>
      SIMPLE_METHOD (
        REPEAT1 (
          CHANGED_PROP (
            (TRY (Clasimp.auto_tac ctxt)) THEN
            Local_Defs.unfold_tac ctxt thms THEN
            (TRY (Clasimp.auto_tac ctxt))
          )
        )
      )
    )
  ) "repeated unfold and auto"
)
\<close>

locale matiyasevich_polynomial = section5
begin

type_synonym \<tau>=real

(* \<rat>-versions of section5_given *)
definition x' :: "\<tau> mpoly" where "x' \<equiv> of_int_mpoly x"
definition \<A>\<^sub>1' :: "\<tau> mpoly" where "\<A>\<^sub>1' \<equiv> of_int_mpoly \<A>\<^sub>1"
definition \<A>\<^sub>2' :: "\<tau> mpoly" where "\<A>\<^sub>2' \<equiv> of_int_mpoly \<A>\<^sub>2"
definition \<A>\<^sub>3' :: "\<tau> mpoly" where "\<A>\<^sub>3' \<equiv> of_int_mpoly \<A>\<^sub>3"
definition \<X>\<^sub>3' :: "\<tau> mpoly" where "\<X>\<^sub>3' \<equiv> of_int_mpoly \<X>\<^sub>3"

(* \<rat>-versions of section5_variables *)
definition \<S>' :: "\<tau> mpoly" where "\<S>' \<equiv> of_int_mpoly \<S>"
definition \<T>' :: "\<tau> mpoly" where "\<T>' \<equiv> of_int_mpoly \<T>"
definition \<R>' :: "\<tau> mpoly" where "\<R>' \<equiv> of_int_mpoly \<R>"
definition \<I>' :: "\<tau> mpoly" where "\<I>' \<equiv> of_int_mpoly \<I>"
definition \<Y>' :: "\<tau> mpoly" where "\<Y>' \<equiv> of_int_mpoly \<Y>"
definition \<Z>' :: "\<tau> mpoly" where "\<Z>' \<equiv> of_int_mpoly \<ZZ>"
definition \<J>' :: "\<tau> mpoly" where "\<J>' \<equiv> of_int_mpoly \<J>"
definition \<n>' :: "\<tau> mpoly" where "\<n>' \<equiv> of_int_mpoly \<n>"

definition \<U>' ::"\<tau> mpoly" where "\<U>' = of_int_mpoly \<U>"
definition \<V>' ::"\<tau> mpoly" where "\<V>' = of_int_mpoly \<V>"
definition J3' :: "\<tau> mpoly" where "J3' = of_int_mpoly J3"
definition \<psi>' :: "nat \<Rightarrow> \<tau> mpoly" where "\<psi>' = of_int_mpoly \<circ> ((\<lambda>_. 0)(0 := \<T>^2+\<S>^2*\<n> -\<T>^2*\<U>- \<X>\<^sub>3^3*\<U>, 1 := \<U>^2*\<A>\<^sub>1, 2 := \<U>^2*\<A>\<^sub>2, 3 := \<U>^2*\<A>\<^sub>3))"
definition M3_poly' :: "\<tau> mpoly" where "M3_poly' \<equiv> of_int_mpoly M3_poly"

lemma Pi_equals_M3_rationals:
  fixes A\<^sub>1 A\<^sub>2 A\<^sub>3 R S T n :: int
  defines "X \<equiv> X\<^sub>0 \<pi>"
  defines "I \<equiv> I\<^sub>0 \<pi>"
  defines "U \<equiv> U\<^sub>0 \<pi>"
  defines "V \<equiv> V\<^sub>0 \<pi>"
  (* \<phi> :: nat \<Rightarrow> int mpoly *)
  defines "\<phi> \<equiv> (\<lambda>_. 0)(0 := Var 0, 1 := Const A\<^sub>1, 2 := Const A\<^sub>2, 3 := Const A\<^sub>3)"
  (* \<phi>' :: nat \<Rightarrow> 'a mpoly *)
  defines "\<phi>' \<equiv> of_int_mpoly \<circ> \<phi>"
  defines "\<F> \<equiv> poly_subst \<phi> J3"
  defines "\<F>' \<equiv> of_int_mpoly \<F> :: \<tau> mpoly"
  defines "q \<equiv> MPoly_Type.degree \<F> 0"
  defines "\<Pi> \<equiv> pi_relations.\<Pi> \<F> 0"
  (* G_sub :: nat \<Rightarrow> int mpoly *)
  defines "G_sub \<equiv> pi_relations.G_sub \<F> 0"
  (* G_sub' :: nat \<Rightarrow> 'a mpoly *)
  defines "G_sub' \<equiv> of_int_mpoly \<circ> (pi_relations.G_sub \<F> 0)"
  (* \<xi> :: nat \<Rightarrow> int *)
  defines "\<xi> \<equiv> ((\<lambda>_. 0)(4 := S, 5 := T, 6:=R, 7:=X^3, 11:=n))"
  (* \<xi>' :: nat \<Rightarrow> int *)
  defines "\<xi>' \<equiv> of_int \<circ> \<xi>"

  assumes "U \<noteq> 0"
  assumes "q = 8"
  assumes F_monom_over_0: "vars \<F> \<subseteq> {0}"
      and F_one_0: "MPoly_Type.coeff \<F> (Abs_poly_mapping (\<lambda>k. (MPoly_Type.degree \<F> 0 when k = 0))) = 1"

  shows "insertion \<xi> \<Pi> = M3 \<pi>" (* equality in \<int> *)
proof -
  have U_ev: "insertion \<xi> \<U> = U" unfolding defs U_def U\<^sub>0_def \<xi>_def power2_eq_square 
    by auto 
  have V_ev: "insertion \<xi> \<V> = V" unfolding defs V_def V\<^sub>0_def \<xi>_def power2_eq_square
    by auto 

  have j_in_sum: "\<And>j. j\<le>q \<longrightarrow> of_int (insertion \<xi> ((G_sub j) * \<V>^j * \<U>^(q-j))) 
                                = insertion \<xi> (G_sub j) * (V/U)^j * U^q"
  proof 
    fix j 
    assume "j \<le> q"
    have "insertion \<xi> ((G_sub j) * \<V>^j * \<U>^(q-j) )
     = (insertion \<xi> ((G_sub j) * \<V>^j) * (insertion \<xi> \<U>^(q-j)))" by auto
    also have "... = insertion \<xi> (G_sub j) * V^j * U^(q-j)" 
      by (auto simp: U_ev V_ev)
    also have "... = insertion \<xi> (G_sub j) * V^j * U^q / U^j" 
      using power_diff[of "U" "j" "q"] `U \<noteq> 0` `j\<le> q` apply simp
      by (metis (no_types, lifting) of_int_0_eq_iff of_int_power power_diff times_divide_eq_right)
    also have "... = insertion \<xi> (G_sub j) * (V/U)^j * U^q" 
      using power_divide[of "V" "U" "j"] by auto
    finally show "insertion \<xi> ((G_sub j) * \<V>^j * \<U>^(q-j)) = insertion \<xi> (G_sub j) * (V/U)^j * U^q"
      by auto
  qed

  have XI3: "I = X^3" 
    unfolding I_def I\<^sub>0_def X_def by simp

  interpret pi_relations: pi_relations \<F> 0
    using F_monom_over_0 F_one_0
    by (unfold_locales; auto)

  have X1_unfold:"(of_int_mpoly (Const 1 + \<A>\<^sub>1\<^sup>2 + \<A>\<^sub>2\<^sup>2 + \<A>\<^sub>3\<^sup>2)) 
     = (of_int_mpoly (Const 1) + (of_int_mpoly \<A>\<^sub>1)\<^sup>2 + (of_int_mpoly \<A>\<^sub>2)\<^sup>2 + (of_int_mpoly \<A>\<^sub>3)\<^sup>2)"
    unfolding of_int_mpoly_simps ..

  have aux0: "(\<lambda>x. insertion ((\<lambda>_. 0)(0 := real_of_int V / real_of_int U - real_of_int I - (real_of_int T)\<^sup>2))
                (of_int_mpoly (((\<lambda>_. 0)(0 := Var 0, Suc 0 := Const A\<^sub>1, 2 := Const A\<^sub>2, 3 := Const A\<^sub>3)) x))) i
        = ((\<lambda>_. 0)(0 := real_of_int V / real_of_int U - real_of_int I - (real_of_int T)\<^sup>2,
                    Suc 0 := real_of_int A\<^sub>1, 2 := real_of_int A\<^sub>2, 3 := real_of_int A\<^sub>3)) i" for i
    apply (cases "i = 0")
    by (auto simp: of_int_mpoly_simps)

  have G_sub_vars: "vars (G_sub j) \<subseteq> {5, 7}" for j
    unfolding G_sub_def pi_relations.G_sub_def \<I>_def \<T>_def
            defs diff_conv_add_uminus
    apply (rule subset_trans[OF vars_setsum]; simp)
    apply (rule UN_least)
    unfolding power2_eq_square of_int_Const of_nat_Const diff_conv_add_uminus
    by mpoly_vars
  have G_sub_aux0: "insertion \<xi> (G_sub j)
                    = insertion ((\<lambda>_. 0)(5 := T, 7 := X ^ 3)) (G_sub j)" for j
    unfolding \<xi>_def
    apply (rule insertion_irrelevant_vars)
    using G_sub_vars[of j] by auto

  {
    fix j
    have "real_of_int (insertion ((\<lambda>_. 0)(5 := T, 7 := X ^ 3)) (local.pi_relations.G_sub j))
      = insertion (of_int \<circ> ((\<lambda>_. 0)(5 := T, 7 := X ^ 3))) (of_int_mpoly (G_sub j))"
      unfolding G_sub_def[symmetric] insertion_of_int_mpoly ..
    also have "... = insertion
         ((\<lambda>x. real_of_int (((\<lambda>_. 0)(5 := T, 7 := X ^ 3)) x))(8 := real_of_int V / real_of_int U))
         (of_int_mpoly (G_sub j))"
      apply (intro insertion_irrelevant_vars)
      using vars_of_int_mpoly[of "G_sub j"] G_sub_vars[of j] by auto
    also have "...
       = insertion ((\<lambda>x. real_of_int
             (((\<lambda>_. 0)(5 := T, 7 := X ^ 3)) x))(8 := real_of_int V / real_of_int U))
        (of_int_mpoly (local.pi_relations.G_sub j))"
      unfolding G_sub_def[symmetric] ..
    finally have G_sub_aux1: "real_of_int (insertion ((\<lambda>_. 0)(5 := T, 7 := X ^ 3)) (local.pi_relations.G_sub j))
      = insertion ((\<lambda>x. real_of_int (((\<lambda>_. 0)(5 := T, 7 := X ^ 3)) x))(8 := real_of_int V / real_of_int U))
        (of_int_mpoly (local.pi_relations.G_sub j))" .
  }
  note G_sub_aux1 = this

  have degree_aux_lt: "MPoly_Type.degree \<F>' 0 \<le> q"
    unfolding q_def \<F>'_def
    by (simp add: le_funD)

  have vars_\<F>': "vars \<F>' \<subseteq> {0}"
    unfolding \<F>'_def
    apply (rule subset_trans[OF vars_of_int_mpoly])
    by (auto simp add: F_monom_over_0)

  have coeff_\<F>': "MPoly_Type.coeff \<F>' = MPoly_Type.coeff \<F>"
    unfolding \<F>'_def of_int_mpoly_coeff ..

  have degree_aux_gt: "MPoly_Type.degree \<F>' 0 \<ge> q"
  proof -
    have "MPoly_Type.coeff \<F>' (Abs_poly_mapping (\<lambda>k. (q when k = 0))) = 1"
      using F_one_0 coeff_\<F>' q_def by simp

    thus ?thesis
      unfolding MPoly_Type.degree.rep_eq apply (intro Max_ge)
      subgoal by simp
      apply (rule insertI2)
      unfolding keys.rep_eq image_iff bex_simps(6) coeff_def
      apply (rule exI[of _ "Poly_Mapping.single 0 q"])
      by (auto simp: Poly_Mapping.single.abs_eq when_def)
  qed

  have degree_aux: "MPoly_Type.degree \<F>' 0 = q"
    using degree_aux_lt degree_aux_gt by simp

  have univariate_expansion:
    "\<F>' = (\<Sum>d = 0..MPoly_Type.degree \<F>' 0. of_int (pi_relations.coeff_F d) * (Var 0) ^ d)"
    apply (subst mpoly_univariate_expansion_sum[of \<F>' 0, OF vars_\<F>'])
    apply (rule sum.cong, simp)
    unfolding pi_relations.coeff_F_def Poly_Mapping.single.abs_eq coeff_\<F>' of_int_general_Const
    by (simp add: of_int_mpoly_simps)

  have X_unfold:"X = insertion
        ((\<lambda>_. 0)
         (0 := real_of_int V / real_of_int U - real_of_int I - (real_of_int T)\<^sup>2,
          Suc 0 := real_of_int A\<^sub>1, 2 := real_of_int A\<^sub>2, 3 := real_of_int A\<^sub>3)) \<X>\<^sub>3'"
      unfolding x'_def \<A>\<^sub>1'_def \<A>\<^sub>2'_def \<A>\<^sub>3'_def \<X>\<^sub>3'_def x_def \<A>\<^sub>1_def \<A>\<^sub>2_def \<A>\<^sub>3_def \<X>\<^sub>3_def X_def X\<^sub>0_def X1_unfold of_int_mpoly_simps
      by simp

   have U_V_cancel: "of_int U * (of_int V/of_int U) = (of_int V :: real)"
      by (simp add: \<open>U \<noteq> 0\<close>)

   have "insertion \<xi> \<Pi> = insertion \<xi> (\<Sum>j=0..q. G_sub j * \<V>^j * \<U>^(q-j))"
    unfolding \<Pi>_def pi_relations.\<Pi>_def
    unfolding q_def pi_relations.q_def
    unfolding G_sub_def pi_relations.G_sub_def
    unfolding defs
    by (auto simp: algebra_simps)
  also have "... = (\<Sum>j=0..q. insertion \<xi> ((G_sub j) * \<V>^j * \<U>^(q-j)))"
    by auto
  also have "of_int (...) = (\<Sum>j=0..q. insertion \<xi> (G_sub j) * (V/U)^j * U^q)"
    apply (subst of_int_sum)
    apply (rule sum.cong)
    using j_in_sum by auto
  also have "... = U^q * (\<Sum>j=0..q. insertion \<xi> (G_sub j) * (V/U)^j)"
    apply (subst sum_distrib_left)
    by (simp add: algebra_simps)
  
  also have "... = U^q * insertion ((\<lambda>_. 0)(5:=T, 7:=I, 8:=V/U)) (of_int_mpoly (pi_relations.G))"
    unfolding pi_relations.G_in_Y G_sub_aux0
    apply (simp only: of_int_mpoly_simps \<Y>_def G_sub_def)
    using insertion_of_int_mpoly[where ?P = "local.pi_relations.G_sub _"
                                   and ?\<alpha> = "((\<lambda>_. 0)(4 := S, 5 := T, 6 := R, 7 := X ^ 3, 11 := n))"]
    apply (subst insertion_simps)
    subgoal by simp
    unfolding q_def pi_relations.q_def comp_def of_int_mpoly_simps \<open>I = X^3\<close>
    apply (subst insertion_simps)+
    unfolding G_sub_aux1
    by (simp add: mult.commute)
  also have "... = U^q * insertion ((\<lambda>_. 0)(0:=of_int V/of_int U - of_int I - of_int T^2)) \<F>'"
    unfolding pi_relations.G_def
    apply (subst univariate_expansion)
    apply (simp add: defs of_int_mpoly_simps pi_relations.q_def pi_relations.coeff_F_def)
    apply (rule disjI2)
    apply (rule sum.cong)
    subgoal by (simp add: degree_aux q_def)
    unfolding of_int_Const of_int_mpoly_Const
    apply (simp only: insertion_simps)
    unfolding of_int_general_Const of_int_mpoly_Const
    by simp
  also have "... = U^q * insertion ((\<lambda>_. 0)(0:=of_int V/of_int U - of_int I - of_int T^2, 
                                            1:=of_int A\<^sub>1, 2:=of_int A\<^sub>2, 3:=of_int A\<^sub>3)) J3'"
    unfolding \<F>'_def \<F>_def J3'_def \<phi>_def
    apply simp
    unfolding of_int_mpoly_poly_subst
    unfolding insertion_poly_subst comp_def
    apply (subst aux0)
    by simp

  also have "
    ... =
    (
      ((
        (
          (
            (of_int V - of_int U * of_int I - of_int U * of_int T^2)^2
              + (of_int U)^2 * A\<^sub>1
              + (of_int U)^2 * A\<^sub>2 * X^2
              - (of_int U)^2 * A\<^sub>3 * X^4
          )
        )^2 
          + 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>1
          - 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>2 * X^2
          - 4 * (of_int U)^4 * A\<^sub>1 * A\<^sub>2 * X^2
      )^2)
        - A\<^sub>1 * ((of_int U) * (
          4
            * (of_int V - (of_int U) * of_int I - (of_int U) * of_int T^2)
            * (
              ((of_int V - (of_int U) * of_int I - (of_int U) * of_int T^2))^2
                + (of_int U)^2 * A\<^sub>1
                + (of_int U)^2 * A\<^sub>2 * X^2
                - (of_int U)^2 * A\<^sub>3 * X^4
              )
                - 8
                  * (of_int U)^2
                  * (of_int V - (of_int U) * of_int I - (of_int U) * of_int T^2)
                  * A\<^sub>2
                  * X^2
        ))^2
    )
  " 
  proof -
    have "
      ... =
      (of_int U)^8 * (
        (
          (
            (of_int V/of_int U - of_int I - of_int T^2)^2
              + A\<^sub>1
              + A\<^sub>2 * X^2 - A\<^sub>3 * X^4
          )^2 
            + 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>1
            - 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>2 * X^2 
            - 4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2
          - A\<^sub>1 * (
            4
              * (of_int V/of_int U - of_int I - of_int T^2)
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                )
                  - 8 * (of_int V/of_int U - of_int I - of_int T^2) * A\<^sub>2 * X^2
          )^2
       )
    "
      by (unfold_auto \<open>q = 8\<close> J3'_def x'_def \<A>\<^sub>1'_def \<A>\<^sub>2'_def \<A>\<^sub>3'_def \<X>\<^sub>3'_def J3_def x_def \<A>\<^sub>1_def
          \<A>\<^sub>2_def \<A>\<^sub>3_def \<X>\<^sub>3_def X_unfold insertion_simps of_int_mpoly_simps)
      also have "
      ... =
      (((of_int U)^4)^2) * (
        (
          (
            (of_int V/of_int U - of_int I - of_int T^2)^2
              + A\<^sub>1
              + A\<^sub>2 * X^2
              - A\<^sub>3 * X^4
          )^2 
            + 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>1
            - 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>2 * X^2 
            - 4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2
          - A\<^sub>1 * (
            4
              * (of_int V/of_int U - of_int I - of_int T^2)
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                )
                  - 8 * (of_int V/of_int U - of_int I - of_int T^2) * A\<^sub>2 * X^2
          )^2
      )
    "
      by simp
    also have "
      ... =
      (
        ((((of_int U)^4)^2) * (
          (
            (of_int V/of_int U - of_int I - of_int T^2)^2
              + A\<^sub>1
              + A\<^sub>2 * X^2
              - A\<^sub>3 * X^4
          )^2 
            + 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>1
            - 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>2 * X^2 
            - 4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - (of_int U)^8 * (A\<^sub>1 * (
            4
              * (of_int V/of_int U - of_int I - of_int T^2)
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                )
                  - 8 * (of_int V/of_int U - of_int I - of_int T^2) * A\<^sub>2 * X^2
          )^2)
      )
    "
      unfolding right_diff_distrib by simp
    also have "
      ... =
      (
        ((((of_int U)^4)^2) * (
          (
            (of_int V/of_int U - of_int I - of_int T^2)^2
              + A\<^sub>1
              + A\<^sub>2 * X^2
              - A\<^sub>3 * X^4
          )^2 
            + 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>1
            - 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>2 * X^2 
            - 4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * (((of_int U)^4) * (
            4
              * (of_int V/of_int U - of_int I - of_int T^2)
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                )
                  - 8 * (of_int V/of_int U - of_int I - of_int T^2) * A\<^sub>2 * X^2
          ))^2
      )
    "
      unfolding power_mult_distrib by simp
    also have "
      ... =
      (
        ((((of_int U)^4) * (
          (
            (of_int V/of_int U - of_int I - of_int T^2)^2
              + A\<^sub>1
              + A\<^sub>2 * X^2
              - A\<^sub>3 * X^4
          )^2 
            + 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>1
            - 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>2 * X^2
            - 4 * A\<^sub>1 * A\<^sub>2 * X^2
        ))^2)
          - A\<^sub>1 * (((of_int U)^4) * (
            4
              * (of_int V/of_int U - of_int I - of_int T^2)
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                )
                  - 8 * (of_int V/of_int U - of_int I - of_int T^2) * A\<^sub>2 * X^2
          ))^2
      )
    "
      unfolding power_mult_distrib by simp
    also have "
      ... =
      (
        ((
          ((of_int U)^2^2) * (
            (of_int V/of_int U - of_int I - of_int T^2)^2
              + A\<^sub>1
              + A\<^sub>2 * X^2
              - A\<^sub>3 * X^4
          )^2 
            + ((of_int U)^4) * 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>1
            - ((of_int U)^4) * 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>2 * X^2
            - ((of_int U)^4) * 4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * (((of_int U)^4) * (
            4
              * (of_int V/of_int U - of_int I - of_int T^2)
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                )
                  - 8 * (of_int V/of_int U - of_int I - of_int T^2) * A\<^sub>2 * X^2
          ))^2
      )
    "
      unfolding distrib_left right_diff_distrib mult.assoc by simp
    also have "
      ... =
      (
        ((
          (
            (of_int U)^2 * (
              (of_int V/of_int U - of_int I - of_int T^2)^2
                + A\<^sub>1
                + A\<^sub>2 * X^2
                - A\<^sub>3 * X^4
            )
          )^2 
            + ((of_int U)^4) * 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>1
            - ((of_int U)^4) * 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>2 * X^2
            - ((of_int U)^4) * 4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * (((of_int U)^4) * (
            4
              * (of_int V/of_int U - of_int I - of_int T^2)
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                )
                  - 8 * (of_int V/of_int U - of_int I - of_int T^2) * A\<^sub>2 * X^2
          ))^2
      )
    "
      unfolding power_mult_distrib by simp
    also have "
      ... =
      (
        ((
          (
            (
              (of_int U)^2 * (of_int V/of_int U - of_int I - of_int T^2)^2
                + (of_int U)^2 * A\<^sub>1
                + (of_int U)^2 * A\<^sub>2 * X^2
                - (of_int U)^2 * A\<^sub>3 * X^4
            )
          )^2 
            + ((of_int U)^4) * 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>1
            - ((of_int U)^4) * 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>2 * X^2
            - ((of_int U)^4) * 4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * (((of_int U)^4) * (
            4
              * (of_int V/of_int U - of_int I - of_int T^2)
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                )
                  - 8 * (of_int V/of_int U - of_int I - of_int T^2) * A\<^sub>2 * X^2
          ))^2
      )
    "
      unfolding distrib_left right_diff_distrib mult.assoc by simp
    also have "
      ... =
      (
        ((
          (
            (
              ((of_int U) * (of_int V/of_int U - of_int I - of_int T^2))^2
                + (of_int U)^2 * A\<^sub>1
                + (of_int U)^2 * A\<^sub>2 * X^2
                - (of_int U)^2 * A\<^sub>3 * X^4
            )
          )^2 
            + ((of_int U)^4) * 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>1
            - ((of_int U)^4) * 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>2 * X^2
            - ((of_int U)^4) * 4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * (((of_int U)^4) * (
            4
              * (of_int V/of_int U - of_int I - of_int T^2)
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                )
                  - 8 * (of_int V/of_int U - of_int I - of_int T^2) * A\<^sub>2 * X^2
          ))^2
      )
    "
      unfolding power_mult_distrib by simp
    also have "
      ... =
      (
        ((
          (
            (
              (of_int V - of_int U * of_int I - of_int U * of_int T^2)^2
                + (of_int U)^2 * A\<^sub>1
                + (of_int U)^2 * A\<^sub>2 * X^2
                - (of_int U)^2 * A\<^sub>3 * X^4
            )
          )^2 
            + ((of_int U)^4) * 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>1
            - ((of_int U)^4) * 4 * (of_int V/of_int U - of_int I - of_int T^2)^2 * A\<^sub>2 * X^2
            - ((of_int U)^4) * 4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * (((of_int U)^4) * (
            4
              * (of_int V/of_int U - of_int I - of_int T^2)
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                )
                  - 8 * (of_int V/of_int U - of_int I - of_int T^2) * A\<^sub>2 * X^2
          ))^2
      )
    "
      unfolding distrib_left right_diff_distrib U_V_cancel by simp
    also have "
      ... =
      (
        ((
          (
            (
              (of_int V - of_int U * of_int I - of_int U * of_int T^2)^2
                + (of_int U)^2 * A\<^sub>1
                + (of_int U)^2 * A\<^sub>2 * X^2
                - (of_int U)^2 * A\<^sub>3 * X^4
            )
          )^2 
            + 4 * (of_int U)^2 * ((of_int U)^2 * (of_int V/of_int U - of_int I - of_int T^2)^2) * A\<^sub>1
            - 4 * (of_int U)^2 * ((of_int U)^2 * (of_int V/of_int U - of_int I - of_int T^2)^2) * A\<^sub>2 * X^2
            - 4 * ((of_int U)^4) * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * (((of_int U)^4) * (
            4
              * (of_int V/of_int U - of_int I - of_int T^2)
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                )
                  - 8 * (of_int V/of_int U - of_int I - of_int T^2) * A\<^sub>2 * X^2
          ))^2
      )
    "
      unfolding ab_semigroup_mult_class.mult.commute[of 4] mult.assoc by simp
    also have "
      ... =
      (
        ((
          (
            (
              (of_int V - of_int U * of_int I - of_int U * of_int T^2)^2
                + (of_int U)^2 * A\<^sub>1
                + (of_int U)^2 * A\<^sub>2 * X^2
                - (of_int U)^2 * A\<^sub>3 * X^4
            )
          )^2 
            + 4 * (of_int U)^2 * ((of_int U) * (of_int V/of_int U - of_int I - of_int T^2))^2 * A\<^sub>1
            - 4 * (of_int U)^2 * ((of_int U) * (of_int V/of_int U - of_int I - of_int T^2))^2 * A\<^sub>2 * X^2
            - 4 * (of_int U)^4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * ((of_int U)^4 * (
            4
              * (of_int V/of_int U - of_int I - of_int T^2)
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                )
                  - 8 * (of_int V/of_int U - of_int I - of_int T^2) * A\<^sub>2 * X^2
          ))^2
      )
    "
      unfolding power_mult_distrib ..
    also have "
      ... =
      (
        ((
          (
            (
              (of_int V - of_int U * of_int I - of_int U * of_int T^2)^2
                + (of_int U)^2 * A\<^sub>1
                + (of_int U)^2 * A\<^sub>2 * X^2
                - (of_int U)^2 * A\<^sub>3 * X^4
            )
          )^2 
            + 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>1
            - 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>2 * X^2
            - 4 * (of_int U)^4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * ((of_int U)^4 * (
            4
              * (of_int V/of_int U - of_int I - of_int T^2)
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                )
                  - 8 * (of_int V/of_int U - of_int I - of_int T^2) * A\<^sub>2 * X^2
          ))^2
      )
    "
      unfolding distrib_left right_diff_distrib U_V_cancel by simp
    also have "
      ... =
      (
        ((
          (
            (
              (of_int V - of_int U * of_int I - of_int U * of_int T^2)^2
                + (of_int U)^2 * A\<^sub>1
                + (of_int U)^2 * A\<^sub>2 * X^2
                - (of_int U)^2 * A\<^sub>3 * X^4
            )
          )^2 
            + 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>1
            - 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>2 * X^2
            - 4 * (of_int U)^4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * ((of_int U) * ((of_int U)^3 * (
            4
              * (of_int V/of_int U - of_int I - of_int T^2)
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                )
                  - 8 * (of_int V/of_int U - of_int I - of_int T^2) * A\<^sub>2 * X^2
          )))^2
      )
    "
      unfolding power_def mult.assoc by simp
    also have "
      ... =
      (
        ((
          (
            (
              (of_int V - of_int U * of_int I - of_int U * of_int T^2)^2
                + (of_int U)^2 * A\<^sub>1
                + (of_int U)^2 * A\<^sub>2 * X^2
                - (of_int U)^2 * A\<^sub>3 * X^4
            )
          )^2 
            + 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>1
            - 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>2 * X^2
            - 4 * (of_int U)^4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * ((of_int U) * (
            (of_int U)^3
              * (4
              * (of_int V/of_int U - of_int I - of_int T^2)
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                ))
                  - (of_int U)^3 * (8 * (of_int V/of_int U - of_int I - of_int T^2) * A\<^sub>2 * X^2)
          ))^2
      )
    "
      unfolding right_diff_distrib ..
    also have "
      ... =
      (
        ((
          (
            (
              (of_int V - of_int U * of_int I - of_int U * of_int T^2)^2
                + (of_int U)^2 * A\<^sub>1
                + (of_int U)^2 * A\<^sub>2 * X^2
                - (of_int U)^2 * A\<^sub>3 * X^4
            )
          )^2 
            + 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>1
            - 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>2 * X^2
            - 4 * (of_int U)^4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * ((of_int U) * (
            4
              * (of_int U)^3
              * (of_int V/of_int U - of_int I - of_int T^2)
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                )
                  - 8 * (of_int U)^3 * (of_int V/of_int U - of_int I - of_int T^2) * A\<^sub>2 * X^2
          ))^2
      )
    "
      unfolding ab_semigroup_mult_class.mult.commute[of 4] ab_semigroup_mult_class.mult.commute[of 8] mult.assoc by simp
    also have "
      ... =
      (
        ((
          (
            (
              (of_int V - of_int U * of_int I - of_int U * of_int T^2)^2
                + (of_int U)^2 * A\<^sub>1
                + (of_int U)^2 * A\<^sub>2 * X^2
                - (of_int U)^2 * A\<^sub>3 * X^4
            )
          )^2 
            + 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>1
            - 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>2 * X^2
            - 4 * (of_int U)^4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * ((of_int U) * (
            4
              * (of_int U)
              * (of_int U)^2
              * (of_int V/of_int U - of_int I - of_int T^2)
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                )
                  - 8
                    * (of_int U)^2
                    * (of_int U) * (of_int V/of_int U - of_int I - of_int T^2)
                    * A\<^sub>2
                    * X^2
          ))^2
      )
    "
      unfolding power2_eq_square power3_eq_cube mult.assoc ..
    also have "
      ... =
      (
        ((
          (
            (
              (of_int V - of_int U * of_int I - of_int U * of_int T^2)^2
                + (of_int U)^2 * A\<^sub>1
                + (of_int U)^2 * A\<^sub>2 * X^2
                - (of_int U)^2 * A\<^sub>3 * X^4
            )
          )^2 
            + 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>1
            - 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>2 * X^2
            - 4 * (of_int U)^4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * ((of_int U) * (
            4
              * ((of_int U)
              * (of_int V/of_int U - of_int I - of_int T^2))
              * ((of_int U)^2
              * (
                (of_int V/of_int U - of_int I - of_int T^2)^2
                  + A\<^sub>1
                  + A\<^sub>2 * X^2
                  - A\<^sub>3 * X^4
                ))
                  - 8
                    * (of_int U)^2 * (of_int U) 
                    * (of_int V/of_int U - of_int I - of_int T^2)
                    * A\<^sub>2
                    * X^2
          ))^2
      )
    "
      unfolding ab_semigroup_mult_class.mult.commute[of "(of_int U)^2"] mult.assoc by simp
    also have "
      ... =
      (
        ((
          (
            (
              (of_int V - of_int U * of_int I - of_int U * of_int T^2)^2
                + (of_int U)^2 * A\<^sub>1
                + (of_int U)^2 * A\<^sub>2 * X^2
                - (of_int U)^2 * A\<^sub>3 * X^4
            )
          )^2 
            + 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>1
            - 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>2 * X^2
            - 4 * (of_int U)^4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * ((of_int U) * (
            4
              * ((of_int U) * (of_int V/of_int U) - (of_int U) * of_int I - (of_int U) * of_int T^2)
              * (
                (of_int U)^2 * (of_int V/of_int U - of_int I - of_int T^2)^2
                  + (of_int U)^2 * A\<^sub>1
                  + (of_int U)^2 * A\<^sub>2 * X^2
                  - (of_int U)^2 * A\<^sub>3 * X^4
                )
                  - 8
                    * (of_int U)^2
                    * ((of_int U) * (of_int V/of_int U - of_int I - of_int T^2))
                    * A\<^sub>2
                    * X^2
          ))^2
      )
    "
      unfolding distrib_left right_diff_distrib mult.assoc by simp
    also have "
      ... =
      (
        ((
          (
            (
              (of_int V - of_int U * of_int I - of_int U * of_int T^2)^2
                + (of_int U)^2 * A\<^sub>1
                + (of_int U)^2 * A\<^sub>2 * X^2
                - (of_int U)^2 * A\<^sub>3 * X^4
            )
          )^2 
            + 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>1
            - 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>2 * X^2
            - 4 * (of_int U)^4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * ((of_int U) * (
            4
              * ((of_int U) * (of_int V/of_int U) - (of_int U) * of_int I - (of_int U) * of_int T^2)
              * (
                ((of_int U) * (of_int V/of_int U - of_int I - of_int T^2))^2
                  + (of_int U)^2 * A\<^sub>1
                  + (of_int U)^2 * A\<^sub>2 * X^2
                  - (of_int U)^2 * A\<^sub>3 * X^4
                )
                  - 8
                    * (of_int U)^2
                    * ((of_int U) * (of_int V/of_int U - of_int I - of_int T^2))
                    * A\<^sub>2
                    * X^2
          ))^2
      )
    "
      unfolding power_mult_distrib ..
    also have "
      ... =
      (
        ((
          (
            (
              (of_int V - of_int U * of_int I - of_int U * of_int T^2)^2
                + (of_int U)^2 * A\<^sub>1
                + (of_int U)^2 * A\<^sub>2 * X^2
                - (of_int U)^2 * A\<^sub>3 * X^4
            )
          )^2 
            + 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>1
            - 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>2 * X^2
            - 4 * (of_int U)^4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * ((of_int U) * (
            4
              * ((of_int U) * (of_int V/of_int U) - (of_int U) * of_int I - (of_int U) * of_int T^2)
              * (
                (((of_int U) * (of_int V/of_int U) - (of_int U) * of_int I - (of_int U) * of_int T^2))^2
                  + (of_int U)^2 * A\<^sub>1
                  + (of_int U)^2 * A\<^sub>2 * X^2
                  - (of_int U)^2 * A\<^sub>3 * X^4
                )
                  - 8
                    * (of_int U)^2
                    * ((of_int U) * (of_int V/of_int U) - (of_int U) * of_int I - (of_int U) * of_int T^2)
                    * A\<^sub>2
                    * X^2
          ))^2
      )
    "
      unfolding distrib_left right_diff_distrib ..
    also have "
      ... =
      (
        ((
          (
            (
              (of_int V - of_int U * of_int I - of_int U * of_int T^2)^2
                + (of_int U)^2 * A\<^sub>1
                + (of_int U)^2 * A\<^sub>2 * X^2
                - (of_int U)^2 * A\<^sub>3 * X^4
            )
          )^2 
            + 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>1
            - 4 * (of_int U)^2 * ((of_int V) - (of_int U) * of_int I - (of_int U) * of_int T^2)^2 * A\<^sub>2 * X^2
            - 4 * (of_int U)^4 * A\<^sub>1 * A\<^sub>2 * X^2
        )^2)
          - A\<^sub>1 * ((of_int U) * (
            4
              * (of_int V - (of_int U) * of_int I - (of_int U) * of_int T^2)
              * (
                ((of_int V - (of_int U) * of_int I - (of_int U) * of_int T^2))^2
                  + (of_int U)^2 * A\<^sub>1
                  + (of_int U)^2 * A\<^sub>2 * X^2
                  - (of_int U)^2 * A\<^sub>3 * X^4
                )
                  - 8
                    * (of_int U)^2
                    * (of_int V - (of_int U) * of_int I - (of_int U) * of_int T^2)
                    * A\<^sub>2
                    * X^2
          ))^2
      )
    "
      unfolding U_V_cancel by simp
    finally show ?thesis .
  qed

  also have "... = M3 \<pi>" unfolding M3_def X_def I_def U_def V_def by auto
  finally show "insertion \<xi> \<Pi> = M3 \<pi>" by auto
qed

end

end