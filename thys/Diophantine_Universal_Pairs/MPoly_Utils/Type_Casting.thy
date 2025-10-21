theory Type_Casting
  imports Substitutions
begin

subsection \<open>Type casting for polynomials\<close>

named_theorems of_int_mpoly_simps "Lemmas about of_int_mpoly"

definition of_int_mpoly :: "int mpoly \<Rightarrow> 'a::ring_1 mpoly" where
  "of_int_mpoly P = MPoly (Abs_poly_mapping (of_int \<circ> lookup (mapping_of P)))"

lemma of_int_mpoly_coeff [simp, of_int_mpoly_simps]:
  "coeff (of_int_mpoly P) a = of_int (coeff P a)"
  unfolding of_int_mpoly_def comp_def coeff_def
  apply (subst MPoly_inverse)
  subgoal by blast
  subgoal
    apply (subst Abs_poly_mapping_inverse)
    subgoal by (simp; metis (mono_tags, lifting) finite_lookup finite_subset mem_Collect_eq of_int_0 subsetI)
    subgoal ..
    done
  done

lemma of_int_mpoly_zero [of_int_mpoly_simps]:
  "of_int_mpoly 0 = 0"
  unfolding of_int_mpoly_def zero_mpoly.rep_eq lookup_zero comp_apply of_int_0 
  unfolding zero_mpoly_def 
  by auto

lemma eq_onp_intF:
  fixes \<F> :: "int mpoly"
  shows "eq_onp (\<lambda>f. finite {x. f x \<noteq> 0}) (\<lambda>x. of_int (lookup (mapping_of \<F>) x))
   (\<lambda>x. of_int (lookup (mapping_of \<F>) x))"
proof - 
  have incl:"{x. of_int (lookup (mapping_of \<F>) x) \<noteq> 0} \<subseteq> {x. (lookup (mapping_of \<F>) x) \<noteq> 0}" by auto
  have "finite {x. (lookup (mapping_of \<F>) x) \<noteq> 0}" by auto
  then have fin:"finite {x. of_int (lookup (mapping_of \<F>) x) \<noteq> 0}" 
    using incl Finite_Set.rev_finite_subset[of "{x. (lookup (mapping_of \<F>) x) \<noteq> 0}" "{x. of_int (lookup (mapping_of \<F>) x) \<noteq> 0}"] by auto
  thus ?thesis unfolding eq_onp_def by auto
qed

lemma of_int_mpoly_one [of_int_mpoly_simps]:
  "of_int_mpoly 1 = 1"
  unfolding of_int_mpoly_def one_mpoly.rep_eq lookup_one comp_apply
  unfolding one_mpoly_def one_poly_mapping_def
  apply (simp add: MPoly_inject)
  apply (subst Abs_poly_mapping_inject)
  by (auto simp: when_def)

lemma of_int_mpoly_Var [of_int_mpoly_simps]:
  "of_int_mpoly (Var n) = Var n"
  unfolding of_int_mpoly_def Var.rep_eq Var\<^sub>0_def comp_def
  unfolding Var.abs_eq Var\<^sub>0_def
  apply (simp add: MPoly_inject)
  apply (subst (3) Poly_Mapping.single.abs_eq)
  apply (subst Abs_poly_mapping_inject, simp_all)
  by (auto simp add: when_def)

lemma of_int_mpoly_Const [of_int_mpoly_simps]:
  "of_int_mpoly (Const c) = Const (of_int c)"
  unfolding of_int_mpoly_def Const.rep_eq Const\<^sub>0_def Poly_Mapping.single.abs_eq comp_def
  apply (simp add: Const_def MPoly_inject)
  unfolding Const\<^sub>0_def Poly_Mapping.single.abs_eq
  apply (subst Abs_poly_mapping_inject)
  apply simp_all
  subgoal by (smt (verit, ccfv_SIG) "when"(2) finite.intros(1) finite_insert finite_subset
                  insert_iff mem_Collect_eq of_int_0 subsetI)
  subgoal by (metis "when"(1) "when"(2) of_int_0)
  done

lemma of_int_mpoly_numeral [of_int_mpoly_simps]:
  "of_int_mpoly (numeral n) = numeral n"
  unfolding Const_numeral[symmetric]
  by (simp add: of_int_mpoly_simps)

lemma of_int_mpoly_add [of_int_mpoly_simps]:
  fixes \<F> \<G> :: "int mpoly"
  shows "of_int_mpoly (\<F> + \<G>) = of_int_mpoly \<F> + of_int_mpoly \<G> "
proof -
  have Abs_distrib:"(Abs_poly_mapping (\<lambda>x. of_int (lookup (mapping_of \<F>) x)) +
      Abs_poly_mapping (\<lambda>x. of_int (lookup (mapping_of \<G>) x)))
   = (Abs_poly_mapping
       (\<lambda>x. of_int (lookup (mapping_of \<F>) x) + of_int (lookup (mapping_of \<G>) x)))"
    using eq_onp_intF[of "\<F>"] eq_onp_intF[of "\<G>"]
      Poly_Mapping.plus_poly_mapping.abs_eq[of "\<lambda>x. of_int (lookup (mapping_of \<F>) x)" "\<lambda>x. of_int (lookup (mapping_of \<G>) x)"]
    by auto

  have LHS:"of_int_mpoly (\<F> + \<G>) = MPoly
     (Abs_poly_mapping
       (\<lambda>x. of_int (lookup (mapping_of \<F>) x) + of_int (lookup (mapping_of \<G>) x)))"
  unfolding of_int_mpoly_def
  unfolding MPoly_Type.plus_mpoly.rep_eq MPoly_Type.plus_mpoly.abs_eq
  unfolding Poly_Mapping.plus_poly_mapping.rep_eq
  unfolding comp_apply
  unfolding Int.ring_1_class.of_int_add 
  by auto

  have "of_int_mpoly \<F> + of_int_mpoly \<G> =   MPoly
     (Abs_poly_mapping (\<lambda>x. of_int (lookup (mapping_of \<F>) x)) +
      Abs_poly_mapping (\<lambda>x. of_int (lookup (mapping_of \<G>) x)))" 
  unfolding of_int_mpoly_def
  unfolding MPoly_Type.plus_mpoly.rep_eq MPoly_Type.plus_mpoly.abs_eq
  unfolding comp_apply
  by auto

  also have " ... = MPoly (Abs_poly_mapping
       (\<lambda>x. of_int (lookup (mapping_of \<F>) x) + of_int (lookup (mapping_of \<G>) x)))" 
    using Abs_distrib MPoly_inject by auto
  finally have RHS:"of_int_mpoly \<F> + of_int_mpoly \<G> = MPoly (Abs_poly_mapping
       (\<lambda>x. of_int (lookup (mapping_of \<F>) x) + of_int (lookup (mapping_of \<G>) x)))" by auto
  show ?thesis unfolding LHS RHS by auto
qed

lemma of_int_mpoly_neg [of_int_mpoly_simps]:
  fixes \<G> :: "int mpoly"
  shows "of_int_mpoly (- \<G>) = - of_int_mpoly \<G>"
proof -
  have Abs_minus:"- Abs_poly_mapping (\<lambda>x. of_int (( lookup (mapping_of \<G>)) x)) = Abs_poly_mapping (- (\<lambda>x. of_int (( lookup (mapping_of \<G>)) x)))"
    using eq_onp_intF Poly_Mapping.uminus_poly_mapping.abs_eq[of "\<lambda>x. of_int (( lookup (mapping_of \<G>)) x)"] 
    by auto
  have "of_int_mpoly (- \<G>) = MPoly (Abs_poly_mapping (\<lambda>x. of_int ((- lookup (mapping_of \<G>)) x)))"
    unfolding of_int_mpoly_def MPoly_Type.uminus_mpoly.rep_eq
    unfolding Poly_Mapping.uminus_poly_mapping.rep_eq
    unfolding comp_apply by auto
  also have "... = MPoly (Abs_poly_mapping (\<lambda>x. - of_int (( lookup (mapping_of \<G>)) x)))"
    unfolding Int.ring_1_class.of_int_minus[symmetric] by auto
  also have "... = MPoly (Abs_poly_mapping (- (\<lambda>x. of_int (( lookup (mapping_of \<G>)) x))))"
    unfolding uminus_apply by auto
  also have "... = MPoly (- Abs_poly_mapping (\<lambda>x. of_int (( lookup (mapping_of \<G>)) x)))"
    unfolding Abs_minus MPoly_inject by auto
  also have "... = - MPoly (Abs_poly_mapping (\<lambda>x. of_int (( lookup (mapping_of \<G>)) x)))"
    unfolding uminus_mpoly.abs_eq by auto 
  also have "... = - of_int_mpoly \<G>" unfolding of_int_mpoly_def comp_apply by auto
  finally show ?thesis by auto
qed

lemma of_int_mpoly_diff [of_int_mpoly_simps]:
  fixes \<F> \<G> :: "int mpoly"
  shows "of_int_mpoly (\<F> - \<G>) = of_int_mpoly \<F> - of_int_mpoly \<G>"
  unfolding group_add_class.diff_conv_add_uminus
  unfolding of_int_mpoly_add of_int_mpoly_neg
  by auto

lemma of_int_mpoly_mult [of_int_mpoly_simps]:
  fixes \<F> \<G> :: "int mpoly"
  shows "(of_int_mpoly (\<F> * \<G>) :: ('a::ring_1) mpoly) = of_int_mpoly \<F> * of_int_mpoly \<G>" 
proof -
  have Abs_distrib:"(Abs_poly_mapping (\<lambda>x. of_int (lookup (mapping_of \<F>) x)) *
      Abs_poly_mapping (\<lambda>x. of_int (lookup (mapping_of \<G>) x)))
   = (Abs_poly_mapping
       (prod_fun (\<lambda>x. of_int (lookup (mapping_of \<F>) x)) (\<lambda>x. of_int (lookup (mapping_of \<G>) x))))"
    using eq_onp_intF[of "\<F>"] eq_onp_intF[of "\<G>"]
      Poly_Mapping.times_poly_mapping.abs_eq[of "\<lambda>x. of_int (lookup (mapping_of \<F>) x)" "\<lambda>x. of_int (lookup (mapping_of \<G>) x)"]
    by auto

  have of_int_prod_fun: "of_int (prod_fun (lookup (mapping_of \<F>)) (lookup (mapping_of \<G>)) x)
        = prod_fun (\<lambda>x. of_int (lookup (mapping_of \<F>) x)) (\<lambda>x. of_int (lookup (mapping_of \<G>) x)) x" for x :: "nat \<Rightarrow>\<^sub>0 nat"
    unfolding prod_fun_def
    unfolding of_int_Sum_any
    apply (subst of_int_Sum_any, simp)
    unfolding comp_def of_int_sum of_int_mult
    apply (subst of_int_Sum_any, simp)
    apply (rule Sum_any.cong)
    apply (simp add: when_def)
    by (metis (mono_tags, opaque_lifting) of_int_0)

  have "of_int_mpoly (\<F> * \<G>) = MPoly (Abs_poly_mapping
       (\<lambda>x. of_int (prod_fun (lookup (mapping_of \<F>)) (lookup (mapping_of \<G>)) x)))"
      unfolding of_int_mpoly_def
      unfolding MPoly_Type.times_mpoly.rep_eq MPoly_Type.times_mpoly.abs_eq
      unfolding Poly_Mapping.times_poly_mapping.rep_eq
      unfolding comp_apply
      by auto
  also have "... = MPoly (Abs_poly_mapping
       (prod_fun (\<lambda>x. of_int (lookup (mapping_of \<F>) x)) (\<lambda>x. of_int (lookup (mapping_of \<G>) x))))"
    using of_int_prod_fun
    apply (simp add: MPoly_inject)
    apply (subst Abs_poly_mapping_inject)
    subgoal
      by (metis eq_onp_def eq_onp_intF mem_Collect_eq times_mpoly.rep_eq
          times_poly_mapping.rep_eq) 
    subgoal 
      by (metis eq_onp_def eq_onp_intF finite_prod_fun mem_Collect_eq) 
    subgoal
      using of_int_prod_fun by blast 
    done
  finally have LHS: "of_int_mpoly (\<F> * \<G>) = MPoly (Abs_poly_mapping
       (prod_fun (\<lambda>x. of_int (lookup (mapping_of \<F>) x)) (\<lambda>x. of_int (lookup (mapping_of \<G>) x))))"
    by auto
  
  have "of_int_mpoly \<F> * of_int_mpoly \<G> =   MPoly
     (Abs_poly_mapping (\<lambda>x. of_int (lookup (mapping_of \<F>) x)) *
      Abs_poly_mapping (\<lambda>x. of_int (lookup (mapping_of \<G>) x)))" 
  unfolding of_int_mpoly_def
  unfolding MPoly_Type.times_mpoly.rep_eq MPoly_Type.times_mpoly.abs_eq
  unfolding comp_apply
  by auto

  also have " ... = MPoly (Abs_poly_mapping
       (prod_fun (\<lambda>x. of_int (lookup (mapping_of \<F>) x)) (\<lambda>x. of_int (lookup (mapping_of \<G>) x))))" 
    using Abs_distrib MPoly_inject by auto 
  finally have RHS:"of_int_mpoly \<F> * of_int_mpoly \<G> = 
        MPoly (Abs_poly_mapping
        (prod_fun (\<lambda>x. of_int (lookup (mapping_of \<F>) x)) (\<lambda>x. of_int (lookup (mapping_of \<G>) x))))" 
    by auto
  show ?thesis unfolding LHS RHS by auto
qed

lemma of_int_mpoly_power [of_int_mpoly_simps]:
  fixes \<F> :: "int mpoly"
  shows "of_int_mpoly (\<F> ^ n) = (of_int_mpoly \<F>) ^ n"
  by (induction n; simp add: of_int_mpoly_simps)

lemma of_int_mpoly_sum [of_int_mpoly_simps]:
  fixes f :: "'a \<Rightarrow> int mpoly" and S
  shows "of_int_mpoly (sum f S) = sum (of_int_mpoly \<circ> f) S"
  by (rule infinite_finite_induct; auto simp add: of_int_mpoly_simps)

lemma of_int_mpoly_prod [of_int_mpoly_simps]:
  fixes f :: "'a \<Rightarrow> int mpoly" and S
  shows "of_int_mpoly (prod f S) = prod (of_int_mpoly \<circ> f) S"
  by (rule infinite_finite_induct; auto simp add: of_int_mpoly_simps)

lemma of_int_mpoly_Sum_any:
  fixes f :: "'a \<Rightarrow> int mpoly"
  assumes "finite {a. f a \<noteq> 0}"
  shows "(of_int_mpoly (Sum_any f) :: 'b::ring_1 mpoly) = Sum_any (of_int_mpoly \<circ> f)"
proof -
  have "of_int_mpoly (sum f {a. f a \<noteq> 0}) = sum (of_int_mpoly \<circ> f) {a. f a \<noteq> 0}"
    by (rule of_int_mpoly_sum)
  also have "... = sum (of_int_mpoly \<circ> f :: 'a \<Rightarrow> 'b mpoly) {a. (of_int_mpoly \<circ> f :: 'a \<Rightarrow> 'b mpoly) a \<noteq> 0}"
    apply (rule sum.mono_neutral_cong_right)
    using assms apply (auto simp add: of_int_mpoly_simps)
    done
  finally show ?thesis unfolding Sum_any.expand_set .
qed

lemma of_int_mpoly_Prod_any:
  fixes f :: "'a \<Rightarrow> int mpoly"
  assumes "finite {a. f a \<noteq> 1}"
  shows "(of_int_mpoly (Prod_any f) :: 'b::comm_ring_1 mpoly) = Prod_any (of_int_mpoly \<circ> f)"
proof -
  have "of_int_mpoly (prod f {a. f a \<noteq> 1}) = prod (of_int_mpoly \<circ> f) {a. f a \<noteq> 1}"
    by (rule of_int_mpoly_prod)
  also have "... = prod (of_int_mpoly \<circ> f :: 'a \<Rightarrow> 'b mpoly) {a. (of_int_mpoly \<circ> f :: 'a \<Rightarrow> 'b mpoly) a \<noteq> 1}"
    apply (rule prod.mono_neutral_cong_right)
    using assms apply (auto simp add: of_int_mpoly_simps)
    done
  finally show ?thesis unfolding Prod_any.expand_set .
qed

lemma insertion_of_int_mpoly:
  "insertion (of_int \<circ> \<alpha>) ((of_int_mpoly P) :: 'a::comm_ring_1 mpoly) = of_int (insertion \<alpha> P)"
proof -
  show ?thesis
    unfolding of_int_mpoly_def
    unfolding insertion_def insertion_aux_def insertion_fun_def
    apply (simp add: MPoly_inverse)
    apply (subst of_int_Sum_any)
    subgoal by simp
    subgoal
      unfolding comp_def
      apply (rule Sum_any.cong)
      unfolding of_int_mult
      apply (rule arg_cong2[of _ _ _ _ times])
      subgoal
        apply (subst Abs_poly_mapping_inverse)
        subgoal
          using finite_imageI[of _ "of_int"] finite_lookup
          by (smt (verit, best) finite_subset mem_Collect_eq of_int_0 subsetI)
        subgoal ..
        done
      subgoal for a
        apply (subst of_int_Prod_any)
        subgoal
          apply (rule rev_finite_subset[of "{x. lookup a x \<noteq> 0}"])
          subgoal by simp
          subgoal using power_0 Collect_mono_iff by fastforce
          done
        subgoal by simp
        done
      done
    done
qed

lemma of_int_mpoly_poly_subst_monom [of_int_mpoly_simps]:
  "of_int_mpoly (poly_subst_monom f a) = poly_subst_monom (of_int_mpoly \<circ> f :: nat \<Rightarrow> 'a::comm_ring_1 mpoly) a"
  unfolding poly_subst_monom_def comp_def
  apply (subst of_int_mpoly_Prod_any)
  subgoal by (smt (verit, best) Collect_mono_iff finite_lookup power_0 rev_finite_subset)
  subgoal by (simp add: of_int_mpoly_simps)
  done

lemma of_int_mpoly_poly_subst [of_int_mpoly_simps]:
  "of_int_mpoly (poly_subst f P) = poly_subst (of_int_mpoly \<circ> f :: nat \<Rightarrow> 'a::comm_ring_1 mpoly) (of_int_mpoly P)"
  unfolding poly_subst_def
  unfolding coeff_def times_mpoly.rep_eq times_poly_mapping.rep_eq prod_fun_def
  unfolding coeff_def[symmetric]
  apply (subst of_int_mpoly_Sum_any)
  subgoal by (metis (mono_tags, lifting) Collect_mono coeff_def finite_lookup mult_zero_left of_int_0_eq_iff of_int_Const rev_finite_subset)
  subgoal
    apply (rule Sum_any.cong)
    apply (simp add: of_int_mpoly_simps)
    done
  done

lemma of_int_general_Const: "(of_int x :: ('a::ring_1) mpoly) = of_int_mpoly (Const x)"
  by (metis Const.abs_eq Const\<^sub>0_def monom.abs_eq monom_of_int of_int_mpoly_Const)

lemma of_int_mpoly_degree[simp]:
  "MPoly_Type.degree (of_int_mpoly P :: ('a::ring_1) mpoly) \<le> MPoly_Type.degree P"
proof -

  have a: "{k. (of_int \<circ> lookup (mapping_of P)) k \<noteq> 0} \<subseteq> {k. (lookup (mapping_of P)) k \<noteq> 0}"
    by auto

  hence b: "insert 0 ((\<lambda>m. lookup m x) ` {k. (of_int \<circ> lookup (mapping_of P)) k \<noteq> 0})
            \<subseteq> insert 0 ((\<lambda>m. lookup m x) ` {k. (lookup (mapping_of P)) k \<noteq> 0})" for x
    by auto

  show ?thesis
    unfolding MPoly_Type.degree.rep_eq of_int_mpoly_def
    apply (subst MPoly_inverse)
    subgoal by simp
    apply (rule le_funI) 
    unfolding keys.rep_eq
    apply (subst Abs_poly_mapping_inverse)
    subgoal by auto (metis (mono_tags, lifting) finite_lookup finite_subset mem_Collect_eq of_int_0 subsetI)
    unfolding comp_def
    using Max_mono[OF b] by auto
qed

lemma vars_of_int_mpoly:
  "vars (of_int_mpoly P :: ('a :: {comm_semiring_1, ring_1}) mpoly) \<subseteq> vars P"
  unfolding of_int_mpoly_def vars_def
  by (metis SUP_mono coeff_keys dual_order.refl of_int_0 of_int_mpoly_coeff of_int_mpoly_def)


end