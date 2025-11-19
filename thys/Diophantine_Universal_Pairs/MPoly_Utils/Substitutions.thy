theory Substitutions
  imports Poly_Expansions
begin

subsection \<open>Substitution\<close>

text \<open>The following definitions allow substituting polynomials into the variables of the given
      polynomial p. They correspond to \<open>{@const subst_pp}\<close> and \<open>{@const poly_subst\<close> in the
      AFP entry \<open>{@afp Polynomials.Poly_PM}\<close>\<close>

definition poly_subst_monom :: "(nat \<Rightarrow> 'a::comm_semiring_1 mpoly) \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a mpoly"
  where "poly_subst_monom f t = (\<Prod>x. (f x) ^ (lookup t x))"

definition poly_subst :: "(nat \<Rightarrow> 'a::comm_semiring_1 mpoly) \<Rightarrow> 'a mpoly \<Rightarrow> 'a mpoly"
  where "poly_subst f p = Sum_any (\<lambda>t. (Const (coeff p t)) * (poly_subst_monom f t))"

definition poly_subst_list where "poly_subst_list \<equiv> poly_subst \<circ> (!\<^sub>0)"
abbreviation insertion_list where "insertion_list \<equiv> insertion \<circ> (!\<^sub>0)"

lemma poly_subst_monom_alt: "poly_subst_monom f t = (\<Prod>x \<in> keys t. (f x) ^ (lookup t x))"
  unfolding poly_subst_monom_def
  apply (rule Prod_any.expand_superset)
  subgoal by simp
  subgoal using in_keys_iff by fastforce
  done

lemma poly_subst_alt: "poly_subst f p = (\<Sum>t \<in> keys (mapping_of p). (Const (coeff p t)) * (poly_subst_monom f t))"
  unfolding poly_subst_def
  apply (rule Sum_any.expand_superset)
  subgoal by simp
  subgoal using Const_zero coeff_keys mult_not_zero by fastforce
  done

lemma poly_subst_list_id:
  fixes p :: "'a::{comm_semiring_1,ring_no_zero_divisors} mpoly"
  assumes "k \<ge> max_vars p"
  shows "poly_subst_list (map Var [0..<Suc k]) p = p"
proof - 
  have h0: "\<And>x t. x\<in>keys t \<and> t \<in> keys (mapping_of p) \<Longrightarrow> x < Suc (max_vars p)"
    unfolding max_vars_def vars_def
    apply (subst less_Suc_eq_le)
    by (subst Max.coboundedI, auto)
  hence "\<And>x t. x\<in>keys t \<and> t \<in> keys (mapping_of p) \<Longrightarrow> x < Suc k"
    using assms by fastforce
  hence h1: "\<And>x t. x\<in>keys t \<and> t \<in> keys (mapping_of p) \<Longrightarrow>
                map Var [0..<Suc k] !\<^sub>0 x = (Var x)"
    unfolding nth0_def
    apply (subst nth_map, simp)
    by (subst nth_upt, simp_all)

  show ?thesis
    unfolding poly_subst_list_def comp_def
    unfolding poly_subst_alt poly_subst_monom_alt
    apply (subst (9) mpoly_multivariate_expansion')
    apply (rule sum.cong, simp)
    apply (subst mult_left_cancel, metis Const_zero coeff_Const_zero coeff_keys)
    apply (rule prod.mono_neutral_cong_left, simp)
    using h0 less_Suc_eq_le apply force
    apply (simp add: in_keys_iff)
    by (subst h1, simp_all add: assms)
qed


lemma insertion_poly_subst_monom:
  "insertion g (poly_subst_monom f t) = (\<Prod>x. (insertion g (f x)) ^ (lookup t x))"
  unfolding poly_subst_monom_alt
  apply (subst insertion_prod)
  subgoal by simp
  subgoal
    unfolding insertion_pow
    apply (rule Prod_any.expand_superset[symmetric])
    subgoal by simp
    subgoal using in_keys_iff by fastforce
    done
  done

lemma insertion_poly_subst:
  "insertion g (poly_subst f p) = insertion ((insertion g) \<circ> f) p"
  unfolding poly_subst_alt
  apply (subst (7) poly_eq_sum_monom_alt)
  apply (subst (1 2) insertion_sum)
  subgoal by simp
  subgoal
    unfolding insertion_mult insertion_Const
    unfolding insertion_poly_subst_monom
    unfolding insertion_monom
    by simp
  done

lemma insertion_nth0: "insertion f (l !\<^sub>0 x) = (map (insertion f) l) !\<^sub>0 x"
  unfolding nth0_def
  apply (induction l)
  by simp (metis insertion_zero length_map nth_map when_def)

lemma poly_subst_monom_zero [simp]:
  "poly_subst_monom f 0 = 1"
  unfolding poly_subst_monom_alt keys_zero
  by simp

lemma poly_subst_monom_single [simp]:
  "poly_subst_monom f (Poly_Mapping.single v 1) = f v"
  unfolding poly_subst_monom_alt
  by simp

lemma poly_subst_monom_add: "poly_subst_monom f (m\<^sub>1 + m\<^sub>2) = poly_subst_monom f m\<^sub>1 * poly_subst_monom f m\<^sub>2"
  unfolding poly_subst_monom_def lookup_add power_add
  apply (rule Prod_any.distrib)
  apply (metis (mono_tags, lifting) finite_keys finite_nat_set_iff_bounded in_keys_iff mem_Collect_eq power_0)+
  done

lemma poly_subst_zero [simp]:
  "poly_subst f 0 = 0"
  unfolding poly_subst_def poly_subst_monom_def coeff_def zero_mpoly.rep_eq zero_poly_mapping.rep_eq Const_when when_mult Sum_any_when_equal Const_zero
  by simp

lemma poly_subst_one [simp]:
  "poly_subst f 1 = 1"
  unfolding poly_subst_def poly_subst_monom_def coeff_def one_mpoly.rep_eq one_poly_mapping.rep_eq Const_when when_mult Sum_any_when_equal Const_one
  by simp

lemma poly_subst_Var [simp]:
  "poly_subst f (Var v) = f v"
  unfolding poly_subst_alt Var.rep_eq keys.rep_eq Var\<^sub>0_def lookup_single when_neq_zero
  apply simp
  apply (subst (2) power_one_right[symmetric])
  unfolding One_nat_def[symmetric]
  apply (subst coeff_var_power_eq)
  unfolding poly_subst_monom_single Const_one
  by simp

lemma poly_subst_Const [simp]:
  "poly_subst f (Const c) = (Const c)"
  unfolding poly_subst_alt Const.rep_eq keys.rep_eq Const\<^sub>0_def lookup_single when_neq_zero
  apply (cases "c = 0")
  by (auto simp add: Const_zero coeff_Const_zero)

lemma poly_subst_numeral[simp]:
  "poly_subst f (numeral n) = (numeral n)"
  unfolding Const_numeral[symmetric]
  by simp

lemma poly_subst_add [simp]:
  "poly_subst f (P + Q) = poly_subst f P + poly_subst f Q"
proof -
  have 0: "\<And>P. {a. Const (lookup (mapping_of P) a) * poly_subst_monom f a \<noteq> 0}
            \<subseteq> {a. lookup (mapping_of P) a \<noteq> 0}"
    by (auto simp: Const_zero)

  have H: "finite {a. Const (lookup (mapping_of P) a) * poly_subst_monom f a \<noteq> 0}" for P
    using 0[of P] finite_lookup
    by (rule finite_subset)

  thus ?thesis
    unfolding poly_subst_def coeff_add[symmetric] Const_add[symmetric]
    unfolding coeff_def
    unfolding Sum_any.distrib[OF H H, symmetric]
    unfolding coeff_def[symmetric]
    by (auto simp: algebra_simps)
qed  

lemma poly_subst_uminus [simp]:
  "poly_subst f (- P) = - poly_subst f P "
  by (metis add_cancel_right_right add_eq_0_iff poly_subst_add)

lemma poly_subst_diff [simp]:
  "poly_subst f ((P::('a::{ab_group_add,comm_semiring_1}) mpoly) - Q) = poly_subst f P - poly_subst f Q"
  by (metis diff_eq_eq poly_subst_add)

lemma poly_subst_sum:
  "poly_subst f (sum P A) = sum (poly_subst f \<circ> P) A"
  by (induct A rule: infinite_finite_induct; auto)

lemma poly_subst_mult [simp]:
  "poly_subst f (P * Q) = poly_subst f P * poly_subst f Q"
  unfolding poly_subst_def
  unfolding coeff_def times_mpoly.rep_eq times_poly_mapping.rep_eq prod_fun_def
  unfolding coeff_def[symmetric]
proof -
  have 0: "finite {m. coeff P m \<noteq> 0}" by (simp add: coeff_def)
  have 1: "finite {m. coeff Q m \<noteq> 0}" by (simp add: coeff_def)

  have "finite ({m\<^sub>1. coeff P m\<^sub>1 \<noteq> 0} \<times> {m\<^sub>2. coeff Q m\<^sub>2 \<noteq> 0})"
    using 0 1 by simp
  hence "finite {(m\<^sub>1, m\<^sub>2). coeff P m\<^sub>1 \<noteq> 0 \<and> coeff Q m\<^sub>2 \<noteq> 0}"
    apply (rule back_subst)
    apply (rule arg_cong[of _ _ finite])
    apply auto
    done
  hence 2: "finite {(m\<^sub>1, m\<^sub>2). Const (coeff P m\<^sub>1) * Const (coeff Q m\<^sub>2) * poly_subst_monom f (m\<^sub>1 + m\<^sub>2) \<noteq> 0}"
    apply (rule rev_finite_subset)
    apply (auto simp add: Const_zero)
    done

  have "Sum_any (\<lambda>m. Const (Sum_any (\<lambda>m\<^sub>1. coeff P m\<^sub>1 * Sum_any (\<lambda>m\<^sub>2. coeff Q m\<^sub>2 when m = m\<^sub>1 + m\<^sub>2))) * poly_subst_monom f m) =
    Sum_any (\<lambda>m. Sum_any (\<lambda>m\<^sub>1. (Const (coeff P m\<^sub>1)) * Sum_any (\<lambda>m\<^sub>2. Const ((coeff Q m\<^sub>2) when m = m\<^sub>1 + m\<^sub>2))) * poly_subst_monom f m)"
    unfolding Const_sum_Any comp_def Const_mult[symmetric] ..
  also have "... = Sum_any (\<lambda>m. Sum_any (\<lambda>m\<^sub>1. Sum_any (\<lambda>m\<^sub>2. (Const (coeff P m\<^sub>1)) * Const ((coeff Q m\<^sub>2) when m = m\<^sub>1 + m\<^sub>2))) * poly_subst_monom f m)"
    apply (subst Sum_any_right_distrib)
    subgoal by (rule rev_finite_subset[OF 1]; auto simp add: Const_zero)
    subgoal ..
    done
  also have "... = Sum_any (\<lambda>m. Sum_any (\<lambda>m\<^sub>1. Sum_any (\<lambda>m\<^sub>2. (Const (coeff P m\<^sub>1)) * Const (coeff Q m\<^sub>2) when m = m\<^sub>1 + m\<^sub>2)) * poly_subst_monom f m)"
    unfolding Const_when mult_when ..
  also have "... = Sum_any (\<lambda>m. Sum_any (\<lambda>m\<^sub>1. Sum_any (\<lambda>m\<^sub>2. (Const (coeff P m\<^sub>1)) * Const (coeff Q m\<^sub>2) * poly_subst_monom f (m\<^sub>1 + m\<^sub>2) when m = m\<^sub>1 + m\<^sub>2)))"
    apply (subst Sum_any_left_distrib)
    subgoal by (rule finite_subset[OF _ 0]; auto simp add: Const_zero)
    subgoal
      apply (subst Sum_any_left_distrib)
      subgoal by (rule finite_subset[OF _ 1]; auto simp add: Const_zero)
      subgoal
        apply (rule Sum_any.cong)
        apply (rule Sum_any.cong)
        apply (rule Sum_any.cong)
        unfolding when_mult
        apply (rule when_cong[OF refl])
        apply simp
        done
      done
    done
  also have "... = Sum_any (\<lambda>m\<^sub>1. Sum_any (\<lambda>m\<^sub>2. (Const (coeff P m\<^sub>1)) * (Const (coeff Q m\<^sub>2)) * poly_subst_monom f (m\<^sub>1 + m\<^sub>2)))"
    by (rule Sum_any_rev_image_add[OF 2])
  also have "... = Sum_any (\<lambda>m\<^sub>1. Sum_any (\<lambda>m\<^sub>2. (Const (coeff P m\<^sub>1) * poly_subst_monom f m\<^sub>1) * (Const (coeff Q m\<^sub>2) * poly_subst_monom f m\<^sub>2)))"
    unfolding poly_subst_monom_add by (simp add: algebra_simps)
  also have "... = Sum_any (\<lambda>m\<^sub>1. Const (coeff P m\<^sub>1) * poly_subst_monom f m\<^sub>1) * Sum_any (\<lambda>m\<^sub>2. Const (coeff Q m\<^sub>2) * poly_subst_monom f m\<^sub>2)"
    apply (rule Sum_any_product[symmetric])
    subgoal by (rule finite_subset[OF _ 0]; auto simp add: Const_zero)
    subgoal by (rule finite_subset[OF _ 1]; auto simp add: Const_zero)
    done
  finally show "Sum_any (\<lambda>m. Const (Sum_any (\<lambda>m\<^sub>1. coeff P m\<^sub>1 * Sum_any (\<lambda>m\<^sub>2. coeff Q m\<^sub>2 when m = m\<^sub>1 + m\<^sub>2))) * poly_subst_monom f m) =
    Sum_any (\<lambda>m\<^sub>1. Const (coeff P m\<^sub>1) * poly_subst_monom f m\<^sub>1) * Sum_any (\<lambda>m\<^sub>2. Const (coeff Q m\<^sub>2) * poly_subst_monom f m\<^sub>2)"
    .
qed

lemma poly_subst_prod:
  "poly_subst f (prod P A) = prod (poly_subst f \<circ> P) A"
  by (induct A rule: infinite_finite_induct; auto)

lemma poly_subst_monom_id: "poly_subst_monom (Var) t = monom t 1"
proof -
  have "mapping_of (poly_subst_monom (Var) t) = Poly_Mapping.single t 1"
    unfolding poly_subst_monom_alt
    apply (subst monom.rep_eq[symmetric])
    apply (subst monom_expansion)
    by (subst mapping_of_inject, simp add: Const_one)

  thus ?thesis
    unfolding monom.abs_eq by (smt (verit) mapping_of_inverse)
qed

lemma poly_subst_id: "poly_subst (Var) p = p"
  apply (induct p rule: mpoly_induct, simp_all)
  apply (simp add: poly_subst_def poly_subst_monom_id)
  by (smt (verit, ccfv_SIG) Const.abs_eq Const\<^sub>0_def Sum_any.cong monom.abs_eq mult.right_neutral
          poly_eq_sum_monom smult_conv_mult smult_monom)

text \<open>Vars of substitutions\<close>

lemma vars_poly_subst_monom: "vars (poly_subst_monom f t) \<subseteq> \<Union> (vars ` (f ` keys t))"
  unfolding poly_subst_monom_alt
  apply (rule subset_trans[OF vars_prod])
  using vars_pow by auto

lemma vars_poly_subst_monom': "vars (poly_subst_monom ((!\<^sub>0) ls) t) \<subseteq> \<Union> (vars ` set ls)"
  apply (rule subset_trans[OF vars_poly_subst_monom])
  unfolding nth0_def when_def keys.rep_eq
  using nth_mem Const_zero MPoly_Type.degree_zero vars_non_zero_degree by force

lemma vars_poly_subst_list: "vars (poly_subst_list ls p) \<subseteq> \<Union> (vars ` set ls)"
  unfolding poly_subst_alt comp_def poly_subst_list_def
  apply (rule subset_trans[OF vars_setsum], simp_all)
  using vars_poly_subst_monom' vars_mult by fastforce

lemma vars_poly_subst_monom_bounded:
  "\<forall>v\<in>(keys t). v \<le> bound \<Longrightarrow> vars (poly_subst_monom ((!\<^sub>0) ls) t) \<subseteq> \<Union> (vars ` set (take (Suc bound) ls))"
  unfolding poly_subst_monom_alt
  apply (rule subset_trans[OF vars_prod], auto)
  apply (drule set_mp[OF vars_pow])
  subgoal for m v
  proof (rule bexI[of _ "ls !\<^sub>0 v"], assumption)
    assume "\<forall>v\<in>(keys t). v \<le> bound"
    moreover assume "v \<in> keys t"
    ultimately have "v \<le> bound" by auto
    moreover assume "m \<in> vars (ls !\<^sub>0 v)"
    ultimately show "ls !\<^sub>0 v \<in> set (take (Suc bound) ls)"
      apply (cases "v < length ls", simp_all add: nth0_def)
      unfolding in_set_conv_nth by (intro exI[of _ v], auto)
  qed done

lemma aux0: "max_vars p \<le> bound \<Longrightarrow> m \<in> keys (mapping_of p) \<Longrightarrow> \<forall>v\<in>(keys m). v \<le> bound"
  unfolding max_vars_def vars_def by auto

lemma vars_poly_subst_list_bounded:
  assumes "max_vars p \<le> bound"
  shows "vars (poly_subst_list ls p) \<subseteq> \<Union> (vars ` set (take (Suc bound) ls))"
proof -
  from assms have a: "t\<in>keys (mapping_of p) \<Longrightarrow> \<forall>v\<in>(keys t). v \<le> bound" for t
    by (simp add: aux0)
  hence b: "t\<in>keys (mapping_of p) \<Longrightarrow> vars (poly_subst_monom ((!\<^sub>0) ls) t)
                                   \<subseteq> \<Union> (vars ` set (take (Suc bound) ls))" for t
    by (rule vars_poly_subst_monom_bounded, simp)
  show ?thesis
    apply (simp add: poly_subst_list_def poly_subst_alt)
    apply (rule subset_trans[OF vars_setsum], auto simp: vars_mult)
    subgoal for x t
      using vars_mult b[of t] apply simp
      by (smt (verit, del_insts) UN_iff subset_iff sup_bot_left vars_Const vars_mult)
    done
qed


lemma vars_poly_subst: 
  "vars (poly_subst f p) \<subseteq> (\<Union>t \<in> vars p. vars (f t))"
proof -
  {
    fix x y
    assume "x \<in> keys (mapping_of p)"
      and "y \<in> (\<lambda>xa. f xa ^ lookup x xa) ` keys x"
    from this obtain z where "z \<in> keys x" and y_def: "y = f z ^ lookup x z"
      by auto

    from this have z_in: "z \<in> vars p"
      unfolding vars_def image_def
      apply (intro UnionI[of "keys x" "{y. \<exists>x\<in>keys (mapping_of p). y = keys x}" z])
      unfolding mem_Collect_eq
       apply (rule bexI[of _ x])
      using `x \<in> keys (mapping_of p)`
      by auto

    have 0: "vars (f z) \<in> {y. \<exists>x\<in>\<Union> {y. \<exists>x\<in>keys (mapping_of p). y = keys x}.
                       y = \<Union> {y. \<exists>x\<in>keys (mapping_of (f x)). y = keys x}}"
      unfolding mem_Collect_eq
      unfolding image_def[symmetric] vars_def[symmetric] y_def
      by (rule bexI[of _ z, OF _ z_in]; simp)

    {
      fix w
      assume "w \<in> {ya. \<exists>x\<in>keys (mapping_of y). ya = keys x}"
      from this obtain v where "v \<in> keys (mapping_of y)" and w_def: "w = keys v"
        by auto
      hence "keys v \<subseteq> vars y"
        unfolding vars_def
        by auto

      have "w \<subseteq> vars (f z)"
        unfolding w_def
        apply (rule subset_trans[OF `keys v \<subseteq> vars y`])
        unfolding y_def
        by (simp add: vars_pow)

      from this and 0
      have "\<exists>y. y \<in> {y. \<exists>x\<in>\<Union> {y. \<exists>x\<in>keys (mapping_of p). y = keys x}.
                         y = \<Union> {y. \<exists>x\<in>keys (mapping_of (f x)). y = keys x}} \<and>
                w \<subseteq> y"
        by auto
    }
    note 0 = this

    hence "vars y \<subseteq> (\<Union>t\<in>vars p. vars (f t))"
      unfolding vars_def UN_simps image_def
      apply (intro Union_subsetI)
      by assumption
  }
  note 0 = this
  {
    fix x
    assume Hx: "x \<in> keys (mapping_of p)"
    have "vars (Const (coeff p x) * poly_subst_monom f x) \<subseteq> vars (poly_subst_monom f x)"
      apply (rule subset_trans[OF vars_mult Un_least])
      by simp_all

    also have "... \<subseteq> (\<Union>t\<in>vars p. vars (f t))"
      unfolding poly_subst_monom_alt
      apply (rule subset_trans[OF vars_prod])
      apply (rule UN_least)
      using 0[OF Hx] by assumption

    finally have "vars (Const (coeff p x) * poly_subst_monom f x) \<subseteq> (\<Union>t\<in>vars p. vars (f t))" .
  }
  note 0 = this
  show ?thesis
    unfolding poly_subst_alt
    apply (rule subset_trans[OF vars_setsum[OF finite_keys]])
    apply (rule UN_least)
    using 0 by assumption
qed

lemma max_vars_poly_subst_list_general:
  shows "max_vars (poly_subst_list ls p) \<le> Max (max_vars ` set ls)"
  unfolding max_vars_def
  apply (rule Max.boundedI, auto simp add: vars_finite)
  subgoal for a
  proof -
    assume "a \<in> vars (poly_subst_list ls p)"
    hence "a \<in> \<Union> (vars ` set ls)" using vars_poly_subst_list by force
    thus "a \<le> (MAX P\<in>set ls. Max (insert 0 (vars P)))"
      apply simp
      by (smt (verit, best) List.finite_set Max_ge dual_order.trans finite_imageI finite_insert
              imageI insert_absorb insert_subset subset_insertI vars_finite)
  qed done

lemma max_vars_poly_subst_list_bounded:
  "max_vars p \<le> bound \<Longrightarrow> max_vars (poly_subst_list ls p) \<le> Max (max_vars ` set (take (Suc bound) ls))"
proof -
  assume a: "max_vars p \<le> bound"

  {
    fix a
    assume "a \<in> vars (poly_subst_list ls p)"
    hence "a \<in> \<Union> (vars ` set (take (Suc bound) ls))"
      using vars_poly_subst_list_bounded[OF a] by auto
    hence "a \<le> (MAX P\<in>set (take (Suc bound) ls). Max (insert 0 (vars P)))"
      apply simp
      by (smt (verit, best) List.finite_set Max_ge dual_order.trans finite_imageI finite_insert
              imageI insert_absorb insert_subset subset_insertI vars_finite)
  } note b = this

  show ?thesis
    unfolding max_vars_def 
    by (rule Max.boundedI, auto simp add: vars_finite b)
qed

lemma max_vars_id:
  fixes p :: "'a::{comm_semiring_1,ring_no_zero_divisors} mpoly"
  shows "max_vars (poly_subst_list (map Var [0..<Suc k]) p) \<le> k"
  by (rule le_trans[OF max_vars_poly_subst_list_general], auto simp: max_vars_def)

text \<open>Degrees of substitutions\<close>

lemma degree_poly_subst_monom:
  fixes f
  assumes "finite {k. f k \<noteq> 0}"
  defines "degree_monom \<equiv> (\<lambda>m t. (lookup m) t)" (* Intentionally written this way for clarity *)
  shows "degree (poly_subst_monom f m) v
         \<le> (\<Sum>t | v\<in>vars (f t). degree_monom m t * degree (f t) v)"
proof -  
  have a0: "v \<notin> vars (f k) \<Longrightarrow> degree (f k ^ lookup m k) v = 0" for k
    unfolding le_0_eq[of "degree _ v", symmetric]
    apply (rule le_trans[OF degree_pow])
    by (simp add: in_vars_non_zero_degree)

  have a1: "(\<Sum>t | v \<in> vars (f t). lookup m t * degree (f t) v)
        = (\<Sum>t | t \<in> keys m \<and> v \<in> vars (f t). lookup m t * degree (f t) v)"
    unfolding keys.rep_eq apply (rule sum.mono_neutral_right, auto)
    using assms
    by (smt (verit, del_insts) MPoly_Type.degree_zero finite_nat_set_iff_bounded
            in_vars_non_zero_degree mem_Collect_eq)

  show ?thesis
    unfolding poly_subst_monom_alt degree_monom_def
    apply (subst a1)
    apply (rule le_trans[OF degree_prod[OF finite_keys]])
    apply (subst sum.setdiff_irrelevant[OF finite_keys,
                                         of "\<lambda>k. degree (f k ^ lookup m k) v", symmetric])
    apply (rule le_trans[OF sum_mono[OF degree_pow]])
    apply (rule sum_mono2, auto)
    by (rule ccontr, auto simp: a0)
qed

lemma degree_poly_subst: 
  fixes p :: "'a::comm_ring_1 mpoly"
  fixes f :: "nat \<Rightarrow> 'a mpoly"
  assumes "finite {k. f k \<noteq> 0}"
  shows "degree (poly_subst f p) v \<le> (\<Sum>t | v \<in> vars (f t). degree p t * degree (f t) v)"
proof -
  have "a \<in> keys (mapping_of p) \<Longrightarrow> degree (poly_subst_monom f a) v
             \<le> (\<Sum>t | v \<in> vars (f t). degree p t * degree (f t) v)" for a
    apply (rule le_trans[OF degree_poly_subst_monom[of f, OF assms]])
    apply (rule sum_mono, simp)
    unfolding degree.rep_eq by auto

  hence a0: "Max (insert 0 ((\<lambda>i. degree (poly_subst_monom f i) v) ` keys (mapping_of p)))
        \<le> (\<Sum>t | v \<in> vars (f t). degree p t * degree (f t) v)"
    by auto

  show ?thesis
    unfolding poly_subst_alt
    apply (rule le_trans[OF _ a0])
    apply (rule le_trans[OF degree_sum[OF finite_keys, of "\<lambda>t. Const (coeff p t) * poly_subst_monom f t"
                                        "mapping_of p" v]])
    using degree_mult degree_Const
    by simp (smt (verit, best) Max.coboundedI add_cancel_right_right degree_Const degree_mult
                 finite_imageI finite_insert finite_keys imageI insert_iff le_trans mult.commute)
qed

lemma degree_poly_subst': 
  fixes p :: "'a::comm_ring_1 mpoly"
  fixes f :: "nat \<Rightarrow> 'a mpoly"
  assumes "finite {k. f k \<noteq> 0}" (* this assumption is not actually required, it's just an artifact
  the proof method using the above intermediate result, written differently *)
  shows "degree (poly_subst f p) v \<le> (\<Sum>t\<in>vars p. degree p t * degree (f t) v)"
  apply (rule le_trans[OF degree_poly_subst], simp add: assms)
  apply (subst sum.mono_neutral_right[of "{t. v \<in> vars (f t)}" "vars p \<inter> {t. v \<in> vars (f t)}"])
  using in_vars_non_zero_degree assms
  subgoal by (smt (verit) Collect_mono emptyE rev_finite_subset vars_zero vars_finite)
  subgoal by auto
  subgoal using in_vars_non_zero_degree by auto
  subgoal by (simp add: sum_mono2 vars_finite) 
  done

lemma degree_poly_subst_list: 
  fixes p :: "'a::comm_ring_1 mpoly"
  shows "degree (poly_subst_list ls p) v \<le> (\<Sum>t | v \<in> vars (ls !\<^sub>0 t). degree p t * degree (ls !\<^sub>0 t) v)"
  unfolding poly_subst_list_def
  using degree_poly_subst[OF nth0_finite] by auto

lemma degree_poly_subst_list': 
  fixes p :: "'a::comm_ring_1 mpoly"
  shows "degree (poly_subst_list ls p) v \<le> (\<Sum>t \<le> length ls. degree p t * degree (ls !\<^sub>0 t) v)"
  apply (rule le_trans[OF degree_poly_subst_list])
  by (rule sum_mono2, auto simp: nth0_def when_def in_vars_non_zero_degree)


text \<open>Total degree of substitions\<close>

lemma deg_imp_tot_deg_zero: "(\<forall>v \<in> vars P. degree P v = 0) \<Longrightarrow> total_degree P = 0"
  by (metis bot_nat_0.extremum_uniqueI sum.neutral total_degree_bound)

lemma total_degree_poly_subst_monom:
  fixes f
  defines "degree_monom \<equiv> (\<lambda>m t. (lookup m) t)" (* Intentionally written this way for clarity *)
  shows "total_degree (poly_subst_monom f m)
         \<le> (\<Sum>t\<in>keys m. degree_monom m t * total_degree (f t))"
  unfolding poly_subst_monom_alt degree_monom_def
  apply (rule le_trans[OF total_degree_prod[OF finite_keys]])
  apply (rule le_trans[OF sum_mono[OF total_degree_pow]])
  by (rule sum_mono2) auto

lemma total_degree_poly_subst: 
  shows "total_degree (poly_subst f p) \<le> (\<Sum>t\<in>vars p. degree p t * total_degree (f t))"
proof -
  have "a \<in> keys (mapping_of p) \<Longrightarrow> total_degree (poly_subst_monom f a)
             \<le> (\<Sum>t\<in>vars p. degree p t * total_degree (f t))" for a
    apply (rule le_trans[OF total_degree_poly_subst_monom[of f]])
    apply (rule sum_le_included[of _ _ _ "\<lambda>x. x"], auto simp add: vars_finite vars_def)
    unfolding degree.rep_eq by auto

  hence a0: "Max (insert 0 ((\<lambda>i. total_degree (poly_subst_monom f i)) ` keys (mapping_of p)))
        \<le> (\<Sum>t\<in>vars p. degree p t * total_degree (f t))"
    by auto

  show ?thesis
    unfolding poly_subst_alt
    apply (rule le_trans[OF _ a0])
    apply (rule le_trans[OF total_degree_sum[OF finite_keys]])
    using total_degree_mult total_degree_Const
    apply simp
    by (smt (verit, del_insts) Max_ge add_0 dual_order.trans finite_imageI finite_insert
            finite_keys image_eqI insert_iff total_degree_Const total_degree_mult)
qed

lemma total_degree_poly_subst_list: 
  fixes p :: "'a::comm_ring_1 mpoly"
  shows "total_degree (poly_subst_list ls p) \<le> (\<Sum>t\<in>vars p. degree p t * total_degree (ls !\<^sub>0 t))"
  unfolding poly_subst_list_def
  using total_degree_poly_subst by auto

lemma total_degree_poly_subst_list':
  fixes p :: "'a::comm_ring_1 mpoly"
  assumes "max_vars p \<le> length ls"
  shows "total_degree (poly_subst_list ls p) \<le> (\<Sum>t\<le>length ls. degree p t * total_degree (ls !\<^sub>0 t))"
  apply (rule le_trans[OF total_degree_poly_subst_list])
  apply (cases "vars p = {}", simp_all)
  apply (rule sum_mono2, simp_all)
  using assms[unfolded max_vars_def]
  by (simp add: subset_iff vars_finite)

(* This lemma is suboptimal by a factor of length ls due to the double use of the bounds
      total_degree \<le> sum degree vars
      sum degree vars \<le> total_degree * length. *)
lemma total_degree_poly_subst_list'': 
  fixes p :: "'a::comm_ring_1 mpoly"
  assumes "\<forall>i \<le> length ls. card (vars (ls ! i)) \<le> 1"
  shows "total_degree (poly_subst_list ls p) \<le>
                length ls * (\<Sum>t \<le> length ls. degree p t * total_degree (ls !\<^sub>0 t))"
proof -
  from assms have asm: "\<And>i. i \<in> set ls \<Longrightarrow> card (vars i) \<le> 1"
    by (metis in_set_conv_nth less_or_eq_imp_le)

  have card0: "card (vars (poly_subst_list ls p)) \<le> length ls"
    apply (rule le_trans[OF card_mono[OF _ vars_poly_subst_list]], simp add: vars_finite)
    apply (rule le_trans[OF card_UN_le], simp)
    apply (rule le_trans[OF sum_bounded_above[OF asm]])
    by (auto simp add: card_length)

  have "sum (degree (poly_subst_list ls p)) (vars (poly_subst_list ls p))
        \<le> sum (\<lambda>v. \<Sum>t \<le> length ls. degree p t * degree (ls !\<^sub>0 t) v) (vars (poly_subst_list ls p))"
    apply (rule sum_mono)
    using degree_poly_subst_list' by auto
  also have "... = (\<Sum>t \<le> length ls. degree p t * sum (degree (ls !\<^sub>0 t)) (vars (poly_subst_list ls p)))"
    apply (subst sum.swap)
    by (subst sum_distrib_left, simp)
  also have "... \<le> (\<Sum>t \<le> length ls. degree p t * length ls * total_degree (ls !\<^sub>0 t))"
    apply (rule sum_mono, auto)
    apply (rule le_trans[OF sum_bounded_above, of _ _ "total_degree (ls !\<^sub>0 _)"])
    using degree_total_degree_bound vars_poly_subst_list card0 by auto

  finally show ?thesis
    apply simp
    apply (rule le_trans[OF total_degree_bound])
    apply (subst sum_distrib_left)
    by (smt (verit) ab_semigroup_mult_class.mult_ac(1) mult.commute sum.cong)
qed

end