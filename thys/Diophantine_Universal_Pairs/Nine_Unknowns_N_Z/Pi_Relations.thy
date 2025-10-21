theory Pi_Relations
  imports J3_Relations
begin

subsection \<open>The $\Pi$ polynomial\<close>

(* Auxiliary lemma *)
lemma finite_when: "finite {x. (f x when x = c) \<noteq> 0}"
  by auto

locale section5_variables
begin

definition \<S> :: "int mpoly" where "\<S> \<equiv> Var 4"
definition \<T> :: "int mpoly" where "\<T> \<equiv> Var 5"
definition \<R> :: "int mpoly" where "\<R> \<equiv> Var 6"
definition \<I> :: "int mpoly" where "\<I> \<equiv> Var 7"
definition \<Y> :: "int mpoly" where "\<Y> \<equiv> Var 8"
definition \<ZZ> :: "int mpoly" where "\<ZZ> \<equiv> Var 9"
definition \<J> :: "int mpoly" where "\<J> \<equiv> Var 10"
definition \<n> :: "int mpoly" where "\<n> \<equiv> Var 11"

definition \<U> ::"int mpoly" where "\<U> = \<S>^2 * (2*\<R>-1)"
definition \<V> ::"int mpoly" where "\<V> = \<T>^2 + \<S>^2 * \<n>"

lemmas defs = \<S>_def \<T>_def \<R>_def \<I>_def \<Y>_def \<ZZ>_def \<J>_def \<n>_def \<U>_def \<V>_def

end 

locale pi_relations = section5_variables + 
  fixes \<F> :: "int mpoly"
    and v :: nat
  assumes F_monom_over_v: "vars \<F> \<subseteq> {v}"
      and F_one: "coeff \<F> (Abs_poly_mapping (\<lambda>k. (degree \<F> v when k = v))) = 1"
begin

definition coeff_F where 
  "coeff_F d = coeff \<F> (Abs_poly_mapping (\<lambda>k. (d when k = v)))"
definition q :: nat where 
  "q = degree \<F> v"
definition G :: "int mpoly" where 
  "G = (\<Sum>i=0..q. of_int (coeff_F i) * (\<Y>-\<I>-\<T>^2)^i)"
definition G_sub :: "nat\<Rightarrow>int mpoly" where
  "G_sub j = (\<Sum>i=j..q. of_int (coeff_F i) * of_nat (i choose j) * (-\<I>-\<T>^2)^(i-j))"
definition H :: "int mpoly" where 
  "H = (\<Sum>j=0..q. G_sub j * \<ZZ>^j * \<J>^(q-j))"
definition \<Pi> :: "int mpoly" where 
  "\<Pi> = (\<Sum>j=0..q. G_sub j * (\<S>^2*\<n> + \<T>^2)^j * (\<S>^2*(2*\<R>-1))^(q-j))"

lemma eval_F:
  "insertion f \<F> = (\<Sum>d = 0..q. coeff_F d * (f v ^ d))"
proof -
  have aux1: " {a. lookup (mapping_of \<F>) a * (\<Prod>v. f v ^ lookup a v) \<noteq> 0}
    \<subseteq> {a \<in> range (\<lambda>d. Abs_poly_mapping (\<lambda>k. d when k = v)).
        lookup (mapping_of \<F>) a * (\<Prod>v. f v ^ lookup a v) \<noteq> 0}"
  proof -
    have "lookup (mapping_of \<F>) a \<noteq> 0 \<Longrightarrow>
         (\<Prod>v. f v ^ lookup a v) \<noteq> 0 \<Longrightarrow>
         a \<in> range (\<lambda>d. Abs_poly_mapping (\<lambda>k. d when k = v))" for a 
    proof -
      assume "lookup (mapping_of \<F>) a \<noteq> 0"
      hence "a \<in> keys (mapping_of \<F>)"
        unfolding keys.rep_eq
        by simp
      hence "\<And>v'. v \<noteq> v' \<Longrightarrow> lookup a v' = 0"
        subgoal for v'
        proof (cases "lookup a v' = 0")
          case True
          then show ?thesis by simp
        next
          case False
          assume "lookup a v' \<noteq> 0"
          hence "v' \<in> \<Union> (keys ` keys (mapping_of \<F>))"
            using `a \<in> keys (mapping_of \<F>)`
            unfolding keys.rep_eq
            apply simp
            apply (rule exI[where ?x=a])
            by simp
          hence 0: "v' = v"
            using F_monom_over_v vars_def
            by auto
          assume 1: "v \<noteq> v'"
          from 0 and 1 show ?thesis by simp
        qed
        done
      hence "a = Abs_poly_mapping (\<lambda>k. (lookup a v) when k = v)"
        apply (subst lookup_inverse[symmetric])
        apply (rule arg_cong[where ?f=Abs_poly_mapping])
        by (metis (mono_tags, opaque_lifting) "when"(1) "when"(2))
      thus "a \<in> range (\<lambda>d. Abs_poly_mapping (\<lambda>k. d when k = v))"
        by simp
    qed
    thus ?thesis by auto
  qed

  have aux2: "lookup (mapping_of \<F>) (Abs_poly_mapping (\<lambda>k. d when k = v)) \<noteq> 0 \<Longrightarrow>
    (\<Prod>va. f va ^ lookup (Abs_poly_mapping (\<lambda>k. d when k = v)) va) \<noteq> 0 \<Longrightarrow> d \<in> {0..q}" for d
  proof - 
    assume "lookup (mapping_of \<F>) (Abs_poly_mapping (\<lambda>k. d when k = v)) \<noteq> 0"
    thus "d \<in> {0..q}"
      unfolding q_def degree.rep_eq keys.rep_eq
      apply (subst atLeastAtMost_iff)
      apply simp
      apply (rule Max_ge)
      subgoal by simp
      apply (rule insertI2)
      apply (rule image_eqI[where ?x="Abs_poly_mapping (\<lambda>k. d when k = v)"])
      subgoal
        apply (subst lookup_Abs_poly_mapping)
        subgoal using finite_when[where ?f="\<lambda>_. d"] by simp
        by auto
      by simp
  qed

  have aux3: "x \<le> q \<Longrightarrow> y \<le> q \<Longrightarrow>
    Abs_poly_mapping (\<lambda>k. x when k = v) = Abs_poly_mapping (\<lambda>k. y when k = v) \<Longrightarrow> x = y" for x y
    proof -
      assume "Abs_poly_mapping (\<lambda>k. x when k = v) = Abs_poly_mapping (\<lambda>k. y when k = v)"
      hence 0: "(\<lambda>k. x when k = v) = (\<lambda>k. y when k = v)"
        apply (subst Abs_poly_mapping_inject[symmetric])
        subgoal
          apply (rule CollectI)
          using finite_when[where ?f="\<lambda>_. x"] by simp
        subgoal
          apply (rule CollectI)
          using finite_when[where ?f="\<lambda>_. y"] by simp
        by simp
      have "(x when v = v) = (y when v = v)"
        by (rule fun_cong[OF 0, where ?x=v])
      thus ?thesis
        by simp
    qed

  have aux4: "lookup (mapping_of \<F>) (Abs_poly_mapping (\<lambda>k. d when k = v)) \<noteq> 0 \<Longrightarrow>
    (\<Prod>va. f va ^ lookup (Abs_poly_mapping (\<lambda>k. d when k = v)) va) \<noteq> 0 \<Longrightarrow>
    Abs_poly_mapping (\<lambda>k. d when k = v) \<in> (\<lambda>d. Abs_poly_mapping (\<lambda>k. d when k = v)) ` {0..q}" for d
    apply (rule image_eqI[where ?x=d, OF refl])
    using aux2 by simp

  have "insertion f \<F> = (\<Sum>m\<in>{a. lookup (mapping_of \<F>) a * (\<Prod>v. f v ^ lookup a v) \<noteq> 0}.
       lookup (mapping_of \<F>) m * (\<Prod>v. f v ^ lookup m v))"
    unfolding insertion.rep_eq insertion_aux.rep_eq insertion_fun_def
    unfolding Sum_any.expand_set
    by simp
  also have "... =
    (\<Sum>m\<in>{a \<in> range (\<lambda>d. Abs_poly_mapping (\<lambda>k. d when k = v)).
          lookup (mapping_of \<F>) a * (\<Prod>v. f v ^ lookup a v) \<noteq> 0}.
      lookup (mapping_of \<F>) m * (\<Prod>v. f v ^ lookup m v))"
    apply (rule sum.mono_neutral_right[symmetric])
    subgoal by auto
    subgoal using aux1 by auto
    subgoal by auto
    done
  also have "... =
    (\<Sum>m\<in>{a \<in> (\<lambda>d. Abs_poly_mapping (\<lambda>k. d when k = v)) ` {0..q}.
          lookup (mapping_of \<F>) a * (\<Prod>v. f v ^ lookup a v) \<noteq> 0}.
      lookup (mapping_of \<F>) m * (\<Prod>v. f v ^ lookup m v))"
    apply (rule arg_cong[where ?f="sum _"])
    apply standard
    subgoal using aux4 by auto
    subgoal by auto
    done
  also have "... =
    (\<Sum>m\<in>(\<lambda>d. Abs_poly_mapping (\<lambda>k. d when k = v)) ` {0..q}.
      lookup (mapping_of \<F>) m * (\<Prod>v. f v ^ lookup m v))"
    apply (rule sum.mono_neutral_right[symmetric])
    by auto
  also have "... =
    sum
      ((\<lambda>m. lookup (mapping_of \<F>) m *
       (\<Prod>v. f v ^ lookup m v)) \<circ> (\<lambda>d. Abs_poly_mapping (\<lambda>k. d when k = v)))
      {0..q}"
    apply (rule sum.reindex) unfolding inj_on_def using aux3 by auto
  also have "... =
    (\<Sum>d\<in>{0..q}. lookup (mapping_of \<F>) (Abs_poly_mapping (\<lambda>k. d when k = v)) *
      (\<Prod>va. f va ^ lookup (Abs_poly_mapping (\<lambda>k. d when k = v)) va))"
    by simp
  finally show ?thesis
    unfolding coeff_F_def coeff_def
    apply simp
    apply (rule arg_cong[where ?f="\<lambda>f. (\<Sum>d = 0..q. _ d * f d)"])
    apply (rule ext)
    subgoal for d
      apply (subst lookup_Abs_poly_mapping)
      subgoal using finite_when[where ?f="\<lambda>_. d"] by simp
    proof (cases d)
      case 0
      then show "(\<Prod>va. f va ^ (d when va = v)) = f v ^ d"
        apply (subst `d = 0`)
        by simp
    next
      case (Suc nat)
      then show "(\<Prod>va. f va ^ (d when va = v)) = f v ^ d"
        apply (subst pow_when)
        by simp_all
    qed
    done
qed

(* Auxiliary lemma *)
lemma triangular_sum: "(\<Sum>k=0..(n::nat). (\<Sum>j=0..k. f j k)) = (\<Sum>j=0..(n::nat). (\<Sum>k=j..n. f j k))"
proof -
  have 0: "k\<in>{0..n} \<Longrightarrow> (\<Sum>j=0..k. f j k) = (\<Sum>j=0..n. (if j\<le>k then f j k else 0))" for k
  proof -
    assume k_prop: "k\<in>{0..n}"
    hence "(\<Sum>j=0..k. f j k) = (\<Sum>j=0..k. f j k) + (\<Sum>j=(k+1)..n. 0)" by simp
    also have "... = (\<Sum>j=0..k. (if j\<le>k then f j k else 0)) + (\<Sum>j=(k+1)..n. (if j\<le>k then f j k else 0))"
      by simp
    also have "... = (\<Sum>j=0..n. (if j\<le>k then f j k else 0))"
      using sum.union_disjoint[of "{0..k}" "{(k+1)..n}"]
      by (smt (verit) atLeastAtMost_iff k_prop le_iff_add sum.ub_add_nat zero_order(1))
    finally show ?thesis by blast
  qed
  have 1: "j\<in>{0..n} \<Longrightarrow> (\<Sum>k=j..n. f j k) = (\<Sum>k=0..n. (if j\<le>k then f j k else 0))" for j
  proof -
    assume j_prop: "j\<in>{0..n}"
    hence "(\<Sum>k=j..n. f j k) = (\<Sum>k<j. 0) + (\<Sum>k=j..n. f j k)" by simp
    also have "... = (\<Sum>k<j. (if j\<le>k then f j k else 0)) + (\<Sum>k=j..n. (if j\<le>k then f j k else 0))"
      by simp
    also have "... = (\<Sum>k=0..n. (if j\<le>k then f j k else 0))"
      using sum.union_disjoint[of "{0..<j}" "{j..n}"]
      by (smt (verit, best) atLeast0LessThan atLeastAtMost_iff finite_atLeastAtMost finite_atLeastLessThan ivl_disj_int_two(7) ivl_disj_un_two(7) j_prop)
    finally show ?thesis by blast
  qed
  hence "(\<Sum>k=0..(n::nat). (\<Sum>j=0..k. f j k)) = (\<Sum>k=0..n. (\<Sum>j=0..n. (if j\<le>k then f j k else 0)))"
    using 0 by simp
  also have "... = (\<Sum>j=0..n. (\<Sum>k=0..n. (if j\<le>k then f j k else 0)))" using sum.swap by fast
  finally show ?thesis using 1 by simp
qed


lemma G_expr:
  "G = (\<Sum>j=0..q. \<Y>^j * (\<Sum>i=j..q. of_int (coeff_F i) * of_nat (i choose j) * (-\<I>-\<T>^2)^(i-j)))"
proof -
  have "\<Y>-\<I>-\<T>^2 = \<Y> + (-\<I>-\<T>^2)" by simp
  hence "(\<Y>-\<I>-\<T>^2)^i = (\<Sum>j\<le>i. of_nat (i choose j) * \<Y>^j * (-\<I>-\<T>^2)^(i-j))" for i
    using binomial_ring[of \<Y> "-\<I>-\<T>^2" i] by presburger
  hence "G = (\<Sum>i=0..q. of_int (coeff_F i) * (\<Sum>j\<le>i. of_nat (i choose j) * \<Y>^j * (-\<I>-\<T>^2)^(i-j)))"
    using G_def by presburger
  also have "... = (\<Sum>i=0..q. (\<Sum>j=0..i. of_int (coeff_F i) * of_nat (i choose j) * \<Y>^j * (-\<I>-\<T>^2)^(i-j) ))"
    (is "(\<Sum>i=_.._. ?f i) = (\<Sum>i=_.._. ?g i)")
  proof (rule sum.cong[OF refl])
    fix i
    have "?f i = of_int (coeff_F i) * (\<Sum>j=0..i. of_nat (i choose j) * \<Y>^j * (-\<I>-\<T>^2)^(i-j) )"
      using atMost_atLeast0 by simp
    thus "?f i = ?g i"
      unfolding mult.assoc
      by (simp add: sum_distrib_left)
  qed
  also have "... = (\<Sum>j=0..q. (\<Sum>i=j..q. of_int (coeff_F i) * of_nat (i choose j) * \<Y>^j * (-\<I>-\<T>^2)^(i-j) ))"
    using triangular_sum[of "(\<lambda>j. (\<lambda>i. of_int (coeff_F i) * of_nat (i choose j) * \<Y>^j * (-\<I>-\<T>^2)^(i-j)))" q]
    by blast
  also have "... = (\<Sum>j=0..q. (\<Sum>i=j..q. \<Y>^j * of_int (coeff_F i) * of_nat (i choose j) * (-\<I>-\<T>^2)^(i-j) ))"
    apply (rule sum.cong[OF refl])
    apply (rule sum.cong[OF refl])
    by simp
  also have "... = (\<Sum>j=0..q. \<Y>^j * (\<Sum>i=j..q. of_int (coeff_F i) * of_nat (i choose j) * (-\<I>-\<T>^2)^(i-j) ))"
    (is "(\<Sum>j=_.._. ?f j) = (\<Sum>j=_.._. ?g j)")
    apply (rule sum.cong[OF refl])
    unfolding mult.assoc
    by (simp add: sum_distrib_left)
  finally show ?thesis by simp
qed


lemma G_in_Y: "G = (\<Sum>j=0..q. \<Y>^j * G_sub j)" 
  unfolding G_sub_def using G_expr by blast

lemma Gq_eq_1: "G_sub q = 1"
proof -
  have "coeff_F q = 1" using q_def F_one unfolding coeff_F_def by simp
  have "G_sub q = of_int (coeff_F q)" unfolding G_sub_def by simp
  also have "... = of_int 1" using q_def using \<open>coeff_F q = 1\<close> by presburger
  finally show ?thesis using Const\<^sub>0_one one_mpoly_def by simp
qed

lemma lemma_J_div_Z :
  "(\<Sum>j'=0..q. insertion f (G_sub j') * z^j' * j^(q-j')) = 0 \<Longrightarrow> j dvd z" for f z j
proof (cases "j=0 \<and> z=0")
  case True
  then show ?thesis by blast
next
  case False
  assume assm: "(\<Sum>j'=0..q. insertion f (G_sub j') * z^j' * j^(q-j')) = 0"
  define d where "d = gcd j z"
  have "d dvd j" using d_def by blast
  then obtain j0 where j0_def: "j = d * j0" by blast
  have "d dvd z" using d_def by blast
  then obtain z0 where z0_def: "z = d * z0" by blast
  have "gcd j z = d * gcd j0 z0" using d_def j0_def z0_def
    by (metis abs_gcd_int gcd_mult_distrib_int)
  hence coprime: "gcd j0 z0 = 1" using d_def using False by simp

  have dn0: "d\<noteq>0" using False d_def by simp

  have "j'\<le>q \<Longrightarrow> j' + (q-j') =q" for j' by simp
  hence nat_pow: "j'\<le>q \<Longrightarrow> d^j' * d^(q-j') = d^q" for j' using power_add by metis
  have "z^j' * j^(q-j') = d^j' * z0^j' * d^(q-j') * j0^(q-j')" for j'
    using j0_def z0_def by (simp add: power_mult_distrib)
  hence "j'\<le>q \<Longrightarrow> z^j' * j^(q-j') =  d^q * z0^j' * j0^(q-j')" for j'
    using power_add nat_pow by simp
  hence "0 = (\<Sum>j'=0..q. insertion f (G_sub j') * d^q * z0^j' * j0^(q-j'))"
    using assm
    by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) atLeastAtMost_iff sum.cong)
  also have "... = (\<Sum>j'=0..q. d^q * insertion f (G_sub j') * z0^j' * j0^(q-j'))"
    using mult.commute by (metis (no_types, opaque_lifting))
  also have "... = d^q * (\<Sum>j'=0..q. insertion f (G_sub j') * z0^j' * j0^(q-j'))"
    using sum_distrib_left[of "d^q" "(\<lambda>j'. insertion f (G_sub j') * z0^j' * j0^(q-j'))" "{0..q}"]
    by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) sum.cong)
  finally have pol_red_0: "(\<Sum>j'=0..q. insertion f (G_sub j') * z0^j' * j0^(q-j')) = 0"
    using dn0 by simp

  have inser_Gq_1: "insertion f (G_sub q) = 1" using Gq_eq_1 by simp
  have j0_pow: "j'<q \<Longrightarrow> j0^(q-j') = j0^(q-j'-1) * j0" for j'
    by (metis power_minus_mult zero_less_diff)
  have "(\<Sum>j'=0..q. insertion f (G_sub j') * z0^j' * j0^(q-j'))
        = (\<Sum>j'=0..<q. insertion f (G_sub j') * z0^j' * j0^(q-j')) + insertion f (G_sub q) * z0^q * j0^(q-q)"
    by (simp add: sum.last_plus)
  also have "... = (\<Sum>j'=0..<q. insertion f (G_sub j') * z0^j' * j0^(q-j')) + z0^q"
    using inser_Gq_1 by simp
  also have "... = (\<Sum>j'=0..<q. insertion f (G_sub j') * z0^j' * j0^(q-j'-1)*j0) + z0^q"
    using j0_pow sum.cong by (simp add: ab_semigroup_mult_class.mult_ac(1))
  also have "... = (\<Sum>j'=0..<q. insertion f (G_sub j') * z0^j' * j0^(q-j'-1)) * j0 + z0^q"
    using sum_distrib_right[of _ _ "j0"] by metis
  finally have "z0^q = -(\<Sum>j'=0..<q. insertion f (G_sub j') * z0^j' * j0^(q-j'-1)) * j0"
    using pol_red_0 by simp
  hence "j0 dvd z0^q" by simp
  hence "j0 dvd z0" using coprime
    by (metis coprime_dvd_mult_left_iff coprime_dvd_mult_right_iff coprime_power_right_iff is_unit_gcd one_dvd)
  thus "j dvd z" using j0_def z0_def by simp
qed

lemma lemma_pos: 
  assumes "(\<Sum>j'=0..q. insertion f (G_sub j') * z^j' * j^(q-j')) = 0"
          "j\<noteq>0" "z = z' * j"
  shows "insertion (\<lambda>_. z' - f 7 - (f 5)^2) \<F> = 0"
proof -
  have "z^j' = z'^j' * j^j'" for j' using power_mult_distrib[of "z'" "j" "j'"] assms by blast
  hence 0: "0 = (\<Sum>j'=0..q. insertion f (G_sub j') * z'^j' * j^j' * j^(q-j'))" using assms
    by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) sum.cong)
  also have "... = (\<Sum>j'=0..q. insertion f (G_sub j') * z'^j' * j^(j'+(q-j')))"
    using power_add[of "j"] by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1))
  also have "... = (\<Sum>j'=0..q. insertion f (G_sub j') * z'^j' * j^q)" by simp
  also have "... = (\<Sum>j'=0..q. insertion f (G_sub j') * z'^j') * j^q"
    using sum_distrib_right[of _ _ "j^q"] by metis
  finally have G_is_0: "(\<Sum>j'=0..q. insertion f (G_sub j') * z'^j') = 0" using assms by simp

  define f' where "f' = (\<lambda>x. f x)(8:=z')" (* variable 8 is Y *)
  hence "insertion f' \<Y> = z'"
    by (simp add: \<Y>_def)
  hence ins_f'_Y: "insertion f' (\<Y>^j') = z'^j'" for j'::nat using insertion_pow by blast
  have ins_f'_Gsub: "insertion f' (G_sub j') = insertion f (G_sub j')" for j'
  (* Basically f and f' only differ on Y, and G_sub doesn't contain Y *)
  (* A better proof could be done with lemma insertion_irrelevant_vars *)
  proof (rule insertion_irrelevant_vars)
    fix v
    assume H: "v \<in> vars (G_sub j')"
    have "vars (G_sub j') \<subseteq> vars \<I> \<union> vars \<T>"
      unfolding G_sub_def
      apply (rule subset_trans[OF vars_setsum])
      subgoal by simp
      apply (rule union_subset)
      subgoal for x
        apply (rule subset_trans[OF vars_mult])
        apply (rule Un_least)
         apply (rule subset_trans[OF vars_mult])
         apply (subst of_int_Const)
         apply (subst of_nat_Const)
        using vars_Const
        subgoal by simp
        apply (rule subset_trans[OF vars_pow])
        apply (subst diff_conv_add_uminus)
        apply (rule subset_trans[OF vars_add])
        apply (rule Un_mono)
        using vars_neg
        subgoal by auto
        apply (subst vars_neg)
        apply (subst power2_eq_square)
        apply (rule subset_trans[OF vars_mult])
        by simp
      done
    also have "... \<subseteq> {5, 7}"
      unfolding defs
      unfolding MPoly_Type.Var.abs_eq[symmetric]
      by simp
    finally have "v \<noteq> 8"
      using H
      by auto
    thus "f' v = f v"
      unfolding f'_def
      by auto
  qed

  have "(\<Sum>j'=0..q. insertion f' (G_sub j') * insertion f' (\<Y>^j')) = 0"
    using ins_f'_Y ins_f'_Gsub G_is_0 by presburger
  hence "(\<Sum>j'=0..q. insertion f' (G_sub j' * \<Y>^j')) = 0"
    using insertion_mult by (metis (no_types, lifting) sum.cong)
  hence "insertion f' (\<Sum>j'=0..q. G_sub j' * \<Y>^j') = 0" using insertion_sum[of "{0..q}" "f'"] by simp
  hence "insertion f' G = 0" using G_in_Y mult.commute
    by (metis (no_types, lifting) sum.cong)

  hence "(\<Sum>i = 0..q. insertion f' (of_int (coeff_F i) * (\<Y> - \<I> - \<T>\<^sup>2) ^ i)) = 0"
    unfolding G_def using insertion_sum[of "{0..q}" "f'"] by simp 
  hence "(\<Sum>i = 0..q. coeff_F i * insertion f' ((\<Y> - \<I> - \<T>\<^sup>2) ^ i)) = 0"
    by simp
  hence 1: "(\<Sum>i = 0..q. coeff_F i * (insertion f' (\<Y> - \<I> - \<T>\<^sup>2)) ^ i) = 0"
    using insertion_pow[of "f'"] by simp
  
  have "insertion f' (\<Y> - \<I> - \<T>\<^sup>2) = z' - f 7 - (f 5)^2"
  proof -
    have "insertion f' (\<Y> - \<I> - \<T>\<^sup>2) = insertion f' \<Y> + insertion f' (-\<I>-\<T>*\<T>)"
      using insertion_add[of "f'" \<Y> "-\<I>-\<T>*\<T>"] power2_eq_square[of \<T>] add.assoc
      by (metis ab_group_add_class.ab_diff_conv_add_uminus)
    also have "... = insertion f' \<Y> - insertion f' \<I> - insertion f' (\<T>*\<T>)"
      by simp
    also have "... = insertion f' \<Y> - insertion f' \<I> - (insertion f' \<T>)^2"
      using insertion_mult[of "f'" \<T> \<T>] power2_eq_square by metis
    also have "... = f' 8 - f' 7 - (f' 5)^2"
      unfolding \<Y>_def \<I>_def \<T>_def by simp
    finally show ?thesis using f'_def by simp
  qed

  hence "(\<Sum>i = 0..q. coeff_F i * (z' - f 7 - (f 5)^2) ^ i) = 0" using 1 by simp
  thus "insertion (\<lambda>_. z' - f 7 - (f 5)^2) \<F> = 0"
    using q_def eval_F
    by simp
qed

lemma \<Pi>_encodes_correctly:
  fixes S T R I :: int
  assumes "S \<noteq> 0" 
          "(\<forall>x. insertion (\<lambda>_. x) \<F> = 0 \<longrightarrow> x > -I)"
      and "S dvd T"
          "R > 0"
          "insertion (\<lambda>_. y) \<F> = 0"
  defines "\<phi> n \<equiv> (\<lambda>_. 0)(4:= S, 5:=T, 6:=R, 7:=I, 11:=int n)"
  shows "\<exists>n :: nat. insertion (\<phi> n) \<Pi> = 0 \<and> n = (2*R-1)*(y + I + T^2) - (T div S) ^ 2"
proof -
  obtain TdS where TdS_def: "T = TdS * S" using \<open>S dvd T\<close> by force
  define n\<^sub>i where "n\<^sub>i = (2*R-1)*(y+I+T^2) - TdS^2"
  have nBe0: "n\<^sub>i\<ge>0"
  proof -
    have 0: "(2*R-1) \<ge> 1" using assms by simp
    have "y > -I" using assms by blast
    hence 1: "y+I+T^2 > T^2" by linarith
    have "T^2 \<ge>0" by simp
    hence "y+I+T^2 > 0" using 1 by linarith
    hence "(2*R-1)*(y+I+T^2) \<ge> y+I+T^2" using 0 by simp
    hence 2: "(2*R-1)*(y+I+T^2) \<ge> T^2" using 1 by simp

    have 3: "T^2 = TdS^2 * S^2" unfolding TdS_def using power_mult_distrib by blast
    have "S^2 > 0" using assms by simp
    hence 4: "S^2 \<ge> 1" by linarith
    have "TdS^2 \<ge> 0" by simp
    hence "TdS^2 * S^2 \<ge> TdS^2" using 4 by (metis mult_cancel_left1 mult_left_mono)
    hence "T^2 \<ge> TdS^2" using 3 by simp

    thus ?thesis unfolding n\<^sub>i_def using 2 by simp
  qed
  then obtain n where n_def: "int n = n\<^sub>i" using nonneg_int_cases by metis

  define f::"nat\<Rightarrow>int" where "f = (\<lambda>_. 0) (4 := S, 5 := T, 6 := R, 7 := I, 11 := int n)"
  have 0: "insertion f \<Pi>
  = (\<Sum>j = 0..q. insertion f (G_sub j * (\<S>\<^sup>2 * \<n> + \<T>\<^sup>2) ^ j * (\<S>\<^sup>2 * (2 * \<R> - 1)) ^ (q - j)))"
    unfolding \<Pi>_def using insertion_sum by blast
  have 1: "insertion f (G_sub j * (\<S>\<^sup>2 * \<n> + \<T>\<^sup>2) ^ j * (\<S>\<^sup>2 * (2 * \<R> - 1)) ^ (q - j))
       = insertion f (G_sub j) * (S^2 * n + T^2)^j * (S^2 * (2*R- 1)) ^ (q - j)" for j
  proof -
    have 0: "insertion f (G_sub j * (\<S>\<^sup>2 * \<n> + \<T>\<^sup>2) ^ j * (\<S>\<^sup>2 * (2 * \<R> - 1)) ^ (q - j))
       = insertion f (G_sub j) * insertion f ((\<S>\<^sup>2 * \<n> + \<T>\<^sup>2) ^ j) * insertion f ((\<S>\<^sup>2 * (2 * \<R> - 1)) ^ (q - j))"
      using insertion_mult[of f] by simp
    have 1: "insertion f ((\<S>\<^sup>2 * \<n> + \<T>\<^sup>2) ^ j) * insertion f ((\<S>\<^sup>2 * (2 * \<R> - 1)) ^ (q - j))
        = (insertion f (\<S>\<^sup>2 * \<n> + \<T>\<^sup>2)) ^ j * (insertion f (\<S>\<^sup>2 * (2 * \<R> - 1))) ^ (q - j)"
      using insertion_pow by metis
    have "insertion f (\<S>\<^sup>2 * \<n> + \<T>\<^sup>2) = insertion f (\<S>*\<S>) * insertion f \<n> + insertion f (\<T>*\<T>)"
      using insertion_add[of f] insertion_mult[of f] power2_eq_square by metis
    also have "... = (insertion f \<S>)^2 * insertion f \<n> + (insertion f \<T>)^2"
      using insertion_mult[of f] power2_eq_square by metis
    also have "... = S^2 * n + T^2"
      unfolding \<S>_def \<n>_def \<T>_def using f_def by simp
    finally have 2: "insertion f (\<S>\<^sup>2 * \<n> + \<T>\<^sup>2) = S^2 * n + T^2" by simp
    have "insertion f (\<S>\<^sup>2 * (2 * \<R> - 1)) = (insertion f \<S>)^2 * insertion f (2 * \<R> - 1)"
      using insertion_mult[of f] power2_eq_square by metis
    also have "... = (insertion f \<S>)^2 * (insertion f (2*\<R>) - insertion f 1)"
      by simp
    also have "... = (insertion f \<S>)^2 * (2 * insertion f \<R> - 1)"
      by (simp add: insertion_mult[of f])
    also have "... = S^2 * (2*R-1)"
      unfolding \<S>_def \<R>_def using f_def by simp
    finally have 3: "insertion f (\<S>\<^sup>2 * (2 * \<R> - 1)) = S^2 * (2*R-1)" by simp
    show ?thesis using 0 1 2 3 by simp
  qed
  have 2: "j\<le>q \<Longrightarrow> (S^2 * n + T^2)^j * (S^2 * (2*R- 1)) ^ (q - j)
      = (y+I+T^2)^j * (S^2 * (2*R- 1)) ^ q" for j
  proof -
    assume jLeq: "j\<le>q"
    have "S^2 * n + T^2 = S^2*(2*R-1)*(y+I+T^2) - S^2 * TdS^2 + T^2" unfolding n_def n\<^sub>i_def
      by (simp add: right_diff_distrib)
    also have "... = S^2*(2*R-1)*(y+I+T^2) - (S* TdS)^2 + T^2" using power_mult_distrib by metis
    also have "... = S^2*(2*R-1)*(y+I+T^2)" using TdS_def by (simp add: mult.commute)
    finally have "(S^2 * n + T^2)^j * (S^2 * (2*R- 1)) ^ (q - j)
      = (S^2*(2*R-1)*(y+I+T^2))^j * (S^2 * (2*R- 1)) ^ (q - j)" by simp
    also have "... = (y+I+T^2)^j * (S^2*(2*R-1))^j * (S^2 * (2*R- 1)) ^ (q - j)"
      using power_mult_distrib mult.commute by metis
    also have "... = (y+I+T^2)^j * (S^2 * (2*R- 1))^q" using power_add jLeq
      by (metis (no_types, lifting) add_diff_cancel_left' mult.assoc nat_le_iff_add)
    finally show ?thesis by simp
  qed           
  hence "insertion f \<Pi>
       = (\<Sum>j = 0..q. insertion f (G_sub j) * (S^2 * n + T^2)^j * (S^2 * (2*R- 1)) ^ (q - j))"
    using 0 1 by presburger
  also have "... = (\<Sum>j = 0..q. insertion f (G_sub j) * (y+I+T^2)^j * (S^2 * (2*R- 1)) ^ q)"
    using 2 by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) atLeastAtMost_iff sum.cong)
  finally have inser_expr_1: "insertion f \<Pi> =
              (\<Sum>j = 0..q. insertion f (G_sub j) * (y+I+T^2)^j) * (S^2 * (2*R- 1)) ^ q"
    using sum_distrib_right[of _ _ "(S^2 * (2*R- 1)) ^ q"] by metis

  have inser_G_sub:  "insertion f (G_sub j) = (\<Sum>i=j..q. coeff_F i * of_nat (i choose j) * (-I-T^2)^(i-j))"
    for j
  proof -
    have "insertion f (G_sub j)
        = insertion f (\<Sum>i=j..q. of_int (coeff_F i) * of_nat (i choose j) * (-\<I>-\<T>^2)^(i-j))"
      unfolding G_sub_def by blast 
    also have "... = (\<Sum>i=j..q. insertion f (of_int (coeff_F i) * of_nat (i choose j) * (-\<I>-\<T>^2)^(i-j)))"
      using insertion_sum by blast
    also have "... = (\<Sum>i=j..q. (coeff_F i) * of_nat (i choose j) * insertion f ((-\<I>-\<T>^2)^(i-j)))"
    proof -
      have 1: "insertion f (of_int (coeff_F i) * of_nat (i choose j) * (-\<I>-\<T>^2)^(i-j))
         = (coeff_F i) * insertion f (of_nat (i choose j) * (-\<I>-\<T>^2)^(i-j))" for i
        using mult.assoc insertion_of_int_times by metis
      moreover have "(coeff_F i) * insertion f (of_nat (i choose j) * (-\<I>-\<T>^2)^(i-j))
         = (coeff_F i) * (i choose j) * insertion f ((-\<I>-\<T>^2)^(i-j))" for i
          using insertion_mult 
          by (smt (verit) ab_semigroup_mult_class.mult_ac(1) insertion_of_int_times mult.commute 
              of_int_of_nat_eq) 
      ultimately show ?thesis by presburger
    qed
    also have "... = (\<Sum>i=j..q. (coeff_F i) * of_nat (i choose j) * (insertion f (-\<I>-\<T>^2))^(i-j))"
    proof -
      have "insertion f ((-\<I>-\<T>^2)^(i-j)) = (insertion f (-\<I>-\<T>^2))^(i-j)" for i
        using insertion_pow by blast
      thus ?thesis by simp
    qed
    also have "... = (\<Sum>i=j..q. (coeff_F i) * of_nat (i choose j) * (-insertion f \<I> - (insertion f \<T>) ^2 )^(i-j))"
    proof -
      have "insertion f (-\<I>-\<T>^2) = -insertion f (\<I> + \<T>^2)" by simp
      also have "... = -insertion f \<I> - (insertion f (\<T>^2))" by simp
      finally have "insertion f (-\<I>-\<T>^2) = -insertion f \<I> - (insertion f \<T>) ^2"
        using insertion_mult[of "f" \<T> \<T>] power2_eq_square by metis
      thus ?thesis by simp
    qed
    also have "... = (\<Sum>i=j..q. coeff_F i * of_nat (i choose j) * (-I-T^2)^(i-j))"
      unfolding defs using f_def by simp
    finally show ?thesis by blast
  qed

  hence "(\<Sum>j = 0..q. insertion f (G_sub j) * (y+I+T^2)^j)
      = (\<Sum>j = 0..q. (\<Sum>i=j..q. coeff_F i * of_nat (i choose j) * (-I-T^2)^(i-j)) * (y+I+T^2)^j)"
    using inser_G_sub by presburger
  also have "... = (\<Sum>j = 0..q. (\<Sum>i=j..q. coeff_F i * of_nat (i choose j) * (-I-T^2)^(i-j) * (y+I+T^2)^j))"
  proof -
    have "(\<Sum>i=j..q. coeff_F i * of_nat (i choose j) * (-I-T^2)^(i-j)) * (y+I+T^2)^j
         = (\<Sum>i=j..q. coeff_F i * of_nat (i choose j) * (-I-T^2)^(i-j) * (y+I+T^2)^j)" for j
      using sum_distrib_right by blast
    thus ?thesis by presburger
  qed
  also have "... = (\<Sum>i = 0..q. (\<Sum>j=0..i. coeff_F i * of_nat (i choose j) * (-I-T^2)^(i-j) * (y+I+T^2)^j))"
    using triangular_sum[of "(\<lambda>j. (\<lambda>i. coeff_F i * of_nat (i choose j) * (-I-T^2)^(i-j) * (y+I+T^2)^j))" q]
    by argo
  also have "... = (\<Sum>i = 0..q. coeff_F i * (\<Sum>j=0..i. of_nat (i choose j) * (-I-T^2)^(i-j) * (y+I+T^2)^j))"
  proof -
    have "(\<Sum>j=0..i. coeff_F i *  of_nat (i choose j) * (-I-T^2)^(i-j) * (y+I+T^2)^j)
         = coeff_F i * (\<Sum>j=0..i. of_nat (i choose j) * (-I-T^2)^(i-j) * (y+I+T^2)^j)" for i
      using sum_distrib_left[of "coeff_F i" "(\<lambda>j. of_nat (i choose j) * (-I-T^2)^(i-j) * (y+I+T^2)^j)" "{0..i}"]
      by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) sum.cong)
    thus ?thesis by presburger
  qed
  also have "... = (\<Sum>i = 0..q. coeff_F i * y^i)"
  proof -
    have "(\<Sum>j=0..i. of_nat (i choose j) * (-I-T^2)^(i-j) * (y+I+T^2)^j) = y^i" for i
      using binomial_ring[of "y+I+T^2" "-I-T^2" i]
      by (smt (verit, best) ab_semigroup_mult_class.mult_ac(1) atLeast0AtMost mult.commute sum.cong)
    thus ?thesis by simp
  qed
  also have "... = insertion (\<lambda>_. y) \<F>" using q_def eval_F by metis
  also have "... = 0" using assms by blast
  finally have "insertion f \<Pi> = 0" using inser_expr_1 by presburger

  hence "insertion (\<phi> n) \<Pi> = 0" 
    unfolding f_def \<phi>_def by auto

  moreover have "n = (2*R-1)*(y + I + T^2) - (T div S) ^ 2" 
    unfolding n_def n\<^sub>i_def TdS_def using \<open>S \<noteq> 0\<close> by auto

  ultimately show "?thesis" by auto
qed



lemma \<Pi>_encodes_correctly_2:
  fixes S T R I :: int
  assumes "S \<noteq> 0" 
          "(\<forall>x. insertion (\<lambda>_. x) \<F> = 0 \<longrightarrow> x > -I)"
  defines "\<phi> n \<equiv> (\<lambda>_. 0)(4:= S, 5:=T, 6:=R, 7:=I, 11:=int n)"
  assumes "\<exists>n :: nat. insertion (\<phi> n) \<Pi> = 0"
  shows "S dvd T \<and> R > 0 \<and> (\<exists>x::int. (insertion (\<lambda>_. x) \<F>) = 0)"
proof - 
  from assms obtain n where 
    prop_2_n: "insertion ((\<lambda>_. 0) (4 := S, 5:=T, 6:=R, 7:= I, 11:= int n)) \<Pi> = 0"
    unfolding \<phi>_def by auto
  define subst::"nat\<Rightarrow>int" where "subst = ((\<lambda>_. 0) (4 := S, 5 := T, 6 := R, 7 := I, 11 := n))"
  define J::int where "J = S^2 * (2*R-1)"
  have "2*R-1 \<noteq> 0" by presburger
  hence Jnot0: "J\<noteq>0" unfolding J_def using assms by simp

  have "0 = insertion subst (\<Sum>j=0..q. G_sub j * (\<S>^2 * \<n> + \<T>^2)^j * (\<S>^2*(2*\<R>-1))^(q-j))"
    using prop_2_n unfolding \<Pi>_def[symmetric] subst_def by argo
  also have "... = (\<Sum>j=0..q. insertion subst (G_sub j * (\<S>^2 * \<n> + \<T>^2)^j * (\<S>^2*(2*\<R>-1))^(q-j)))"
    using insertion_sum by blast
  also have "... = (\<Sum>j=0..q. insertion subst (G_sub j) * insertion subst ((\<S>^2 * \<n> + \<T>^2)^j * (\<S>^2*(2*\<R>-1))^(q-j)))"
  proof -
    have "insertion subst (G_sub j * (\<S>^2 * \<n> + \<T>^2)^j * (\<S>^2*(2*\<R>-1))^(q-j))
          = insertion subst (G_sub j) * insertion subst ((\<S>^2 * \<n> + \<T>^2)^j * (\<S>^2*(2*\<R>-1))^(q-j))" for j
      using insertion_mult[of subst] by simp
    thus ?thesis by presburger
  qed
  also have "... = (\<Sum>j=0..q. insertion subst (G_sub j) * (S^2 * n + T^2)^j * (S^2*(2*R-1))^(q-j))"
  proof -
    have "insertion subst ((\<S>^2 * \<n> + \<T>^2)^j * (\<S>^2*(2*\<R>-1))^(q-j)) = (S^2 * n + T^2)^j * (S^2*(2*R-1))^(q-j)" for j
    proof -
    have 0: "insertion subst ((\<S>\<^sup>2 * \<n> + \<T>\<^sup>2) ^ j * (\<S>\<^sup>2 * (2 * \<R> - 1)) ^ (q - j))
       = insertion subst ((\<S>\<^sup>2 * \<n> + \<T>\<^sup>2) ^ j) * insertion subst ((\<S>\<^sup>2 * (2 * \<R> - 1)) ^ (q - j))"
      using insertion_mult[of subst] by simp
    have 1: "insertion subst ((\<S>\<^sup>2 * \<n> + \<T>\<^sup>2) ^ j) * insertion subst ((\<S>\<^sup>2 * (2 * \<R> - 1)) ^ (q - j))
        = (insertion subst (\<S>\<^sup>2 * \<n> + \<T>\<^sup>2)) ^ j * (insertion subst (\<S>\<^sup>2 * (2 * \<R> - 1))) ^ (q - j)"
      using insertion_pow by metis
    have "insertion subst (\<S>\<^sup>2 * \<n> + \<T>\<^sup>2) = insertion subst (\<S>*\<S>) * insertion subst \<n> + insertion subst (\<T>*\<T>)"
      using insertion_add[of subst] insertion_mult[of subst] power2_eq_square by metis
    also have "... = (insertion subst \<S>)^2 * insertion subst \<n> + (insertion subst \<T>)^2"
      using insertion_mult[of subst] power2_eq_square by metis
    also have "... = S^2 * n + T^2"
      unfolding \<S>_def \<n>_def \<T>_def using subst_def by simp
    finally have 2: "insertion subst (\<S>\<^sup>2 * \<n> + \<T>\<^sup>2) = S^2 * n + T^2" by simp
    have "insertion subst (\<S>\<^sup>2 * (2 * \<R> - 1)) = (insertion subst \<S>)^2 * insertion subst (2 * \<R> - 1)"
      using insertion_mult[of subst] power2_eq_square by metis
    also have "... = (insertion subst \<S>)^2 * (insertion subst (2*\<R>) - insertion subst 1)"
      by simp
    also have "... = (insertion subst \<S>)^2 * (2 * insertion subst \<R> - 1)"
      using insertion_of_int_times[of subst 2] by simp
    also have "... = S^2 * (2*R-1)"
      unfolding \<S>_def \<R>_def using subst_def by simp
    finally have 3: "insertion subst (\<S>\<^sup>2 * (2 * \<R> - 1)) = S^2 * (2*R-1)" by simp
      show ?thesis using 0 1 2 3 by argo
    qed
    thus ?thesis using sum.cong by (simp add: ab_semigroup_mult_class.mult_ac(1))
  qed
  finally have \<Pi>_eq_0: "(\<Sum>j=0..q. insertion subst (G_sub j) * (S^2 * n + T^2)^j * (S^2*(2*R-1))^(q-j)) = 0"
    by simp
  hence J_div_ST: "J dvd S^2 * n + T^2" using lemma_J_div_Z unfolding J_def by blast
  hence "S^2 dvd S^2 * n + T^2" unfolding J_def by fastforce
  hence "S^2 dvd (S^2*n + T^2) - S^2*n" by fastforce
  hence "S^2 dvd T^2" by simp
  hence S_dvd_T: "S dvd T" by simp

  obtain Z::int where Z_prop: "S^2 * n + T^2 = Z * J" using J_div_ST by fastforce
  hence "insertion (\<lambda>_. Z - subst 7 - (subst 5)^2) \<F> = 0"
    using \<Pi>_eq_0 Jnot0 lemma_pos[of subst "S^2*n+T^2" "J" "Z"]
    unfolding J_def by blast
  hence F_cancels: "insertion (\<lambda>_. Z - I - T^2) \<F> = 0"
    unfolding subst_def by simp
  hence "Z - I - T^2 > -I"
    using assms by blast           
  hence "Z > T^2" by simp
  hence "Z \<noteq> 0" by fastforce
  hence SnT_not_0: "S^2 * n + T^2 \<noteq> 0" using Z_prop Jnot0 by simp
  have Snt: "S^2 * n + T^2 \<ge> 0" using prop_2_n by simp
  hence SnT_B_0: "S^2 * n + T^2 > 0" using SnT_not_0 by linarith
  have "T^2 \<ge>0" by simp
  hence ZB0:"Z > 0" using \<open>Z > T^2\<close> by linarith
  hence "J\<le>0 \<Longrightarrow> False"
  proof -
    assume "J\<le>0"
    hence "J<0" using Jnot0 by simp
    hence "S^2 * n + T^2 < 0" using Z_prop ZB0 
      by (metis SnT_B_0 one_dvd plus_int_code(2) zdvd_not_zless zero_less_mult_pos zless_add1_eq)
    thus "False" using Snt by simp
  qed
  hence JB0:"J>0" by fastforce
  hence "S^2 * (2 * R- 1) > 0" unfolding J_def by blast
  hence "2 * R- 1 > 0"
    by (metis mult_eq_0_iff zero_eq_power2 zero_less_mult_pos zero_less_power2)
  hence "2*R > 0" by simp
  hence RB0: "R > 0" by simp
  thus "?thesis" using S_dvd_T RB0 F_cancels by blast
qed

end

end
