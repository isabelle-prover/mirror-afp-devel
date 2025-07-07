(*  Title:       Computational p-Adics: Product of All Prime-Order Finite Fields
    Author:      Jeremy Sylvestre <jeremy.sylvestre at ualberta.ca>, 2025
    Maintainer:  Jeremy Sylvestre <jeremy.sylvestre at ualberta.ca>
*)


theory Fin_Field_Product

imports
  Distinguished_Quotients
  pAdic_Product

begin

section \<open>
  Finite fields of prime order as quotients of the ring of integers of p-adic fields
\<close>

subsection \<open>The type\<close>

subsubsection \<open>
  The prime ideal as the distinguished ideal of the ring of adelic integers
\<close>

instantiation adelic_int ::
  (nontrivial_factorial_idom) comm_ring_1_with_distinguished_ideal
begin

definition distinguished_subset_adelic_int :: "'a adelic_int set"
  where distinguished_subset_adelic_int_def[simp]:
    "distinguished_subset_adelic_int \<equiv> \<P>\<^sub>\<forall>\<^sub>p"

instance
proof (standard, safe)
  show "(\<N> ::'a adelic_int set) = {} \<Longrightarrow> False"
    using global_p_depth_adelic_int.global_depth_set_0 by auto
next
  fix g h :: "'a adelic_int"
  assume "g \<in> \<N>" and "h \<in> \<N>"
  thus "g - h \<in> \<N>"
    using global_p_depth_adelic_int.global_depth_set_minus by auto
next
  fix r x :: "'a adelic_int"
  assume "x \<in> \<N>"
  thus "r * x \<in> \<N>"
    using global_p_depth_adelic_int.global_depth_set_ideal nonpos_global_depth_set_adelic_int
    by    fastforce
next
  define n where "n \<equiv> (1::'a adelic_int)"
  moreover assume "n \<in> \<N>"
  ultimately show False using global_p_depth_adelic_int.pos_global_depth_set_1 by force
qed

end (* instantiation *)

lemma distinguished_subset_adelic_int_inverse:
  "inverse x = 0" if "x \<in> \<P>\<^sub>\<forall>\<^sub>p"
  for x :: "'a::nontrivial_factorial_unique_euclidean_bezout adelic_int"
  using that global_p_depth_adelic_int.global_depth_setD adelic_int_inverse_eq0_iff by fastforce

subsubsection \<open>The finite field product type as a quotient\<close>

text \<open>Create type wrapper @{type coset_by_dist_sbgrp} over @{type adelic_int}.\<close>

typedef (overloaded) 'a adelic_int_quot =
  "UNIV :: 'a::nontrivial_factorial_idom adelic_int coset_by_dist_sbgrp set"
  ..

abbreviation
  "adelic_int_quot \<equiv> \<lambda>x. Abs_adelic_int_quot (distinguished_quotient_coset x)"
abbreviation "p_adic_prod_int_quot \<equiv> \<lambda>x. adelic_int_quot (Abs_adelic_int x)"

lemma adelic_int_quot_cases [case_names adelic_int_quot]:
  obtains y where "x = adelic_int_quot y"
proof (cases x)
  case (Abs_adelic_int_quot y) with that show thesis by (cases y) blast
qed

lemma Abs_adelic_int_quot_cases [case_names adelic_int_quot_Abs_adelic_int]:
  obtains z where "x = p_adic_prod_int_quot z" "z \<in> \<O>\<^sub>\<forall>\<^sub>p"
proof (cases x rule: adelic_int_quot_cases)
  case (adelic_int_quot y) with that show thesis by (cases y) blast
qed

lemmas  two_adelic_int_quot_cases   = adelic_int_quot_cases[case_product adelic_int_quot_cases]
  and   three_adelic_int_quot_cases =
    adelic_int_quot_cases[case_product adelic_int_quot_cases[case_product adelic_int_quot_cases]]

lemma abs_adelic_int_eq_iff:
  "adelic_int_quot x = adelic_int_quot y \<longleftrightarrow>
    y - x \<in> \<P>\<^sub>\<forall>\<^sub>p"
  using Abs_adelic_int_quot_inject distinguished_quotient_coset_eq_iff by force

lemma p_adic_prod_int_quot_eq_iff:
  "p_adic_prod_int_quot x = p_adic_prod_int_quot y \<longleftrightarrow>
    y - x \<in> \<P>\<^sub>\<forall>\<^sub>p"
  if "x \<in> \<O>\<^sub>\<forall>\<^sub>p" and "y \<in> \<O>\<^sub>\<forall>\<^sub>p"
  using that abs_adelic_int_eq_iff[of "Abs_adelic_int x" "Abs_adelic_int y"] Abs_adelic_int_inject
        minus_adelic_int_abs_eq[of y x] nonneg_global_depth_set_adelic_int_eq_projection[of 1]
        global_p_depth_p_adic_prod.global_depth_set_minus[of y 0 x]
        global_p_depth_p_adic_prod.global_depth_set_antimono[of 0 1]
  by    fastforce

subsubsection \<open>Algebraic instantiations\<close>

instantiation adelic_int_quot :: (nontrivial_factorial_idom) comm_ring_1
begin

definition "0 = Abs_adelic_int_quot 0"

lemma zero_adelic_int_quot_rep_eq: "Rep_adelic_int_quot 0 = 0"
  using Abs_adelic_int_quot_inverse by (simp add: zero_adelic_int_quot_def)

lemma zero_adelic_int_quot: "0 = adelic_int_quot 0"
  using zero_adelic_int_quot_def zero_coset_by_dist_sbgrp.abs_eq by simp

definition "1 \<equiv> Abs_adelic_int_quot 1"

lemma one_adelic_int_quot_rep_eq: "Rep_adelic_int_quot 1 = 1"
  using Abs_adelic_int_quot_inverse by (simp add: one_adelic_int_quot_def)

lemma one_adelic_int_quot: "1 = adelic_int_quot 1"
  using one_adelic_int_quot_def one_coset_by_dist_sbgrp.abs_eq by simp

definition "x + y = Abs_adelic_int_quot (Rep_adelic_int_quot x + Rep_adelic_int_quot y)"

lemma plus_adelic_int_quot_rep_eq:
  "Rep_adelic_int_quot (a + b) = Rep_adelic_int_quot a + Rep_adelic_int_quot b"
  using     Rep_adelic_int_quot Abs_adelic_int_quot_inverse
  unfolding plus_adelic_int_quot_def
  by        blast

lemma plus_adelic_int_quot_abs_eq:
  "Abs_adelic_int_quot x + Abs_adelic_int_quot y = Abs_adelic_int_quot (x + y)"
  using     Abs_adelic_int_quot_inverse[of x] Abs_adelic_int_quot_inverse[of y]
  unfolding plus_adelic_int_quot_def
  by        simp

lemma plus_adelic_int_quot: "adelic_int_quot x + adelic_int_quot y = adelic_int_quot (x + y)"
  using plus_adelic_int_quot_abs_eq plus_coset_by_dist_sbgrp.abs_eq by fastforce

definition "-x = Abs_adelic_int_quot (- Rep_adelic_int_quot x)"

lemma uminus_adelic_int_quot_rep_eq: "Rep_adelic_int_quot (- x) = - Rep_adelic_int_quot x"
  using     Rep_adelic_int_quot Abs_adelic_int_quot_inverse
  unfolding uminus_adelic_int_quot_def
  by        blast

lemma uminus_adelic_int_quot_abs_eq: "- Abs_adelic_int_quot x = Abs_adelic_int_quot (- x)"
  using Abs_adelic_int_quot_inverse[of x] unfolding uminus_adelic_int_quot_def by simp

lemma uminus_adelic_int_quot: "- adelic_int_quot x = adelic_int_quot (-x)"
  using uminus_adelic_int_quot_abs_eq uminus_coset_by_dist_sbgrp.abs_eq by fastforce

definition minus_adelic_int_quot ::
  "'a adelic_int_quot \<Rightarrow> 'a adelic_int_quot \<Rightarrow> 'a adelic_int_quot"
  where "minus_adelic_int_quot \<equiv> (\<lambda>x y. x + - y)"

lemma minus_adelic_int_quot_rep_eq:
  "Rep_adelic_int_quot (x - y) = Rep_adelic_int_quot x - Rep_adelic_int_quot y"
  using plus_adelic_int_quot_rep_eq uminus_adelic_int_quot_rep_eq
  by    (simp add: minus_adelic_int_quot_def)

lemma minus_adelic_int_quot_abs_eq:
  "Abs_adelic_int_quot x - Abs_adelic_int_quot y = Abs_adelic_int_quot (x - y)"
  by    (simp add:
          minus_adelic_int_quot_def uminus_adelic_int_quot_abs_eq
          plus_adelic_int_quot_abs_eq
        )

lemma minus_adelic_int_quot: "adelic_int_quot x - adelic_int_quot y = adelic_int_quot (x - y)"
  using minus_adelic_int_quot_abs_eq minus_coset_by_dist_sbgrp.abs_eq by fastforce

definition "x * y = Abs_adelic_int_quot (Rep_adelic_int_quot x * Rep_adelic_int_quot y)"

lemma times_adelic_int_quot_rep_eq:
  "Rep_adelic_int_quot (x * y) = Rep_adelic_int_quot x * Rep_adelic_int_quot y"
  using     Rep_adelic_int_quot Abs_adelic_int_quot_inverse
  unfolding times_adelic_int_quot_def
  by        blast

lemma times_adelic_int_quot_abs_eq:
  "Abs_adelic_int_quot x * Abs_adelic_int_quot y = Abs_adelic_int_quot (x * y)"
  using     Abs_adelic_int_quot_inverse[of x] Abs_adelic_int_quot_inverse[of y]
  unfolding times_adelic_int_quot_def
  by        simp

lemma times_adelic_int_quot: "adelic_int_quot x * adelic_int_quot y = adelic_int_quot (x * y)"
  using times_adelic_int_quot_abs_eq times_coset_by_dist_sbgrp.abs_eq by auto

instance
proof

  fix a b c :: "'a adelic_int_quot"

  show "a + b + c = a + (b + c)"
    by (cases a, cases b, cases c) (simp add: plus_adelic_int_quot_abs_eq add.assoc)
  show "a + b = b + a" by (cases a, cases b) (simp add: plus_adelic_int_quot_abs_eq add.commute)
  show "0 + a = a"
    using plus_adelic_int_quot_abs_eq[of 0] by (cases a, simp add: zero_adelic_int_quot_def)
  show "1 * a = a"
    using times_adelic_int_quot_abs_eq[of 1] by (cases a) (simp add: one_adelic_int_quot_def)

  show "- a + a = 0"
    by  (cases a)
        (simp add:
          uminus_adelic_int_quot_abs_eq plus_adelic_int_quot_abs_eq zero_adelic_int_quot_def
        )

  show "a - b = a + - b" by (simp add: minus_adelic_int_quot_def)

  show "a * b * c = a * (b * c)"
    by  (cases a, cases b, cases c)
        (simp add: times_adelic_int_quot_abs_eq mult.assoc)

  show "a * b = b * a" by (cases a, cases b) (simp add: times_adelic_int_quot_abs_eq mult.commute)

  show "(a + b) * c = a * c + b * c"
    by  (cases a, cases b, cases c)
        (simp add: plus_adelic_int_quot_abs_eq times_adelic_int_quot_abs_eq distrib_right)

  show "(0::'a adelic_int_quot) \<noteq> 1"
    using Abs_adelic_int_quot_inject[of "0::'a adelic_int coset_by_dist_sbgrp" 1]
    by    (simp add: zero_adelic_int_quot_def one_adelic_int_quot_def)

qed

end (* instantiation adelic_int_quot :: comm_ring *)

instantiation adelic_int_quot ::
  (nontrivial_factorial_unique_euclidean_bezout) "{divide_trivial, inverse}"
begin

lift_definition inverse_adelic_int_coset ::
  "'a adelic_int coset_by_dist_sbgrp \<Rightarrow> 'a adelic_int coset_by_dist_sbgrp"
  is inverse
  unfolding distinguished_subset_adelic_int_def
proof
  fix x y :: "'a adelic_int"
  assume xy: "- y + x \<in> \<P>\<^sub>\<forall>\<^sub>p"
  show "- inverse y + inverse x \<in> \<P>\<^sub>\<forall>\<^sub>p"
  proof (intro adelic_int_global_depth_setI)
    fix p :: "'a prime"
    assume xy': "- inverse y + inverse x \<not>\<simeq>\<^sub>p 0"
    have "((inverse x - inverse y)\<degree>\<^sup>p) > 0"
    proof (intro adelic_int_diff_cancel_lead_coeff)
      from xy' show "x \<not>\<simeq>\<^sub>p y"
        using p_equality_adelic_int.conv_0 adelic_int_inverse_pcong by fastforce
      with xy show "((x - y)\<degree>\<^sup>p) > 0"
        using p_equality_adelic_int.conv_0 global_p_depth_adelic_int.global_depth_setD
        by    fastforce
      moreover from this xy' show "x \<not>\<simeq>\<^sub>p 0" and "y \<not>\<simeq>\<^sub>p 0"
        using adelic_int_inverse_equiv0_iff global_p_depth_adelic_int.depth_diff_equiv0_left[of p x]
              global_p_depth_adelic_int.depth_diff_equiv0_right[of p y]
              p_equality_adelic_int.minus_0[of p "inverse x" "inverse y"]
        by    (force, force)
      ultimately show "(x\<degree>\<^sup>p) = 0" and "(y\<degree>\<^sup>p) = 0"
        using xy' adelic_int_depth adelic_int_inverse_equiv0_iff
              global_p_depth_adelic_int.depth_pre_nonarch_diff_left[of p x y]
              global_p_depth_adelic_int.depth_pre_nonarch_diff_right[of p y x]
              p_equality_adelic_int.minus_0[of p "inverse x" "inverse y"]
        by    (force, force)
    qed
    thus "((- inverse y + inverse x)\<degree>\<^sup>p) \<ge> 1" by force
  qed
qed simp

definition inverse_adelic_int_quot :: "'a adelic_int_quot \<Rightarrow> 'a adelic_int_quot"
  where
    "inverse_adelic_int_quot x \<equiv>
      Abs_adelic_int_quot (inverse_adelic_int_coset (Rep_adelic_int_quot x))"

lemma inverse_adelic_int_quot: "inverse (adelic_int_quot x) = adelic_int_quot (inverse x)"
  unfolding inverse_adelic_int_quot_def
  by        (simp add: Abs_adelic_int_quot_inverse inverse_adelic_int_coset.abs_eq)

lemma inverse_adelic_int_quot_0[simp]: "inverse (0 :: 'a adelic_int_quot) = 0"
  by (metis zero_adelic_int_quot inverse_adelic_int_quot adelic_int_inverse0)

lemma inverse_adelic_int_quot_1[simp]: "inverse (1 :: 'a adelic_int_quot) = 1"
  by (metis one_adelic_int_quot inverse_adelic_int_quot adelic_int_inverse1)

definition divide_adelic_int_quot ::
  "'a adelic_int_quot \<Rightarrow> 'a adelic_int_quot \<Rightarrow> 'a adelic_int_quot"
  where divide_adelic_int_quot_def[simp]: "divide_adelic_int_quot x y \<equiv> x * inverse y"

instance by standard simp_all

end

lemma divide_adelic_int_quot: "adelic_int_quot x / adelic_int_quot y = adelic_int_quot (x / y)"
  for x y :: "'a::nontrivial_factorial_unique_euclidean_bezout adelic_int"
  using     times_adelic_int_quot inverse_adelic_int_quot
  unfolding divide_adelic_int_quot_def divide_adelic_int_def
  by        metis


subsection \<open>Equivalence relative to a prime\<close>

subsubsection \<open>Equivalence\<close>

overloading
  p_equal_adelic_int_coset \<equiv>
    "p_equal :: 'a::nontrivial_factorial_idom prime \<Rightarrow>
      'a adelic_int coset_by_dist_sbgrp \<Rightarrow>
      'a adelic_int coset_by_dist_sbgrp \<Rightarrow> bool"
  p_equal_adelic_int_quot \<equiv>
    "p_equal :: 'a::nontrivial_factorial_idom prime \<Rightarrow>
      'a adelic_int_quot \<Rightarrow> 'a adelic_int_quot \<Rightarrow> bool"
  p_restrict_adelic_int_coset \<equiv>
    "p_restrict :: 'a adelic_int coset_by_dist_sbgrp \<Rightarrow>
      ('a prime \<Rightarrow> bool) \<Rightarrow> 'a adelic_int coset_by_dist_sbgrp"
  p_restrict_adelic_int_quot \<equiv>
    "p_restrict :: 'a adelic_int_quot \<Rightarrow>
      ('a prime \<Rightarrow> bool) \<Rightarrow> 'a adelic_int_quot"
begin

lift_definition p_equal_adelic_int_coset ::
  "'a::nontrivial_factorial_idom prime \<Rightarrow>
    'a adelic_int coset_by_dist_sbgrp \<Rightarrow>
    'a adelic_int coset_by_dist_sbgrp \<Rightarrow> bool"
  is "\<lambda>p x y. x \<simeq>\<^sub>p y \<or> ((x - y)\<degree>\<^sup>p) \<ge> 1"
  unfolding distinguished_subset_adelic_int_def
proof-
  fix p :: "'a prime" and w x y z :: "'a adelic_int"
  assume "-w + y \<in> \<P>\<^sub>\<forall>\<^sub>p" and "-x + z \<in> \<P>\<^sub>\<forall>\<^sub>p"
  moreover have
    "\<And>w x y z :: 'a adelic_int.
      y - w \<in> \<P>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
      z - x \<in> \<P>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
      w \<simeq>\<^sub>p x \<or> ((w - x)\<degree>\<^sup>p) \<ge> 1 \<Longrightarrow>
      ((y - z)\<degree>\<^sup>p) \<ge> 1 \<or> y \<simeq>\<^sub>p z"
  proof clarify
    fix w x y z :: "'a adelic_int"
    assume  wy    : "y - w \<in> \<P>\<^sub>\<forall>\<^sub>p"
      and   xz    : "z - x \<in> \<P>\<^sub>\<forall>\<^sub>p"
      and   equiv : "w \<simeq>\<^sub>p x \<or> ((w - x)\<degree>\<^sup>p) \<ge> 1"
      and   nequiv: "y \<not>\<simeq>\<^sub>p z"
    have 1: "y - z = w - x + ((y - w) - (z - x))" by simp
    from wy xz have 2: "(y - w) - (z - x) \<in> \<P>\<^sub>\<forall>\<^sub>p"
      using global_p_depth_adelic_int.global_depth_set_minus by auto
    show "((y - z)\<degree>\<^sup>p) \<ge> 1"
    proof (
      cases "w \<simeq>\<^sub>p x" "(y - w) \<simeq>\<^sub>p (z - x)"
        rule: case_split[case_product case_split],
      metis nequiv 1 p_equality_adelic_int.conv_0 p_equality_adelic_int.add_0,
      metis 1 2 p_equality_adelic_int.conv_0 global_p_depth_adelic_int.depth_add_equiv0_left
            global_p_depth_adelic_int.global_depth_setD global_depth_set_adelic_int_def,
      metis equiv 1 p_equality_adelic_int.conv_0
            global_p_depth_adelic_int.depth_add_equiv0_right
    )
      case False_False
      hence   wx: "w - x \<not>\<simeq>\<^sub>p 0"
        and   wyxz: "(y - w) - (z - x) \<not>\<simeq>\<^sub>p 0"
        using p_equality_adelic_int.conv_0
        by    (fast, fast)
      with nequiv equiv False_False(1) show ?thesis
        using 1 2 global_p_depth_adelic_int.depth_nonarch p_equality_adelic_int.conv_0
              global_p_depth_adelic_int.global_depth_setD[of p "(y - w) - (z - x)" 1]
        by    fastforce
    qed
  qed
  ultimately show
    "w \<simeq>\<^sub>p x \<or> ((w - x)\<degree>\<^sup>p) \<ge> 1 \<longleftrightarrow>
      y \<simeq>\<^sub>p z \<or> ((y - z)\<degree>\<^sup>p) \<ge> 1"
    by (metis uminus_add_conv_diff symp_lcosetrel distinguished_subset_adelic_int_def)
qed

definition p_equal_adelic_int_quot ::
  "'a::nontrivial_factorial_idom prime \<Rightarrow>
    'a adelic_int_quot \<Rightarrow> 'a adelic_int_quot \<Rightarrow> bool"
  where
    "p_equal_adelic_int_quot p x y \<equiv>
      (Rep_adelic_int_quot x) \<simeq>\<^sub>p (Rep_adelic_int_quot y)"

lift_definition p_restrict_adelic_int_coset ::
  "'a::nontrivial_factorial_idom adelic_int coset_by_dist_sbgrp \<Rightarrow>
    ('a prime \<Rightarrow> bool) \<Rightarrow> 'a adelic_int coset_by_dist_sbgrp"
  is "\<lambda>x P. x prestrict P"
  by (
    simp  add:  global_p_depth_adelic_int.global_depth_set_p_restrict
          flip: global_p_depth_adelic_int.p_restrict_minus
  )

definition p_restrict_adelic_int_quot ::
  "'a::nontrivial_factorial_idom adelic_int_quot \<Rightarrow>
    ('a prime \<Rightarrow> bool) \<Rightarrow> 'a adelic_int_quot"
  where
    "p_restrict_adelic_int_quot x P \<equiv>
      Abs_adelic_int_quot ((Rep_adelic_int_quot x) prestrict P)"

end  (* overloading *)

context
  fixes p :: "'a::nontrivial_factorial_idom prime"
begin

lemma p_equal_adelic_int_coset_abs_eq0:
  "distinguished_quotient_coset x \<simeq>\<^sub>p 0 \<longleftrightarrow>
    x \<simeq>\<^sub>p 0 \<or> (x\<degree>\<^sup>p) \<ge> 1"
  for x :: "'a adelic_int"
  unfolding p_equal_adelic_int_coset.abs_eq zero_coset_by_dist_sbgrp.abs_eq by simp

lemma p_equal_adelic_int_coset_abs_eq1:
  "distinguished_quotient_coset x \<simeq>\<^sub>p 1 \<longleftrightarrow>
    x \<simeq>\<^sub>p 1 \<or> ((x - 1)\<degree>\<^sup>p) \<ge> 1"
  for x :: "'a adelic_int"
  unfolding p_equal_adelic_int_coset.abs_eq one_coset_by_dist_sbgrp.abs_eq by simp

lemma p_equal_adelic_int_quot_abs_eq:
  "(adelic_int_quot x) \<simeq>\<^sub>p (adelic_int_quot y) \<longleftrightarrow>
    x \<simeq>\<^sub>p y \<or> ((x - y)\<degree>\<^sup>p) \<ge> 1"
  for x y :: "'a adelic_int"
  using     Abs_adelic_int_quot_inverse[of "distinguished_quotient_coset x"]
            Abs_adelic_int_quot_inverse[of "distinguished_quotient_coset y"]
            p_equal_adelic_int_coset.abs_eq
  unfolding p_equal_adelic_int_quot_def
  by        auto

lemma p_equal_adelic_int_quot_abs_eq0:
  "adelic_int_quot x \<simeq>\<^sub>p 0 \<longleftrightarrow>
    x \<simeq>\<^sub>p 0 \<or> (x\<degree>\<^sup>p) \<ge> 1"
  for x :: "'a adelic_int"
  using p_equal_adelic_int_quot_abs_eq unfolding zero_adelic_int_quot by fastforce

lemma p_equal_adelic_int_quot_abs_eq1:
  "adelic_int_quot x \<simeq>\<^sub>p 1 \<longleftrightarrow>
    x \<simeq>\<^sub>p 1 \<or> ((x - 1)\<degree>\<^sup>p) \<ge> 1"
  for x :: "'a adelic_int"
  using p_equal_adelic_int_quot_abs_eq unfolding one_adelic_int_quot by fastforce

end (* context nontrivial_factorial_idom *)

lemma p_restrict_adelic_int_quot_abs_eq:
  "(adelic_int_quot x) prestrict P = adelic_int_quot (x  prestrict P)"
  for P :: "'a::nontrivial_factorial_idom prime \<Rightarrow> bool" and x :: "'a adelic_int"
  unfolding p_restrict_adelic_int_quot_def
  by        (simp add: Abs_adelic_int_quot_inverse p_restrict_adelic_int_coset.abs_eq)

global_interpretation p_equality_adelic_int_quot:
  p_equality_no_zero_divisors_1
    "p_equal :: 'a::nontrivial_euclidean_ring_cancel prime \<Rightarrow>
      'a adelic_int_quot \<Rightarrow> 'a adelic_int_quot \<Rightarrow> bool"
proof

  fix p :: "'a prime"

  define E :: "'a adelic_int_quot \<Rightarrow> 'a adelic_int_quot \<Rightarrow> bool"
    where "E \<equiv> p_equal p"
  have "reflp E"
    unfolding E_def
  proof (intro reflpI)
    fix x :: "'a adelic_int_quot" show "x \<simeq>\<^sub>p x"
      by (cases x rule: adelic_int_quot_cases, simp add: p_equal_adelic_int_quot_abs_eq)
  qed
  moreover have "symp E"
    unfolding E_def
  proof (intro sympI)
    fix x y :: "'a adelic_int_quot"
    show "x \<simeq>\<^sub>p y \<Longrightarrow> y \<simeq>\<^sub>p x"
      by (
        cases x y rule: two_adelic_int_quot_cases, simp add: p_equal_adelic_int_quot_abs_eq,
            metis p_equality_adelic_int.sym global_p_depth_adelic_int.depth_diff
      )
  qed
  moreover have "transp E"
    unfolding E_def
  proof (intro transpI)
    fix x y z :: "'a adelic_int_quot"
    assume xy: "x \<simeq>\<^sub>p y" and yz: "y \<simeq>\<^sub>p z"
    show "x \<simeq>\<^sub>p z"
    proof (cases x y z rule: three_adelic_int_quot_cases)
      case (adelic_int_quot_adelic_int_quot_adelic_int_quot a b c)
      have "a \<simeq>\<^sub>p c \<or> ((a - c)\<degree>\<^sup>p) \<ge> 1"
      proof (rule iffD1, rule disj_commute, intro disjCI)
        assume ac: "a \<not>\<simeq>\<^sub>p c"
        with xy yz adelic_int_quot_adelic_int_quot_adelic_int_quot consider
          (ab) "a \<simeq>\<^sub>p b" "1 \<le> ((b - c)\<degree>\<^sup>p)" |
          (bc) "b \<simeq>\<^sub>p c" "1 \<le> ((a - b)\<degree>\<^sup>p)" |
          (neither) "1 \<le> ((a - b)\<degree>\<^sup>p)" "1 \<le> ((b - c)\<degree>\<^sup>p)"
          using p_equal_adelic_int_quot_abs_eq p_equality_adelic_int.trans by meson
        thus "1 \<le> ((a - c)\<degree>\<^sup>p)"
        proof cases
          case ab thus ?thesis using adelic_int_diff_depth_gt0_equiv_trans[of 0 p a b c] by simp
        next
          case bc thus ?thesis
            using adelic_int_diff_depth_gt0_equiv_trans[of 0 p c b a] p_equality_adelic_int.sym
                  global_p_depth_adelic_int.depth_diff[of p b a]
                  global_p_depth_adelic_int.depth_diff[of p a c]
            by    force
        next
          case neither with ac show ?thesis
            using adelic_int_diff_depth_gt0_trans[of 0 p a b c] by simp
        qed
      qed
      with adelic_int_quot_adelic_int_quot_adelic_int_quot(1,3) show ?thesis
        using p_equal_adelic_int_quot_abs_eq by auto
    qed
  qed
  ultimately show "equivp E" by (auto intro: equivpI)

  fix x y :: "'a adelic_int_quot"

  show "(x \<simeq>\<^sub>p y) = (x - y \<simeq>\<^sub>p 0)"
    by (
      cases x y rule: two_adelic_int_quot_cases,
      simp add: minus_adelic_int_quot p_equal_adelic_int_quot_abs_eq
                p_equal_adelic_int_quot_abs_eq0,
      metis p_equality_adelic_int.conv_0
    )

  show "y \<simeq>\<^sub>p 0 \<Longrightarrow> x * y \<simeq>\<^sub>p 0"
  proof (cases x y rule: two_adelic_int_quot_cases)
    case (adelic_int_quot_adelic_int_quot a b)
    assume "y \<simeq>\<^sub>p 0"
    with adelic_int_quot_adelic_int_quot(2)
      have  "b \<simeq>\<^sub>p 0 \<or> 1 \<le> (b\<degree>\<^sup>p)"
      using p_equal_adelic_int_quot_abs_eq0
      by    fast
    hence "a * b \<simeq>\<^sub>p 0 \<or> 1 \<le> ((a * b)\<degree>\<^sup>p)"
      using adelic_int_depth[of p a] global_p_depth_adelic_int.depth_mult_additive
            p_equality_adelic_int.mult_0_right
      by    fastforce
    with adelic_int_quot_adelic_int_quot show ?thesis
      using times_adelic_int_quot p_equal_adelic_int_quot_abs_eq0 by metis
  qed

  have "(1::'a adelic_int_quot) \<not>\<simeq>\<^sub>p 0"
    unfolding p_equal_adelic_int_quot_def
    by (
      simp only: zero_adelic_int_quot_rep_eq one_adelic_int_quot_rep_eq, transfer,
      simp, rule p_equality_adelic_int.one_p_nequal_zero
    )
  thus "\<exists>x::'a adelic_int_quot. x \<not>\<simeq>\<^sub>p 0" by blast

  show
    "x \<not>\<simeq>\<^sub>p 0 \<Longrightarrow> y \<not>\<simeq>\<^sub>p 0 \<Longrightarrow>
      x * y \<not>\<simeq>\<^sub>p 0"
  proof (cases x y rule: two_adelic_int_quot_cases)
    case (adelic_int_quot_adelic_int_quot a b)
    assume x: "x \<not>\<simeq>\<^sub>p 0" and y: "y \<not>\<simeq>\<^sub>p 0"
    with adelic_int_quot_adelic_int_quot
      have  a: "a \<not>\<simeq>\<^sub>p 0" "(a\<degree>\<^sup>p) < 1"
      and   b: "b \<not>\<simeq>\<^sub>p 0" "(b\<degree>\<^sup>p) < 1"
      using p_equal_adelic_int_quot_abs_eq0
      by    (fast, fastforce, fast, fastforce)
    from a(1) b(1) have "a * b \<not>\<simeq>\<^sub>p 0"
      using p_equality_adelic_int.no_zero_divisors by blast
    moreover from this a(2) b(2) have "((a * b)\<degree>\<^sup>p) < 1"
      using adelic_int_depth global_p_depth_adelic_int.depth_mult_additive by fastforce
    ultimately have "adelic_int_quot (a * b) \<not>\<simeq>\<^sub>p 0"
      using p_equal_adelic_int_quot_abs_eq0 by fastforce
    with adelic_int_quot_adelic_int_quot times_adelic_int_quot show "x * y \<not>\<simeq>\<^sub>p 0"
      by metis
  qed

qed

overloading
  globally_p_equal_adelic_int_quot \<equiv>
    "globally_p_equal ::
      'a::nontrivial_euclidean_ring_cancel adelic_int_quot \<Rightarrow>
        'a adelic_int_quot \<Rightarrow> bool"
begin

definition globally_p_equal_adelic_int_quot ::
  "'a::nontrivial_euclidean_ring_cancel adelic_int_quot \<Rightarrow>
    'a adelic_int_quot \<Rightarrow> bool"
  where globally_p_equal_adelic_int_quot_def[simp]:
    "globally_p_equal_adelic_int_quot = p_equality_adelic_int_quot.globally_p_equal"

end  (* overloading *)

subsubsection \<open>Embedding of constants\<close>

global_interpretation global_p_equal_adelic_int_quot:
  global_p_equal_w_consts
    "p_equal :: 'a::nontrivial_euclidean_ring_cancel prime \<Rightarrow>
      'a adelic_int_quot \<Rightarrow> 'a adelic_int_quot \<Rightarrow> bool"
    "p_restrict ::
      'a adelic_int_quot \<Rightarrow> ('a prime \<Rightarrow> bool) \<Rightarrow>
        'a adelic_int_quot"
    "\<lambda>f. adelic_int_quot (adelic_int_consts f)"
proof (unfold_locales, fold globally_p_equal_adelic_int_quot_def)

  fix p :: "'a prime"
  and x y :: "'a adelic_int_quot"

  show "x \<simeq>\<^sub>\<forall>\<^sub>p y \<Longrightarrow> x = y"
  proof (cases x y rule: two_adelic_int_quot_cases)
    case (adelic_int_quot_adelic_int_quot a b)
    moreover assume xy: "x \<simeq>\<^sub>\<forall>\<^sub>p y"
    ultimately have
      "\<forall>p::'a prime.
        - a + b \<not>\<simeq>\<^sub>p 0 \<longrightarrow> ((- a + b)\<degree>\<^sup>p) \<ge> 1"
      using p_equality_adelic_int.conv_0[of _ b a] p_equal_adelic_int_quot_abs_eq[of _ a b]
            p_equality_adelic_int.sym[of _ a b]
            global_p_depth_adelic_int.depth_diff[of _ a b]
      by    fastforce
    with adelic_int_quot_adelic_int_quot show "x = y"
      using distinguished_quotient_coset_eqI[of a b] global_p_depth_adelic_int.global_depth_setI
      by    fastforce
  qed

  fix P :: "'a prime \<Rightarrow> bool"

  show "P p \<Longrightarrow> x prestrict P \<simeq>\<^sub>p x"
    by (
      cases x rule: adelic_int_quot_cases,
      simp add: p_restrict_adelic_int_quot_abs_eq p_equal_adelic_int_quot_abs_eq
                global_p_depth_adelic_int.p_restrict_equiv
    )

  show "\<not> P p \<Longrightarrow> x prestrict P \<simeq>\<^sub>p 0"
    by (
      cases x rule: adelic_int_quot_cases,
      simp add: p_restrict_adelic_int_quot_abs_eq p_equal_adelic_int_quot_abs_eq0,
      metis global_p_depth_adelic_int.p_restrict_equiv0
    )

  fix f g :: "'a prime \<Rightarrow> 'a"

  show
    "adelic_int_quot (adelic_int_consts (f - g)) =
      adelic_int_quot (adelic_int_consts f) - adelic_int_quot (adelic_int_consts g)"
    using global_p_depth_adelic_int.consts_diff minus_adelic_int_quot by metis

  show
    "adelic_int_quot (adelic_int_consts (f * g)) =
      adelic_int_quot (adelic_int_consts f) * adelic_int_quot (adelic_int_consts g)"
    using global_p_depth_adelic_int.consts_mult times_adelic_int_quot by metis

qed (metis global_p_depth_adelic_int.consts_1 one_adelic_int_quot)

abbreviation "adelic_int_quot_consts \<equiv> global_p_equal_adelic_int_quot.consts"
abbreviation "adelic_int_quot_const  \<equiv> global_p_equal_adelic_int_quot.const"

lemma p_equal_adelic_int_quot_consts_iff:
  "(adelic_int_quot_consts f) \<simeq>\<^sub>p (adelic_int_quot_consts g) \<longleftrightarrow>
    (f p) pmod p = (g p) pmod p"
  (is "?L \<longleftrightarrow> ?R")
proof-
  have "((\<lambda>p. fls_const (f p)) - (\<lambda>p. fls_const (g p))) p = fls_const (f p - g p)"
    by (simp add: fls_minus_const)
  have "?L \<longleftrightarrow> f p = g p \<or> 1 \<le> int (pmultiplicity p ((f - g) p))"
    using p_equal_adelic_int_quot_abs_eq global_p_depth_adelic_int.consts_diff
          global_p_depth_adelic_int.p_equal_func_of_consts
          global_p_depth_adelic_int.p_depth_func_of_consts
    by    metis
  also have "\<dots> \<longleftrightarrow> ?R"
    using Rep_prime_not_unit multiplicity_gt_zero_iff[of "f p - g p"]
          mod_eq_dvd_iff[of "f p" "Rep_prime p" "g p"]
    by    force
  finally show ?thesis by blast
qed

lemma p_equal0_adelic_int_quot_consts_iff:
  "(adelic_int_quot_consts f) \<simeq>\<^sub>p 0 \<longleftrightarrow> (f p) pmod p = 0"
  (is "?L \<longleftrightarrow> ?R")
proof-
  have "?L \<longleftrightarrow> f p pmod p = 0 pmod p"
    by (
      metis global_p_equal_adelic_int_quot.consts_0 p_equal_adelic_int_quot_consts_iff
            zero_fun_apply
    )
  thus ?thesis by auto
qed

lemma adelic_int_quot_consts_eq_iff:
  "adelic_int_quot_consts f = adelic_int_quot_consts g \<longleftrightarrow>
    (\<forall>p. (f p) pmod p = (g p) pmod p)"
  using global_p_equal_adelic_int_quot.global_eq_iff p_equal_adelic_int_quot_consts_iff[of _ f g]
  by    auto

lemma adelic_int_quot_consts_eq0_iff:
  "(adelic_int_quot_consts f) = 0 \<longleftrightarrow>
    (\<forall>p. (f p) pmod p = 0)"
  using global_p_equal_adelic_int_quot.global_eq_iff p_equal0_adelic_int_quot_consts_iff[of _ f]
  by    auto

lemmas
  p_equal_adelic_int_quot_const_iff =
    p_equal_adelic_int_quot_consts_iff[of _ "\<lambda>p. _" "\<lambda>p. _"]
and p_equal0_adelic_int_quot_const_iff = p_equal0_adelic_int_quot_consts_iff[of _ "\<lambda>p. _"]
and adelic_int_quot_const_eq_iff = adelic_int_quot_consts_eq_iff[of "\<lambda>p. _" "\<lambda>p. _"]
and adelic_int_quot_const_eq0_iff = adelic_int_quot_consts_eq0_iff[of "\<lambda>p. _"]

lemma adelic_int_quot_UNIV_eq_consts_range:
  "(UNIV::'a::nontrivial_euclidean_ring_cancel adelic_int_quot set) =
    range (adelic_int_quot_consts)"
proof (standard, standard)
  fix x :: "'a adelic_int_quot"
  show "x \<in> range adelic_int_quot_consts"
  proof (cases x rule: Abs_adelic_int_quot_cases)
    case (adelic_int_quot_Abs_adelic_int a)
    have  "p_adic_prod_int_quot a \<in> range adelic_int_quot_consts"
    proof (cases a)
      case (abs_p_adic_prod X)
      with adelic_int_quot_Abs_adelic_int(2)
        have  dX: "\<forall>p::'a prime. (X\<degree>\<^sup>p) \<ge> 0"
        using global_p_depth_p_adic_prod.nonpos_global_depth_setD
              p_depth_p_adic_prod.abs_eq[of _ X]
        by    fastforce
      define f :: "'a prime \<Rightarrow> 'a" where "f \<equiv> \<lambda>p. (X p pmod p) $$ 0"
      have "adelic_int_consts f - Abs_adelic_int a \<in> \<P>\<^sub>\<forall>\<^sub>p"
        unfolding global_depth_set_adelic_int_def
      proof (intro global_p_depth_adelic_int.global_depth_setI)
        fix p :: "'a prime"
        assume "(adelic_int_consts f - Abs_adelic_int a) \<not>\<simeq>\<^sub>p 0"
        with adelic_int_quot_Abs_adelic_int(2) abs_p_adic_prod
          have  nequiv: "(fls_const (f p)) \<not>\<simeq>\<^sub>p (X p pmod p)"
          using p_equality_adelic_int.conv_0
                global_p_depth_p_adic_prod.global_depth_set_consts p_equal_adelic_int_abs_eq
                p_equal_p_adic_prod.abs_eq global_depth_set_p_adic_prod_def p_equal_fls_pseq_def
                fls_pmod_equiv p_equality_fls.trans_left
          by    metis
        have "\<forall>k<0. (X p pmod p) $$ k = 0"
        proof clarify
          fix k :: int assume "k < 0"
          moreover have "(X p\<degree>\<^sup>p) \<ge> 0" using dX by auto
          ultimately show "(X p pmod p) $$ k = 0" using fls_pmod_subdegree[of _ p] by simp
        qed
        moreover have "fls_const (f p) \<noteq> X p pmod p" using nequiv by auto
        ultimately have "fls_subdegree (fls_const (f p) - X p pmod p) > 0"
          by (auto intro: fls_subdegree_greaterI simp add: f_def)
        moreover from adelic_int_quot_Abs_adelic_int(2) abs_p_adic_prod have
          "((adelic_int_consts f - Abs_adelic_int a)\<degree>\<^sup>p) =
            ((fls_const (f p) - X p pmod p)\<degree>\<^sup>p)"
          using global_p_depth_p_adic_prod.global_depth_set_consts minus_apply[of _ X p]
                p_depth_adelic_int_diff_abs_eq[of _ a p] p_depth_p_adic_prod_diff_abs_eq[of p _ X]
                p_depth_fls_pseq_def global_depth_set_p_adic_prod_def p_depth_fls.depth_equiv
                p_equality_fls.minus_left fls_pmod_equiv
          by    metis
        ultimately show "((adelic_int_consts f - Abs_adelic_int a)\<degree>\<^sup>p) \<ge> 1"
          using nequiv p_equality_fls.conv_0 p_depth_fls_ge_p_equal_subdegree' by fastforce
      qed
      hence
        "p_adic_prod_int_quot a =
          p_adic_prod_int_quot (abs_p_adic_prod (\<lambda>p. fls_const (f p)))"
        using Abs_adelic_int_quot_inject distinguished_quotient_coset_eqI by force
      thus "adelic_int_quot (Abs_adelic_int a) \<in> range adelic_int_quot_consts" by blast
    qed
    with adelic_int_quot_Abs_adelic_int(1) show ?thesis by blast
  qed
qed simp

lemma adelic_int_quot_constsE:
  fixes x :: "'a::nontrivial_euclidean_ring_cancel adelic_int_quot"
  obtains f where "x = adelic_int_quot_consts f"
  using adelic_int_quot_UNIV_eq_consts_range by blast

lemma adelic_int_quot_reduced_constsE:
  fixes x :: "'a::nontrivial_euclidean_ring_cancel adelic_int_quot"
  obtains f
    where "x = adelic_int_quot_consts f"
    and   "\<forall>p::'a prime. (f p) pdiv p = 0"
proof-
  obtain g where g: "x = adelic_int_quot_consts g"
    using adelic_int_quot_constsE by blast
  define f :: "'a prime \<Rightarrow> 'a" where "f \<equiv> \<lambda>p. g p pmod p"
  hence "\<forall>p::'a prime. (f p) pdiv p = 0"
    using div_mult_mod_eq by fastforce
  moreover from g f_def have "x = adelic_int_quot_consts f"
    using adelic_int_quot_consts_eq_iff by force
  ultimately show thesis using that by presburger
qed

lemma adelic_int_quot_prestrict_zero_depth_abs_eq:
  "adelic_int_quot (x prestrict (\<lambda>p::'a prime. (x\<degree>\<^sup>p) = 0)) =
    adelic_int_quot x"
  for x :: "'a::nontrivial_euclidean_ring_cancel adelic_int"
proof (intro global_p_equal_adelic_int_quot.global_imp_eq, standard)
  fix p :: "'a prime"
  define P :: "'a prime \<Rightarrow> bool" where "P \<equiv> \<lambda>p. (x\<degree>\<^sup>p) = 0"
  hence
    "x prestrict P \<not>\<simeq>\<^sub>p x \<Longrightarrow>
      ((x prestrict P - x)\<degree>\<^sup>p) \<ge> 1"
    using adelic_int_prestrict_zero_depth by fast
  thus "(adelic_int_quot (x prestrict P)) \<simeq>\<^sub>p (adelic_int_quot x)"
    using p_equal_adelic_int_quot_abs_eq by blast
qed

subsubsection \<open>Division and inverses\<close>

global_interpretation p_equal_div_inv_adelic_int_quot:
  global_p_equal_div_inv
    "p_equal :: 'a::nontrivial_factorial_unique_euclidean_bezout prime \<Rightarrow>
      'a adelic_int_quot \<Rightarrow> 'a adelic_int_quot \<Rightarrow> bool"
    "p_restrict ::
      'a adelic_int_quot \<Rightarrow> ('a prime \<Rightarrow> bool) \<Rightarrow>
        'a adelic_int_quot"
proof

  define A :: "'a adelic_int coset_by_dist_sbgrp \<Rightarrow> 'a adelic_int_quot"
    where "A \<equiv> Abs_adelic_int_quot"

  fix p :: "'a prime" and x y :: "'a adelic_int_quot"

  show "inverse (inverse x) = x"
  proof (cases x rule: adelic_int_quot_cases)
    case (adelic_int_quot a)
    moreover define P :: "'a prime \<Rightarrow> bool"
      where "P \<equiv> \<lambda>p. (a\<degree>\<^sup>p) = 0"
    moreover from this have "adelic_int_quot (a prestrict P) = adelic_int_quot a"
      using global_p_equal_adelic_int_quot.global_imp_eq p_equal_adelic_int_quot_abs_eq
            adelic_int_prestrict_zero_depth
      by    fast
    ultimately show "inverse (inverse x) = x"
      using inverse_adelic_int_quot adelic_int_inverse_inverse by metis
  qed

  show "(inverse x \<simeq>\<^sub>p 0) = (x \<simeq>\<^sub>p 0)"
    by (
      cases x rule: adelic_int_quot_cases,
      simp add: A_def inverse_adelic_int_quot p_equal_adelic_int_quot_abs_eq0
                adelic_int_inverse_depth adelic_int_inverse_equiv0_iff'
    )

  show "x \<not>\<simeq>\<^sub>p 0 \<Longrightarrow> x / x \<simeq>\<^sub>p 1"
  proof (cases x rule: adelic_int_quot_cases)
    case (adelic_int_quot a)
    moreover assume "x \<not>\<simeq>\<^sub>p 0"
    ultimately have "a \<not>\<simeq>\<^sub>p 0" and "a\<degree>\<^sup>p = 0"
      using p_equal_adelic_int_quot_abs_eq0 adelic_int_depth[of p a] by (blast, fastforce)
    hence "a / a \<simeq>\<^sub>p 1"
      using adelic_int_divide_self[of a] global_p_depth_adelic_int.p_restrict_equiv[of _ p]
      by    presburger
    with adelic_int_quot show "x / x \<simeq>\<^sub>p 1"
      using p_equal_adelic_int_quot_abs_eq1 divide_adelic_int_quot by metis
  qed

  show "inverse (x * y) = inverse x * inverse y"
    by (
      cases x y rule: two_adelic_int_quot_cases,
      simp add: A_def inverse_adelic_int_quot times_adelic_int_quot adelic_int_inverse_mult
    )

qed simp


subsection \<open>Special case of integer\<close>

context
  fixes p :: "int prime"
begin

lemma inj_on_const_prestrict_single_int_prime:
  "inj_on (\<lambda>k. adelic_int_quot_const k prestrict ((=) p)) {0..Rep_prime p - 1}"
proof (standard, unfold atLeastAtMost_iff, clarify)
  define pp :: int and C :: "int \<Rightarrow> int adelic_int_quot"
    where "pp \<equiv> Rep_prime p"
    and   "C \<equiv> \<lambda>k. adelic_int_quot_const k prestrict ((=) p)"
  fix j k :: int
  show
    "\<lbrakk> j \<ge> 0; j \<le> pp - 1; k \<ge> 0; k \<le> pp - 1; C j = C k \<rbrakk>
      \<Longrightarrow> j = k"
  proof (induct j k rule: linorder_wlog)
    fix j k :: int
    assume  j : "j \<ge> 0" "j \<le> pp - 1"
      and   k : "k \<ge> 0" "k \<le> pp - 1"
      and   jk: "j \<le> k" "C j = C k"
    from pp_def j(1) k(2) jk(1) have "((k - j)\<degree>\<^sup>p) = 0"
      using p_depth_const[of p "k - j"] zdvd_imp_le[of pp "k - j"] not_dvd_imp_multiplicity_0
      by    (cases "j = k") auto
    hence "\<not> ((k - j)\<degree>\<^sup>p) \<ge> 1" by presburger
    with C_def jk(2) show "j = k"
      using global_p_equal_adelic_int_quot.p_equal_iff_p_restrict_eq adelic_int_p_depth_const
            global_p_depth_adelic_int.const_diff global_p_depth_adelic_int.const_p_equal[of p]
            p_equal_adelic_int_quot_abs_eq[of p "adelic_int_const k" "adelic_int_const j"]
      by    metis
  qed simp
qed

lemma range_prestrict_single_int_prime:
  "range (\<lambda>x. x prestrict ((=) p)) =
    (\<lambda>k. adelic_int_quot_const k prestrict ((=) p)) ` {0..Rep_prime p - 1}"
proof safe
  define pp :: int and C :: "int \<Rightarrow> int adelic_int_quot"
    where "pp \<equiv> Rep_prime p"
    and   "C \<equiv> \<lambda>k. adelic_int_quot_const k prestrict ((=) p)"
  fix x :: "int adelic_int_quot"
  obtain f where f: "x = adelic_int_quot_consts f" "(f p) pdiv p = 0"
    using adelic_int_quot_reduced_constsE by blast
  from f(2) pp_def have "f p \<in> {0..pp - 1}"
    using div_mult_mod_eq[of "f p" "Rep_prime p"] prime_gt_0_int Rep_prime pos_mod_sign[of pp "f p"]
          pos_mod_bound[of pp "f p"]
    by    auto
  with f(1) show "x prestrict ((=) p) \<in> C ` {0..pp - 1}"
    using     p_equal_adelic_int_quot_consts_iff
    unfolding C_def
    by        (fastforce intro: global_p_equal_adelic_int_quot.p_restrict_eq_p_restrictI)
qed simp

lemma finite_range_prestrict_single_int_prime:
  "finite (range (\<lambda>x::int adelic_int_quot. x prestrict ((=) p)))"
  using range_prestrict_single_int_prime finite_image_iff inj_on_const_prestrict_single_int_prime
  by    simp

lemma card_range_prestrict_single_int_prime:
  "card (range (\<lambda>x::int adelic_int_quot. x prestrict ((=) p))) = nat (Rep_prime p)"
  using bij_betw_imageI[of _ _ "range (\<lambda>x. x prestrict ((=) p))"] bij_betw_same_card
        inj_on_const_prestrict_single_int_prime range_prestrict_single_int_prime[symmetric]
  by    fastforce

end (* int prime *)

end (* theory *)
