(*  Title:   Hyperdual.thy
    Authors: Filip Smola and Jacques D. Fleuriot, University of Edinburgh, 2019-2021
*)

theory Hyperdual
  imports "HOL-Analysis.Analysis"
begin

section\<open>Hyperdual Numbers\<close>
text\<open>
  Let \<open>\<tau>\<close> be some type.
  Second-order hyperdual numbers over \<open>\<tau>\<close> take the form \<open>a\<^sub>1 + a\<^sub>2\<epsilon>\<^sub>1 + a\<^sub>3\<epsilon>\<^sub>2 + a\<^sub>4\<epsilon>\<^sub>1\<epsilon>\<^sub>2\<close> where all
  \<open>a\<^sub>i :: \<tau>\<close>, and \<open>\<epsilon>\<^sub>1\<close> and \<open>\<epsilon>\<^sub>2\<close> are non-zero but nilpotent infinitesimals: \<open>\<epsilon>\<^sub>1\<^sup>2 = \<epsilon>\<^sub>2\<^sup>2 = (\<epsilon>\<^sub>1\<epsilon>\<^sub>2)\<^sup>2 = 0\<close>.

  We define second-order hyperdual numbers as a coinductive data type with four components: the base
  component, two first-order hyperdual components and one second-order hyperdual component.
\<close>
codatatype 'a hyperdual = Hyperdual (Base: 'a) (Eps1: 'a) (Eps2: 'a) (Eps12: 'a)

text\<open>Two hyperduals are equal iff all their components are equal.\<close>
lemma hyperdual_eq_iff [iff]:
  "x = y \<longleftrightarrow> ((Base x = Base y) \<and> (Eps1 x = Eps1 y) \<and> (Eps2 x = Eps2 y) \<and> (Eps12 x = Eps12 y))"
  using hyperdual.expand by auto

lemma hyperdual_eqI:
  assumes "Base x = Base y"
      and "Eps1 x = Eps1 y"
      and "Eps2 x = Eps2 y"
      and "Eps12 x = Eps12 y"
    shows "x = y"
  by (simp add: assms)

text\<open>
  The embedding from the component type to hyperduals requires the component type to have a zero
  element.
\<close>
definition of_comp :: "('a :: zero) \<Rightarrow> 'a hyperdual"
  where "of_comp a = Hyperdual a 0 0 0"

lemma of_comp_simps [simp]:
  "Base (of_comp a) = a"
  "Eps1 (of_comp a) = 0"
  "Eps2 (of_comp a) = 0"
  "Eps12 (of_comp a) = 0"
  by (simp_all add: of_comp_def)

subsection \<open>Addition and Subtraction\<close>

text\<open>We define hyperdual addition, subtraction and unary minus pointwise, and zero by embedding.\<close>
(* Define addition using component addition *)
instantiation hyperdual :: (plus) plus
begin

primcorec plus_hyperdual
  where
    "Base (x + y) = Base x + Base y"
  | "Eps1 (x + y) = Eps1 x + Eps1 y"
  | "Eps2 (x + y) = Eps2 x + Eps2 y"
  | "Eps12 (x + y) = Eps12 x + Eps12 y"

instance by standard
end

(* Define zero by embedding component zero *)
instantiation hyperdual :: (zero) zero
begin

definition zero_hyperdual
  where "0 = of_comp 0"

instance by standard
end

lemma zero_hyperdual_simps [simp]:
  "Base 0 = 0"
  "Eps1 0 = 0"
  "Eps2 0 = 0"
  "Eps12 0 = 0"
  "Hyperdual 0 0 0 0 = 0"
  by (simp_all add: zero_hyperdual_def)

(* Define minus using component minus *)
instantiation hyperdual :: (uminus) uminus
begin

primcorec uminus_hyperdual
  where
    "Base (-x) = - Base x"
  | "Eps1 (-x) = - Eps1 x"
  | "Eps2 (-x) = - Eps2 x"
  | "Eps12 (-x) = - Eps12 x"

instance by standard
end

(* Define subtraction using component subtraction *)
instantiation hyperdual :: (minus) minus
begin

primcorec minus_hyperdual
  where
    "Base (x - y) = Base x - Base y"
  | "Eps1 (x - y) = Eps1 x - Eps1 y"
  | "Eps2 (x - y) = Eps2 x - Eps2 y"
  | "Eps12 (x - y) = Eps12 x - Eps12 y"

instance by standard
end

text\<open>If the components form a commutative group under addition then so do the hyperduals.\<close>
instance hyperdual :: (semigroup_add) semigroup_add
  by standard (simp add: add.assoc)

instance hyperdual :: (monoid_add) monoid_add
  by standard simp_all

instance hyperdual :: (ab_semigroup_add) ab_semigroup_add
  by standard (simp_all add: add.commute)

instance hyperdual :: (comm_monoid_add) comm_monoid_add
  by standard simp

instance hyperdual :: (group_add) group_add
  by standard simp_all

instance hyperdual :: (ab_group_add) ab_group_add
  by standard simp_all

lemma of_comp_add:
  fixes a b :: "'a :: monoid_add"
  shows "of_comp (a + b) = of_comp a + of_comp b"
  by simp

lemma
  fixes a b :: "'a :: group_add"
  shows of_comp_minus: "of_comp (- a) = - of_comp a"
    and of_comp_diff: "of_comp (a - b) = of_comp a - of_comp b"
  by simp_all

subsection \<open>Multiplication and Scaling\<close>

text\<open>
  Multiplication of hyperduals is defined by distributing the expressions and using the nilpotence
  of \<open>\<epsilon>\<^sub>1\<close> and \<open>\<epsilon>\<^sub>2\<close>, resulting in the definition used here.
  The hyperdual one is again defined by embedding.
\<close>
(* Define one by embedding the component one, which also requires it to have zero *)
instantiation hyperdual :: ("{one, zero}") one
begin

definition one_hyperdual
  where "1 = of_comp 1"

instance by standard
end

lemma one_hyperdual_simps [simp]:
  "Base 1 = 1"
  "Eps1 1 = 0"
  "Eps2 1 = 0"
  "Eps12 1 = 0"
  "Hyperdual 1 0 0 0 = 1"
  by (simp_all add: one_hyperdual_def)

(* Define multiplication using component multiplication and addition *)
instantiation hyperdual :: ("{times, plus}") times
begin

primcorec times_hyperdual
  where
    "Base (x * y) = Base x * Base y"
  | "Eps1 (x * y) = (Base x * Eps1 y) + (Eps1 x * Base y)"
  | "Eps2 (x * y) = (Base x * Eps2 y) + (Eps2 x * Base y)"
  | "Eps12 (x * y) = (Base x * Eps12 y) + (Eps1 x * Eps2 y) + (Eps2 x * Eps1 y) + (Eps12 x * Base y)"

instance by standard
end

text\<open>If the components form a ring then so do the hyperduals.\<close>
instance hyperdual :: (semiring) semiring
  by standard (simp_all add: mult.assoc distrib_left distrib_right add.assoc add.left_commute)

instance hyperdual :: ("{monoid_add, mult_zero}") mult_zero
  by standard simp_all

instance hyperdual :: (ring) ring
  by standard

instance hyperdual :: (comm_ring) comm_ring
  by standard (simp_all add: mult.commute distrib_left)

instance hyperdual :: (ring_1) ring_1
  by standard simp_all

instance hyperdual :: (comm_ring_1) comm_ring_1
  by standard simp

lemma of_comp_times:
  fixes a b :: "'a :: semiring_0"
  shows "of_comp (a * b) = of_comp a * of_comp b"
  by (simp add: of_comp_def times_hyperdual.code)

text\<open>Hyperdual scaling is multiplying each component by a factor from the component type.\<close>
(* Named scaleH for hyperdual like scaleR is for real *)
primcorec scaleH :: "('a :: times) \<Rightarrow> 'a hyperdual \<Rightarrow> 'a hyperdual"  (infixr "*\<^sub>H" 75)
  where
    "Base (f *\<^sub>H x) = f * Base x"
  | "Eps1 (f *\<^sub>H x) = f * Eps1 x"
  | "Eps2 (f *\<^sub>H x) = f * Eps2 x"
  | "Eps12 (f *\<^sub>H x) = f * Eps12 x"

lemma scaleH_times:
  fixes f :: "'a :: {monoid_add, mult_zero}"
  shows "f *\<^sub>H x = of_comp f * x"
  by simp

lemma scaleH_add:
  fixes a :: "'a :: semiring"
  shows "(a + a') *\<^sub>H b = a *\<^sub>H b + a' *\<^sub>H b"
    and "a *\<^sub>H (b + b') = a *\<^sub>H b + a *\<^sub>H b'"
  by (simp_all add: distrib_left distrib_right)

lemma scaleH_diff:
  fixes a :: "'a :: ring"
  shows "(a - a') *\<^sub>H b = a *\<^sub>H b - a' *\<^sub>H b"
    and "a *\<^sub>H (b - b') = a *\<^sub>H b - a *\<^sub>H b'"
  by (auto simp add: left_diff_distrib right_diff_distrib scaleH_times of_comp_diff)

lemma scaleH_mult:
  fixes a :: "'a :: semigroup_mult"
  shows "(a * a') *\<^sub>H b = a *\<^sub>H a' *\<^sub>H b"
  by (simp add: mult.assoc)

lemma scaleH_one [simp]:
  fixes b :: "('a :: monoid_mult) hyperdual"
  shows "1 *\<^sub>H b = b"
  by simp

lemma scaleH_zero [simp]:
  fixes b :: "('a :: {mult_zero, times}) hyperdual"
  shows "0 *\<^sub>H b = 0"
  by simp

lemma
  fixes b :: "('a :: ring_1) hyperdual"
  shows scaleH_minus [simp]:"- 1 *\<^sub>H b = - b"
    and scaleH_minus_left: "- (a *\<^sub>H b) = - a *\<^sub>H b"
    and scaleH_minus_right: "- (a *\<^sub>H b) = a *\<^sub>H - b"
  by simp_all

text\<open>Induction rule for natural numbers that takes 0 and 1 as base cases.\<close>
lemma nat_induct01Suc[case_names 0 1 Suc]:
  assumes "P 0"
      and "P 1"
      and "\<And>n. n > 0 \<Longrightarrow> P n \<Longrightarrow> P (Suc n)"
    shows "P n"
  by (metis One_nat_def assms nat_induct neq0_conv)

lemma hyperdual_power:
  fixes x :: "('a :: comm_ring_1) hyperdual"
  shows "x ^ n = Hyperdual ((Base x) ^ n)
                           (Eps1 x * of_nat n * (Base x) ^ (n - 1))
                           (Eps2 x * of_nat n * (Base x) ^ (n - 1))
                           (Eps12 x * of_nat n * (Base x) ^ (n - 1) + Eps1 x * Eps2 x * of_nat n * of_nat (n - 1) * (Base x) ^ (n - 2))"
proof (induction n rule: nat_induct01Suc)
  case 0
  show ?case
    by simp
next
  case 1
  show ?case
    by simp
next
  case hyp: (Suc n)
  show ?case
  proof (simp add: hyp, intro conjI)
    show "Base x * (Eps1 x * of_nat n * Base x ^ (n - Suc 0)) + Eps1 x * Base x ^ n = Eps1 x * (1 + of_nat n) * Base x ^ n"
     and "Base x * (Eps2 x * of_nat n * Base x ^ (n - Suc 0)) + Eps2 x * Base x ^ n = Eps2 x * (1 + of_nat n) * Base x ^ n"
      by (simp_all add: distrib_left distrib_right power_eq_if)
    show
      "2 * (Eps1 x * (Eps2 x * (of_nat n * Base x ^ (n - Suc 0)))) +
       Base x * (Eps12 x * of_nat n * Base x ^ (n - Suc 0) + Eps1 x * Eps2 x * of_nat n * of_nat (n - Suc 0) * Base x ^ (n - 2)) +
       Eps12 x * Base x ^ n =
       Eps12 x * (1 + of_nat n) * Base x ^ n + Eps1 x * Eps2 x * (1 + of_nat n) * of_nat n * Base x ^ (n - Suc 0)"
    proof -
      have
        "2 * (Eps1 x * (Eps2 x * (of_nat n * Base x ^ (n - Suc 0)))) +
         Base x * (Eps12 x * of_nat n * Base x ^ (n - Suc 0) + Eps1 x * Eps2 x * of_nat n * of_nat (n - Suc 0) * Base x ^ (n - 2)) +
         Eps12 x * Base x ^ n =
         2 * Eps1 x * Eps2 x * of_nat n * Base x ^ (n - Suc 0) +
         Eps12 x * of_nat (n + 1) * Base x ^ n + Eps1 x * Eps2 x * of_nat n * of_nat (n - Suc 0) * Base x ^ (n - Suc 0)"
        by (simp add: field_simps power_eq_if)
      also have "... = Eps12 x * of_nat (n + 1) * Base x ^ n + of_nat (n - 1 + 2) * Eps1 x * Eps2 x * of_nat n * Base x ^ (n - Suc 0)"
        by (simp add: distrib_left mult.commute)
      finally show ?thesis
        by (simp add: hyp.hyps)
    qed
  qed
qed

lemma hyperdual_power_simps [simp]:
  shows "Base ((x :: 'a :: comm_ring_1 hyperdual) ^ n) = Base x ^ n"
    and "Eps1 ((x :: 'a :: comm_ring_1 hyperdual) ^ n) = Eps1 x * of_nat n * (Base x) ^ (n - 1)"
    and "Eps2 ((x :: 'a :: comm_ring_1 hyperdual) ^ n) = Eps2 x * of_nat n * (Base x) ^ (n - 1)"
    and "Eps12 ((x :: 'a :: comm_ring_1 hyperdual) ^ n) =
  (Eps12 x * of_nat n * (Base x) ^ (n - 1) + Eps1 x * Eps2 x * of_nat n * of_nat (n - 1) * (Base x) ^ (n - 2))"
  by (simp_all add: hyperdual_power)

text\<open>Squaring the hyperdual one behaves as expected from the reals.\<close>
(* Commutativity required to reorder times definition expressions, division algebra required for
    base component's x * x = 1 \<longrightarrow> x = 1 \<or> x = -1 *)
lemma hyperdual_square_eq_1_iff [iff]:
  fixes x :: "('a :: {real_div_algebra, comm_ring}) hyperdual"
  shows "x * x = 1 \<longleftrightarrow> x = 1 \<or> x = - 1"
proof
  assume a: "x * x = 1"

  have base: "Base x * Base x = 1"
    using a by simp
  moreover have e1: "Eps1 x = 0"
  proof -
    have "Base x * Eps1 x = - (Base x * Eps1 x)"
      using mult.commute[of "Base x"] add_eq_0_iff[of "Base x * Eps1 x"] times_hyperdual.simps(2)[of x x]
      by (simp add: a)
    then have "Base x * Base x * Eps1 x = - Base x * Base x * Eps1 x"
      using mult_left_cancel[of "Base x"] base by fastforce
    then show ?thesis
      using base mult_right_cancel[of "Eps1 x" "Base x * Base x" "- Base x * Base x"] one_neq_neg_one
      by auto
  qed
  moreover have e2: "Eps2 x = 0"
  proof -
    have "Base x * Eps2 x = - (Base x * Eps2 x)"
      using a mult.commute[of "Base x" "Eps2 x"] add_eq_0_iff[of "Base x * Eps2 x"] times_hyperdual.simps(3)[of x x]
      by simp
    then have "Base x * Base x * Eps2 x = - Base x * Base x * Eps2 x"
      using mult_left_cancel[of "Base x"] base by fastforce
    then show ?thesis
      using base mult_right_cancel[of "Eps2 x" "Base x * Base x" "- Base x * Base x"] one_neq_neg_one
      by auto
  qed
  moreover have "Eps12 x = 0"
  proof -
    have "Base x * Eps12 x = - (Base x * Eps12 x)"
      using a e1 e2 mult.commute[of "Base x" "Eps12 x"] add_eq_0_iff[of "Base x * Eps12 x"] times_hyperdual.simps(4)[of x x]
      by simp
    then have "Base x * Base x * Eps12 x = - Base x * Base x * Eps12 x"
      using mult_left_cancel[of "Base x"] base by fastforce
    then show ?thesis
      using base mult_right_cancel[of "Eps12 x" "Base x * Base x" "- Base x * Base x"] one_neq_neg_one
      by auto
  qed
  ultimately show "x = 1 \<or> x = - 1"
    using square_eq_1_iff[of "Base x"] by simp
next
  assume "x = 1 \<or> x = - 1"
  then show "x * x = 1"
    by (simp, safe, simp_all)
qed

subsubsection\<open>Properties of Zero Divisors\<close>

text\<open>Unlike the reals, hyperdual numbers may have non-trivial divisors of zero as we show below.\<close>

text\<open>
  First, if the components have no non-trivial zero divisors then that behaviour is preserved on the
  base component.
\<close>
lemma divisors_base_zero:
  fixes a b :: "('a :: ring_no_zero_divisors) hyperdual"
  assumes "Base (a * b) = 0"
  shows "Base a = 0 \<or> Base b = 0"
  using assms by auto
lemma hyp_base_mult_eq_0_iff [iff]:
  fixes a b :: "('a :: ring_no_zero_divisors) hyperdual"
  shows "Base (a * b) = 0 \<longleftrightarrow> Base a = 0 \<or> Base b = 0"
  by simp

text\<open>
  However, the conditions are relaxed on the full hyperdual numbers.
  This is due to some terms vanishing in the multiplication and thus not constraining the result.
\<close>
lemma divisors_hyperdual_zero [iff]:
  fixes a b :: "('a :: ring_no_zero_divisors) hyperdual"
  shows "a * b = 0 \<longleftrightarrow> (a = 0 \<or> b = 0 \<or> (Base a = 0 \<and> Base b = 0 \<and> Eps1 a * Eps2 b = - Eps2 a * Eps1 b))"
proof
  assume mult: "a * b = 0"
  then have split: "Base a = 0 \<or> Base b = 0"
    by simp
  show "a = 0 \<or> b = 0 \<or> Base a = 0 \<and> Base b = 0 \<and> Eps1 a * Eps2 b = - Eps2 a * Eps1 b"
  proof (cases "Base a = 0")
    case aT: True
    then show ?thesis
    proof (cases "Base b = 0")
      \<comment> \<open>@{term "Base a = 0 \<and> Base b = 0"}\<close>
      case bT: True
      then have "Eps12 (a * b) = Eps1 a * Eps2 b + Eps2 a * Eps1 b"
        by (simp add: aT)
      then show ?thesis
        by (simp add: aT bT mult eq_neg_iff_add_eq_0)
    next
      \<comment> \<open>@{term "Base a = 0 \<and> Base b \<noteq> 0"}\<close>
      case bF: False
      then have e1: "Eps1 a = 0"
      proof -
        have "Eps1 (a * b) = Eps1 a * Base b"
          by (simp add: aT)
        then show ?thesis
          by (simp add: bF mult)
      qed
      moreover have e2: "Eps2 a = 0"
      proof -
        have "Eps2 (a * b) = Eps2 a * Base b"
          by (simp add: aT)
        then show ?thesis
          by (simp add: bF mult)
      qed
      moreover have "Eps12 a = 0"
      proof -
        have "Eps12 (a * b) = Eps1 a * Eps2 b + Eps2 a * Eps1 b"
          by (simp add: e1 e2 mult)
        then show ?thesis
          by (simp add: aT bF)
      qed
      ultimately show ?thesis
        by (simp add: aT)
    qed
  next
    case aF: False
    then show ?thesis
    proof (cases "Base b = 0")
      \<comment> \<open>@{term "Base a \<noteq> 0 \<and> Base b = 0"}\<close>
      case bT: True
      then have e1: "Eps1 b = 0"
      proof -
        have "Eps1 (a * b) = Base a * Eps1 b"
          by (simp add: bT)
        then show ?thesis
          by (simp add: aF mult)
      qed
      moreover have e2: "Eps2 b = 0"
      proof -
        have "Eps2 (a * b) = Base a * Eps2 b"
          by (simp add: bT)
        then show ?thesis
          by (simp add: aF mult)
      qed
      moreover have "Eps12 b = 0"
      proof -
        have "Eps12 (a * b) = Eps1 a * Eps2 b + Eps2 a * Eps1 b"
          by (simp add: e1 e2 mult)
        then show ?thesis
          by (simp add: bT aF)
      qed
      ultimately show ?thesis
        by (simp add: bT)
    next
      \<comment> \<open>@{term "Base a \<noteq> 0 \<and> Base b \<noteq> 0"}\<close>
      case bF: False
      then have "False"
        using split aF by blast
      then show ?thesis
        by simp
    qed
  qed
next
  show "a = 0 \<or> b = 0 \<or> Base a = 0 \<and> Base b = 0 \<and> Eps1 a * Eps2 b = - Eps2 a * Eps1 b \<Longrightarrow> a * b = 0"
    by (simp, auto)
qed

subsubsection\<open>Multiplication Cancellation\<close>

text\<open>
  Similarly to zero divisors, multiplication cancellation rules for hyperduals are not exactly the
  same as those for reals.
\<close>

text\<open>
  First, cancelling a common factor has a relaxed condition compared to reals.
  It only requires the common factor to have base component zero, instead of requiring the whole
  number to be zero.
\<close>
lemma hyp_mult_left_cancel [iff]:
  fixes a b c :: "('a :: ring_no_zero_divisors) hyperdual"
  assumes baseC: "Base c \<noteq> 0"
  shows "c * a = c * b \<longleftrightarrow> a = b"
proof
  assume mult: "c * a = c * b"
  show "a = b"
  proof (simp, safe)
    show base: "Base a = Base b"
      using mult mult_cancel_left baseC by simp_all
    show "Eps1 a = Eps1 b"
     and "Eps2 a = Eps2 b"
      using mult base mult_cancel_left baseC by simp_all
    then show "Eps12 a = Eps12 b"
      using mult base mult_cancel_left baseC by simp_all
  qed
next
  show "a = b \<Longrightarrow> c * a = c * b"
    by simp
qed

lemma hyp_mult_right_cancel [iff]:
  fixes a b c :: "('a :: ring_no_zero_divisors) hyperdual"
  assumes baseC: "Base c \<noteq> 0"
    shows "a * c = b * c \<longleftrightarrow> a = b"
proof
  assume mult: "a * c = b * c"
  show "a = b"
  proof (simp, safe)
    show base: "Base a = Base b"
      using mult mult_cancel_left baseC by simp_all
    show "Eps1 a = Eps1 b"
     and "Eps2 a = Eps2 b"
      using mult base mult_cancel_left baseC by simp_all
    then show "Eps12 a = Eps12 b"
      using mult base mult_cancel_left baseC by simp_all
  qed
next
  show "a = b \<Longrightarrow> a * c = b * c"
    by simp
qed

text\<open>
  Next, when a factor absorbs another there are again relaxed conditions compared to reals.
  For reals, either the absorbing factor is zero or the absorbed is the unit.
  However, with hyperduals there are more possibilities again due to terms vanishing during the
  multiplication.
\<close>
lemma hyp_mult_cancel_right1 [iff]:
  fixes a b :: "('a :: ring_1_no_zero_divisors) hyperdual"
  shows "a = b * a \<longleftrightarrow> a = 0 \<or> b = 1 \<or> (Base a = 0 \<and> Base b = 1 \<and> Eps1 b * Eps2 a = - Eps2 b * Eps1 a)"
proof
  assume mult: "a = b * a"
  show "a = 0 \<or> b = 1 \<or> (Base a = 0 \<and> Base b = 1 \<and> Eps1 b * Eps2 a = - Eps2 b * Eps1 a)"
  proof (cases "Base a = 0")
    case aT: True
    then show ?thesis
    proof (cases "Base b = 1")
      \<comment> \<open>@{term "Base a = 0 \<and> Base b = 1"}\<close>
      case bT: True
      then show ?thesis
        using aT mult add_cancel_right_right add_eq_0_iff[of "Eps1 b * Eps2 a"] times_hyperdual.simps(4)[of b a]
        by simp
    next
      \<comment> \<open>@{term "Base a = 0 \<and> Base b \<noteq> 1"}\<close>
      case bF: False
      then show ?thesis
        using aT mult by (simp, auto)
    qed
  next
    case aF: False
    then show ?thesis
    proof (cases "Base b = 1")
      \<comment> \<open>@{term "Base a \<noteq> 0 \<and> Base b = 1"}\<close>
      case bT: True
      then show ?thesis
        using aF mult by (simp, auto)
    next
      \<comment> \<open>@{term "Base a \<noteq> 0 \<and> Base b \<noteq> 1"}\<close>
      case bF: False
      then show ?thesis
        using aF mult by simp
    qed
  qed
next
  have "a = 0 \<Longrightarrow> a = b * a"
   and "b = 1 \<Longrightarrow> a = b * a"
    by simp_all
  moreover have "Base a = 0 \<and> Base b = 1 \<and> Eps1 b * Eps2 a = - Eps2 b * Eps1 a \<Longrightarrow> a = b * a"
    by simp
  ultimately show "a = 0 \<or> b = 1 \<or> (Base a = 0 \<and> Base b = 1 \<and> Eps1 b * Eps2 a = - Eps2 b * Eps1 a) \<Longrightarrow> a = b * a"
    by blast
qed
lemma hyp_mult_cancel_right2 [iff]:
  fixes a b :: "('a :: ring_1_no_zero_divisors) hyperdual"
  shows "b * a = a \<longleftrightarrow> a = 0 \<or> b = 1 \<or> (Base a = 0 \<and> Base b = 1 \<and> Eps1 b * Eps2 a = - Eps2 b * Eps1 a)"
  using hyp_mult_cancel_right1 by smt

lemma hyp_mult_cancel_left1 [iff]:
  fixes a b :: "('a :: ring_1_no_zero_divisors) hyperdual"
  shows "a = a * b \<longleftrightarrow> a = 0 \<or> b = 1 \<or> (Base a = 0 \<and> Base b = 1 \<and> Eps1 a * Eps2 b = - Eps2 a * Eps1 b)"
proof
  assume mult: "a = a * b"
  show "a = 0 \<or> b = 1 \<or> (Base a = 0 \<and> Base b = 1 \<and> Eps1 a * Eps2 b = - Eps2 a * Eps1 b)"
  proof (cases "Base a = 0")
    case aT: True
    then show ?thesis
    proof (cases "Base b = 1")
      \<comment> \<open>@{term "Base a = 0 \<and> Base b = 1"}\<close>
      case bT: True
      then show ?thesis
        using aT mult add_cancel_right_right add_eq_0_iff[of "Eps1 a * Eps2 b"] times_hyperdual.simps(4)[of a b]
        by simp
    next
      \<comment> \<open>@{term "Base a = 0 \<and> Base b \<noteq> 1"}\<close>
      case bF: False
      then show ?thesis
        using aT mult by (simp, auto)
    qed
  next
    case aF: False
    then show ?thesis
    proof (cases "Base b = 1")
      \<comment> \<open>@{term "Base a \<noteq> 0 \<and> Base b = 1"}\<close>
      case bT: True
      then show ?thesis
        using aF mult by (simp, auto)
    next
      \<comment> \<open>@{term "Base a \<noteq> 0 \<and> Base b \<noteq> 1"}\<close>
      case bF: False
      then show ?thesis
        using aF mult by simp
    qed
  qed
next
  have "a = 0 \<Longrightarrow> a = a * b"
   and "b = 1 \<Longrightarrow> a = a * b"
    by simp_all
  moreover have "Base a = 0 \<and> Base b = 1 \<and> Eps1 a * Eps2 b = - Eps2 a * Eps1 b \<Longrightarrow> a = a * b"
    by simp
  ultimately show "a = 0 \<or> b = 1 \<or> (Base a = 0 \<and> Base b = 1 \<and> Eps1 a * Eps2 b = - Eps2 a * Eps1 b) \<Longrightarrow> a = a * b"
    by blast
qed
lemma hyp_mult_cancel_left2 [iff]:
  fixes a b :: "('a :: ring_1_no_zero_divisors) hyperdual"
  shows "a * b = a \<longleftrightarrow> a = 0 \<or> b = 1 \<or> (Base a = 0 \<and> Base b = 1 \<and> Eps1 a * Eps2 b = - Eps2 a * Eps1 b)"
  using hyp_mult_cancel_left1 by smt

subsection\<open>Multiplicative Inverse and Division\<close>

text\<open>
  If the components form a ring with a multiplicative inverse then so do the hyperduals.
  The hyperdual inverse of @{term a} is defined as the solution to @{term "a * x = 1"}.
  Hyperdual division is then multiplication by divisor's inverse.

  Each component of the inverse has as denominator a power of the base component.
  Therefore this inverse is only well defined for hyperdual numbers with non-zero base components.
\<close>
instantiation hyperdual :: ("{inverse, ring_1}") inverse
begin

primcorec inverse_hyperdual
  where
    "Base (inverse a) = 1 / Base a"
  | "Eps1 (inverse a) = - Eps1 a / (Base a)^2"
  | "Eps2 (inverse a) = - Eps2 a / (Base a)^2"
  | "Eps12 (inverse a) = 2 * (Eps1 a * Eps2 a / (Base a)^3) - Eps12 a / (Base a)^2"

primcorec divide_hyperdual
  where
    "Base (divide a b) = Base a / Base b"
  | "Eps1 (divide a b) = (Eps1 a * Base b - Base a * Eps1 b) / ((Base b)^2)"
  | "Eps2 (divide a b) = (Eps2 a * Base b - Base a * Eps2 b) / ((Base b)^2)"
  | "Eps12 (divide a b) = (2 * Base a * Eps1 b * Eps2 b -
                           Base a * Base b * Eps12 b -
                           Eps1 a * Base b * Eps2 b -
                           Eps2 a * Base b * Eps1 b +
                           Eps12 a * ((Base b)^2)) / ((Base b)^3)"
instance
  by standard
end

text\<open>
  Because hyperduals have non-trivial zero divisors, they do not form a division ring and so we
  can't use the @{class division_ring} type class to establish properties of hyperdual division.
  However, if the components form a division ring as well as a commutative ring, we can prove some
  similar facts about hyperdual division inspired by @{class division_ring}.
\<close>

text\<open>Inverse is multiplicative inverse from both sides.\<close>
lemma
  fixes a :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  assumes "Base a \<noteq> 0"
  shows hyp_left_inverse [simp]: "inverse a * a = 1"
    and hyp_right_inverse [simp]: "a * inverse a = 1"
  by (simp_all add: assms power2_eq_square power3_eq_cube field_simps)

text\<open>Division is multiplication by inverse.\<close>
lemma hyp_divide_inverse:
  fixes a b :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "a / b = a * inverse b"
  by (cases "Base b = 0" ; simp add: field_simps power2_eq_square power3_eq_cube)

text\<open>Hyperdual inverse is zero when not well defined.\<close>
lemma zero_base_zero_inverse:
  fixes a :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  assumes "Base a = 0"
  shows "inverse a = 0"
  by (simp add: assms)

lemma zero_inverse_zero_base:
  fixes a :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  assumes "inverse a = 0"
  shows "Base a = 0"
  using assms right_inverse hyp_left_inverse by force

lemma hyp_inverse_zero:
  fixes a :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "(inverse a = 0) = (Base a = 0)"
  using zero_base_zero_inverse[of a] zero_inverse_zero_base[of a] by blast

text\<open>Inverse preserves invertibility.\<close>
lemma hyp_invertible_inverse:
  fixes a :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "(Base a = 0) = (Base (inverse a) = 0)"
  by (safe, simp_all add: divide_inverse)

text\<open>Inverse is the only number that satisfies the defining equation.\<close>
lemma hyp_inverse_unique:
  fixes a b :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  assumes "a * b = 1"
  shows "b = inverse a"
proof -
  have "Base a \<noteq> 0"
    using assms one_hyperdual_def of_comp_simps zero_neq_one hyp_base_mult_eq_0_iff by smt
  then show ?thesis
    by (metis assms hyp_right_inverse mult.left_commute mult.right_neutral)
qed

text\<open>Multiplicative inverse commutes with additive inverse.\<close>
lemma hyp_minus_inverse_comm:
  fixes a :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "inverse (- a) = - inverse a"
proof (cases "Base a = 0")
  case True
  then show ?thesis
    by (simp add: zero_base_zero_inverse)
next
  case False
  then show ?thesis
    by (simp, simp add: nonzero_minus_divide_right)
qed

text\<open>
  Inverse is an involution (only) where well defined.
  Counter-example for non-invertible is @{term "Hyperdual 0 0 0 0"} with inverse
  @{term "Hyperdual 0 0 0 0"} which then inverts to @{term "Hyperdual 0 0 0 0"}.
\<close>
lemma hyp_inverse_involution:
  fixes a :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  assumes "Base a \<noteq> 0"
  shows "inverse (inverse a) = a"
  by (metis assms hyp_inverse_unique hyp_right_inverse mult.commute)

lemma inverse_inverse_neq_Ex:
  "\<exists>a :: ('a :: {inverse, comm_ring_1, division_ring}) hyperdual . inverse (inverse a) \<noteq> a"
proof -
  have "\<exists>a :: 'a hyperdual . Base a = 0 \<and> a \<noteq> 0"
    by (metis (full_types) hyperdual.sel(1) hyperdual.sel(4) zero_neq_one)
  moreover have "\<And>a :: 'a hyperdual . (Base a = 0 \<and> a \<noteq> 0) \<Longrightarrow> (inverse (inverse a) \<noteq> a)"
    using hyp_inverse_zero hyp_invertible_inverse by smt
  ultimately show ?thesis
    by blast
qed

text\<open>
  Inverses of equal invertible numbers are equal.
  This includes the other direction by inverse preserving invertibility and being an involution.

  From a different point of view, inverse is injective on invertible numbers.
  The other direction for is again by inverse preserving invertibility and being an involution.
\<close>
lemma hyp_inverse_injection:
  fixes a b :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  assumes "Base a \<noteq> 0"
      and "Base b \<noteq> 0"
    shows "(inverse a = inverse b) = (a = b)"
  by (metis assms hyp_inverse_involution)

text\<open>One is its own inverse.\<close>
lemma hyp_inverse_1 [simp]:
  "inverse (1 :: ('a :: {inverse, comm_ring_1, division_ring}) hyperdual) = 1"
  using hyp_inverse_unique mult.left_neutral by metis

text\<open>Inverse distributes over multiplication (even when not well defined).\<close>
lemma hyp_inverse_mult_distrib:
  fixes a b :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "inverse (a * b) = inverse b * inverse a"
proof (cases "Base a = 0 \<or> Base b = 0")
  case True
  then show ?thesis
    by (metis hyp_base_mult_eq_0_iff mult_zero_left mult_zero_right zero_base_zero_inverse)
next
  case False
  then have "a * (b * inverse b) * inverse a = 1"
    by simp
  then have "a * b * (inverse b * inverse a) = 1"
    by (simp only: mult.assoc)
  thus ?thesis
    using hyp_inverse_unique[of "a * b" "(inverse b * inverse a)"] by simp
qed

text\<open>We derive expressions for addition and subtraction of inverses.\<close>
lemma hyp_inverse_add:
  fixes a b :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  assumes "Base a \<noteq> 0"
      and "Base b \<noteq> 0"
    shows "inverse a + inverse b = inverse a * (a + b) * inverse b"
  by (simp add: assms distrib_left mult.commute semiring_normalization_rules(18) add.commute)

lemma hyp_inverse_diff:
  fixes a b :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  assumes a: "Base a \<noteq> 0"
      and b: "Base b \<noteq> 0"
    shows "inverse a - inverse b = inverse a * (b - a) * inverse b"
proof -
  have x: "inverse a - inverse b = inverse b * (inverse a * b - 1)"
    by (simp add: b mult.left_commute right_diff_distrib')
  show ?thesis
    by (simp add: x a mult.commute right_diff_distrib')
qed

text\<open>Division is one only when dividing by self.\<close>
lemma hyp_divide_self:
  fixes a b :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  assumes "Base b \<noteq> 0"
    shows "a / b = 1 \<longleftrightarrow> a = b"
  by (metis assms hyp_divide_inverse hyp_inverse_unique hyp_right_inverse mult.commute)

text\<open>Taking inverse is the same as division of one, even when not invertible.\<close>
lemma hyp_inverse_divide_1 [divide_simps]:
  fixes a :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "inverse a = 1 / a"
  by (simp add: hyp_divide_inverse)

text\<open>Division distributes over addition and subtraction.\<close>
lemma hyp_add_divide_distrib:
  fixes a b c :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "(a + b) / c = a/c + b/c"
  by (simp add: distrib_right hyp_divide_inverse)

lemma hyp_diff_divide_distrib:
  fixes a b c :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "(a - b) / c = a / c - b / c"
  by (simp add: left_diff_distrib hyp_divide_inverse)

text\<open>Multiplication associates with division.\<close>
lemma hyp_times_divide_assoc [simp]:
  fixes a b c :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "a * (b / c) = (a * b) / c"
  by (simp add: hyp_divide_inverse mult.assoc)

text\<open>Additive inverse commutes with division, because it is multiplication by inverse.\<close>
lemma hyp_divide_minus_left [simp]:
  fixes a b :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "(-a) / b = - (a / b)"
  by (simp add: hyp_divide_inverse)

lemma hyp_divide_minus_right [simp]:
  fixes a b :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "a / (-b) = - (a / b)"
  by (simp add: hyp_divide_inverse hyp_minus_inverse_comm)

text\<open>Additive inverses on both sides of division cancel out.\<close>
lemma hyp_minus_divide_minus:
  fixes a b :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "(-a) / (-b) = a / b"
  by simp

text\<open>We can multiply both sides of equations by an invertible denominator.\<close>
lemma hyp_denominator_eliminate [divide_simps]:
  fixes a b c :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  assumes "Base c \<noteq> 0"
    shows "a = b / c \<longleftrightarrow> a * c = b"
  by (metis assms hyp_divide_self hyp_times_divide_assoc mult.commute mult.right_neutral)

text\<open>We can move addition and subtraction to a common denominator in the following ways:\<close>
lemma hyp_add_divide_eq_iff:
  fixes x y z :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  assumes "Base z \<noteq> 0"
  shows "x + y / z = (x * z + y) / z"
  by (metis assms hyp_add_divide_distrib hyp_denominator_eliminate)

text\<open>Result of division by non-invertible number is not invertible.\<close>
lemma hyp_divide_base_zero [simp]:
  fixes a b :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  assumes "Base b = 0"
    shows "Base (a / b) = 0"
  by (simp add: assms)

text\<open>Division of self is 1 when invertible, 0 otherwise.\<close>
lemma hyp_divide_self_if [simp]:
  fixes a :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "a / a = (if Base a = 0 then 0 else 1)"
  by (metis hyp_divide_inverse zero_base_zero_inverse hyp_divide_self mult_zero_right)

text\<open>Repeated division is division by product of the denominators.\<close>
lemma hyp_denominators_merge:
  fixes a b c :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "(a / b) / c = a / (c * b)"
  using hyp_inverse_mult_distrib[of c b]
  by (simp add: hyp_divide_inverse mult.assoc)

text\<open>Finally, we derive general simplifications for division with addition and subtraction.\<close>
lemma hyp_add_divide_eq_if_simps [divide_simps]:
  fixes a b z :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "a + b / z = (if Base z = 0 then a else (a * z + b) / z)"
    and "a / z + b = (if Base z = 0 then b else (a + b * z) / z)"
    and "- (a / z) + b = (if Base z = 0 then b else (-a + b * z) / z)"
    and "a - b / z = (if Base z = 0 then a else (a * z - b) / z)"
    and "a / z - b = (if Base z = 0 then -b else (a - b * z) / z)"
    and "- (a / z) - b = (if Base z = 0 then -b else (- a - b * z) / z)"
  by (simp_all add: algebra_simps hyp_add_divide_eq_iff hyp_divide_inverse zero_base_zero_inverse)

lemma hyp_divide_eq_eq [divide_simps]:
  fixes a b c :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "b / c = a \<longleftrightarrow> (if Base c \<noteq> 0 then b = a * c else a = 0)"
  by (metis hyp_divide_inverse hyp_denominator_eliminate mult_not_zero zero_base_zero_inverse)

lemma hyp_eq_divide_eq [divide_simps]:
  fixes a b c :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "a = b / c \<longleftrightarrow> (if Base c \<noteq> 0 then a * c = b else a = 0)"
  by (metis hyp_divide_eq_eq)

lemma hyp_minus_divide_eq_eq [divide_simps]:
  fixes a b c :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "- (b / c) = a \<longleftrightarrow> (if Base c \<noteq> 0 then - b = a * c else a = 0)"
  by (metis hyp_divide_minus_left hyp_eq_divide_eq)

lemma hyp_eq_minus_divide_eq [divide_simps]:
  fixes a b c :: "('a :: {inverse, comm_ring_1, division_ring}) hyperdual"
  shows "a = - (b / c) \<longleftrightarrow> (if Base c \<noteq> 0 then a * c = - b else a = 0)"
  by (metis hyp_minus_divide_eq_eq)

subsection \<open>Real Scaling, Real Vector and Real Algebra\<close>

text\<open>
  If the components can be scaled by real numbers then so can the hyperduals.
  We define the scaling pointwise.
\<close>
instantiation hyperdual :: (scaleR) scaleR
begin

primcorec scaleR_hyperdual
  where
    "Base (f *\<^sub>R x) = f *\<^sub>R Base x"
  | "Eps1 (f *\<^sub>R x) = f *\<^sub>R Eps1 x"
  | "Eps2 (f *\<^sub>R x) = f *\<^sub>R Eps2 x"
  | "Eps12 (f *\<^sub>R x) = f *\<^sub>R Eps12 x"

instance
  by standard
end

text\<open>If the components form a real vector space then so do the hyperduals.\<close>
instance hyperdual :: (real_vector) real_vector
  by standard (simp_all add: algebra_simps)

text\<open>If the components form a real algebra then so do the hyperduals\<close>
instance hyperdual :: (real_algebra_1) real_algebra_1
  by standard (simp_all add: algebra_simps)

text\<open>
  If the components are reals then @{const of_real} matches our embedding @{const of_comp}, and
  @{const scaleR} matches our scalar product @{const scaleH}.
\<close>
lemma "of_real = of_comp"
  by (standard, simp add: of_real_def)

lemma scaleR_eq_scale:
  "(*\<^sub>R) = (*\<^sub>H)"
  by (standard, standard, simp)

text\<open>Hyperdual scalar product @{const scaleH} is compatible with @{const scaleR}.\<close>
lemma scaleH_scaleR:
  fixes a :: "'a :: real_algebra_1"
    and b :: "'a hyperdual"
  shows "(f *\<^sub>R a) *\<^sub>H b = f *\<^sub>R a *\<^sub>H b"
    and "a *\<^sub>H f *\<^sub>R b = f *\<^sub>R a *\<^sub>H b"
  by simp_all

subsection\<open>Real Inner Product and Real-Normed Vector Space\<close>

text\<open>
  We now take a closer look at hyperduals as a real vector space.

  If the components form a real inner product space then we can define one on the hyperduals as the
  sum of componentwise inner products.
  The norm is then defined as the square root of that inner product.
  We define signum, distance, uniformity and openness similarly as they are defined for complex
  numbers.
\<close>
instantiation hyperdual :: (real_inner) real_inner
begin

definition inner_hyperdual :: "'a hyperdual \<Rightarrow> 'a hyperdual \<Rightarrow> real"
  where "x \<bullet> y = Base x \<bullet> Base y + Eps1 x \<bullet> Eps1 y + Eps2 x \<bullet> Eps2 y + Eps12 x \<bullet> Eps12 y"

definition norm_hyperdual :: "'a hyperdual \<Rightarrow> real"
  where "norm_hyperdual x = sqrt (x \<bullet> x)"

definition sgn_hyperdual :: "'a hyperdual \<Rightarrow> 'a hyperdual"
  where "sgn_hyperdual x = x /\<^sub>R norm x"

definition dist_hyperdual :: "'a hyperdual \<Rightarrow> 'a hyperdual \<Rightarrow> real"
  where "dist_hyperdual a b = norm(a - b)"

definition uniformity_hyperdual :: "('a hyperdual \<times> 'a hyperdual) filter"
  where "uniformity_hyperdual = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition open_hyperdual :: "('a hyperdual) set \<Rightarrow> bool"
  where  "open_hyperdual U \<longleftrightarrow> (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

instance
proof
  fix x y z :: "'a hyperdual"
  fix U :: "('a hyperdual) set"
  fix r :: real

  show "dist x y = norm (x - y)"
    by (simp add: dist_hyperdual_def)
  show "sgn x = x /\<^sub>R norm x"
    by (simp add: sgn_hyperdual_def)
  show "uniformity = (INF e\<in>{0<..}. principal {(x :: 'a hyperdual, y). dist x y < e})"
    using uniformity_hyperdual_def by blast
  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)"
    using open_hyperdual_def by blast
  show  "x \<bullet> y = y \<bullet> x"
    by (simp add: inner_hyperdual_def inner_commute)
  show "(x + y) \<bullet> z = x \<bullet> z + y \<bullet> z"
    and "r *\<^sub>R x \<bullet> y = r * (x \<bullet> y)"
    and "0 \<le> x \<bullet> x"
    and "norm x = sqrt (x \<bullet> x)"
    by (simp_all add: inner_hyperdual_def norm_hyperdual_def algebra_simps)
  show "(x \<bullet> x = 0) = (x = 0)"
  proof
    assume "x \<bullet> x = 0"
    then have "Base x \<bullet> Base x + Eps1 x \<bullet> Eps1 x + Eps2 x \<bullet> Eps2 x + Eps12 x \<bullet> Eps12 x = 0"
      by (simp add: inner_hyperdual_def)
    then have "Base x = 0 \<and> Eps1 x = 0 \<and> Eps2 x = 0 \<and> Eps12 x = 0"
      using inner_gt_zero_iff inner_ge_zero add_nonneg_nonneg
      by smt
    then show "x = 0"
      by simp
  next
    assume "x = 0"
    then show "x \<bullet> x = 0"
      by (simp add: inner_hyperdual_def)
  qed
qed
end

text\<open>
  We then show that with this norm hyperduals with components that form a real normed algebra do not
  themselves form a normed algebra, by counter-example to the assumption that class adds.
\<close>
(* Components must be real_inner for hyperduals to have a norm *)
(* Components must be real_normed_algebra_1 to know |1| = 1, because we need some element with known
    norm of its square. Otherwise we would need the precise definition of the norm. *)
lemma not_normed_algebra:
  shows "\<not>(\<forall>x y :: ('a :: {real_normed_algebra_1, real_inner}) hyperdual . norm (x * y) \<le> norm x * norm y)"
proof -
  have "norm (Hyperdual (1 :: 'a) 1 1 1) = 2"
    by (simp add: norm_hyperdual_def inner_hyperdual_def dot_square_norm)
  moreover have "(Hyperdual (1 :: 'a) 1 1 1) * (Hyperdual 1 1 1 1) = Hyperdual 1 2 2 4"
    by (simp add: hyperdual.expand)
  moreover have "norm (Hyperdual (1 :: 'a) 2 2 4) > 4"
    by (simp add: norm_hyperdual_def inner_hyperdual_def dot_square_norm)
  ultimately have "\<exists>x y :: 'a hyperdual . norm (x * y) > norm x * norm y"
    by (smt power2_eq_square real_sqrt_four real_sqrt_pow2)
  then show ?thesis
    by (simp add: not_le)
qed

subsection\<open>Euclidean Space\<close>

text\<open>
  Next we define a basis for the space, consisting of four elements one for each component with \<open>1\<close>
  in the relevant component and \<open>0\<close> elsewhere.
\<close>
definition ba :: "('a :: zero_neq_one) hyperdual"
  where "ba = Hyperdual 1 0 0 0"
definition e1 :: "('a :: zero_neq_one) hyperdual"
  where "e1 = Hyperdual 0 1 0 0"
definition e2 :: "('a :: zero_neq_one) hyperdual"
  where "e2 = Hyperdual 0 0 1 0"
definition e12 :: "('a :: zero_neq_one) hyperdual"
  where "e12 = Hyperdual 0 0 0 1"

lemmas hyperdual_bases = ba_def e1_def e2_def e12_def

text\<open>
  Using the constructor @{const Hyperdual} is equivalent to using the linear combination with
  coefficients the relevant arguments.
\<close>
lemma Hyperdual_eq:
  fixes a b c d :: "'a :: ring_1"
  shows "Hyperdual a b c d = a *\<^sub>H ba + b *\<^sub>H e1 + c *\<^sub>H e2 + d *\<^sub>H e12"
  by (simp add: hyperdual_bases)

text\<open>Projecting from the combination returns the relevant coefficient:\<close>
lemma hyperdual_comb_sel [simp]:
  fixes a b c d :: "'a :: ring_1"
  shows "Base (a *\<^sub>H ba + b *\<^sub>H e1 + c *\<^sub>H e2 + d *\<^sub>H e12) = a"
    and "Eps1 (a *\<^sub>H ba + b *\<^sub>H e1 + c *\<^sub>H e2 + d *\<^sub>H e12) = b"
    and "Eps2 (a *\<^sub>H ba + b *\<^sub>H e1 + c *\<^sub>H e2 + d *\<^sub>H e12) = c"
    and "Eps12 (a *\<^sub>H ba + b *\<^sub>H e1 + c *\<^sub>H e2 + d *\<^sub>H e12) = d"
  using Hyperdual_eq hyperdual.sel by metis+

text\<open>Any hyperdual number is a linear combination of these four basis elements.\<close>
lemma hyperdual_linear_comb:
  fixes x :: "('a :: ring_1) hyperdual"
  obtains a b c d :: 'a where "x = a *\<^sub>H ba + b *\<^sub>H e1 + c *\<^sub>H e2 + d *\<^sub>H e12"
  using hyperdual.exhaust Hyperdual_eq by metis

text\<open>
  The linear combination expressing any hyperdual number has as coefficients the projections of
  that number onto the relevant basis element.
\<close>
lemma hyperdual_eq:
  fixes x :: "('a :: ring_1) hyperdual"
  shows "x = Base x *\<^sub>H ba + Eps1 x *\<^sub>H e1 + Eps2 x *\<^sub>H e2 + Eps12 x *\<^sub>H e12"
  using Hyperdual_eq hyperdual.collapse by smt

text\<open>Equality of hyperduals as linear combinations is equality of corresponding components.\<close>
lemma hyperdual_eq_parts_cancel [simp]:
  fixes a b c d :: "'a :: ring_1"
  shows "(a *\<^sub>H ba + b *\<^sub>H e1 + c *\<^sub>H e2 + d *\<^sub>H e12 = a' *\<^sub>H ba + b' *\<^sub>H e1 + c' *\<^sub>H e2 + d' *\<^sub>H e12) \<equiv>
         (a = a' \<and> b = b' \<and> c = c' \<and> d = d')"
  by (smt Hyperdual_eq hyperdual.inject)

lemma scaleH_cancel [simp]:
  fixes a b :: "'a :: ring_1"
  shows "(a *\<^sub>H ba = b *\<^sub>H ba) \<equiv> (a = b)"
    and "(a *\<^sub>H e1 = b *\<^sub>H e1) \<equiv> (a = b)"
    and "(a *\<^sub>H e2 = b *\<^sub>H e2) \<equiv> (a = b)"
    and "(a *\<^sub>H e12 = b *\<^sub>H e12) \<equiv> (a = b)"
  by (auto simp add: hyperdual_bases)+

text\<open>We can now also show that the multiplication we use indeed has the hyperdual units nilpotent.\<close>
(* The components must have multiplication and addition for this to be defined and have an absorbing
   zero to prove it. *)
lemma epsilon_squares [simp]:
  "(e1 :: ('a :: ring_1) hyperdual) * e1 = 0"
  "(e2 :: ('a :: ring_1) hyperdual) * e2 = 0"
  "(e12 :: ('a :: ring_1) hyperdual) * e12 = 0"
  by (simp_all add: hyperdual_bases)

text\<open>However none of the hyperdual units is zero.\<close>
lemma hyperdual_bases_nonzero [simp]:
  "ba \<noteq> 0"
  "e1 \<noteq> 0"
  "e2 \<noteq> 0"
  "e12 \<noteq> 0"
  by (simp_all add: hyperdual_bases)

text\<open>Hyperdual units are orthogonal.\<close>
lemma hyperdual_bases_ortho [simp]:
  "(ba :: ('a :: {real_inner,zero_neq_one}) hyperdual) \<bullet> e1 = 0"
  "(ba :: ('a :: {real_inner,zero_neq_one}) hyperdual) \<bullet> e2 = 0"
  "(ba :: ('a :: {real_inner,zero_neq_one}) hyperdual) \<bullet> e12 = 0"
  "(e1 :: ('a :: {real_inner,zero_neq_one}) hyperdual) \<bullet> e2 = 0"
  "(e1 :: ('a :: {real_inner,zero_neq_one}) hyperdual) \<bullet> e12 = 0"
  "(e2 :: ('a :: {real_inner,zero_neq_one}) hyperdual) \<bullet> e12 = 0"
  by (simp_all add: hyperdual_bases inner_hyperdual_def)

text\<open>Hyperdual units of norm equal to 1.\<close>
lemma hyperdual_bases_norm [simp]:
  "(ba :: ('a :: {real_inner,real_normed_algebra_1}) hyperdual) \<bullet> ba = 1"
  "(e1 :: ('a :: {real_inner,real_normed_algebra_1}) hyperdual) \<bullet> e1 = 1"
  "(e2 :: ('a :: {real_inner,real_normed_algebra_1}) hyperdual) \<bullet> e2 = 1"
  "(e12 :: ('a :: {real_inner,real_normed_algebra_1}) hyperdual) \<bullet> e12 = 1"
  by (simp_all add: hyperdual_bases inner_hyperdual_def norm_eq_1[symmetric])

text\<open>We can also express earlier operations in terms of the linear combination.\<close>
lemma add_hyperdual_parts:
  fixes a b c d :: "'a :: ring_1"
  shows "(a *\<^sub>H ba + b *\<^sub>H e1 + c *\<^sub>H e2 + d *\<^sub>H e12) + (a' *\<^sub>H ba + b' *\<^sub>H e1 + c' *\<^sub>H e2 + d' *\<^sub>H e12) =
         (a + a') *\<^sub>H ba + (b + b') *\<^sub>H e1 + (c + c') *\<^sub>H e2 + (d + d') *\<^sub>H e12"
  by (simp add: scaleH_add(1))

lemma times_hyperdual_parts:
  fixes a b c d :: "'a :: ring_1"
  shows "(a *\<^sub>H ba + b *\<^sub>H e1 + c *\<^sub>H e2 + d *\<^sub>H e12) * (a' *\<^sub>H ba + b' *\<^sub>H e1 + c' *\<^sub>H e2 + d' *\<^sub>H e12) =
         (a * a') *\<^sub>H ba + (a * b' + b * a') *\<^sub>H e1 + (a * c' + c * a') *\<^sub>H e2 + (a * d' + b * c' + c * b' + d * a') *\<^sub>H e12"
  by (simp add: hyperdual_bases)

lemma inverse_hyperdual_parts:
  fixes a b c d :: "'a :: {inverse,ring_1}"
  shows "inverse (a *\<^sub>H ba + b *\<^sub>H e1 + c *\<^sub>H e2 + d *\<^sub>H e12) =
         (1 / a) *\<^sub>H ba + (- b / a ^ 2) *\<^sub>H e1 + (- c / a ^ 2) *\<^sub>H e2 + (2 * (b * c / a ^ 3) - d / a ^ 2) *\<^sub>H e12"
  by (simp add: hyperdual_bases)

text\<open>
  Next we show that hyperduals form a euclidean space with the help of the basis we defined earlier
  and the above inner product if the component is an instance of @{class euclidean_space} and
  @{class real_algebra_1}.
  The basis of this space is each of the basis elements we defined scaled by each of the basis
  elements of the component type, representing the expansion of the space for each component of the
  hyperdual numbers.
\<close>
instantiation hyperdual :: ("{euclidean_space, real_algebra_1}") euclidean_space
begin

definition Basis_hyperdual :: "('a hyperdual) set"
  where "Basis = (\<Union>i\<in>{ba,e1,e2,e12}. (\<lambda>u. u *\<^sub>H i) ` Basis)"

instance
proof
  fix x y z :: "'a hyperdual"
  show "(Basis :: ('a hyperdual) set) \<noteq> {}"
    and "finite (Basis :: ('a hyperdual) set)"
    by (simp_all add: Basis_hyperdual_def)
  show "x \<in> Basis \<Longrightarrow> y \<in> Basis \<Longrightarrow> x \<bullet> y = (if x = y then 1 else 0)"
    unfolding Basis_hyperdual_def inner_hyperdual_def hyperdual_bases
    by (auto dest: inner_not_same_Basis)
  show "(\<forall>u\<in>Basis. x \<bullet> u = 0) = (x = 0)"
    by (auto simp add: Basis_hyperdual_def ball_Un inner_hyperdual_def hyperdual_bases euclidean_all_zero_iff)
qed
end

subsection\<open>Bounded Linear Projections\<close>

text\<open>Now we can show that each projection to a basis element is a bounded linear map.\<close>
lemma bounded_linear_Base: "bounded_linear Base"
proof
  show "\<And>b1 b2. Base (b1 + b2) = Base b1 + Base b2"
    by simp
  show "\<And>r b. Base (r *\<^sub>R b) = r *\<^sub>R Base b"
    by simp
  have "\<forall>x. norm (Base x) \<le> norm x"
    by (simp add: inner_hyperdual_def norm_eq_sqrt_inner)
  then show "\<exists>K. \<forall>x. norm (Base x) \<le> norm x * K"
    by (metis mult.commute mult.left_neutral)
qed
lemma bounded_linear_Eps1: "bounded_linear Eps1"
proof
  show "\<And>b1 b2. Eps1 (b1 + b2) = Eps1 b1 + Eps1 b2"
    by simp
  show "\<And>r b. Eps1 (r *\<^sub>R b) = r *\<^sub>R Eps1 b"
    by simp
  have "\<forall>x. norm (Eps1 x) \<le> norm x"
    by (simp add: inner_hyperdual_def norm_eq_sqrt_inner)
  then show "\<exists>K. \<forall>x. norm (Eps1 x) \<le> norm x * K"
    by (metis mult.commute mult.left_neutral)
qed
lemma bounded_linear_Eps2: "bounded_linear Eps2"
proof
  show "\<And>b1 b2. Eps2 (b1 + b2) = Eps2 b1 + Eps2 b2"
    by simp
  show "\<And>r b. Eps2 (r *\<^sub>R b) = r *\<^sub>R Eps2 b"
    by simp
  have "\<forall>x. norm (Eps2 x) \<le> norm x"
    by (simp add: inner_hyperdual_def norm_eq_sqrt_inner)
  then show "\<exists>K. \<forall>x. norm (Eps2 x) \<le> norm x * K"
    by (metis mult.commute mult.left_neutral)
qed
lemma bounded_linear_Eps12: "bounded_linear Eps12"
proof
  show "\<And>b1 b2. Eps12 (b1 + b2) = Eps12 b1 + Eps12 b2"
    by simp
  show "\<And>r b. Eps12 (r *\<^sub>R b) = r *\<^sub>R Eps12 b"
    by simp
  have "\<forall>x. norm (Eps12 x) \<le> norm x"
    by (simp add: inner_hyperdual_def norm_eq_sqrt_inner)
  then show "\<exists>K. \<forall>x. norm (Eps12 x) \<le> norm x * K"
    by (metis mult.commute mult.left_neutral)
qed

text\<open>
  This bounded linearity gives us a range of useful theorems about limits, convergence and
  derivatives of these projections.
\<close>
lemmas tendsto_Base = bounded_linear.tendsto[OF bounded_linear_Base]
lemmas tendsto_Eps1 = bounded_linear.tendsto[OF bounded_linear_Eps1]
lemmas tendsto_Eps2 = bounded_linear.tendsto[OF bounded_linear_Eps2]
lemmas tendsto_Eps12 = bounded_linear.tendsto[OF bounded_linear_Eps12]

lemmas has_derivative_Base = bounded_linear.has_derivative[OF bounded_linear_Base]
lemmas has_derivative_Eps1 = bounded_linear.has_derivative[OF bounded_linear_Eps1]
lemmas has_derivative_Eps2 = bounded_linear.has_derivative[OF bounded_linear_Eps2]
lemmas has_derivative_Eps12 = bounded_linear.has_derivative[OF bounded_linear_Eps12]

subsection\<open>Convergence\<close>
lemma inner_mult_le_mult_inner:
  fixes a b :: "'a :: {real_inner,real_normed_algebra}"
  shows "((a * b) \<bullet> (a * b)) \<le> (a \<bullet> a) * (b \<bullet> b)"
  by (metis real_sqrt_le_iff norm_eq_sqrt_inner real_sqrt_mult norm_mult_ineq)

lemma bounded_bilinear_scaleH:
  "bounded_bilinear ((*\<^sub>H) :: ('a :: {real_normed_algebra_1, real_inner}) \<Rightarrow> 'a hyperdual \<Rightarrow> 'a hyperdual)"
proof (auto simp add: bounded_bilinear_def scaleH_add scaleH_scaleR del:exI intro!:exI)
  fix a :: 'a
  and b :: "'a hyperdual"
  have "norm (a *\<^sub>H b) = sqrt ((a * Base b) \<bullet> (a * Base b) + (a * Eps1 b) \<bullet> (a * Eps1 b) + (a * Eps2 b) \<bullet> (a * Eps2 b) + (a * Eps12 b) \<bullet> (a * Eps12 b))"
    by (simp add: norm_eq_sqrt_inner inner_hyperdual_def)
  moreover have "norm a * norm b = sqrt (a \<bullet> a * (Base b \<bullet> Base b + Eps1 b \<bullet> Eps1 b + Eps2 b \<bullet> Eps2 b + Eps12 b \<bullet> Eps12 b))"
    by (simp add: norm_eq_sqrt_inner inner_hyperdual_def real_sqrt_mult)
  moreover have "sqrt ((a * Base b) \<bullet> (a * Base b) + (a * Eps1 b) \<bullet> (a * Eps1 b) + (a * Eps2 b) \<bullet> (a * Eps2 b) + (a * Eps12 b) \<bullet> (a * Eps12 b)) \<le>
                 sqrt (a \<bullet> a * (Base b \<bullet> Base b + Eps1 b \<bullet> Eps1 b + Eps2 b \<bullet> Eps2 b + Eps12 b \<bullet> Eps12 b))"
    by (simp add: distrib_left add_mono inner_mult_le_mult_inner)
  ultimately show "norm (a *\<^sub>H b) \<le> norm a * norm b * 1"
    by simp
qed

lemmas tendsto_scaleH = bounded_bilinear.tendsto[OF bounded_bilinear_scaleH]

text\<open>
  We describe how limits behave for general hyperdual-valued functions.

  First we prove that we can go from convergence of the four component functions to the convergence
  of the hyperdual-valued function whose components they define.
\<close>
lemma tendsto_Hyperdual:
  fixes f :: "'a \<Rightarrow> ('b :: {real_normed_algebra_1, real_inner})"
  assumes "(f \<longlongrightarrow> a) F"
      and "(g \<longlongrightarrow> b) F"
      and "(h \<longlongrightarrow> c) F"
      and "(i \<longlongrightarrow> d) F"
    shows "((\<lambda>x. Hyperdual (f x) (g x) (h x) (i x)) \<longlongrightarrow> Hyperdual a b c d) F"
proof -
  have "((\<lambda>x. (f x) *\<^sub>H ba) \<longlongrightarrow> a *\<^sub>H ba) F"
       "((\<lambda>x. (g x) *\<^sub>H e1) \<longlongrightarrow> b *\<^sub>H e1) F"
       "((\<lambda>x. (h x) *\<^sub>H e2) \<longlongrightarrow> c *\<^sub>H e2) F"
       "((\<lambda>x. (i x) *\<^sub>H e12) \<longlongrightarrow> d *\<^sub>H e12) F"
    by (rule tendsto_scaleH[OF _ tendsto_const], rule assms)+
  then have "((\<lambda>x. (f x) *\<^sub>H ba + (g x) *\<^sub>H e1 + (h x) *\<^sub>H e2 + (i x) *\<^sub>H e12) \<longlongrightarrow>
             a *\<^sub>H ba + b *\<^sub>H e1 + c *\<^sub>H e2 + d *\<^sub>H e12) F"
    by (rule tendsto_add[OF tendsto_add[OF tendsto_add]] ; assumption)
  then show ?thesis
    by (simp add: Hyperdual_eq)
qed

text\<open>
  Next we complete the equivalence by proving the other direction, from convergence of a
  hyperdual-valued function to the convergence of the projected component functions.
\<close>
lemma tendsto_hyperdual_iff:
  fixes f :: "'a \<Rightarrow> ('b :: {real_normed_algebra_1, real_inner}) hyperdual"
  shows "(f \<longlongrightarrow> x) F \<longleftrightarrow>
    ((\<lambda>x. Base (f x)) \<longlongrightarrow> Base x) F \<and>
    ((\<lambda>x. Eps1 (f x)) \<longlongrightarrow> Eps1 x) F \<and>
    ((\<lambda>x. Eps2 (f x)) \<longlongrightarrow> Eps2 x) F \<and>
    ((\<lambda>x. Eps12 (f x)) \<longlongrightarrow> Eps12 x) F"
proof safe
  assume "(f \<longlongrightarrow> x) F"
  then show "((\<lambda>x. Base (f x)) \<longlongrightarrow> Base x) F"
        and "((\<lambda>x. Eps1 (f x)) \<longlongrightarrow> Eps1 x) F"
        and "((\<lambda>x. Eps2 (f x)) \<longlongrightarrow> Eps2 x) F"
        and "((\<lambda>x. Eps12 (f x)) \<longlongrightarrow> Eps12 x) F"
    by (simp_all add: tendsto_Base tendsto_Eps1 tendsto_Eps2 tendsto_Eps12)
next
  assume "((\<lambda>x. Base (f x)) \<longlongrightarrow> Base x) F"
     and "((\<lambda>x. Eps1 (f x)) \<longlongrightarrow> Eps1 x) F"
     and "((\<lambda>x. Eps2 (f x)) \<longlongrightarrow> Eps2 x) F"
     and "((\<lambda>x. Eps12 (f x)) \<longlongrightarrow> Eps12 x) F"
  then show "(f \<longlongrightarrow> x) F"
    using tendsto_Hyperdual[of "\<lambda>x. Base (f x)" "Base x" F "\<lambda>x. Eps1 (f x)" "Eps1 x" "\<lambda>x. Eps2 (f x)" "Eps2 x" "\<lambda>x. Eps12 (f x)" "Eps12 x"]
    by simp
qed

subsection\<open>Derivatives\<close>

text\<open>
  We describe how derivatives of hyperdual-valued functions behave.
  Due to hyperdual numbers not forming a normed field, the derivative relation we must use is the
  general Fréchet derivative @{const has_derivative}.

  The left to right implication of the following equivalence is easily proved by the known
  derivative behaviour of the projections.
  The other direction is more difficult, because we have to construct the two requirements of the
  @{const has_derivative} relation, the limit and the bounded linearity of the derivative.
  While the limit is simple to construct from the component functions by previous lemma, the bounded
  linearity is more involved.
\<close>
(* The derivative of a hyperdual function is composed of the derivatives of its coefficient functions *)
lemma has_derivative_hyperdual_iff:
  fixes f :: "('a :: real_normed_vector) \<Rightarrow> ('b :: {real_normed_algebra_1, real_inner}) hyperdual"
  shows "(f has_derivative Df) F \<longleftrightarrow>
    ((\<lambda>x. Base (f x)) has_derivative (\<lambda>x. Base (Df x))) F \<and>
    ((\<lambda>x. Eps1 (f x)) has_derivative (\<lambda>x. Eps1 (Df x))) F \<and>
    ((\<lambda>x. Eps2 (f x)) has_derivative (\<lambda>x. Eps2 (Df x))) F \<and>
    ((\<lambda>x. Eps12 (f x)) has_derivative (\<lambda>x. Eps12 (Df x))) F"
proof safe
  \<comment> \<open>Left to Right\<close>
  assume assm: "(f has_derivative Df) F"
  show "((\<lambda>x. Base (f x)) has_derivative (\<lambda>x. Base (Df x))) F"
    using assm has_derivative_Base by blast
  show "((\<lambda>x. Eps1 (f x)) has_derivative (\<lambda>x. Eps1 (Df x))) F"
    using assm has_derivative_Eps1 by blast
  show "((\<lambda>x. Eps2 (f x)) has_derivative (\<lambda>x. Eps2 (Df x))) F"
    using assm has_derivative_Eps2 by blast
  show "((\<lambda>x. Eps12 (f x)) has_derivative (\<lambda>x. Eps12 (Df x))) F"
    using assm has_derivative_Eps12 by blast
next
  \<comment> \<open>Right to Left\<close>
  assume assm:
    "((\<lambda>x. Base (f x)) has_derivative (\<lambda>x. Base (Df x))) F"
    "((\<lambda>x. Eps1 (f x)) has_derivative (\<lambda>x. Eps1 (Df x))) F"
    "((\<lambda>x. Eps2 (f x)) has_derivative (\<lambda>x. Eps2 (Df x))) F"
    "((\<lambda>x. Eps12 (f x)) has_derivative (\<lambda>x. Eps12 (Df x))) F"

  \<comment> \<open>First prove the limit from component function limits\<close>
  have "((\<lambda>y. Base (((f y - f (Lim F (\<lambda>x. x))) - Df (y - Lim F (\<lambda>x. x))) /\<^sub>R norm (y - Lim F (\<lambda>x. x)))) \<longlongrightarrow> Base 0) F"
    using assm has_derivative_def[of "(\<lambda>x. Base (f x))" "(\<lambda>x. Base (Df x))" F] by simp
  moreover have "((\<lambda>y. Eps1 (((f y - f (Lim F (\<lambda>x. x))) - Df (y - Lim F (\<lambda>x. x))) /\<^sub>R norm (y - Lim F (\<lambda>x. x)))) \<longlongrightarrow> Base 0) F"
    using assm has_derivative_def[of "(\<lambda>x. Eps1 (f x))" "(\<lambda>x. Eps1 (Df x))" F] by simp
  moreover have "((\<lambda>y. Eps2 (((f y - f (Lim F (\<lambda>x. x))) - Df (y - Lim F (\<lambda>x. x))) /\<^sub>R norm (y - Lim F (\<lambda>x. x)))) \<longlongrightarrow> Base 0) F"
    using assm has_derivative_def[of "(\<lambda>x. Eps2 (f x))" "(\<lambda>x. Eps2 (Df x))" F] by simp
  moreover have "((\<lambda>y. Eps12 (((f y - f (Lim F (\<lambda>x. x))) - Df (y - Lim F (\<lambda>x. x))) /\<^sub>R norm (y - Lim F (\<lambda>x. x)))) \<longlongrightarrow> Base 0) F"
    using assm has_derivative_def[of "(\<lambda>x. Eps12 (f x))" "(\<lambda>x. Eps12 (Df x))" F] by simp
  ultimately have "((\<lambda>y. ((f y - f (Lim F (\<lambda>x. x))) - Df (y - Lim F (\<lambda>x. x))) /\<^sub>R norm (y - Lim F (\<lambda>x. x))) \<longlongrightarrow> 0) F"
    by (simp add: tendsto_hyperdual_iff)

  \<comment> \<open>Next prove bounded linearity of the composed derivative by proving each of that class'
      assumptions from bounded linearity of the component derivatives\<close>
  moreover have "bounded_linear Df"
  proof
    have bl:
      "bounded_linear (\<lambda>x. Base (Df x))"
      "bounded_linear (\<lambda>x. Eps1 (Df x))"
      "bounded_linear (\<lambda>x. Eps2 (Df x))"
      "bounded_linear (\<lambda>x. Eps12 (Df x))"
      using assm has_derivative_def by blast+
    then have "linear (\<lambda>x. Base (Df x))"
     and "linear (\<lambda>x. Eps1 (Df x))"
     and "linear (\<lambda>x. Eps2 (Df x))"
     and "linear (\<lambda>x. Eps12 (Df x))"
      using bounded_linear.linear by blast+
    then show "\<And>x y. Df (x + y) = Df x + Df y"
          and "\<And>x y. Df (x *\<^sub>R y) = x *\<^sub>R Df y"
      using plus_hyperdual.code scaleR_hyperdual.code by (simp_all add: linear_iff)

    show "\<exists>K. \<forall>x. norm (Df x) \<le> norm x * K"
    proof -
      obtain k_re k_eps1 k_eps2 k_eps12
       where "\<forall>x. (norm (Base (Df x)))^2 \<le> (norm x * k_re)^2"
         and "\<forall>x. (norm (Eps1 (Df x)))^2 \<le> (norm x * k_eps1)^2"
         and "\<forall>x. (norm (Eps2 (Df x)))^2 \<le> (norm x * k_eps2)^2"
         and "\<forall>x. (norm (Eps12 (Df x)))^2 \<le> (norm x * k_eps12)^2"
        using bl bounded_linear.bounded norm_ge_zero power_mono by metis
      moreover have "\<forall>x. (norm (Df x))^2 = (norm (Base (Df x)))^2 + (norm (Eps1 (Df x)))^2 + (norm (Eps2 (Df x)))^2 + (norm (Eps12 (Df x)))^2"
        using inner_hyperdual_def power2_norm_eq_inner by metis
      ultimately have "\<forall>x. (norm (Df x))^2 \<le> (norm x * k_re)^2 + (norm x * k_eps1)^2 + (norm x * k_eps2)^2 + (norm x * k_eps12)^2"
        by smt
      then have "\<forall>x. (norm (Df x))^2 \<le> (norm x)^2 * (k_re^2 + k_eps1^2 + k_eps2^2 + k_eps12^2)"
        by (simp add: distrib_left power_mult_distrib)
      then have final: "\<forall>x. norm (Df x) \<le> norm x * sqrt(k_re^2 + k_eps1^2 + k_eps2^2 + k_eps12^2)"
        using real_le_rsqrt real_sqrt_mult real_sqrt_pow2 by fastforce
      then show "\<exists>K. \<forall>x. norm (Df x) \<le> norm x * K"
        by blast
    qed
  qed
  \<comment> \<open>Finally put the two together to finish the proof\<close>
  ultimately show "(f has_derivative Df) F"
    by (simp add: has_derivative_def)
qed

text\<open>Stop automatically unfolding hyperduals into components outside this theory:\<close>
lemmas [iff del] = hyperdual_eq_iff

end
