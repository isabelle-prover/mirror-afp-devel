(* Title:      Extended Reals
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section {* Extended Reals *}

text {*
In this theory we extend real numbers by a least element and a greatest element.
We then show that extended reals form a Stone algebra using minimum and maximum as lattice operations.
It follows that they also form a Stone relation algebra.
Moreover we show that extended reals form a commutative monoid using a suitably extended addition operation.
We conclude by deriving various additional properties of extended reals that are not captured by these algebras.
*}

theory Extended_Reals

imports Real Relation_Algebras

begin

text {*
We disable the unary minus operation on reals because it conflicts with the pseudocomplement in Stone algebras.
*}

no_notation
  uminus ("- _" [81] 80)

datatype ext_real = MinusInfinity | Real real | PlusInfinity

text {*
Our first result shows that extended reals form a Stone algebra.
*}

instantiation ext_real :: stone_algebra
begin

text {*
Join and meet are maximum and minimum extended so that @{text MinusInfinity} becomes the least element and @{text PlusInfinity} becomes the greatest element.
*}

fun sup_ext_real :: "ext_real \<Rightarrow> ext_real \<Rightarrow> ext_real" where
  "sup_ext_real MinusInfinity x = x"
| "sup_ext_real (Real x) MinusInfinity = Real x"
| "sup_ext_real (Real x) (Real y) = Real (max x y)"
| "sup_ext_real (Real x) PlusInfinity = PlusInfinity"
| "sup_ext_real PlusInfinity x = PlusInfinity"

fun inf_ext_real :: "ext_real \<Rightarrow> ext_real \<Rightarrow> ext_real" where
  "inf_ext_real MinusInfinity x = MinusInfinity"
| "inf_ext_real (Real x) MinusInfinity = MinusInfinity"
| "inf_ext_real (Real x) (Real y) = Real (min x y)"
| "inf_ext_real (Real x) PlusInfinity = Real x"
| "inf_ext_real PlusInfinity x = x"

text {*
The pseudocomplement takes the least element to the greatest element and every other element to the least element.
*}

fun uminus_ext_real :: "ext_real \<Rightarrow> ext_real" where
  "uminus_ext_real MinusInfinity = PlusInfinity"
| "uminus_ext_real (Real x) = MinusInfinity"
| "uminus_ext_real PlusInfinity = MinusInfinity"

fun minus_ext_real :: "ext_real \<Rightarrow> ext_real \<Rightarrow> ext_real" where
  "minus_ext_real x y = x \<sqinter> (uminus y)"

definition bot_ext_real :: ext_real where "bot_ext_real \<equiv> MinusInfinity"
definition top_ext_real :: ext_real where "top_ext_real \<equiv> PlusInfinity"

text {*
The order extends the standard order on reals.
*}

fun less_eq_ext_real :: "ext_real \<Rightarrow> ext_real \<Rightarrow> bool" where
  "less_eq_ext_real MinusInfinity x = True"
| "less_eq_ext_real (Real x) MinusInfinity = False"
| "less_eq_ext_real (Real x) (Real y) = (x \<le> y)"
| "less_eq_ext_real (Real x) PlusInfinity = True"
| "less_eq_ext_real PlusInfinity MinusInfinity = False"
| "less_eq_ext_real PlusInfinity (Real y) = False"
| "less_eq_ext_real PlusInfinity PlusInfinity = True"

definition less_ext_real :: "ext_real \<Rightarrow> ext_real \<Rightarrow> bool" where "less_ext_real x y \<equiv> x \<le> y \<and> \<not> y \<le> x"

text {*
Proofs over extended reals often work by separately considering the three cases per variable.
*}

instance
proof
  fix x y :: ext_real
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_ext_real_def)
next
  fix x :: ext_real
  show "x \<le> x"
    by (cases x) simp_all
next
  fix x y z :: ext_real
  assume "x \<le> y" and "y \<le> z"
  thus "x \<le> z"
    by (cases x; cases y; cases z) simp_all
next
  fix x y :: ext_real
  assume "x \<le> y" and "y \<le> x"
  thus "x = y"
    by (cases x; cases y) simp_all
next
  fix x y :: ext_real
  show "x \<sqinter> y \<le> x"
    by (cases x; cases y) simp_all
next
  fix x y :: ext_real
  show "x \<sqinter> y \<le> y"
    by (cases x; cases y) simp_all
next
  fix x y z :: ext_real
  assume "x \<le> y" and "x \<le> z"
  thus "x \<le> y \<sqinter> z"
    by (cases x; cases y; cases z) simp_all
next
  fix x y :: ext_real
  show "x \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
next
  fix x y :: ext_real
  show "y \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
next
  fix x y z :: ext_real
  assume "y \<le> x" and "z \<le> x"
  thus "y \<squnion> z \<le> x"
    by (cases x; cases y; cases z) simp_all
next
  fix x :: ext_real
  show "bot \<le> x"
    by (simp add: bot_ext_real_def)
next
  fix x :: ext_real
  show "x \<le> top"
    by (cases x) (simp_all add: top_ext_real_def)
next
  fix x y z :: ext_real
  show "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
    by (cases x; cases y; cases z) simp_all
next
  fix x y :: ext_real
  show "x \<sqinter> y = bot \<longleftrightarrow> x \<le> uminus y"
    by (cases x; cases y) (simp_all add: bot_ext_real_def)
next
  fix x :: ext_real
  show "uminus x \<squnion> uminus (uminus x) = top"
    by (cases x) (simp_all add: top_ext_real_def)
qed

end

text {*
The Stone algebra structure extends to Stone relation algebras by reusing some of the operations.
This is mostly done to simplify the lifting to matrices later.
*}

instantiation ext_real :: stone_relation_algebra
begin

definition times_ext_real :: "ext_real \<Rightarrow> ext_real \<Rightarrow> ext_real" where "times_ext_real = inf"
definition conv_ext_real :: "ext_real \<Rightarrow> ext_real" where "conv_ext_real = id"
definition one_ext_real :: "ext_real" where "one_ext_real = top"

instance
proof (intro_classes, goal_cases)
  case 2 show ?case by (simp add: inf_sup_distrib2 times_ext_real_def)
qed (auto simp: inf_assoc times_ext_real_def inf_sup_distrib2 one_ext_real_def
     inf_commute inf.commute inf_left_commute conv_ext_real_def)

end

text {*
The standard addition on reals, extended so that @{text MinusInfinity} is neutral and @{text PlusInfinity} is absorbing, forms another commutative monoid.
*}

instantiation ext_real :: comm_monoid_add
begin

fun plus_ext_real :: "ext_real \<Rightarrow> ext_real \<Rightarrow> ext_real" where
  "plus_ext_real MinusInfinity x = x"
| "plus_ext_real (Real x) MinusInfinity = Real x"
| "plus_ext_real (Real x) (Real y) = Real (x + y)"
| "plus_ext_real (Real x) PlusInfinity = PlusInfinity"
| "plus_ext_real PlusInfinity x = PlusInfinity"

definition zero_ext_real :: ext_real where "zero_ext_real \<equiv> MinusInfinity"

instance
proof
  fix x y z :: ext_real
  show "(x + y) + z = x + (y + z)"
    by (cases x; cases y; cases z) simp_all
next
  fix x y z :: ext_real
  show "x + y = y + x"
    by (cases x; cases y) simp_all
next
  fix x :: ext_real
  show "0 + x = x"
    by (cases x) (simp_all add: zero_ext_real_def)
qed

end

lemma ext_real_comm_monoid_add:
  "class.comm_monoid_add plus (0::ext_real)"
  ..

lemma ext_real_sum:
  "comm_monoid_add.sum plus (0::ext_real) = sum"
  by (metis comm_monoid_add.sum_def ext_real_comm_monoid_add sum_def)

text {*
Extended reals satisfy a number of further useful properties.
First, the order on extended reals is total and join and meet are selective.
*}

lemma ext_real_total:
  fixes x y :: ext_real
  shows "x \<le> y \<or> y \<le> x"
  by (cases x; cases y) auto

lemma ext_real_sup_selective:
  fixes x y :: ext_real
  shows "x \<squnion> y = x \<or> x \<squnion> y = y"
  by (cases x; cases y) (simp_all add: max_def)

lemma ext_real_inf_selective:
  fixes x y :: ext_real
  shows "x \<sqinter> y = x \<or> x \<sqinter> y = y"
  by (cases x; cases y) (simp_all add: min_def)

lemma ext_real_inf_less_eq:
  fixes x y z :: ext_real
  shows "x \<sqinter> y \<le> z \<longleftrightarrow> x \<le> z \<or> y \<le> z"
  by (cases x; cases y; cases z) (simp_all add: min_le_iff_disj)

lemma ext_real_top_sum:
  fixes x y :: ext_real
  shows "x \<noteq> top \<Longrightarrow> y \<noteq> top \<Longrightarrow> x \<squnion> y \<noteq> top"
  by (metis ext_real_sup_selective)

lemma ext_real_bot_product:
  fixes x y :: ext_real
  shows "x \<noteq> bot \<Longrightarrow> y \<noteq> bot \<Longrightarrow> x * y \<noteq> bot"
  by (metis bot.extremum_uniqueI ext_real_total inf.idem mult_right_isotone semiring.mult_right_mono times_ext_real_def)

lemma ext_real_sup_not_bot:
  fixes x y :: ext_real
  shows "x \<noteq> bot \<Longrightarrow> x \<squnion> y \<noteq> bot"
  by simp

text {*
Next, the regular elements among the extended reals are the least and greatest elements.
All elements except the least element are dense.
*}

lemma ext_real_regular:
  fixes x :: ext_real
  shows "regular x \<longleftrightarrow> x = bot \<or> x = top"
  by (cases x) (simp_all add: bot_ext_real_def top_ext_real_def)

lemma ext_real_dense:
  fixes x :: ext_real
  shows "x \<noteq> bot \<Longrightarrow> --x = top"
  by (metis p_bot top_ext_real_def uminus_ext_real.elims)

text {*
Next, standard addition is isotone.
*}

lemma plus_ext_real_isotone_right:
  fixes x y :: ext_real
  shows "--x = --y \<Longrightarrow> x \<le> y \<Longrightarrow> z + x \<le> z + y"
  by (cases x; cases y; cases z) simp_all

lemma ext_real_plus_not_bot:
  fixes x y :: ext_real
  shows "x \<noteq> bot \<Longrightarrow> x + y \<noteq> bot"
  using bot_ext_real_def plus_ext_real.elims by auto

text {*
Finally, the sum of two extended reals is the same as the sum of their minima and maxima.
This is similar to the inclusion-exclusion principle of two sets.
*}

lemma ext_real_plus_sup_inf:
  fixes x y :: ext_real
  shows "x + y = (x \<squnion> y) + (x \<sqinter> y)"
  by (cases x; cases y) simp_all

lemma ext_real_sup_inf_sup:
  fixes x y :: ext_real
  shows "x \<squnion> y = (x \<squnion> y) \<squnion> (x \<sqinter> y)"
  by (metis sup_commute sup_inf_absorb sup_left_commute)

end

