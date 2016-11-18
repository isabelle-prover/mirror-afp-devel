(* Title:      Lattice Basics
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section {* Lattice Basics *}

text {*
This theory provides notations, basic definitions and facts of lattice-related structures used throughout the subsequent development.
*}

theory Lattice_Basics

imports Main

begin

text {*
We use the following notations for the join, meet and complement operations.
Changing the precedence of the unary complement allows us to write terms like @{text "--x"} instead of @{text "-(-x)"}.
*}

context sup
begin

notation sup (infixl "\<squnion>" 65)

definition additive :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "additive f \<equiv> \<forall>x y . f (x \<squnion> y) = f x \<squnion> f y"

end

context inf
begin

notation inf (infixl "\<sqinter>" 67)

end

context uminus
begin

no_notation uminus ("- _" [81] 80)

notation uminus ("- _" [80] 80)

end

text {*
We use the following definition of monotonicity for operations defined in classes.
The standard @{text mono} places a sort constraint on the target type.
We also give basic properties of Galois connections and lift orders to functions.
*}

context ord
begin

definition isotone :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "isotone f \<equiv> \<forall>x y . x \<le> y \<longrightarrow> f x \<le> f y"

definition galois :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "galois l u \<equiv> \<forall>x y . l x \<le> y \<longleftrightarrow> x \<le> u y"

definition lifted_less_eq :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" ("(_ \<le>\<le> _)" [51, 51] 50)
  where "f \<le>\<le> g \<equiv> \<forall>x . f x \<le> g x"

end

context order
begin

lemma order_lesseq_imp:
  "(\<forall>z . x \<le> z \<longrightarrow> y \<le> z) \<longleftrightarrow> y \<le> x"
  using order_trans by blast

lemma galois_char:
  "galois l u \<longleftrightarrow> (\<forall>x . x \<le> u (l x)) \<and> (\<forall>x . l (u x) \<le> x) \<and> isotone l \<and> isotone u"
  apply (rule iffI)
  apply (metis (full_types) galois_def isotone_def order_refl order_trans)
  using galois_def isotone_def order_trans by blast

lemma galois_closure:
  "galois l u \<Longrightarrow> l x = l (u (l x)) \<and> u x = u (l (u x))"
  by (simp add: galois_char isotone_def antisym)

lemma lifted_reflexive:
  "f = g \<Longrightarrow> f \<le>\<le> g"
  by (simp add: lifted_less_eq_def)

lemma lifted_transitive:
  "f \<le>\<le> g \<Longrightarrow> g \<le>\<le> h \<Longrightarrow> f \<le>\<le> h"
  using lifted_less_eq_def order_trans by blast

lemma lifted_antisymmetric:
  "f \<le>\<le> g \<Longrightarrow> g \<le>\<le> f \<Longrightarrow> f = g"
  by (metis (full_types) antisym ext lifted_less_eq_def)

end

text {*
The following are basic facts in semilattices.
*}

context semilattice_sup
begin

lemma sup_left_isotone:
  "x \<le> y \<Longrightarrow> x \<squnion> z \<le> y \<squnion> z"
  using sup.mono by blast

lemma sup_right_isotone:
  "x \<le> y \<Longrightarrow> z \<squnion> x \<le> z \<squnion> y"
  using sup.mono by blast

lemma sup_left_divisibility:
  "x \<le> y \<longleftrightarrow> (\<exists>z . x \<squnion> z = y)"
  using sup.absorb2 sup.cobounded1 by blast

lemma sup_right_divisibility:
  "x \<le> y \<longleftrightarrow> (\<exists>z . z \<squnion> x = y)"
  by (metis sup.cobounded2 sup.orderE)

lemma sup_same_context:
  "x \<le> y \<squnion> z \<Longrightarrow> y \<le> x \<squnion> z \<Longrightarrow> x \<squnion> z = y \<squnion> z"
  by (simp add: le_iff_sup sup_left_commute)

lemma sup_relative_same_increasing:
  "x \<le> y \<Longrightarrow> x \<squnion> z = x \<squnion> w \<Longrightarrow> y \<squnion> z = y \<squnion> w"
  using sup.assoc sup_right_divisibility by auto

end

text {*
Every bounded semilattice is a commutative monoid.
Finite sums defined in commutative monoids are available via the following sublocale.
*}

context bounded_semilattice_sup_bot
begin

sublocale sup_monoid: comm_monoid_add where plus = sup and zero = bot
  apply unfold_locales
  apply (simp add: sup_assoc)
  apply (simp add: sup_commute)
  by simp

end

context semilattice_inf
begin

lemma inf_same_context:
  "x \<le> y \<sqinter> z \<Longrightarrow> y \<le> x \<sqinter> z \<Longrightarrow> x \<sqinter> z = y \<sqinter> z"
  using antisym by auto

end

text {*
The following class requires only the existence of upper bounds, which is a property common to bounded semilattices and (not necessarily bounded) lattices.
We use it in our development of filters.
*}

class directed_semilattice_inf = semilattice_inf +
  assumes ub: "\<exists>z . x \<le> z \<and> y \<le> z"

text {*
We extend the @{text inf} sublocale, which dualises the order in semilattices, to bounded semilattices.
*}

context bounded_semilattice_inf_top
begin

subclass directed_semilattice_inf
  apply unfold_locales
  using top_greatest by blast

sublocale inf: bounded_semilattice_sup_bot where sup = inf and less_eq = greater_eq and less = greater and bot = top
  by unfold_locales (simp_all add: less_le_not_le)

end

context lattice
begin

subclass directed_semilattice_inf
  apply unfold_locales
  using sup_ge1 sup_ge2 by blast

definition dual_additive :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "dual_additive f \<equiv> \<forall>x y . f (x \<squnion> y) = f x \<sqinter> f y"

end

text {*
Not every bounded lattice has complements, but two elements might still be complements of each other as captured in the following definition.
In this situation we can apply, for example, the shunting property shown below.
We introduce most definitions using the @{text abbreviation} command.
*}

context bounded_lattice
begin

abbreviation "complement x y \<equiv> x \<squnion> y = top \<and> x \<sqinter> y = bot"

lemma complement_symmetric:
  "complement x y \<Longrightarrow> complement y x"
  by (simp add: inf.commute sup.commute)

definition conjugate :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "conjugate f g \<equiv> \<forall>x y . f x \<sqinter> y = bot \<longleftrightarrow> x \<sqinter> g y = bot"

end

context distrib_lattice
begin

lemma relative_equality:
  "x \<squnion> z = y \<squnion> z \<Longrightarrow> x \<sqinter> z = y \<sqinter> z \<Longrightarrow> x = y"
  by (metis inf.commute inf_sup_absorb inf_sup_distrib2)

end

text {*
Distributive lattices with a greatest element are widely used in the construction theorem for Stone algebras.
*}

class distrib_lattice_bot = bounded_lattice_bot + distrib_lattice

class distrib_lattice_top = bounded_lattice_top + distrib_lattice

class bounded_distrib_lattice = bounded_lattice + distrib_lattice
begin

subclass distrib_lattice_bot ..

subclass distrib_lattice_top ..

lemma complement_shunting:
  assumes "complement z w"
    shows "z \<sqinter> x \<le> y \<longleftrightarrow> x \<le> w \<squnion> y"
proof
  assume 1: "z \<sqinter> x \<le> y"
  have "x = (z \<squnion> w) \<sqinter> x"
    by (simp add: assms)
  also have "... \<le> y \<squnion> (w \<sqinter> x)"
    using 1 sup.commute sup.left_commute inf_sup_distrib2 sup_right_divisibility by fastforce
  also have "... \<le> w \<squnion> y"
    by (simp add: inf.coboundedI1)
  finally show "x \<le> w \<squnion> y"
    .
next
  assume "x \<le> w \<squnion> y"
  hence "z \<sqinter> x \<le> z \<sqinter> (w \<squnion> y)"
    using inf.sup_right_isotone by auto
  also have "... = z \<sqinter> y"
    by (simp add: assms inf_sup_distrib1)
  also have "... \<le> y"
    by simp
  finally show "z \<sqinter> x \<le> y"
    .
qed

end

text {*
Some results, such as the existence of certain filters, require that the algebras are not trivial.
This is not an assumption of the order and lattice classes that come with Isabelle/HOL; for example, @{text "bot = top"} may hold in bounded lattices.
*}

class non_trivial =
  assumes consistent: "\<exists>x y . x \<noteq> y"

class non_trivial_order = non_trivial + order

class non_trivial_order_bot = non_trivial_order + order_bot

class non_trivial_bounded_order = non_trivial_order_bot + order_top
begin

lemma bot_not_top:
  "bot \<noteq> top"
proof -
  from consistent obtain x y :: 'a where "x \<noteq> y"
    by auto
  thus ?thesis
    by (metis bot_less top.extremum_strict)
qed

text {*
The following results extend basic Isabelle/HOL facts.
*}

lemma if_distrib_2:
  "f (if c then x else y) (if c then z else w) = (if c then f x z else f y w)"
  by simp

lemma left_invertible_inj:
  "(\<forall>x . g (f x) = x) \<Longrightarrow> inj f"
  by (metis injI)

lemma invertible_bij:
  assumes "\<forall>x . g (f x) = x"
      and "\<forall>y . f (g y) = y"
    shows "bij f"
  by (metis assms bijI')

end

end

