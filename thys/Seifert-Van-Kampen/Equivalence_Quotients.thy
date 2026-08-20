theory Equivalence_Quotients
  imports Main
begin

section \<open>Equivalence classes as quotient infrastructure\<close>

text \<open>
  The later pushout and fundamental-group constructions are phrased in terms of
  explicit equivalence classes and quotient carriers. This small theory keeps
  that quotient infrastructure elementary and reusable, so subsequent theories
  can concentrate on the specific relations that matter for Seifert--van
  Kampen.
\<close>

definition equiv_class :: "('a => 'a => bool) => 'a => 'a set" where
  "equiv_class R x = {y. R y x}"

definition quotient_space :: "('a => 'a => bool) => 'a set set" where
  "quotient_space R = equiv_class R ` UNIV"

lemma quotient_spaceI:
  "equiv_class R x \<in> quotient_space R"
  unfolding quotient_space_def by blast

lemma equiv_class_iff [simp]:
  "y \<in> equiv_class R x \<longleftrightarrow> R y x"
  unfolding equiv_class_def by simp

locale equivalence_relation =
  fixes R :: "'a => 'a => bool"
  assumes refl [intro!, simp]: "R x x"
    and sym: "R x y ==> R y x"
    and transitive: "R x y ==> R y z ==> R x z"
begin

lemma equiv_class_eqI:
  assumes "R x y"
  shows "equiv_class R x = equiv_class R y"
  using assms sym transitive
  unfolding equiv_class_def
  by blast

lemma equiv_class_eq_iff:
  "equiv_class R x = equiv_class R y \<longleftrightarrow> R x y"
proof
  assume h : "equiv_class R x = equiv_class R y"
  have "x \<in> equiv_class R x"
    unfolding equiv_class_def by simp
  with h show "R x y"
    unfolding equiv_class_def by simp
next
  assume "R x y"
  then show "equiv_class R x = equiv_class R y"
    by (rule equiv_class_eqI)
qed

lemma quotient_spaceE:
  assumes "Q \<in> quotient_space R"
  obtains x where "Q = equiv_class R x"
  using assms unfolding quotient_space_def by blast

end

end
