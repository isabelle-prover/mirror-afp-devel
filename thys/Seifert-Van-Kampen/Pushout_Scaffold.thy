theory Pushout_Scaffold
  imports Equivalence_Quotients
begin

section \<open>Pushout-style quotients of disjoint sums\<close>

text \<open>
  The pushout of two maps is first presented here as a quotient of the disjoint
  sum by the obvious glue relation. This algebraic infrastructure is independent of
  any topology; the topological quotient is added later, once the point-set
  infrastructure is in place.
\<close>

inductive pushout_rel ::
  "('c => 'a) => ('c => 'b) => ('a + 'b) => ('a + 'b) => bool"
  for f :: "'c => 'a" and g :: "'c => 'b"
where
  refl [intro!, simp]: "pushout_rel f g x x"
| sym: "pushout_rel f g x y ==> pushout_rel f g y x"
| trans: "pushout_rel f g x y ==> pushout_rel f g y z ==> pushout_rel f g x z"
| glue [intro]: "pushout_rel f g (Inl (f c)) (Inr (g c))"

interpretation pushout_equiv: equivalence_relation "pushout_rel f g"
proof
  show "pushout_rel f g x x" for x
    by (rule pushout_rel.refl)
next
  show "pushout_rel f g x y ==> pushout_rel f g y x" for x y
    by (rule pushout_rel.sym)
next
  show "pushout_rel f g x y ==> pushout_rel f g y z ==> pushout_rel f g x z" for x y z
    by (rule pushout_rel.trans)
qed

definition pushout_class ::
  "('c => 'a) => ('c => 'b) => ('a + 'b) => ('a + 'b) set"
where
  "pushout_class f g x = equiv_class (pushout_rel f g) x"

definition pushout_space ::
  "('c => 'a) => ('c => 'b) => ('a + 'b) set set"
where
  "pushout_space f g = quotient_space (pushout_rel f g)"

definition pushout_inl ::
  "('c => 'a) => ('c => 'b) => 'a => ('a + 'b) set"
where
  "pushout_inl f g a = pushout_class f g (Inl a)"

definition pushout_inr ::
  "('c => 'a) => ('c => 'b) => 'b => ('a + 'b) set"
where
  "pushout_inr f g b = pushout_class f g (Inr b)"

lemma pushout_class_eq_iff:
  "pushout_class f g x = pushout_class f g y \<longleftrightarrow> pushout_rel f g x y"
  unfolding pushout_class_def
  by (rule pushout_equiv.equiv_class_eq_iff)

lemma pushout_inl_in_space [intro]:
  "pushout_inl f g a \<in> pushout_space f g"
  unfolding pushout_inl_def pushout_space_def pushout_class_def quotient_space_def
  by blast

lemma pushout_inr_in_space [intro]:
  "pushout_inr f g b \<in> pushout_space f g"
  unfolding pushout_inr_def pushout_space_def pushout_class_def quotient_space_def
  by blast

lemma pushout_glue:
  "pushout_inl f g (f c) = pushout_inr f g (g c)"
  by (simp add: pushout_class_eq_iff pushout_inl_def pushout_inr_def pushout_rel.glue)

definition pushout_case_compatible ::
  "('c => 'a) => ('c => 'b) => ('a => 'd) => ('b => 'd) => bool"
where
  "pushout_case_compatible f g left right \<longleftrightarrow> (\<forall>c. left (f c) = right (g c))"

lemma pushout_rel_case_cong:
  assumes compat: "pushout_case_compatible f g left right"
    and rel: "pushout_rel f g x y"
  shows "case_sum left right x = case_sum left right y"
  using rel
proof (induction rule: pushout_rel.induct)
  case (refl x)
  then show ?case by simp
next
  case (sym x y)
  then show ?case by simp
next
  case (trans x y z)
  then show ?case by simp
next
  case (glue c)
  then show ?case
    using compat unfolding pushout_case_compatible_def by simp
qed

definition pushout_rec ::
  "('c => 'a) => ('c => 'b) => ('a => 'd) => ('b => 'd) => ('a + 'b) set => 'd"
where
  "pushout_rec f g left right X =
     (THE z. \<exists>x. X = pushout_class f g x \<and> z = case_sum left right x)"

lemma pushout_rec_well_defined:
  assumes compat: "pushout_case_compatible f g left right"
    and X_in: "X \<in> pushout_space f g"
  shows "\<exists>! z. \<exists>x. X = pushout_class f g x \<and> z = case_sum left right x"
proof -
  from X_in obtain rep where X_rep: "X = pushout_class f g rep"
    unfolding pushout_space_def quotient_space_def pushout_class_def by blast
  show ?thesis
  proof (rule ex1I[of _ "case_sum left right rep"])
    show "\<exists>x. X = pushout_class f g x \<and> case_sum left right rep = case_sum left right x"
      by (rule exI[where x = rep], simp add: X_rep)
  next
    fix z
    assume hz: "\<exists>x. X = pushout_class f g x \<and> z = case_sum left right x"
    from hz obtain x where
      x: "X = pushout_class f g x" "z = case_sum left right x"
      by blast
    have "pushout_rel f g x rep"
      using X_rep x(1) by (simp add: pushout_class_eq_iff)
    then have rel_rep_x: "pushout_rel f g rep x"
      by (rule pushout_rel.sym)
    from compat rel_rep_x have "case_sum left right rep = case_sum left right x"
      by (rule pushout_rel_case_cong)
    with x show "z = case_sum left right rep"
      by simp
  qed
qed

lemma pushout_rec_inl:
  assumes compat: "pushout_case_compatible f g left right"
  shows "pushout_rec f g left right (pushout_inl f g a) = left a"
proof -
  have uniq:
    "\<exists>! z. \<exists>x. pushout_inl f g a = pushout_class f g x \<and> z = case_sum left right x"
    using pushout_rec_well_defined[OF compat pushout_inl_in_space[of f g a]] .
  have witness:
    "\<exists>x. pushout_inl f g a = pushout_class f g x \<and> left a = case_sum left right x"
    unfolding pushout_inl_def by (intro exI[of _ "Inl a"]) simp
  show ?thesis
    unfolding pushout_rec_def
    by (rule the1_equality[OF uniq witness])
qed

lemma pushout_rec_inr:
  assumes compat: "pushout_case_compatible f g left right"
  shows "pushout_rec f g left right (pushout_inr f g b) = right b"
proof -
  have uniq:
    "\<exists>! z. \<exists>x. pushout_inr f g b = pushout_class f g x \<and> z = case_sum left right x"
    using pushout_rec_well_defined[OF compat pushout_inr_in_space[of f g b]] .
  have witness:
    "\<exists>x. pushout_inr f g b = pushout_class f g x \<and> right b = case_sum left right x"
    unfolding pushout_inr_def by (intro exI[of _ "Inr b"]) simp
  show ?thesis
    unfolding pushout_rec_def
    by (rule the1_equality[OF uniq witness])
qed

end
