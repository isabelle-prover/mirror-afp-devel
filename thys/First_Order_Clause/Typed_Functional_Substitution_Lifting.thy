theory Typed_Functional_Substitution_Lifting
  imports
    Typed_Functional_Substitution
    Abstract_Substitution.Functional_Substitution_Lifting
begin

(* TODO: *)
lemma ext_equiv: "(\<And>x. f x \<equiv> g x) \<Longrightarrow> f \<equiv> g"
  by presburger

locale typed_functional_substitution_lifting =
  sub: typed_functional_substitution where
    vars = sub_vars and subst = sub_subst and welltyped = sub_welltyped and base_vars = base_vars +
    based_functional_substitution_lifting where to_set = to_set and base_vars = base_vars
for
  sub_welltyped :: "('v, 'ty) var_types \<Rightarrow> 'sub \<Rightarrow> 'ty' \<Rightarrow> bool" and
  to_set :: "'expr \<Rightarrow> 'sub set" and
  base_vars :: "'base \<Rightarrow> 'v set"
begin

sublocale typing_lifting where sub_welltyped = "sub_welltyped \<V>"
  by unfold_locales

sublocale typed_functional_substitution where
  vars = vars and subst = subst and welltyped = welltyped
  by unfold_locales

end

(*TODO: Name type_grounding_lifting *)
locale typed_grounding_functional_substitution_lifting =
  typed_functional_substitution_lifting +
  grounding_lifting
begin

sublocale typed_grounding_functional_substitution where
  vars = vars and subst = subst and welltyped = welltyped and to_ground = to_ground and
  from_ground = from_ground
  by unfold_locales

end

(* TODO: This lifting is very primitve \<rightarrow> just rely on a base *)
locale inhabited_typed_functional_substitution_lifting =
  typed_functional_substitution_lifting +
  sub: inhabited_typed_functional_substitution where
  vars = sub_vars and subst = sub_subst and welltyped = sub_welltyped
begin

sublocale inhabited_typed_functional_substitution where
  vars = vars and subst = subst and welltyped = welltyped
  by unfold_locales (simp add: sub.types_inhabited)

end

locale typed_subst_stability_lifting =
  typed_functional_substitution_lifting +
  sub: typed_subst_stability where
    welltyped = sub_welltyped and vars = sub_vars and subst = sub_subst
begin

sublocale typed_subst_stability where welltyped = welltyped and subst = subst and vars = vars
  by unfold_locales (auto simp add: vars_def to_set_image is_welltyped_def)

end

locale replaceable_\<V>_lifting =
  typed_functional_substitution_lifting +
  sub: replaceable_\<V> where welltyped = sub_welltyped and vars = sub_vars and subst = sub_subst
begin

sublocale replaceable_\<V> where
  subst = subst and vars = vars and welltyped = welltyped
  by unfold_locales (metis SUP_upper2 sub.replace_\<V> subset_eq vars_def is_welltyped_def)

end

locale typed_renaming_lifting =
  typed_functional_substitution_lifting where
    base_welltyped = "base_welltyped :: ('v \<Rightarrow> 'ty) \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" +
  renaming_variables_lifting +
  sub: based_typed_renaming where
    subst = sub_subst and vars = sub_vars and welltyped = sub_welltyped
begin

sublocale based_typed_renaming where
  subst = subst and vars = vars and welltyped = welltyped
  by unfold_locales (force simp: vars_def subst_def is_welltyped_def)

end

end
