theory Functional_Substitution_Typing_Lifting
  imports
    Functional_Substitution_Typing
    Typed_Functional_Substitution_Lifting
begin

locale functional_substitution_typing_lifting =
  sub: functional_substitution_typing where
  vars = sub_vars and subst = sub_subst and is_typed = sub_is_typed and
  is_welltyped = sub_is_welltyped +
  based_functional_substitution_lifting where to_set = to_set
for
  to_set :: "'expr \<Rightarrow> 'sub set" and
  sub_is_typed sub_is_welltyped :: "('var, 'ty) var_types \<Rightarrow> 'sub \<Rightarrow> bool"
begin

sublocale typing_lifting where
  sub_is_typed = "sub_is_typed \<V>" and sub_is_welltyped = "sub_is_welltyped \<V>"
  by unfold_locales

sublocale functional_substitution_typing where
  is_typed = is_typed and is_welltyped = is_welltyped and vars = vars and subst = subst
  by unfold_locales

end

locale functional_substitution_uniform_typing_lifting =
  base: base_functional_substitution_typing where
  vars = base_vars and subst = base_subst and typed = base_typed and welltyped = base_welltyped +
  based_functional_substitution_lifting where
  to_set = to_set and sub_vars = base_vars and sub_subst = base_subst
for
  to_set :: "'expr \<Rightarrow> 'base set" and
  base_typed base_welltyped :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool"
begin

sublocale uniform_typing_lifting where
  sub_typed = "base_typed \<V>" and sub_welltyped = "base_welltyped \<V>"
  by unfold_locales

sublocale functional_substitution_typing where
  is_typed = is_typed and is_welltyped = is_welltyped and vars = vars and subst = subst
  by unfold_locales

end

end
