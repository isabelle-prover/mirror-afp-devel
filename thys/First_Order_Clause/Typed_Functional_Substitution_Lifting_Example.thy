theory Typed_Functional_Substitution_Lifting_Example
  imports
    Functional_Substitution_Typing_Lifting
    Typed_Functional_Substitution_Lifting
    Typed_Functional_Substitution_Example
    Abstract_Substitution.Functional_Substitution_Lifting_Example
begin

text \<open>All property locales have corresponding lifting locales\<close>
locale nonground_uniform_typing_lifting =
  functional_substitution_uniform_typing_lifting where
  base_typed = "typed \<F>" and base_welltyped = "welltyped \<F>" +

  is_typed: uniform_typed_subst_stability_lifting where
  base_typed = "typed \<F>" +

  is_welltyped: uniform_typed_subst_stability_lifting where
  base_typed = "welltyped \<F>"
for \<F> :: "('f, 'ty) fun_types"

locale nonground_typing_lifting =
  functional_substitution_typing_lifting where
  base_typed = "typed \<F>" and base_welltyped = "welltyped \<F>" +

  is_typed: typed_subst_stability_lifting where base_typed = "typed \<F>" +

  is_welltyped: typed_subst_stability_lifting where
  sub_is_typed = sub_is_welltyped and base_typed = "welltyped \<F>"
for \<F> :: "('f, 'ty) fun_types"


locale example_typing_lifting =
  fixes \<F> :: "('f, 'ty) fun_types"
begin

sublocale equation:
  uniform_typing_lifting where
  sub_typed = "typed \<F> \<V>" and sub_welltyped = "welltyped \<F> \<V>" and
  to_set = "set_prod"
  by unfold_locales

sublocale equation:
  nonground_uniform_typing_lifting where
  base_vars = vars_term and base_subst = subst_apply_term and map = "\<lambda>f. map_prod f f" and
  to_set = set_prod and comp_subst = subst_compose and id_subst = Var
  by unfold_locales

text \<open>Lifted lemmas and definitions\<close>
thm
  equation.is_welltyped_def
  equation.is_typed_def

  equation.is_welltyped.subst_stability
  equation.is_typed.subst_stability
  equation.is_typed_if_is_welltyped

text \<open>We can lift multiple levels\<close>
sublocale equation_set:
  typing_lifting where
  sub_is_typed = "equation.is_typed \<V>" and sub_is_welltyped = "equation.is_welltyped \<V>" and
  to_set = fset
  by unfold_locales

sublocale equation_set:
  nonground_typing_lifting where
  base_vars = vars_term and base_subst = subst_apply_term and map = fimage and
  to_set = fset and comp_subst = subst_compose and id_subst = Var and
  sub_vars = equation_subst.vars and sub_subst = equation_subst.subst and
  sub_is_welltyped = equation.is_welltyped and sub_is_typed = equation.is_typed
  by unfold_locales

text \<open>Lifted lemmas and definitions\<close>
thm
  equation_set.is_welltyped_def
  equation_set.is_typed_def

  equation_set.is_welltyped.subst_stability
  equation_set.is_typed.subst_stability
  equation_set.is_typed_if_is_welltyped

end

text \<open>Interpretation with Unit-Typing\<close>
global_interpretation example_typing_lifting "\<lambda>_. ([], ())".

end
