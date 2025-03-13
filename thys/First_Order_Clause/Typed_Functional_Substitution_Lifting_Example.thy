theory Typed_Functional_Substitution_Lifting_Example
  imports
    Typed_Functional_Substitution_Lifting
    Typed_Functional_Substitution_Example
    Abstract_Substitution.Functional_Substitution_Lifting_Example
begin

text \<open>All property locales have corresponding lifting locales\<close>


locale nonground_typing_lifting =
  is_typed: typed_subst_stability_lifting where 
  base_typed = "typed \<F>" and sub_typed = sub_typed +
  is_welltyped: typed_subst_stability_lifting where 
  sub_typed = sub_welltyped and base_typed = "welltyped \<F>" +
  typing_lifting' where sub_typed = sub_typed and sub_welltyped = sub_welltyped
for \<F> :: "('f, 'ty) fun_types" and sub_welltyped sub_typed :: "('v \<Rightarrow> 'ty) \<Rightarrow> 'sub \<Rightarrow> 'ty' \<Rightarrow> bool"

locale example_typing_lifting =
  fixes \<F> :: "('f, 'ty) fun_types"
begin

sublocale equation:
  nonground_typing_lifting where
  base_vars = vars_term and base_subst = subst_apply_term and map = "\<lambda>f. map_prod f f" and
  to_set = set_prod and comp_subst = subst_compose and id_subst = Var and
  sub_vars = vars_term and sub_subst = subst_apply_term and sub_typed = "typed \<F>" and
  sub_welltyped = "welltyped \<F>" 
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
  sub_typed = "equation.typed \<V>" and sub_welltyped = "equation.welltyped \<V>" and
  to_set = fset
  by unfold_locales

sublocale equation_set:
  nonground_typing_lifting where
  base_vars = vars_term and base_subst = subst_apply_term and map = fimage and
  to_set = fset and comp_subst = subst_compose and id_subst = Var and
  sub_vars = equation_subst.vars and sub_subst = equation_subst.subst and
  sub_welltyped = equation.welltyped and sub_typed = equation.typed
  by unfold_locales

text \<open>Lifted lemmas and definitions\<close>
thm
  equation_set.is_welltyped_def
  equation_set.is_typed_def

  equation_set.is_welltyped.subst_stability
  equation_set.is_typed.subst_stability
  equation_set.typed_if_welltyped

end

text \<open>Interpretation with unit as type\<close>
global_interpretation example_typing_lifting "\<lambda>_. ([], ())".

end
