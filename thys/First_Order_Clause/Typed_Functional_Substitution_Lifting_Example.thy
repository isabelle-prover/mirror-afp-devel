theory Typed_Functional_Substitution_Lifting_Example
  imports
    Typed_Functional_Substitution_Lifting
    Typed_Functional_Substitution_Example
    Abstract_Substitution.Functional_Substitution_Lifting_Example
begin

text \<open>All property locales have corresponding lifting locales\<close>


locale nonground_typing_lifting =
   typed_subst_stability_lifting where 
   sub_welltyped = sub_welltyped and base_welltyped = "welltyped \<F>"
for \<F> :: "('f, 'ty) fun_types" and sub_welltyped :: "('v \<Rightarrow> 'ty) \<Rightarrow> 'sub \<Rightarrow> 'ty' \<Rightarrow> bool"

locale example_typing_lifting =
  fixes \<F> :: "('f, 'ty) fun_types"
begin

sublocale equation:
  nonground_typing_lifting where
  base_vars = vars_term and base_subst = subst_apply_term and map = "\<lambda>f. map_prod f f" and
  to_set = set_prod and comp_subst = subst_compose and id_subst = Var and
  sub_vars = vars_term and sub_subst = subst_apply_term and
  sub_welltyped = "welltyped \<F>" 
  by unfold_locales

text \<open>Lifted lemmas and definitions\<close>
thm
  equation.is_welltyped_def
  equation.welltyped_subst_stability

term equation.is_welltyped

text \<open>We can lift multiple levels\<close>

sublocale equation_set:
  nonground_typing_lifting where
  base_vars = vars_term and base_subst = subst_apply_term and map = fimage and
  to_set = fset and comp_subst = subst_compose and id_subst = Var and
  sub_vars = equation_subst.vars and sub_subst = equation_subst.subst and
  sub_welltyped = equation.welltyped
  by unfold_locales

text \<open>Lifted lemmas and definitions\<close>
thm
  equation_set.is_welltyped_def
  equation_set.welltyped_subst_stability

term equation_set.is_welltyped

end

text \<open>Interpretation with unit as type\<close>
global_interpretation example_typing_lifting "\<lambda>_. ([], ())".

end
