theory Substitution_Lifting_Example \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close>
  imports
    Based_Substitution_Lifting
    Substitution_First_Order_Term
begin

setup natural_functor_setups

text \<open>Lifting of properties from term to equations (modelled as pairs)\<close>

type_synonym ('f,'v) equation = "('f, 'v) term \<times> ('f, 'v) term"

text \<open>All property locales have corresponding lifting locales\<close>
locale lifting_term_subst_properties =
  based_substitution_lifting where
  id_subst = Var and comp_subst = subst_compose and base_subst = subst_apply_term and
  base_vars = "vars_term :: ('f, 'v) term \<Rightarrow> 'v set" and apply_subst = "\<lambda>x \<sigma>. \<sigma> x" and
  base_is_ground = is_ground +

  finite_variables_lifting where
  id_subst = Var and comp_subst = subst_compose and apply_subst = "\<lambda>x \<sigma>. \<sigma> x"

global_interpretation equation_subst:
  lifting_term_subst_properties where
  sub_vars = vars_term and sub_subst = subst_apply_term and sub_is_ground = is_ground and
  map = "\<lambda>f. map_prod f f" and to_set = set_prod
  by unfold_locales fastforce+

text \<open>Lifted lemmas and defintions\<close>
thm
  equation_subst.vars_id_subst_subset
  equation_subst.vars_subst_subset
  equation_subst.to_fset_is_ground_subst

  equation_subst.vars_def
  equation_subst.subst_def
  equation_subst.is_ground_def

text \<open>We can lift multiple levels\<close>
global_interpretation equation_set_subst:
  lifting_term_subst_properties where
  sub_vars = equation_subst.vars and sub_subst = equation_subst.subst and 
  sub_is_ground = equation_subst.is_ground and map = fimage and to_set = fset
  by unfold_locales blast

text \<open>Lifted lemmas and defintions\<close>
thm
  equation_set_subst.vars_id_subst_subset
  equation_set_subst.vars_subst_subset
  equation_set_subst.to_fset_is_ground_subst

  equation_set_subst.vars_def
  equation_set_subst.subst_def
  equation_set_subst.is_ground_def

end
