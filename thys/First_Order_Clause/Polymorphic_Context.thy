theory Polymorphic_Context
  imports
    Type_Arguments 
    Polymorphic_Ground_Context
    Nonground_Abstract_Context
begin

interpretation poly_context: nonground_abstract_context where  
  comp_subst = "(\<odot>)" and id_subst = id_subst and apply_subst = apply_subst and
  subst_update = update_subst and term_subst = "(\<cdot>p)" and term_vars = poly_term.vars and
  term_to_ground = poly_term.to_ground and term_from_ground = poly_term.from_ground and
  term_is_ground = poly_term.is_ground and Fun = PFun and size = size and subterms = args and
  fun_sym = poly_term.fun_sym and extra = type_args and GFun = PGFun and
  fun_sym\<^sub>G = poly_gterm.fun_sym and extra\<^sub>G = poly_gterm.type_args and
  subterms\<^sub>G = poly_gterm.args and size\<^sub>G = size and extra_is_ground = type_args.is_ground and
  extra_to_ground = type_args.to_ground and extra_from_ground = type_args.from_ground and
  extra_vars = type_args.vars and extra_subst = type_args.subst and extra_apply_subst = apply_subst
  by
    unfold_locales
    (auto simp: type_args.from_ground_def type_args.to_ground_def type_args.is_ground_def
      type_args.subst_def)

end
