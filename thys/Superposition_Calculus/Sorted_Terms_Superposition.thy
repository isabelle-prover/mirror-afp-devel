theory Sorted_Terms_Superposition
  imports 
    Superposition

    First_Order_Clause.IsaFoR_Nonground_Clause_With_Equality
    First_Order_Clause.IsaFoR_Nonground_Context
    First_Order_Clause.Sorted_Terms_Typing
begin

locale sorted_terms_superposition_calculus =
  sorted_terms_typing +

  superposition_calculus where
  comp_subst = "(\<circ>\<^sub>s)" and id_subst = Var and term_subst = "(\<cdot>)" and term_vars = term.vars and
  apply_subst = apply_subst and subst_update = fun_upd and
  compose_context = "(\<circ>\<^sub>c)" and term_from_ground = term.from_ground and
  term_to_ground = term.to_ground and map_context = map_args_actxt and
  to_ground_context_map = map_args_actxt and from_ground_context_map = map_args_actxt and
  context_to_set = set2_actxt and hole = \<box> and apply_context = ctxt_apply_term and 
  occurences = occurences and ground_hole = \<box> and apply_ground_context = apply_ground_context and
  compose_ground_context = "(\<circ>\<^sub>c)" and ground_context_map = map_args_actxt and
  ground_context_to_set = set2_actxt and welltyped = welltyped and
  term_is_ground = term.is_ground and GFun = "\<lambda>f _. GFun f" and GMore = "\<lambda>f _. More f" and
  ground_fun_sym\<^sub>c = fun_sym\<^sub>c and ground_extra\<^sub>c = "\<lambda>_. ()" and ground_subterms\<^sub>l = subterms\<^sub>l and
  ground_subcontext = subcontext and ground_subterms\<^sub>r = subterms\<^sub>r and ground_size = size and
  ground_hole_position = hole_pos and ground_context_at = context_at\<^sub>G and ground_size\<^sub>c = size and
  ground_subterms = gargs and ground_fun_sym = groot_sym and ground_extra = "\<lambda>_. ()"

end
