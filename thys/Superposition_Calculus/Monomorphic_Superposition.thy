theory Monomorphic_Superposition
  imports 
    Superposition

    First_Order_Clause.IsaFoR_Ground_Critical_Pairs
    First_Order_Clause.IsaFoR_Nonground_Clause_With_Equality
    First_Order_Clause.IsaFoR_Nonground_Context
    First_Order_Clause.Monomorphic_Typing
begin

locale monomorphic_superposition_calculus = 
  monomorphic_term_typing +

  superposition_calculus where
  comp_subst = "(\<circ>\<^sub>s)" and Var = Var and term_subst = "(\<cdot>)" and term_vars = term.vars and
  compose_context = "(\<circ>\<^sub>c)" and term_from_ground = term.from_ground and
  term_to_ground = term.to_ground and map_context = map_args_actxt and
  to_ground_context_map = map_args_actxt and from_ground_context_map = map_args_actxt and
  context_to_set = set2_actxt and hole = \<box> and apply_context = ctxt_apply_term and 
  occurences = occurences and ground_hole = \<box> and apply_ground_context = apply_ground_context and
  compose_ground_context = "(\<circ>\<^sub>c)" and ground_context_map = map_args_actxt and
  ground_context_to_set = set2_actxt and welltyped = welltyped

end
