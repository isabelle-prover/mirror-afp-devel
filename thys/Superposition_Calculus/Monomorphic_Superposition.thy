theory Monomorphic_Superposition
  imports 
    Superposition
    First_Order_Clause.IsaFoR_Nonground_Clause_With_Equality
    First_Order_Clause.IsaFoR_Nonground_Context
begin

locale monomorphic_superposition_calculus = superposition_calculus where
  comp_subst = "(\<odot>)" and Var = Var and term_subst = "(\<cdot>t)" and term_vars = term.vars and
  compose_context = "(\<circ>\<^sub>c)" and term_from_ground = term.from_ground and
  term_to_ground = term.to_ground and map_context = map_args_actxt and
  to_ground_context_map = map_args_actxt and from_ground_context_map = map_args_actxt and
  context_to_set = set2_actxt and Hole = \<box> and apply_context = ctxt_apply_term and 
  occurences = occurences

end