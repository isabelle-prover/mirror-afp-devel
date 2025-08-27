theory Monomorphic_Ordered_Resolution
  imports 
    Ordered_Resolution

    First_Order_Clause.IsaFoR_Nonground_Clause
    First_Order_Clause.Monomorphic_Typing
begin

locale monomorphic_ordered_resolution_calculus = 
  monomorphic_term_typing +

  ordered_resolution_calculus where
  comp_subst = "(\<circ>\<^sub>s)" and Var = Var and term_subst = "(\<cdot>)" and term_vars = term.vars and
  term_from_ground = term.from_ground and term_to_ground = term.to_ground and welltyped = welltyped

end
