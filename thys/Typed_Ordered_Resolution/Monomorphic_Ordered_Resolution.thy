theory Monomorphic_Ordered_Resolution
  imports 
    Ordered_Resolution

    First_Order_Clause.IsaFoR_Nonground_Clause
    First_Order_Clause.Monomorphic_Typing
begin

locale monomorphic_ordered_resolution_calculus =
  monomorphic_term_typing +

  ordered_resolution_calculus where
  comp_subst = "(\<circ>\<^sub>s)" and id_subst = Var and term_subst = "(\<cdot>)" and term_vars = term.vars and
  apply_subst = apply_subst and subst_update = fun_upd and
  term_from_ground = term.from_ground and term_to_ground = term.to_ground and
  term_is_ground = term.is_ground and welltyped = welltyped 

end
