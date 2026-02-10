theory Sorted_Terms_Ordered_Resolution
  imports 
    Ordered_Resolution

    First_Order_Clause.IsaFoR_Nonground_Clause
    First_Order_Clause.Sorted_Terms_Typing
begin

locale sorted_terms_ordered_resolution_calculus =
  sorted_terms_typing +

  ordered_resolution_calculus where
  comp_subst = "(\<circ>\<^sub>s)" and id_subst = Var and term_subst = "(\<cdot>)" and term_vars = term.vars and
  apply_subst = apply_subst and subst_update = fun_upd and subst_updates = subst_updates and
  term_from_ground = term.from_ground and term_to_ground = term.to_ground and
  term_is_ground = term.is_ground and welltyped = welltyped 

end
