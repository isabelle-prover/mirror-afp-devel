theory IsaFoR_Nonground_Clause
  imports 
    IsaFoR_Nonground_Term
    Nonground_Clause
begin

interpretation nonground_clause where
  comp_subst = "(\<circ>\<^sub>s)" and id_subst = Var and subst_update = fun_upd and
  subst_updates = subst_updates and apply_subst = apply_subst and term_subst = "(\<cdot>)" and
  term_vars = vars_term and term_to_ground = term.to_ground and term_from_ground = term.from_ground
  by unfold_locales

end
