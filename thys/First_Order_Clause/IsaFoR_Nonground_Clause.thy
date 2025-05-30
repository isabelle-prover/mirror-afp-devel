theory IsaFoR_Nonground_Clause
  imports 
    IsaFoR_Nonground_Term
    Nonground_Clause
begin

interpretation nonground_clause where
  comp_subst = "(\<circ>\<^sub>s)" and Var = Var and term_subst = "(\<cdot>)" and term_vars = vars_term and
  term_to_ground = term.to_ground and term_from_ground = term.from_ground
  by unfold_locales

end
