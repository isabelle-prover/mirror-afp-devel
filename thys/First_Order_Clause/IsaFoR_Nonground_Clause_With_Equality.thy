theory IsaFoR_Nonground_Clause_With_Equality
  imports 
    IsaFoR_Nonground_Term
    Nonground_Clause_With_Equality
begin

interpretation nonground_clause where
  comp_subst = "(\<circ>\<^sub>s)" and Var = Var and term_subst = "(\<cdot>)" and term_vars = vars_term and
  term_to_ground = term.to_ground and term_from_ground = term.from_ground
  by unfold_locales

end
