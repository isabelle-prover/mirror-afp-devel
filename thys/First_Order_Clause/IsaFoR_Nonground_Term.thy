theory IsaFoR_Nonground_Term
  imports 
    Nonground_Term
    Generic_Term
    Abstract_Substitution.Substitution_First_Order_Term
begin

global_interpretation "term": nonground_term where
  comp_subst = "(\<circ>\<^sub>s)" and id_subst = Var and term_subst = "(\<cdot>)" and apply_subst = apply_subst and
  subst_update = fun_upd and subst_updates = subst_updates and term_vars = vars_term and
  term_to_ground = gterm_of_term and term_from_ground = term_of_gterm and
  term_is_ground = is_ground
  by unfold_locales

global_interpretation "term": smaller_subterms where
  subterms = args and size = size and is_var = is_Var
  by unfold_locales (metis in_set_simps(3) supt.intros(1) supt_size term.exhaust_sel term.sel(3))

end
