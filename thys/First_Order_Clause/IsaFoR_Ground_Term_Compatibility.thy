theory IsaFoR_Ground_Term_Compatibility
  imports
    IsaFoR_Nonground_Context
    Abstract_Substitution.Noop_Substitution
begin

interpretation ground: nonground_term where
  comp_subst = noop_comp_subst and id_subst = noop_id_subst and term_vars = noop_vars and
  subst_update = noop_subst_update and apply_subst = noop_apply_subst and
  term_subst = noop_subst and term_to_ground = id and term_from_ground = id and
  term_is_ground = noop_is_ground
  by unfold_locales (use unit.is_right_invertible_def in simp_all)

interpretation ground: nonground_term_with_context where
  comp_subst = noop_comp_subst and id_subst = noop_id_subst and term_vars = noop_vars and
  subst_update = noop_subst_update and apply_subst = noop_apply_subst and
  term_subst = noop_subst and term_to_ground = id and term_from_ground = id and
  apply_context = apply_ground_context and hole = \<box> and  compose_context = "(\<circ>\<^sub>c)" and
  ground_hole = \<box> and compose_ground_context = "(\<circ>\<^sub>c)" and
  apply_ground_context = apply_ground_context and occurences = "\<lambda>_ _. 0" and
  term_is_ground = noop_is_ground and context_is_ground = noop_is_ground and
  context_subst = noop_subst and context_vars = noop_vars and context_from_ground = id and
  context_to_ground = id
  by unfold_locales (simp_all add: noop_vars_def noop_subst_def noop_is_ground_def)

end
