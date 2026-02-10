theory Nonground_Typing
  imports
    Nonground_Typing_Generic
    Clause_Typing
    Nonground_Clause
begin

type_synonym ('t, 'v, 'ty) typed_clause = "('v, 'ty) var_types \<times> 't clause"

locale nonground_typing =
  nonground_clause +
  term_typing_properties
begin

sublocale nonground_typing_generic where 
  atom_vars = term.vars and atom_subst = "(\<cdot>t)" and atom_is_ground = term.is_ground and
  atom_to_ground = term.to_ground and atom_from_ground = term.from_ground and 
  atom_welltyped = welltyped
  by unfold_locales

sublocale clause_typing "welltyped \<V>"
  by unfold_locales

abbreviation is_ground_instance where 
  "is_ground_instance \<V> C \<gamma> \<equiv>
    clause.is_ground (C \<cdot> \<gamma>) \<and>
    type_preserving_on (clause.vars C) \<V> \<gamma> \<and>
    (term.exists_nonground \<longrightarrow> infinite_variables_per_type \<V>)"

sublocale groundable_nonground_clause where 
  atom_subst = "(\<cdot>t)" and atom_vars = term.vars and atom_is_ground = term.is_ground and
  atom_to_ground = term.to_ground and atom_from_ground = term.from_ground and
  is_ground_instance = is_ground_instance
  by unfold_locales simp

end

locale witnessed_nonground_typing =
  nonground_typing +
  base_witnessed_typing_properties where 
  subst = "(\<cdot>t)" and is_ground = term.is_ground and
  comp_subst = "(\<odot>)" and vars = term.vars and to_ground = term.to_ground and
  from_ground = term.from_ground
begin

sublocale witnessed_nonground_typing_generic where
  atom_vars = term.vars and atom_is_ground = term.is_ground and atom_subst = "(\<cdot>t)" and
  atom_to_ground = term.to_ground and atom_from_ground = term.from_ground and
  atom_welltyped = welltyped
  by unfold_locales

end

end
