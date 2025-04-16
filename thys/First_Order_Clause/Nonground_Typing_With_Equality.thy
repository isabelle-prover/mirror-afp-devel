theory Nonground_Typing_With_Equality
  imports
    Nonground_Typing_Generic
    Clause_Typing_With_Equality
    Nonground_Clause_With_Equality
begin

type_synonym ('f, 'v, 'ty) typed_clause = "('f, 'v) atom clause \<times> ('v, 'ty) var_types"

locale nonground_typing =
  nonground_clause +
  nonground_term_typing \<F>
  for \<F> :: "('f, 'ty) fun_types"
begin

sublocale atom: term_based_nonground_typing_lifting where 
  sub_welltyped = welltyped and sub_subst = "(\<cdot>t)" and sub_vars = term.vars and 
  to_set = set_uprod and map = map_uprod and sub_to_ground = term.to_ground and 
  sub_from_ground = term.from_ground and to_ground_map = map_uprod and 
  from_ground_map = map_uprod and ground_map = map_uprod and to_set_ground = set_uprod
  by unfold_locales

sublocale nonground_typing_generic where 
  atom_subst = "(\<cdot>a)" and atom_vars = atom.vars and atom_to_ground = atom.to_ground and
  atom_from_ground = atom.from_ground and atom_welltyped = atom.welltyped
  by unfold_locales

sublocale clause_typing "welltyped \<V>"
  by unfold_locales

end

locale nonground_inhabited_typing =
  nonground_term_inhabited_typing
begin

sublocale nonground_typing .

sublocale atom: term_based_nonground_inhabited_typing_lifting where
  sub_welltyped = welltyped and sub_subst = "(\<cdot>t)" and sub_vars = term.vars and
  to_set = set_uprod and map = map_uprod and sub_to_ground = term.to_ground and
  sub_from_ground = term.from_ground and to_ground_map = map_uprod and
  from_ground_map = map_uprod and ground_map = map_uprod and to_set_ground = set_uprod
  by unfold_locales

sublocale nonground_inhabited_typing_generic where
  atom_welltyped = atom.welltyped and atom_subst = "(\<cdot>a)" and atom_vars = atom.vars and 
  atom_to_ground = atom.to_ground and atom_from_ground = atom.from_ground
  by unfold_locales

end

end
