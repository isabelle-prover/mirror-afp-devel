theory Nonground_Typing
  imports
    Clause_Typing
    Typed_Functional_Substitution_Lifting
    Nonground_Term_Typing
    Nonground_Clause
begin

type_synonym ('f, 'v, 'ty) typed_clause = "('f, 'v) atom clause \<times> ('v, 'ty) var_types"

locale nonground_typed_lifting =
  typed_subst_stability_lifting +
  replaceable_\<V>_lifting +
  typed_renaming_lifting +
  typed_grounding_functional_substitution_lifting

locale nonground_typing_lifting =
  is_welltyped: nonground_typed_lifting where
    sub_welltyped = sub_welltyped and base_welltyped = base_welltyped 
  for base_welltyped sub_welltyped
begin

abbreviation "is_welltyped_ground_instance \<equiv> is_welltyped.is_welltyped_ground_instance"

abbreviation "welltyped_ground_instances \<equiv> is_welltyped.welltyped_ground_instances"

lemmas welltyped_ground_instances_def = is_welltyped.welltyped_ground_instances_def

end

locale nonground_inhabited_typing_lifting =
  nonground_typing_lifting +
  welltyped: inhabited_typed_functional_substitution_lifting where
  sub_welltyped = sub_welltyped and base_welltyped = base_welltyped

locale term_based_nonground_typing_lifting =
  "term": nonground_term +
  nonground_typing_lifting where
  id_subst = Var and comp_subst = "(\<odot>)" and base_subst = "(\<cdot>t)" and base_vars = term.vars

locale term_based_nonground_inhabited_typing_lifting =
  "term": nonground_term +
  nonground_inhabited_typing_lifting where
  id_subst = Var and comp_subst = "(\<odot>)" and base_subst = "(\<cdot>t)" and base_vars = term.vars

locale nonground_typing =
  nonground_clause +
  nonground_term_typing \<F>
  for \<F> :: "('f, 'ty) fun_types"
begin

sublocale clause_typing "welltyped \<V>"
  by unfold_locales

sublocale atom: term_based_nonground_typing_lifting where
  base_welltyped = welltyped and map = map_uprod and to_set = set_uprod and 
  sub_welltyped = welltyped and sub_to_ground = term.to_ground and
  sub_from_ground = term.from_ground and to_ground_map = map_uprod and
  from_ground_map = map_uprod and ground_map = map_uprod and to_set_ground = set_uprod and
  sub_subst = "(\<cdot>t)" and sub_vars = term.vars
  by unfold_locales

sublocale literal: term_based_nonground_typing_lifting where
  base_welltyped = welltyped and sub_vars = atom.vars and sub_subst = "(\<cdot>a)" and
  map = map_literal and to_set = set_literal and sub_welltyped = atom.welltyped and
  sub_to_ground = atom.to_ground and sub_from_ground = atom.from_ground and
  to_ground_map = map_literal and from_ground_map = map_literal and ground_map = map_literal and
  to_set_ground = set_literal
  by unfold_locales

sublocale clause: term_based_nonground_typing_lifting where
  base_welltyped = welltyped and sub_vars = literal.vars and sub_subst = "(\<cdot>l)" and
  map = image_mset and to_set = set_mset and sub_welltyped = literal.welltyped and
  sub_to_ground = literal.to_ground and sub_from_ground = literal.from_ground and
  to_ground_map = image_mset and from_ground_map = image_mset and ground_map = image_mset and
  to_set_ground = set_mset
  by unfold_locales

end

locale nonground_inhabited_typing =
  nonground_typing \<F> +
  nonground_term_inhabited_typing \<F>
  for \<F> :: "('f, 'ty) fun_types"
begin

sublocale atom: term_based_nonground_inhabited_typing_lifting where
  base_welltyped = welltyped and map = map_uprod and to_set = set_uprod and 
  sub_welltyped = welltyped and sub_to_ground = term.to_ground and
  sub_from_ground = term.from_ground and to_ground_map = map_uprod and 
  from_ground_map = map_uprod and ground_map = map_uprod and to_set_ground = set_uprod and 
  sub_subst = "(\<cdot>t)" and sub_vars = term.vars
  by unfold_locales

sublocale literal: term_based_nonground_inhabited_typing_lifting where
  base_welltyped = welltyped and sub_vars = atom.vars and 
  sub_subst = "(\<cdot>a)" and map = map_literal and to_set = set_literal and
  sub_welltyped = atom.welltyped and sub_to_ground = atom.to_ground and
  sub_from_ground = atom.from_ground and to_ground_map = map_literal and
  from_ground_map = map_literal and ground_map = map_literal and to_set_ground = set_literal
  by unfold_locales

sublocale clause: term_based_nonground_inhabited_typing_lifting where
  base_welltyped = welltyped and
  sub_vars = literal.vars and sub_subst = "(\<cdot>l)" and map = image_mset and to_set = set_mset and
  sub_welltyped = literal.welltyped and
  sub_to_ground = literal.to_ground and sub_from_ground = literal.from_ground and
  to_ground_map = image_mset and from_ground_map = image_mset and ground_map = image_mset and
  to_set_ground = set_mset
  by unfold_locales

end

end
