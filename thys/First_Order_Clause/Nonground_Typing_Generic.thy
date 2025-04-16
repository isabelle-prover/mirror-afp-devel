theory Nonground_Typing_Generic
  imports
    Clause_Typing_Generic
    Typed_Functional_Substitution_Lifting
    Nonground_Term_Typing
    Nonground_Clause_Generic
begin

locale nonground_typing_lifting =
  typed_subst_stability_lifting +
  replaceable_\<V>_lifting +
  typed_renaming_lifting +
  typed_grounding_functional_substitution_lifting

locale nonground_inhabited_typing_lifting =
  nonground_typing_lifting +
  inhabited_typed_functional_substitution_lifting where
  sub_welltyped = sub_welltyped and base_welltyped = base_welltyped

locale term_based_nonground_typing_lifting =
  base: nonground_term_typing +
  nonground_typing_lifting where
  base_welltyped = base.welltyped and id_subst = Var and comp_subst = "(\<odot>)" and
  base_subst = "(\<cdot>t)" and base_vars = base.term.vars

locale term_based_nonground_inhabited_typing_lifting =
  base: nonground_term_typing +
  nonground_inhabited_typing_lifting where
  base_welltyped = base.welltyped and id_subst = Var and comp_subst = "(\<odot>)" and
  base_subst = "(\<cdot>t)" and base_vars = base.term.vars

locale nonground_typing_generic =
  literal: term_based_nonground_typing_lifting where sub_welltyped = atom_welltyped and
  sub_to_ground = "atom_to_ground :: 'a \<Rightarrow> 'g" and sub_from_ground = atom_from_ground and
  sub_subst = atom_subst and sub_vars = atom_vars and map = map_literal and to_set = set_literal and
  to_ground_map = map_literal and from_ground_map = map_literal and ground_map = map_literal and
  to_set_ground = set_literal +
  nonground_term_typing +
  nonground_clause_generic
for atom_welltyped  :: "('v, 'ty) var_types \<Rightarrow> 'a \<Rightarrow> 'ty' \<Rightarrow> bool"
begin

sublocale clause_typing_generic "atom_welltyped \<V>"
  by unfold_locales

sublocale clause: term_based_nonground_typing_lifting where
  sub_vars = literal.vars and sub_subst = "(\<cdot>l)" and map = image_mset and to_set = set_mset and
  sub_welltyped = literal.welltyped and sub_to_ground = literal.to_ground and
  sub_from_ground = literal.from_ground and to_ground_map = image_mset and
  from_ground_map = image_mset and ground_map = image_mset and to_set_ground = set_mset
  by unfold_locales

end

locale nonground_inhabited_typing_generic =
  nonground_typing_generic +
  "term": nonground_term_inhabited_typing +
  literal: term_based_nonground_inhabited_typing_lifting where sub_welltyped = atom_welltyped and
  sub_to_ground = atom_to_ground and sub_from_ground = atom_from_ground and
  sub_subst = atom_subst and sub_vars = atom_vars and map = map_literal and to_set = set_literal and
  to_ground_map = map_literal and from_ground_map = map_literal and ground_map = map_literal and 
  to_set_ground = set_literal
begin

sublocale clause: term_based_nonground_inhabited_typing_lifting where
  sub_vars = literal.vars and sub_subst = "(\<cdot>l)" and map = image_mset and to_set = set_mset and
  sub_welltyped = literal.welltyped and
  sub_to_ground = literal.to_ground and sub_from_ground = literal.from_ground and
  to_ground_map = image_mset and from_ground_map = image_mset and ground_map = image_mset and
  to_set_ground = set_mset
  by unfold_locales

end

end
