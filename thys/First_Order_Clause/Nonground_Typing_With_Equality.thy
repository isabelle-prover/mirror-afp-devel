theory Nonground_Typing_With_Equality
  imports
    Nonground_Typing_Generic
    Clause_Typing_With_Equality
    Nonground_Clause_With_Equality
    Weakly_Typed_Substitution
begin

type_synonym ('t, 'v, 'ty) typed_clause = "('v, 'ty) var_types \<times> 't clause"

locale base_weakly_welltyped_properties =
  base_weakly_welltyped_unifier +
  base_weakly_welltyped_subst_stability +
  base_weakly_welltyped_renaming

locale weakly_welltyped_properties_lifting =
  weakly_welltyped_unifier_lifting +
  weakly_welltyped_subst_stability_lifting +
  weakly_welltyped_renaming_lifting

locale term_based_weakly_welltyped_lifting =
  term_typing_properties +
  weakly_welltyped_properties_lifting where base_subst = "(\<cdot>t)" and base_vars = term.vars and
  base_is_ground = term.is_ground and
  base_welltyped = welltyped 

locale nonground_typing =
  nonground_clause +
  term_typing_properties +
  atom: term_based_nonground_typing_lifting where 
  sub_welltyped = welltyped and sub_subst = "(\<cdot>t)" and sub_vars = term.vars and
  sub_is_ground = term.is_ground and
  to_set = set_uprod and map = map_uprod and sub_to_ground = term.to_ground and 
  sub_from_ground = term.from_ground and to_ground_map = map_uprod and 
  from_ground_map = map_uprod and ground_map = map_uprod and to_set_ground = set_uprod
begin

sublocale nonground_typing_generic where 
  atom_subst = "(\<cdot>a)" and atom_vars = atom.vars and atom_is_ground = atom.is_ground and
  atom_to_ground = atom.to_ground and atom_from_ground = atom.from_ground and
  atom_welltyped = atom.welltyped
  by unfold_locales

sublocale clause_typing "welltyped \<V>"
  by unfold_locales

sublocale atom: base_weakly_welltyped_properties where 
  base_subst = "(\<cdot>t)" and base_vars = term.vars and base_is_ground = term.is_ground and
  base_welltyped = welltyped and map = map_uprod and to_set = set_uprod
  by unfold_locales

sublocale literal: term_based_weakly_welltyped_lifting where
  map = map_literal and to_set = set_literal and sub_subst = "(\<cdot>a)" and sub_vars = atom.vars and
  sub_is_ground = atom.is_ground and sub_welltyped = atom.welltyped and
  sub_to_base_set = set_uprod and sub_weakly_welltyped = atom.weakly_welltyped
  by unfold_locales

sublocale clause: term_based_weakly_welltyped_lifting where
  map = image_mset and to_set = set_mset and sub_subst = "(\<cdot>l)" and sub_vars = literal.vars and
  sub_is_ground = literal.is_ground and sub_welltyped = literal.welltyped and
  sub_to_base_set = literal.to_base_set and sub_weakly_welltyped = literal.weakly_welltyped
  by unfold_locales

lemma [intro]:
  assumes "type_preserving_on (term.vars t \<union> term.vars t') \<V> \<mu>" "term.is_imgu \<mu> {{t, t'}}"
  shows
    imgu_weakly_welltyped_literal_Pos: "literal.weakly_welltyped \<V> (t \<approx> t')" and 
    imgu_weakly_welltyped_literal_Neg: "literal.weakly_welltyped \<V> (t !\<approx> t')"
  using atom.is_imgu_weakly_welltyped[of "Upair t t'"] assms
  unfolding literal.weakly_welltyped_def
  by auto

abbreviation is_ground_instance where 
  "is_ground_instance \<V> C \<gamma> \<equiv>
    clause.is_ground (C \<cdot> \<gamma>) \<and>
    type_preserving_on (clause.vars C) \<V> \<gamma> \<and>
    (term.exists_nonground \<longrightarrow> infinite_variables_per_type \<V>) \<and>
    clause.weakly_welltyped \<V> C"

sublocale groundable_nonground_clause where 
  atom_subst = "(\<cdot>a)" and atom_vars = atom.vars and atom_is_ground = atom.is_ground and
  atom_to_ground = atom.to_ground and atom_from_ground = atom.from_ground and
  is_ground_instance = is_ground_instance
  by unfold_locales simp

lemma \<P>_simps:
  assumes "\<P> \<in> {Pos, Neg}"
  shows 
    "\<And>a \<sigma>. \<P> a \<cdot>l \<sigma> = \<P> (a \<cdot>a \<sigma>)"
    "\<And>\<V> a. literal.is_welltyped \<V> (\<P> a) \<longleftrightarrow> atom.is_welltyped \<V> a"
    "\<And>a. literal.vars (\<P> a) = atom.vars a"
    "\<And>a. atm_of (\<P> a) = a"
    "\<And>\<V> a. literal.weakly_welltyped \<V> (\<P> a) \<longleftrightarrow> atom.weakly_welltyped \<V> a"
  using assms
  by (auto simp: literal_is_welltyped_iff_atm_of)

end

locale witnessed_nonground_typing =
  nonground_typing +

  atom: term_based_witnessed_nonground_typing_lifting where
  sub_welltyped = welltyped and sub_subst = "(\<cdot>t)" and sub_vars = term.vars and
  sub_is_ground = term.is_ground and
  to_set = set_uprod and map = map_uprod and sub_to_ground = term.to_ground and
  sub_from_ground = term.from_ground and to_ground_map = map_uprod and
  from_ground_map = map_uprod and ground_map = map_uprod and to_set_ground = set_uprod
begin

sublocale witnessed_nonground_typing_generic where
  atom_welltyped = atom.welltyped and atom_subst = "(\<cdot>a)" and atom_vars = atom.vars and
  atom_is_ground = atom.is_ground and atom_to_ground = atom.to_ground and
  atom_from_ground = atom.from_ground
  by unfold_locales

end

end
