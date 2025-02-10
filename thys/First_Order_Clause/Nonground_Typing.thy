theory Nonground_Typing
  imports
    Clause_Typing
    Functional_Substitution_Typing_Lifting
    Nonground_Term_Typing
    Nonground_Clause
begin

type_synonym ('f, 'v, 'ty) typed_clause = "('f, 'v) atom clause \<times> ('v, 'ty) var_types"

locale nonground_uniform_typed_lifting =
  uniform_typed_subst_stability_lifting +
  uniform_replaceable_\<V>_lifting +
  uniform_typed_renaming_lifting +
  uniform_typed_grounding_functional_substitution_lifting

locale nonground_typed_lifting =
  typed_subst_stability_lifting +
  replaceable_\<V>_lifting +
  typed_renaming_lifting +
  typed_grounding_functional_substitution_lifting

locale nonground_uniform_typing_lifting =
  functional_substitution_uniform_typing_lifting +
  is_typed: nonground_uniform_typed_lifting where base_typed = base_typed +
  is_welltyped: nonground_uniform_typed_lifting where base_typed = base_welltyped
begin

abbreviation "is_typed_ground_instance \<equiv> is_typed.is_typed_ground_instance"

abbreviation "is_welltyped_ground_instance \<equiv> is_welltyped.is_typed_ground_instance"

abbreviation "typed_ground_instances \<equiv> is_typed.typed_ground_instances"

abbreviation "welltyped_ground_instances \<equiv> is_welltyped.typed_ground_instances"

lemmas typed_ground_instances_def = is_typed.typed_ground_instances_def

lemmas welltyped_ground_instances_def = is_welltyped.typed_ground_instances_def

end

(* TODO: is there a way to avoid duplication? *)
locale nonground_typing_lifting =
  functional_substitution_typing_lifting +
  is_typed: nonground_typed_lifting +
  is_welltyped: nonground_typed_lifting where
  sub_is_typed = sub_is_welltyped and base_typed = base_welltyped
begin

abbreviation "is_typed_ground_instance \<equiv> is_typed.is_typed_ground_instance"

abbreviation "is_welltyped_ground_instance \<equiv> is_welltyped.is_typed_ground_instance"

abbreviation "typed_ground_instances \<equiv> is_typed.typed_ground_instances"

abbreviation "welltyped_ground_instances \<equiv> is_welltyped.typed_ground_instances"

lemmas typed_ground_instances_def = is_typed.typed_ground_instances_def

lemmas welltyped_ground_instances_def = is_welltyped.typed_ground_instances_def

end

locale nonground_uniform_inhabited_typing_lifting =
  nonground_uniform_typing_lifting +
  is_typed: uniform_inhabited_typed_functional_substitution_lifting where base_typed = base_typed +
  is_welltyped: uniform_inhabited_typed_functional_substitution_lifting where
  base_typed = base_welltyped

locale nonground_inhabited_typing_lifting =
  nonground_typing_lifting +
  is_typed: inhabited_typed_functional_substitution_lifting where base_typed = base_typed +
  is_welltyped: inhabited_typed_functional_substitution_lifting where
  sub_is_typed = sub_is_welltyped and base_typed = base_welltyped

locale term_based_nonground_typing_lifting =
  "term": nonground_term +
  nonground_typing_lifting where
  id_subst = Var and comp_subst = "(\<odot>)" and base_subst = "(\<cdot>t)" and base_vars = term.vars

locale term_based_nonground_inhabited_typing_lifting =
  "term": nonground_term +
  nonground_inhabited_typing_lifting where
  id_subst = Var and comp_subst = "(\<odot>)" and base_subst = "(\<cdot>t)" and base_vars = term.vars

(* TODO: Try to reduce places where so many parameters need to be provided *)
locale term_based_nonground_uniform_typing_lifting =
  "term": nonground_term +
  nonground_uniform_typing_lifting where
  id_subst = Var and comp_subst = "(\<odot>)" and map = map_uprod and to_set = set_uprod and
  base_vars = term.vars and base_subst = "(\<cdot>t)" and sub_to_ground = term.to_ground and
  sub_from_ground = term.from_ground and to_ground_map = map_uprod and
  from_ground_map = map_uprod and ground_map = map_uprod and to_set_ground = set_uprod

locale term_based_nonground_uniform_inhabited_typing_lifting =
  "term": nonground_term +
  nonground_uniform_inhabited_typing_lifting where
  id_subst = Var and comp_subst = "(\<odot>)" and map = map_uprod and to_set = set_uprod and
  base_vars = term.vars and base_subst = "(\<cdot>t)" and sub_to_ground = term.to_ground and
  sub_from_ground = term.from_ground and to_ground_map = map_uprod and
  from_ground_map = map_uprod and ground_map = map_uprod and to_set_ground = set_uprod

locale nonground_typing =
  nonground_clause +
  nonground_term_typing \<F>
  for \<F> :: "('f, 'ty) fun_types"
begin

sublocale clause_typing "typed (\<V> :: ('v, 'ty) var_types)" "welltyped \<V>"
  by unfold_locales

sublocale atom: term_based_nonground_uniform_typing_lifting where
  base_typed = "typed :: ('v \<Rightarrow> 'ty) \<Rightarrow> ('f, 'v) Term.term \<Rightarrow> 'ty \<Rightarrow> bool" and
  base_welltyped = welltyped
  by unfold_locales

sublocale literal: term_based_nonground_typing_lifting where
  base_typed = "typed :: ('v \<Rightarrow> 'ty) \<Rightarrow> ('f, 'v) Term.term \<Rightarrow> 'ty \<Rightarrow> bool" and
  base_welltyped = welltyped and sub_vars = atom.vars and sub_subst = "(\<cdot>a)" and
  map = map_literal and to_set = set_literal and sub_is_typed = atom.is_typed and
  sub_is_welltyped = atom.is_welltyped and sub_to_ground = atom.to_ground and
  sub_from_ground = atom.from_ground and to_ground_map = map_literal and
  from_ground_map = map_literal and ground_map = map_literal and to_set_ground = set_literal
  by unfold_locales

sublocale clause: term_based_nonground_typing_lifting where
  base_typed = typed and base_welltyped = welltyped and
  sub_vars = literal.vars and sub_subst = "(\<cdot>l)" and map = image_mset and to_set = set_mset and
  sub_is_typed = literal.is_typed and sub_is_welltyped = literal.is_welltyped and
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

sublocale atom: term_based_nonground_uniform_inhabited_typing_lifting where
  base_typed = "typed :: ('v \<Rightarrow> 'ty) \<Rightarrow> ('f, 'v) Term.term \<Rightarrow> 'ty \<Rightarrow> bool" and
  base_welltyped = welltyped
  by unfold_locales

sublocale literal: term_based_nonground_inhabited_typing_lifting where
  base_typed = "typed :: ('v \<Rightarrow> 'ty) \<Rightarrow> ('f, 'v) Term.term \<Rightarrow> 'ty \<Rightarrow> bool" and
  base_welltyped = welltyped and sub_vars = atom.vars and sub_subst = "(\<cdot>a)" and
  map = map_literal and to_set = set_literal and sub_is_typed = atom.is_typed and
  sub_is_welltyped = atom.is_welltyped and sub_to_ground = atom.to_ground and
  sub_from_ground = atom.from_ground and to_ground_map = map_literal and
  from_ground_map = map_literal and ground_map = map_literal and to_set_ground = set_literal
  by unfold_locales

sublocale clause: term_based_nonground_inhabited_typing_lifting where
  base_typed = typed and base_welltyped = welltyped and
  sub_vars = literal.vars and sub_subst = "(\<cdot>l)" and map = image_mset and to_set = set_mset and
  sub_is_typed = literal.is_typed and sub_is_welltyped = literal.is_welltyped and
  sub_to_ground = literal.to_ground and sub_from_ground = literal.from_ground and
  to_ground_map = image_mset and from_ground_map = image_mset and ground_map = image_mset and
  to_set_ground = set_mset
  by unfold_locales

end

end
