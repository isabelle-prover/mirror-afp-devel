theory Nonground_Typing
  imports
    Clause_Typing
    Nonground_Term_Typing
    Typed_Functional_Substitution_Lifting
    Nonground_Clause
    Nonground_Order
begin

type_synonym ('f, 'v, 'ty) typed_clause = "('f, 'v) atom clause \<times> ('v, 'ty) var_types"

locale nonground_typing_lifting =
  is_typed: typed_subst_stability_lifting where base_typed = base_typed +
  is_welltyped: typed_subst_stability_lifting where
  sub_is_typed = sub_is_welltyped and base_typed = base_welltyped +

  is_typed: replaceable_\<V>_lifting where base_typed = base_typed +
  is_welltyped: replaceable_\<V>_lifting where
  sub_is_typed = sub_is_welltyped and base_typed = base_welltyped +

  is_typed: typed_renaming_lifting where base_typed = base_typed +
  is_welltyped: typed_renaming_lifting where
  sub_is_typed = sub_is_welltyped and base_typed = base_welltyped
for base_typed base_welltyped :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" and
    sub_is_welltyped

locale nonground_inhabited_typing_lifting =
  nonground_typing_lifting +
  is_typed: inhabited_typed_functional_substitution_lifting where base_typed = base_typed +
  is_welltyped: inhabited_typed_functional_substitution_lifting where
  sub_is_typed = sub_is_welltyped and base_typed = base_welltyped

locale nonground_uniform_typing_lifting =
  is_typed: uniform_typed_subst_stability_lifting where base_typed = base_typed +
  is_welltyped: uniform_typed_subst_stability_lifting where base_typed = base_welltyped +

  is_typed: uniform_replaceable_\<V>_lifting where base_typed = base_typed +
  is_welltyped: uniform_replaceable_\<V>_lifting where base_typed = base_welltyped +

  is_typed: uniform_typed_renaming_lifting where base_typed = base_typed +
  is_welltyped: uniform_typed_renaming_lifting where base_typed = base_welltyped
for base_typed base_welltyped :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool"

locale nonground_uniform_inhabited_typing_lifting =
  nonground_uniform_typing_lifting +
  is_typed: uniform_inhabited_typed_functional_substitution_lifting where base_typed = base_typed +
  is_welltyped: uniform_inhabited_typed_functional_substitution_lifting where 
  base_typed = base_welltyped

locale term_based_nonground_typing_lifting =
  "term": nonground_term +
  nonground_typing_lifting where  
  id_subst = Var and comp_subst = "(\<odot>)" and base_subst = "(\<cdot>t)" and base_vars = term.vars

locale term_based_nonground_inhabited_typing_lifting =
  "term": nonground_term +
  nonground_inhabited_typing_lifting where  
  id_subst = Var and comp_subst = "(\<odot>)" and base_subst = "(\<cdot>t)" and base_vars = term.vars

locale term_based_nonground_uniform_typing_lifting =
  "term": nonground_term +
  nonground_uniform_typing_lifting where
  id_subst = Var and comp_subst = "(\<odot>)" and map = map_uprod and to_set = set_uprod and
  base_vars = term.vars and base_subst = "(\<cdot>t)"

locale term_based_nonground_uniform_inhabited_typing_lifting =
  "term": nonground_term +
  nonground_uniform_inhabited_typing_lifting where
  id_subst = Var and comp_subst = "(\<odot>)" and map = map_uprod and to_set = set_uprod and
  base_vars = term.vars and base_subst = "(\<cdot>t)"

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
  sub_is_welltyped = atom.is_welltyped
  by unfold_locales

sublocale clause: term_based_nonground_typing_lifting where
  base_typed = typed and base_welltyped = welltyped and
  sub_vars = literal.vars and sub_subst = "(\<cdot>l)" and map = image_mset and to_set = set_mset and
  sub_is_typed = literal.is_typed and sub_is_welltyped = literal.is_welltyped
  by unfold_locales

abbreviation is_welltyped_grounding where
  "is_welltyped_grounding C \<V> \<gamma> \<equiv>
    clause.is_ground (C \<cdot> \<gamma>) \<and>
    clause.is_welltyped \<V> C \<and>
    term.subst.is_welltyped_on (clause.vars C) \<V> \<gamma> \<and>
    infinite_variables_per_type \<V>"

definition clause_groundings :: "('f, 'v, 'ty) typed_clause \<Rightarrow> 'f ground_atom clause set" where
  "clause_groundings C =
    { clause.to_ground (fst C \<cdot> \<gamma>) | \<gamma>. is_welltyped_grounding (fst C) (snd C) \<gamma> }"

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
  sub_is_welltyped = atom.is_welltyped
  by unfold_locales

sublocale clause: term_based_nonground_inhabited_typing_lifting where
  base_typed = typed and base_welltyped = welltyped and
  sub_vars = literal.vars and sub_subst = "(\<cdot>l)" and map = image_mset and to_set = set_mset and
  sub_is_typed = literal.is_typed and sub_is_welltyped = literal.is_welltyped
  by unfold_locales

end

end
