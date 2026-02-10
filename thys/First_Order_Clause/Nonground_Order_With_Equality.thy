theory Nonground_Order_With_Equality
  imports
    Nonground_Clause_With_Equality
    Nonground_Order_Generic
    Ground_Order_With_Equality
begin

section \<open>Nonground Order\<close>

locale nonground_order =
  nonground_clause +
  "term": nonground_term_order
begin

sublocale restricted_term_order_lifting where
  restriction = "range term.from_ground" and pos_to_mset = pos_to_mset and neg_to_mset = neg_to_mset
  by unfold_locales

sublocale literal: nonground_term_based_order_lifting where
  less = less\<^sub>t and sub_subst = "(\<cdot>t)" and sub_vars = term.vars and sub_is_ground = term.is_ground and
  sub_to_ground = term.to_ground and sub_from_ground = term.from_ground and
  map = map_uprod_literal and to_set = uprod_literal_to_set and
  to_ground_map = map_uprod_literal and from_ground_map = map_uprod_literal and
  ground_map = map_uprod_literal and to_set_ground = uprod_literal_to_set and
  to_mset = literal_to_mset
rewrites
  "\<And>l \<sigma>. substitution_lifting.subst (\<cdot>t) map_uprod_literal l \<sigma> = literal.subst l \<sigma>" and
  "\<And>l. substitution_lifting.vars term.vars uprod_literal_to_set l = literal.vars l" and
  "\<And>l. substitution_lifting.is_ground term.is_ground uprod_literal_to_set l
    = literal.is_ground l" and
  "\<And>l\<^sub>G. grounding_lifting.from_ground term.from_ground map_uprod_literal l\<^sub>G
    = literal.from_ground l\<^sub>G" and
  "\<And>l. grounding_lifting.to_ground term.to_ground map_uprod_literal l = literal.to_ground l"
proof unfold_locales
  fix l

  show "set_mset (literal_to_mset l) = uprod_literal_to_set l"
    by (cases l) auto
next
  fix f l

  show "literal_to_mset (map_uprod_literal f l) = image_mset f (literal_to_mset l)"
    by (cases l) (auto simp: mset_uprod_image_mset)
qed (auto simp: inj_literal_to_mset)

notation literal.order.less\<^sub>G (infix "\<prec>\<^sub>l\<^sub>G" 50)
notation literal.order.less_eq\<^sub>G (infix "\<preceq>\<^sub>l\<^sub>G" 50)

sublocale nonground_order_generic where
  atom_subst = atom.subst and atom_vars = atom.vars and atom_is_ground = atom.is_ground and
  atom_from_ground = atom.from_ground and atom_to_ground = atom.to_ground and 
  neg_to_mset = neg_to_mset and pos_to_mset = pos_to_mset and ground_neg_to_mset = neg_to_mset and 
  ground_pos_to_mset = pos_to_mset
  by unfold_locales (simp_all add: atom.from_ground_def mset_uprod_image_mset)

lemma literal_order_less_if_all_lesseq_ex_less_set:
  assumes
    "\<forall>t \<in> set_uprod (atm_of l). t \<cdot>t \<sigma>' \<preceq>\<^sub>t t \<cdot>t \<sigma>"
    "\<exists>t \<in> set_uprod (atm_of l). t \<cdot>t \<sigma>' \<prec>\<^sub>t t \<cdot>t \<sigma>"
  shows "l \<cdot>l \<sigma>' \<prec>\<^sub>l l \<cdot>l \<sigma>"
  using assms literal.order.less_if_all_lesseq_ex_less 
  unfolding literal.order.to_mset_to_set[unfolded uprod_literal_to_set_atm_of]
  by presburger

end

locale context_compatible_nonground_order =
  nonground_order +
  "term": context_compatible_nonground_term_order
begin

sublocale literal.order: subst_update_stable_multiset_extension where
  less = less\<^sub>t and sub_subst = "(\<cdot>t)" and sub_vars = term.vars and sub_is_ground = term.is_ground and
  sub_to_ground = term.to_ground and sub_from_ground = term.from_ground and
  map = map_uprod_literal and to_set = uprod_literal_to_set and
  to_ground_map = map_uprod_literal and from_ground_map = map_uprod_literal and
  ground_map = map_uprod_literal and to_set_ground = uprod_literal_to_set and
  to_mset = literal_to_mset and base_vars = term.vars and base_less = less\<^sub>t and
  base_subst = "(\<cdot>t)" and base_is_ground = term.is_ground
  rewrites
  "\<And>l \<sigma>. substitution_lifting.subst (\<cdot>t) map_uprod_literal l \<sigma> = literal.subst l \<sigma>" and
  "\<And>l. substitution_lifting.vars term.vars uprod_literal_to_set l = literal.vars l" and
   "\<And>l. substitution_lifting.is_ground term.is_ground uprod_literal_to_set l
    = literal.is_ground l" and
  "\<And>l\<^sub>G. grounding_lifting.from_ground term.from_ground map_uprod_literal l\<^sub>G
    = literal.from_ground l\<^sub>G" and
  "\<And>l. grounding_lifting.to_ground term.to_ground map_uprod_literal l = literal.to_ground l"
  by unfold_locales simp_all

sublocale context_compatible_nonground_order_generic where
  atom_subst = atom.subst and atom_vars = atom.vars and atom_is_ground = atom.is_ground and
  atom_from_ground = atom.from_ground and atom_to_ground = atom.to_ground and
  neg_to_mset = neg_to_mset and pos_to_mset = pos_to_mset and ground_neg_to_mset = neg_to_mset and
  ground_pos_to_mset = pos_to_mset
  by unfold_locales

end

end
