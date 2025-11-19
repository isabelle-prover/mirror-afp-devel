theory Nonground_Order
  imports
    Nonground_Clause
    Nonground_Order_Generic
    Ground_Order
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
  less = less\<^sub>t and sub_subst = "(\<cdot>t)" and sub_vars = term.vars and
  sub_to_ground = term.to_ground and sub_from_ground = term.from_ground and map = map_literal and
  to_set = set_literal and to_ground_map = map_literal and from_ground_map = map_literal and 
  ground_map = map_literal and to_set_ground = set_literal and to_mset = literal_to_mset
proof unfold_locales
  fix l

  show "set_mset (literal_to_mset l) = set_literal l"
    by (cases l) auto
next
  fix f l

  show "literal_to_mset (map_literal f l) = image_mset f (literal_to_mset l)"
    by (cases l) auto
qed (simp add: inj_literal_to_mset)

notation literal.order.less\<^sub>G (infix "\<prec>\<^sub>l\<^sub>G" 50)
notation literal.order.less_eq\<^sub>G (infix "\<preceq>\<^sub>l\<^sub>G" 50)

sublocale nonground_order_generic where
  atom_subst = "(\<cdot>t)" and atom_vars = term.vars and atom_from_ground = term.from_ground and
  atom_to_ground = term.to_ground and neg_to_mset = neg_to_mset and pos_to_mset = pos_to_mset and
  ground_neg_to_mset = neg_to_mset and ground_pos_to_mset = pos_to_mset
  by unfold_locales auto

end

locale context_compatible_nonground_order =
  nonground_order +
  "term": context_compatible_nonground_term_order
begin

sublocale literal.order: subst_update_stable_multiset_extension where
  less = less\<^sub>t and sub_subst = "(\<cdot>t)" and sub_vars = term.vars and
  sub_to_ground = term.to_ground and sub_from_ground = term.from_ground and map = map_literal and
  to_set = set_literal and to_ground_map = map_literal and from_ground_map = map_literal and 
  ground_map = map_literal and to_set_ground = set_literal and to_mset = literal_to_mset and
  base_less = less\<^sub>t and base_subst = "(\<cdot>t)" and base_vars = term.vars
  by unfold_locales

sublocale context_compatible_nonground_order_generic where
  atom_subst = "(\<cdot>t)" and atom_vars = term.vars and atom_from_ground = term.from_ground and
  atom_to_ground = term.to_ground and neg_to_mset = neg_to_mset and pos_to_mset = pos_to_mset and
  ground_neg_to_mset = neg_to_mset and ground_pos_to_mset = pos_to_mset
  by unfold_locales

end

end
