theory Ground_Order
  imports Ground_Order_Generic
begin

abbreviation (input) pos_to_mset where 
  "pos_to_mset a \<equiv> {# a #}"

abbreviation (input) neg_to_mset where 
  "neg_to_mset a \<equiv> {# a, a #}"

global_interpretation term_atom_to_mset: atom_to_mset where 
  pos_to_mset = pos_to_mset and neg_to_mset = neg_to_mset
proof unfold_locales

  show "inj pos_to_mset"
    by (simp add: inj_def)
next

  show "inj neg_to_mset"
    by (meson add_eq_conv_ex empty_not_add_mset injI)
qed simp

locale ground_order =
  term.order: ground_term_order
begin

sublocale ground_order_generic where pos_to_mset = pos_to_mset and neg_to_mset = neg_to_mset
  by unfold_locales

end

locale context_compatible_ground_order =
  ground_order +
  term.order: context_compatible_ground_term_order

end
