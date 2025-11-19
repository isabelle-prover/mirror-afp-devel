theory Ground_Order_With_Equality
  imports Ground_Order_Generic Uprod_Extra
begin

abbreviation (input) pos_to_mset where 
  "pos_to_mset \<equiv> mset_uprod"

abbreviation (input) neg_to_mset where 
  "neg_to_mset a \<equiv> mset_uprod a + mset_uprod a"

global_interpretation uprod_to_mset: atom_to_mset where 
  pos_to_mset = pos_to_mset and neg_to_mset = neg_to_mset
proof (unfold_locales; (rule inj_mset_uprod mset_uprod_plus_neq)?)

  show "inj neg_to_mset"
    using inj_mset_plus_same inj_mset_uprod
    unfolding inj_def
    by auto
qed

locale ground_order =
  term.order: ground_term_order
begin

sublocale ground_order_generic where 
  pos_to_mset = pos_to_mset and neg_to_mset = neg_to_mset
  by unfold_locales

end

locale context_compatible_ground_order =
  ground_order +
  term.order: context_compatible_ground_term_order

end
