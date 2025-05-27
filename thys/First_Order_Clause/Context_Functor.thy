theory Context_Functor
  imports 
    Regular_Tree_Relations.Term_Context 
    Abstract_Substitution.Natural_Functor
begin

(* TODO:*)
no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)
no_notation subst_apply_term (infixl "\<cdot>" 67)

type_synonym ('f, 'v) "context" = "('f, 'v) ctxt"

global_interpretation "context": finite_natural_functor where
  map = map_args_actxt and to_set = set2_actxt
proof unfold_locales
  fix t :: 't

  show "\<exists>c. set2_actxt c \<noteq> {}"
    by (metis actxt.set_intros(5) empty_iff in_set_conv_decomp)
next
  fix c :: "('f, 't) actxt"

  show "finite (set2_actxt c)"
    by(induction c) auto
qed (auto
    simp: actxt.set_map(2) actxt.map_comp fun.map_ident actxt.map_ident_strong
    cong: actxt.map_cong)

global_interpretation "context": natural_functor_conversion where
  map = map_args_actxt and to_set = set2_actxt and map_to = map_args_actxt and
  map_from = map_args_actxt and map' = map_args_actxt and to_set' = set2_actxt
  by unfold_locales
    (auto simp: actxt.set_map(2) actxt.map_comp cong: actxt.map_cong)

end
