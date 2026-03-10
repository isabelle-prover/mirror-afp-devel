theory Context_Functor
  imports 
    Regular_Tree_Relations.Term_Context 
    Abstract_Substitution.Natural_Functor
begin

setup natural_functor_setups

type_synonym ('f, 'v) "context" = "('f, 'v) ctxt"

global_interpretation "context": non_empty_finite_natural_functor where
  map = map_args_actxt and to_set = set2_actxt
proof unfold_locales
  (* TODO: To make this automatic, I need the nested set_intros, can I get them in ML? *)
  show "\<exists>c. set2_actxt c \<noteq> {}"
    by (rule non_empty_helper, rule actxt.set_intros(5), rule list.set_intros)
qed

global_interpretation "context": natural_functor_conversion where
  map = map_args_actxt and to_set = set2_actxt and map_to = map_args_actxt and
  map_from = map_args_actxt and map' = map_args_actxt and to_set' = set2_actxt
  by unfold_locales
    (auto simp: actxt.set_map(2) actxt.map_comp cong: actxt.map_cong)

end
