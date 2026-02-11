theory Ground_Term_Context
  imports First_Order_Clause.Generic_Term_Context
begin

(* TODO: Do same pattern for nonground case *)
locale ground_term_context = 
  term_context_interpretation where is_var = "\<lambda>_. False" +
  smaller_subcontext where size = size\<^sub>c +
  replace_at_subterm where is_var = "\<lambda>_. False"
for size\<^sub>c

(* TODO: Name *)
locale ground_term_context' = ground_term_context where
  Fun = GFun and subterms = ground_subterms and fun_sym = ground_fun_sym and
  extra = ground_extra and size = ground_size and

  hole = ground_hole and compose_context = compose_ground_context and
  apply_context = apply_ground_context and subterms\<^sub>l = ground_subterms\<^sub>l and
  subcontext = ground_subcontext and subterms\<^sub>r = ground_subterms\<^sub>r and More = GMore and
  fun_sym\<^sub>c = ground_fun_sym\<^sub>c and extra\<^sub>c = ground_extra\<^sub>c and hole_position = ground_hole_position and
  context_at = ground_context_at and size\<^sub>c = ground_size\<^sub>c
for 
  GFun ground_subterms ground_fun_sym ground_extra ground_hole compose_ground_context
  apply_ground_context ground_subterms\<^sub>l ground_subcontext ground_subterms\<^sub>r GMore ground_fun_sym\<^sub>c
  ground_extra\<^sub>c ground_size ground_hole_position ground_context_at ground_size\<^sub>c


end
