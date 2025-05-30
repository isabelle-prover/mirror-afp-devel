theory Ground_Superposition_Example
  imports 
    Typed_Ground_Superposition 
    First_Order_Clause.Monomorphic_Typing
    Monomorphic_Superposition
begin

(* TODO: Create real example *)
context monomorphic_superposition_calculus
begin

interpretation ground_example: typed_ground_superposition_calculus where
  hole = Hole and compose_context = actxt_compose and 
  apply_context = apply_ground_context and less\<^sub>t = "(\<prec>\<^sub>t\<^sub>G)" and
  select = "\<lambda>_. {#}" and term_welltyped = "Ground_Term_Typing.welltyped \<F>" 
  by unfold_locales auto    

end

end
