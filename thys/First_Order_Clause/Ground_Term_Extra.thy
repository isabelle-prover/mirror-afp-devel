theory Ground_Term_Extra
  imports "Regular_Tree_Relations.Ground_Terms"
begin

(* TODO: *)
no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)
no_notation subst_apply_term (infixl "\<cdot>" 67)
no_notation ctxt_apply_term (\<open>_\<langle>_\<rangle>\<close> [1000, 0] 1000)
no_notation actxt_compose (infixl \<open>\<circ>\<^sub>c\<close> 75)
no_notation Hole (\<open>\<box>\<close>)

type_synonym 'f ground_term = "'f gterm"

end
