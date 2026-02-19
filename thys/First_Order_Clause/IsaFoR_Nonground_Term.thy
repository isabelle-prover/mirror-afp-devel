theory IsaFoR_Nonground_Term
  imports 
    Nonground_Term
    Generic_Term
    Abstract_Substitution.Substitution_First_Order_Term
begin

global_interpretation "term": nonground_term where
  comp_subst = "(\<circ>\<^sub>s)" and id_subst = Var and term_subst = "(\<cdot>)" and apply_subst = apply_subst and
  subst_update = fun_upd and term_vars = vars_term and term_to_ground = gterm_of_term and
  term_from_ground = term_of_gterm and term_is_ground = is_ground
  by unfold_locales

fun fun_sym where
 "fun_sym (Fun f _) = f"

global_interpretation "term": term_interpretation where
  subterms = args and size = size and is_var = term.is_Var and Fun = "\<lambda>f _. Fun f" and 
  fun_sym = fun_sym and extra = "\<lambda>_. ()"
proof unfold_locales
  fix t t' :: "('f, 'v) term"
  assume "t' \<in> set (args t)"

  then show "size t' < size t"
    by (induction t) (auto simp: size_simp1)
next
  fix t :: "('f, 'v) term"

  show "\<not> term.is_Var t \<longleftrightarrow> (\<exists>f e ts. t = Fun f ts)"
    by (metis Term.term.simps(17,4) empty_not_insert term.exhaust_sel)
qed auto

end
