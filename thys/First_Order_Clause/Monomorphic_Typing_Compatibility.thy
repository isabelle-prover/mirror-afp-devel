theory Monomorphic_Typing_Compatibility
  imports 
    Nonground_Term_Typing 
    IsaFoR_Nonground_Term
begin

interpretation "term": compatibility where
  id_subst = "Var :: 'v \<Rightarrow> ('f, 'v) term" and comp_subst = "(\<circ>\<^sub>s)" and subst = "(\<cdot>)" and
  vars = term.vars and is_ground = term.is_ground and apply_subst = apply_subst and
  subst_update = fun_upd
proof unfold_locales
  fix u and t :: "('f, 'v) term" and \<sigma> :: "('f, 'v) subst"
  assume "\<forall>x\<in>term.vars t. fmlookup u x = Some (\<sigma> x)"

  then show "t \<cdot> term.subst_updates Var u = t \<cdot> \<sigma>"
    by (induction t) (auto simp: exists_nonground_term term.subst_updates_var)
next
  fix t :: "('f, 'v) term" and \<gamma> :: "('f, 'v) subst"
  assume "\<forall>x\<in>term.vars t. term.is_ground (\<gamma> x)"

  then show "term.is_ground (t \<cdot> \<gamma>)"
    by (meson ground_subst term_context_ground_iff_term_is_ground)
qed (simp add: eval_same_vars)

end
