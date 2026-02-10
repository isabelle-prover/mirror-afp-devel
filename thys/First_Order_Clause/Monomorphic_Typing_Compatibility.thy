theory Monomorphic_Typing_Compatibility
  imports 
    Nonground_Term_Typing 
    IsaFoR_Nonground_Term
begin

interpretation "term": compatibility where
  id_subst = "Var :: 'v \<Rightarrow> ('f, 'v) term" and comp_subst = "(\<circ>\<^sub>s)" and subst = "(\<cdot>)" and
  vars = term.vars and is_ground = term.is_ground and apply_subst = apply_subst and
  subst_updates = subst_updates
proof unfold_locales
    fix t :: "('f, 'v) term" and X \<sigma> b
  assume "term.vars t \<subseteq> X"

  then show "t \<cdot> (\<lambda>x. get_or (if x \<in> X then Some (\<sigma> x) else b x) (Var x)) = t \<cdot> \<sigma>"
    by (simp add: eval_same_vars subset_iff)
next
  fix t :: "('f, 'v) term" and X \<sigma> b
  assume "term.vars t \<inter> X = {}"

  then show "t \<cdot> (\<lambda>x. get_or (if x \<in> X then b x else Some (\<sigma> x)) (Var x)) = t \<cdot> \<sigma>"
    by (induction t) auto
next
  fix t :: "('f, 'v) term" and \<sigma> \<tau> :: "('f, 'v) subst"
  assume "\<And>x. x \<in> term.vars t \<Longrightarrow> \<sigma> x = \<tau> x" 

  then show "t \<cdot> \<sigma> = t \<cdot> \<tau>"
    by (simp add: eval_same_vars)
next
  fix t :: "('f, 'v) term" and \<gamma> :: "('f, 'v) subst"
  assume "\<forall>x\<in>term.vars t. term.is_ground (\<gamma> x)"

  then show "term.is_ground (t \<cdot> \<gamma>)"
    by (meson ground_subst term_context_ground_iff_term_is_ground)
qed

end
