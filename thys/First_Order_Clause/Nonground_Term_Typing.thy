theory Nonground_Term_Typing
  imports
    Term_Typing
    Typed_Functional_Substitution
    Nonground_Term
begin

(* TODO: Names *)

locale base_typing_properties =
  base_typed_renaming +
  base_typed_subst_stability +
  replaceable_\<V> where
    base_subst = subst and base_vars = vars and base_welltyped = welltyped +
  typed_grounding_functional_substitution where 
    base_subst = subst and base_vars = vars and base_welltyped = welltyped
begin

(* TODO: Does this also work without \<rho> being a renaming? + Move  *)
lemma type_preserving_on_subst_compose_renaming:
  assumes
    \<rho>: "is_renaming \<rho>" and
    \<rho>_type_preserving: "type_preserving_on X \<V> \<rho>" and 
    \<rho>_\<sigma>_type_preserving: "type_preserving_on X \<V> (\<rho> \<odot> \<sigma>)" 
shows "type_preserving_on (\<Union>(vars `\<rho> ` X)) \<V> \<sigma>"
proof (intro ballI impI)
  fix y

  assume y_in_\<rho>_X: "y \<in> \<Union> (vars ` \<rho> ` X)" and y_welltyped: "\<V> \<turnstile> id_subst y : \<V> y"

  obtain x where y: "id_subst y = \<rho> x" and x_in_X: "x \<in> X"
    using obtain_renamed_variable[OF \<rho>] vars_id_subst y_in_\<rho>_X
    by (smt (verit, best) UN_E UN_simps(10) singletonD)

  then have x_is_welltyped: "\<V> \<turnstile> id_subst x : \<V> x"
    using y_welltyped \<rho>_type_preserving welltyped_subst_stability welltyped_id_subst
    by (metis comp_subst_iff left_neutral singletonD vars_id_subst)
  
  then have "\<V> \<turnstile> (comp_subst \<rho> \<sigma>) x : \<V> x"
    using \<rho>_\<sigma>_type_preserving x_in_X 
    by blast

  moreover have "\<V> \<turnstile> \<rho> x : \<V> x"
    using \<rho>_type_preserving x_in_X x_is_welltyped
    by blast

  ultimately show "\<V> \<turnstile> \<sigma> y : \<V> y" 
    unfolding comp_subst_iff
    using y_welltyped y
    by (metis comp_subst_iff left_neutral right_uniqueD)
qed

end

locale term_typing_properties =
  "term": nonground_term +
  base_typed_functional_substitution where (* TODO: Does this work? *)
  id_subst = Var and comp_subst = "(\<odot>)" and subst = "(\<cdot>t)" and vars = term.vars and 
  welltyped = welltyped +
  "term": base_typing_properties where 
  subst = "(\<cdot>t)" and vars = term.vars and id_subst = Var and comp_subst = "(\<odot>)" and 
  to_ground = term.to_ground and from_ground = term.from_ground and welltyped = welltyped 
for welltyped :: "('v, 'ty) var_types \<Rightarrow> ('f, 'v) term \<Rightarrow> 'ty \<Rightarrow> bool" +
assumes "\<And>\<V>. term_typing (welltyped \<V>) Fun"
begin

notation welltyped (\<open>_ \<turnstile> _ : _\<close> [1000, 0, 50] 50)

sublocale "term": base_typing where welltyped = "welltyped \<V>" for \<V>
  by (simp add: base_typing_def typing_axioms)

sublocale "term": term_typing where welltyped = "welltyped \<V>" and Fun = Fun for \<V>
  using
    term_typing_properties_axioms 
    term_typing_properties_axioms_def 
    term_typing_properties_def
  by blast

end

locale base_witnessed_typing_properties =
  base_typing_properties +
  witnessed_typed_functional_substitution where 
  welltyped = welltyped and base_subst = subst and base_vars = vars and base_welltyped = welltyped

end
