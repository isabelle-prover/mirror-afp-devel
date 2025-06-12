theory Nonground_Term_Typing
  imports
    Term_Typing
    Typed_Functional_Substitution
    Nonground_Context
begin

locale base_typing_properties =
  base_typed_renaming +
  base_typed_subst_stability +
  replaceable_\<V> where
    base_subst = subst and base_vars = vars and base_welltyped = welltyped +
  typed_grounding_functional_substitution where 
    base_subst = subst and base_vars = vars and base_welltyped = welltyped
begin

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

  then have x_is_welltyped: "\<V> \<turnstile> id_subst x : \<V> (rename \<rho> x)"
    using \<rho> \<rho>_type_preserving y_welltyped
    by (smt (verit, del_insts) comp_subst_iff id_subst_rename left_neutral
        singletonD vars_id_subst welltyped_id_subst welltyped_subst_stability)

  then have  "\<V> \<turnstile> (comp_subst \<rho> \<sigma>) x : \<V> (rename \<rho> x)"
    by (metis \<rho>_\<sigma>_type_preserving right_uniqueD welltyped_id_subst x_in_X)

  then show "\<V> \<turnstile> \<sigma> y : \<V> y" 
    unfolding comp_subst_iff
    using y_welltyped y
    by (metis (full_types) \<rho> comp_subst_iff id_subst_rename inv_renaming left_neutral)
qed

end

locale term_typing_properties = 
  "term": nonground_term where Var = Var +
  base_typed_functional_substitution where
  id_subst = Var and subst = term_subst and vars = term_vars and 
  welltyped = welltyped +
  "term": base_typing_properties where 
  subst = term_subst and vars = term_vars and id_subst = Var and comp_subst = "(\<odot>)" and 
  to_ground = term_to_ground and from_ground = term_from_ground and welltyped = welltyped  +
  type_preserving_imgu where
  welltyped = welltyped and id_subst = Var and subst = term_subst and vars = term_vars 
for 
  welltyped :: "('v, 'ty) var_types \<Rightarrow> 't \<Rightarrow> 'ty \<Rightarrow> bool" and
  Var :: "'v \<Rightarrow> 't"
begin

(* TODO: Move as far up as possible *)
notation welltyped (\<open>_ \<turnstile> _ : _\<close> [1000, 0, 50] 50)

sublocale "term": base_typing where welltyped = "welltyped \<V>" for \<V>
  using typing_axioms
  unfolding base_typing_def .

end

locale base_witnessed_typing_properties =
  base_typing_properties +
  witnessed_typed_functional_substitution where 
  welltyped = welltyped and base_subst = subst and base_vars = vars and base_welltyped = welltyped

locale context_compatible_term_typing_properties = 
  nonground_term_with_context where Var = Var +
  term_typing_properties where Var = Var and welltyped = welltyped
for 
  welltyped :: "('v, 'ty) var_types \<Rightarrow> 't \<Rightarrow> 'ty \<Rightarrow> bool" and
  Var :: "'v \<Rightarrow> 't" +
assumes "\<And>\<V>. term_typing (welltyped \<V>) apply_context"
begin

sublocale "term": term_typing where 
  welltyped = "welltyped \<V>" and apply_context = apply_context for \<V>
  using
    context_compatible_term_typing_properties_axioms 
    context_compatible_term_typing_properties_axioms_def 
    context_compatible_term_typing_properties_def
  by metis

end

end
