theory Nonground_Term_Typing
  imports
    Term_Typing
    Typed_Substitution
    Nonground_Context
begin

(* TODO: *)
locale compatibility = 
  base_substitution +
  subst_eq +
  vars_grounded_iff_is_grounding +
  subst_updates_compat

locale base_typing_properties =
  base_typed_renaming +
  base_typed_subst_stability +
  base_replaceable_\<V> +
  typed_grounding_substitution where
  base_subst = subst and base_vars = vars and base_is_ground = is_ground and
  base_welltyped = welltyped +
  compatibility
begin

(* TODO: *)
lemma type_preserving_on_subst_compose_renaming:
  assumes
    \<rho>: "is_renaming \<rho>" and
    \<rho>_type_preserving: "type_preserving_on X \<V> \<rho>" and 
    \<rho>_\<sigma>_type_preserving: "type_preserving_on X \<V> (\<rho> \<odot> \<sigma>)" 
  shows "type_preserving_on (\<Union>(vars ` var_subst \<rho> ` X)) \<V> \<sigma>"
proof (intro ballI impI)
  fix y

  assume y_in_\<rho>_X: "y \<in> \<Union> (vars ` var_subst \<rho> ` X)" and y_welltyped: "\<V> \<turnstile> y \<cdot>v id_subst : \<V> y"

  then have exists_nonground: "exists_nonground"
    using no_vars_if_is_ground by auto

  obtain x where y: "y \<cdot>v id_subst = x \<cdot>v \<rho>" and x_in_X: "x \<in> X"
    using obtain_renamed_variable[OF exists_nonground \<rho>] vars_id_subst[OF exists_nonground] y_in_\<rho>_X
    by (smt (verit, best) UN_E UN_simps(10) singletonD)

  then have x_is_welltyped: "\<V> \<turnstile> x \<cdot>v id_subst : \<V> (rename \<rho> x)"
    using \<rho> \<rho>_type_preserving y_welltyped exists_nonground
    by (metis bot_set_def comp_subst_iff id_subst_rename left_neutral
        singleton_iff vars_id_subst welltyped_subst_stability)

  then have "\<V> \<turnstile> x \<cdot>v \<rho> \<odot> \<sigma> : \<V> (rename \<rho> x)"
    by (metis \<rho>_\<sigma>_type_preserving id_subst_subst singletonD
        vars_id_subst_subset welltyped_subst_stability' x_in_X)

  then show "\<V> \<turnstile> y \<cdot>v \<sigma> : \<V> y" 
    using exists_nonground
    unfolding comp_subst_iff
    using y_welltyped y
    by (metis \<rho>_type_preserving id_subst_subst right_uniqueD
        welltyped_id_subst x_in_X x_is_welltyped)
qed

end

locale term_typing_properties = 
  "term": nonground_term where term_vars = term_vars +

  base_typed_substitution where
  subst = term_subst and vars = term_vars and is_ground = term_is_ground and welltyped = welltyped +

  "term": base_typing_properties where 
  subst = term_subst and vars = term_vars and is_ground = term_is_ground and comp_subst = "(\<odot>)" and 
  to_ground = term_to_ground and from_ground = term_from_ground and welltyped = welltyped +

  type_preserving_imgu where
  welltyped = welltyped and subst = term_subst and vars = term_vars and is_ground = term_is_ground
for 
  welltyped :: "('v, 'ty) var_types \<Rightarrow> 't \<Rightarrow> 'ty \<Rightarrow> bool" and
  term_vars :: "'t \<Rightarrow> 'v set"
begin

(* TODO: Move as far up as possible *)
notation welltyped (\<open>_ \<turnstile> _ : _\<close> [1000, 0, 50] 50)

sublocale "term": base_typing where welltyped = "welltyped \<V>" for \<V>
  using typing_axioms
  unfolding base_typing_def .

end

locale base_witnessed_typing_properties =
  base_typing_properties +
  witnessed_typed_substitution where 
  welltyped = welltyped and base_subst = subst and base_vars = vars and
  base_is_ground = is_ground and base_welltyped = welltyped

locale context_compatible_term_typing_properties =
  nonground_term_with_context where term_vars = term_vars +
  term_typing_properties where welltyped = welltyped and term_vars = term_vars
for
  welltyped :: "('v, 'ty) var_types \<Rightarrow> 't \<Rightarrow> 'ty \<Rightarrow> bool" and
  term_vars :: "'t \<Rightarrow> 'v set" +
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
