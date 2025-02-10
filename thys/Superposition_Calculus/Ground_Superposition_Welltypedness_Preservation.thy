theory Ground_Superposition_Welltypedness_Preservation
  imports
    Ground_Superposition
    First_Order_Clause.Ground_Typing
begin

context ground_superposition_calculus
begin

sublocale ground_typing where \<F> = "\<F> :: ('f, 'ty) fun_types"
  by unfold_locales

context
  fixes \<F> :: "('f, 'ty) fun_types"
begin

lemma ground_superposition_preserves_typing:
  assumes
    "superposition D E C"
    "clause.is_welltyped D"
    "clause.is_welltyped E"
  shows "clause.is_welltyped C"
  using assms
  by (cases rule: superposition.cases) (auto 4 3)

lemma ground_eq_resolution_preserves_typing:
  assumes "eq_resolution D C" "clause.is_welltyped D"
  shows "clause.is_welltyped C"
  using assms
  by (cases rule: eq_resolution.cases) auto

lemma ground_eq_factoring_preserves_typing:
  assumes "eq_factoring D C"
  shows "clause.is_welltyped D \<longleftrightarrow> clause.is_welltyped C"
  using assms
  by (cases rule: eq_factoring.cases) auto

end

end

end
