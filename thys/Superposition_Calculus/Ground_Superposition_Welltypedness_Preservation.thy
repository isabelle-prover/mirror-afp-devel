theory Ground_Superposition_Welltypedness_Preservation
  imports
    Ground_Superposition
    First_Order_Clause.Ground_Term_Typing
    First_Order_Clause.Clause_Typing_With_Equality
begin

context ground_superposition_calculus
begin

sublocale clause_typing where
  term_welltyped = "welltyped \<F>"
  by unfold_locales

lemma ground_superposition_preserves_typing:
  assumes
    "superposition D E C"
    "clause.is_welltyped TYPE('ty) \<F> D"
    "clause.is_welltyped TYPE('ty) \<F> E"
  shows "clause.is_welltyped TYPE('ty) \<F> C"
  using assms
  by (cases rule: superposition.cases) (auto 4 3)

lemma ground_eq_resolution_preserves_typing:
  assumes "eq_resolution D C" "clause.is_welltyped TYPE('ty) \<F> D"
  shows "clause.is_welltyped TYPE('ty) \<F> C"
  using assms
  by (cases rule: eq_resolution.cases) auto

lemma ground_eq_factoring_preserves_typing:
  assumes "eq_factoring D C"
  shows "clause.is_welltyped TYPE('ty) \<F> D \<longleftrightarrow> clause.is_welltyped TYPE('ty) \<F> C"
  using assms
  by (cases rule: eq_factoring.cases) auto

end

end
