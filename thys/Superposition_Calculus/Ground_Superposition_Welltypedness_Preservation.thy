theory Ground_Superposition_Welltypedness_Preservation
  imports
    Ground_Superposition
    First_Order_Clause.Ground_Typing
begin

lemma (in ground_superposition_calculus) ground_superposition_preserves_typing:
  fixes \<F> :: "('f, 'ty) fun_types"
  assumes
    "superposition D E C"
    "clause.is_welltyped TYPE('ty) \<F> D"
    "clause.is_welltyped TYPE('ty) \<F> E"
  shows "clause.is_welltyped TYPE('ty) \<F> C"
  using assms
  by (cases rule: superposition.cases) (auto 4 3)

lemma (in ground_superposition_calculus) ground_eq_resolution_preserves_typing:
  fixes \<F> :: "('f, 'ty) fun_types"
  assumes "eq_resolution D C" "clause.is_welltyped TYPE('ty) \<F> D"
  shows "clause.is_welltyped TYPE('ty) \<F> C"
  using assms
  by (cases rule: eq_resolution.cases) auto

lemma (in ground_superposition_calculus) ground_eq_factoring_preserves_typing:
  fixes \<F> :: "('f, 'ty) fun_types"
  assumes "eq_factoring D C"
  shows "clause.is_welltyped TYPE('ty) \<F> D \<longleftrightarrow> clause.is_welltyped TYPE('ty) \<F> C"
  using assms
  by (cases rule: eq_factoring.cases) auto

end
