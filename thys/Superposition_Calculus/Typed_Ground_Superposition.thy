theory Typed_Ground_Superposition
  imports
    Ground_Superposition
    First_Order_Clause.Clause_Typing_With_Equality
    First_Order_Clause.Term_Typing
begin

locale typed_ground_superposition_calculus =
  ground_superposition_calculus where apply_context = apply_context +
  term_typing where apply_context = apply_context and welltyped = term_welltyped
for 
  apply_context :: "'c \<Rightarrow> 't \<Rightarrow> 't" and
  term_welltyped :: "'t \<Rightarrow> 'ty \<Rightarrow> bool"
begin

sublocale clause_typing where term_welltyped = term_welltyped
  by unfold_locales

lemma ground_superposition_preserves_typing:
  assumes
    superposition: "superposition D E C" and
    D_is_welltyped: "clause.is_welltyped D" and
    E_is_welltyped: "clause.is_welltyped E"
  shows "clause.is_welltyped C"
  using assms
  by (cases rule: superposition.cases) (auto 4 4)

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
