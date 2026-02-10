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

lemma eq_resolution_weakly_welltyped:
  assumes eq_resolution: "eq_resolution D C"
  shows "clause.weakly_welltyped D \<longleftrightarrow> clause.weakly_welltyped C"
  using eq_resolution
  by (cases rule: eq_resolution.cases) auto

lemma eq_factoring_weakly_welltyped_clause:
  assumes eq_factoring: "eq_factoring D C"
  shows "clause.weakly_welltyped D \<longleftrightarrow> clause.weakly_welltyped C"
  using eq_factoring
  by (cases rule: eq_factoring.cases) auto

lemma superposition_weakly_welltyped_clause:
  assumes superposition: "superposition D E C"
  shows "clause.weakly_welltyped D \<and> clause.weakly_welltyped E \<Longrightarrow> clause.weakly_welltyped C"
  using superposition
proof (cases rule: superposition.cases)
  case (superpositionI L\<^sub>E E' L\<^sub>D D' \<P> \<kappa> t u t')

  assume "clause.weakly_welltyped D \<and> clause.weakly_welltyped E"

  moreover have
    "atom.weakly_welltyped (Upair t t') \<Longrightarrow> atom.weakly_welltyped (Upair \<kappa>\<langle>t\<rangle> u) \<Longrightarrow>
     atom.weakly_welltyped (Upair \<kappa>\<langle>t'\<rangle> u)"
    unfolding weakly_welltyped_atom_iff
    by (meson welltyped_context_compatible welltyped_subterm)

  ultimately show "clause.weakly_welltyped C"
    using superpositionI(4)
    unfolding superpositionI
    by fastforce
qed

end

end
