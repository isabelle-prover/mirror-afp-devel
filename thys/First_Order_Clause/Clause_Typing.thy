theory Clause_Typing
  imports Clause_Typing_Generic
begin

locale clause_typing = "term": base_typing term_welltyped
  for term_welltyped
begin

sublocale clause_typing_generic where atom_welltyped = term_welltyped
  by unfold_locales

lemma literal_is_welltyped_iff [simp]:
  "literal.is_welltyped (Pos t) \<longleftrightarrow> term.is_welltyped t"
  "literal.is_welltyped (Neg t) \<longleftrightarrow> term.is_welltyped t"
  unfolding literal.is_welltyped_def
  by simp_all

lemma literal_is_welltyped_iff_atm_of:
  "literal.is_welltyped l \<longleftrightarrow> term.is_welltyped (atm_of l)"
  unfolding literal.is_welltyped_def
  by (simp add: set_literal_atm_of)

end

end
