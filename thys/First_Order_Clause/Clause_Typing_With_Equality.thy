theory Clause_Typing_With_Equality
  imports 
    Clause_Typing_Generic
    Uprod_Literal_Functor
begin

locale clause_typing = "term": typing term_welltyped
  for term_welltyped
begin

sublocale atom: typing_lifting where
  sub_welltyped = term_welltyped and to_set = set_uprod
  by unfold_locales

lemma atom_is_welltyped_iff [simp]:
  "atom.is_welltyped (Upair t t') \<longleftrightarrow> (\<exists>\<tau>. term_welltyped t \<tau> \<and> term_welltyped t' \<tau>)"
  unfolding atom.is_welltyped_def
  by simp

sublocale clause_typing_generic where 
  atom_welltyped = atom.welltyped 
  by unfold_locales

lemma literal_is_welltyped_iff [simp]:
  "literal.is_welltyped (t \<approx> t') \<longleftrightarrow> atom.is_welltyped (Upair t t')"
  "literal.is_welltyped (t !\<approx> t') \<longleftrightarrow> atom.is_welltyped (Upair t t')"
  unfolding literal.is_welltyped_def
  by simp_all

lemma literal_is_welltyped_iff_atm_of:
  "literal.is_welltyped l \<longleftrightarrow> atom.is_welltyped (atm_of l)"
  unfolding literal.is_welltyped_def
  by (simp add: set_literal_atm_of)

end

end
