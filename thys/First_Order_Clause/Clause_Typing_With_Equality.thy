theory Clause_Typing_With_Equality
  imports 
    Clause_Typing_Generic
    Uprod_Literal_Functor
    Weak_Typing_Multiset
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

sublocale atom: weakly_welltyped_base where
  sub_welltyped = term_welltyped and to_set = set_uprod
  by unfold_locales

sublocale literal: weakly_welltyped_lifting where
  sub_weakly_welltyped = atom.weakly_welltyped and to_set = set_literal and
  sub_welltyped = atom.welltyped 
  by unfold_locales

sublocale clause: mulitset_weakly_welltyped_lifting where
  sub_weakly_welltyped = literal.weakly_welltyped and sub_welltyped = literal.welltyped 
  by unfold_locales

lemma weakly_welltyped_atom_iff [simp]: 
  "atom.weakly_welltyped (Upair t t') \<longleftrightarrow> (\<forall>\<tau>. term_welltyped t \<tau> \<longleftrightarrow> term_welltyped t' \<tau>)"
  unfolding atom.weakly_welltyped_def
  by auto

lemma weakly_welltyped_literal_iff [simp]:
  "literal.weakly_welltyped (Pos a) \<longleftrightarrow> atom.weakly_welltyped a"
  "literal.weakly_welltyped (Neg a) \<longleftrightarrow> atom.weakly_welltyped a"
  unfolding literal.weakly_welltyped_def
  by auto

end

end
