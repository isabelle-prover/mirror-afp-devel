theory Clause_Typing
  imports
    Multiset_Typing_Lifting

    Clausal_Calculus_Extra
    Multiset_Extra
    Uprod_Extra
begin

locale clause_typing =
  "term": explicit_typing term_typed term_welltyped
  for term_typed term_welltyped
begin

sublocale atom: uniform_typing_lifting where
  sub_typed = term_typed and
  sub_welltyped = term_welltyped and
  to_set = set_uprod
  by unfold_locales

lemma atom_is_typed_iff [simp]:
  "atom.is_typed (Upair t t') \<longleftrightarrow> (\<exists>\<tau>. term_typed t \<tau> \<and> term_typed t' \<tau>)"
  unfolding atom.is_typed_def
  by auto

lemma atom_is_welltyped_iff [simp]:
  "atom.is_welltyped (Upair t t') \<longleftrightarrow> (\<exists>\<tau>. term_welltyped t \<tau> \<and> term_welltyped t' \<tau>)"
  unfolding atom.is_welltyped_def
  by auto

sublocale literal: typing_lifting where
  sub_is_typed = atom.is_typed and
  sub_is_welltyped = atom.is_welltyped and
  to_set = set_literal
  by unfold_locales

lemma literal_is_typed_iff [simp]:
   "literal.is_typed (t \<approx> t') \<longleftrightarrow> atom.is_typed (Upair t t')"
   "literal.is_typed (t !\<approx> t') \<longleftrightarrow> atom.is_typed (Upair t t')"
  unfolding literal.is_typed_def
  by (simp_all add: set_literal_atm_of)

lemma literal_is_welltyped_iff [simp]:
  "literal.is_welltyped (t \<approx> t') \<longleftrightarrow> atom.is_welltyped (Upair t t')"
  "literal.is_welltyped (t !\<approx> t') \<longleftrightarrow> atom.is_welltyped (Upair t t')"
  unfolding literal.is_welltyped_def
  by simp_all

lemma literal_is_typed_iff_atm_of: "literal.is_typed l \<longleftrightarrow> atom.is_typed (atm_of l)"
  unfolding literal.is_typed_def
  by (simp add: set_literal_atm_of)

lemma literal_is_welltyped_iff_atm_of:
  "literal.is_welltyped l \<longleftrightarrow> atom.is_welltyped (atm_of l)"
  unfolding literal.is_welltyped_def
  by (simp add: set_literal_atm_of)

sublocale clause: mulitset_typing_lifting where
  sub_is_typed = literal.is_typed and
  sub_is_welltyped = literal.is_welltyped
  by unfold_locales

end

end
