theory Natural_Magma_Typing_Lifting
  imports
    Abstract_Substitution.Natural_Magma
    Typing
begin

locale natural_magma_is_typed_lifting = 
  natural_magma where to_set = to_set +
  typing_lifting where to_set = to_set and sub_welltyped = sub_welltyped
  for to_set :: "'expr \<Rightarrow> 'sub set" and sub_welltyped :: "'sub \<Rightarrow> unit \<Rightarrow> bool"
begin

abbreviation (input) sub_is_welltyped where
  "sub_is_welltyped expr \<equiv> sub_welltyped expr ()"

lemma add [simp]: "is_welltyped (add sub M) \<longleftrightarrow> (sub_is_welltyped sub \<and> is_welltyped M)"
  unfolding is_welltyped_def
  by auto

lemma plus [simp]:
  "is_welltyped (plus M M') \<longleftrightarrow> is_welltyped M \<and> is_welltyped M'"
  unfolding is_welltyped_def
  by auto

end

locale natural_magma_with_empty_is_typed_lifting =
  natural_magma_is_typed_lifting + natural_magma_with_empty
begin

lemma empty [intro]: "is_welltyped empty"
  unfolding is_welltyped_def
  by simp

end

locale natural_magma_typing_lifting =
  welltyped: natural_magma_is_typed_lifting where sub_welltyped = sub_welltyped +
  typing_lifting +
  natural_magma

locale natural_magma_with_empty_typing_lifting =
  natural_magma_typing_lifting + 
  welltyped: natural_magma_with_empty_is_typed_lifting where sub_welltyped = sub_welltyped

end
