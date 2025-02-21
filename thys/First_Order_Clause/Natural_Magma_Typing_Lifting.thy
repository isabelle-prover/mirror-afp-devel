theory Natural_Magma_Typing_Lifting
  imports
    Abstract_Substitution.Natural_Magma
    Typing
begin

locale natural_magma_is_typed_lifting = natural_magma where to_set = to_set
  for to_set :: "'expr \<Rightarrow> 'sub set" +
  fixes sub_is_typed :: "'sub \<Rightarrow> bool"
begin

abbreviation (input) is_typed where
  "is_typed \<equiv> is_typed_lifting to_set sub_is_typed"

lemma add [simp]:
  "is_typed (add sub M) \<longleftrightarrow> sub_is_typed sub \<and> is_typed M"
  using to_set_add
  unfolding is_typed_lifting_def
  by auto

lemma plus [simp]:
  "is_typed (plus M M') \<longleftrightarrow> is_typed M \<and> is_typed M'"
  unfolding is_typed_lifting_def
  by auto

end

locale natural_magma_with_empty_is_typed_lifting =
  natural_magma_is_typed_lifting + natural_magma_with_empty
begin

lemma empty [intro]: "is_typed empty"
  by (simp add: is_typed_lifting_def)

end

locale natural_magma_typing_lifting = typing_lifting + natural_magma
begin

sublocale is_typed: natural_magma_is_typed_lifting where sub_is_typed = sub_is_typed
  by unfold_locales

sublocale is_welltyped: natural_magma_is_typed_lifting where sub_is_typed = sub_is_welltyped
  by unfold_locales

end

locale natural_magma_with_empty_typing_lifting =
  natural_magma_typing_lifting + natural_magma_with_empty
begin

sublocale is_typed: natural_magma_with_empty_is_typed_lifting where sub_is_typed = sub_is_typed
  by unfold_locales

sublocale is_welltyped: natural_magma_with_empty_is_typed_lifting where
  sub_is_typed = sub_is_welltyped
  by unfold_locales

end

end
