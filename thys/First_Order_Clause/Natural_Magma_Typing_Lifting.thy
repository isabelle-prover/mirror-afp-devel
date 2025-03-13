theory Natural_Magma_Typing_Lifting
  imports
    Abstract_Substitution.Natural_Magma
    Typing
begin

(* TODO: Generalize *)
locale natural_magma_is_typed_lifting = 
  natural_magma where to_set = to_set +
  typed_lifting where to_set = to_set and sub_typed = sub_typed
  for to_set :: "'expr \<Rightarrow> 'sub set" and sub_typed :: "'sub \<Rightarrow> unit \<Rightarrow> bool"
begin

abbreviation (input) sub_is_typed where "sub_is_typed expr \<equiv> sub_typed expr ()"

lemma add [simp]: "is_typed (add sub M) \<longleftrightarrow> (sub_is_typed sub \<and> is_typed M)"
  unfolding is_typed_def
  by auto

lemma plus [simp]:
  "is_typed (plus M M') \<longleftrightarrow> is_typed M \<and> is_typed M'"
  unfolding is_typed_def
  by auto

end

locale natural_magma_with_empty_is_typed_lifting =
  natural_magma_is_typed_lifting + natural_magma_with_empty
begin

lemma empty [intro]: "is_typed empty"
  unfolding is_typed_def
  by simp

end

locale natural_magma_typing_lifting =
  typed: natural_magma_is_typed_lifting where sub_typed = sub_typed  +
  welltyped: natural_magma_is_typed_lifting where sub_typed = sub_welltyped +
  typing_lifting +
  natural_magma

locale natural_magma_with_empty_typing_lifting =
  natural_magma_typing_lifting + 
  typed: natural_magma_with_empty_is_typed_lifting where sub_typed = sub_typed + 
  welltyped: natural_magma_with_empty_is_typed_lifting where sub_typed = sub_welltyped

end
