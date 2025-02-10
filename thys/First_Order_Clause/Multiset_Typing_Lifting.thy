theory Multiset_Typing_Lifting
  imports
    Natural_Magma_Typing_Lifting
    Multiset_Extra
    Abstract_Substitution.Functional_Substitution_Lifting
begin

locale mulitset_typing_lifting = typing_lifting where to_set = set_mset
begin

sublocale natural_magma_with_empty_typing_lifting where
  to_set = set_mset and plus = "(+)" and wrap = "\<lambda>l. {#l#}" and add = add_mset and empty = "{#}"
  by unfold_locales simp

end

end
