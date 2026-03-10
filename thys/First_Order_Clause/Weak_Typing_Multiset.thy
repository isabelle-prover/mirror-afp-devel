theory Weak_Typing_Multiset
  imports 
    Weak_Typing_Magma
    Multiset_Extra
begin

locale mulitset_weakly_welltyped_lifting = 
  weakly_welltyped_lifting where to_set = set_mset 
begin

sublocale weakly_welltyped_magma_with_empty_lifting where
  to_set = set_mset and plus = "(+)" and wrap = "\<lambda>l. {#l#}" and add = add_mset and empty = "{#}"
  by unfold_locales

end

end
