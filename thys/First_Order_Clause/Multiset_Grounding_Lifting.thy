theory Multiset_Grounding_Lifting
  imports
    "HOL-Library.Multiset"
    Abstract_Substitution.Functional_Substitution_Lifting
begin

locale multiset_grounding_lifting =
  functional_substitution_lifting where to_set = set_mset and map = image_mset +
  grounding_lifting where
  to_set = set_mset and map = image_mset and to_ground_map = image_mset and
  from_ground_map = image_mset and ground_map = image_mset and to_set_ground = set_mset
begin

sublocale natural_magma_with_empty_grounding_lifting where
  plus = "(+)" and wrap = "\<lambda>l. {#l#}" and plus_ground = "(+)" and wrap_ground = "\<lambda>l. {#l#}" and
  empty = "{#}" and empty_ground = "{#}" and to_set = set_mset and map = image_mset and
  to_ground_map = image_mset and from_ground_map = image_mset and ground_map = image_mset and
  to_set_ground = set_mset and add = add_mset and add_ground = add_mset
  by unfold_locales (simp_all add: to_ground_def from_ground_def)

sublocale natural_magma_functor_functional_substitution_lifting where
  plus = "(+)" and wrap = "\<lambda>l. {#l#}" and to_set = set_mset and map = image_mset and add = add_mset
  by unfold_locales simp_all

end

end
