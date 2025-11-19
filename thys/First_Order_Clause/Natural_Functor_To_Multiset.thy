theory Natural_Functor_To_Multiset
  imports
    Abstract_Substitution.Natural_Functor
    Multiset_Extra
begin

locale natural_functor_to_multiset = natural_functor where to_set = to_set
for
  to_mset :: "'b \<Rightarrow> 'a multiset" and
  to_set :: "'b \<Rightarrow> 'a set" +
assumes
  to_mset_to_set: "\<And>b. set_mset (to_mset b) = to_set b" and
  to_mset_map: "\<And>f b. to_mset (map f b) = image_mset f (to_mset b)"

global_interpretation id_natural_functor_multiset: natural_functor_to_multiset where
  to_set = set_mset and map = image_mset and to_mset = "\<lambda>x. x"
  by unfold_locales auto

end
