theory Inference_Functor
  imports
    Abstract_Substitution.Natural_Functor
    Saturation_Framework_Extensions.Clausal_Calculus
begin

lemma set_inference_not_empty [iff]: "set_inference \<iota> \<noteq> {}"
  by(cases \<iota>) simp

lemma finite_set_inference [intro]: "finite (set_inference \<iota>)"
  by (metis inference.exhaust inference.set List.finite_set finite.simps finite_Un)

global_interpretation inference_functor: finite_natural_functor where
  map = map_inference and to_set = set_inference
  by
    unfold_locales
    (auto simp: inference.map_comp inference.map_ident inference.set_map intro: inference.map_cong)

global_interpretation inference_functor: natural_functor_conversion where
  map = map_inference and to_set = set_inference and map_to = map_inference and
  map_from = map_inference and map' = map_inference and to_set' = set_inference
 by unfold_locales
    (auto simp: inference.set_map inference.map_comp)

end
