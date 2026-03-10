theory Inference_Functor
  imports
    Abstract_Substitution.Natural_Functor
    Saturation_Framework_Extensions.Clausal_Calculus
begin

lemma set_inference_not_empty [iff]: "set_inference \<iota> \<noteq> {}"
  by (cases \<iota>) simp 

(* TODO: Make this nicer *)
setup "natural_functor_ignore @{type_name Inference_System.inference}"
                                                                  
setup natural_functor_setups
  
global_interpretation inference_functor: natural_functor_conversion where
  map = map_inference and to_set = set_inference and map_to = map_inference and
  map_from = map_inference and map' = map_inference and to_set' = set_inference
  by unfold_locales (auto simp: inference.set_map inference.map_comp)

end
