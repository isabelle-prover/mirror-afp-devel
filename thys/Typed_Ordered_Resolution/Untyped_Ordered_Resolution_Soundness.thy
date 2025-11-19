theory Untyped_Ordered_Resolution_Soundness
  imports 
    Untyped_Ordered_Resolution_Inference_System
    Ordered_Resolution_Soundness
begin

context untyped_ordered_resolution_calculus
begin

sublocale untyped_sound_inference_system where 
  typed_bottom = "\<bottom>\<^sub>F" and typed_entails = typed.entails_\<G> and
  typed_inferences = typed.inferences and bottom = bottom and inferences = inferences and
  entails = entails
  by unfold_locales

end

end
