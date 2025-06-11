theory Untyped_Superposition_Soundness
  imports 
    Untyped_Superposition_Inference_System
    Superposition_Soundness
begin

context untyped_superposition_calculus
begin

sublocale untyped_sound_inference_system where 
  typed_bottom = "\<bottom>\<^sub>F" and typed_entails = typed.entails_\<G> and
  typed_inferences = typed.inferences and bottom = bottom and inferences = inferences and
  entails = entails
  by unfold_locales

end

end
