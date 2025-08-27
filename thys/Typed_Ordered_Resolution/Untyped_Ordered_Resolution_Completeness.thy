theory Untyped_Ordered_Resolution_Completeness
  imports 
    Untyped_Ordered_Resolution_Inference_System
    Ordered_Resolution_Completeness
begin

context untyped_ordered_resolution_calculus
begin

(* TODO: Write own *)
abbreviation Red_F where 
  "Red_F N \<equiv> snd ` typed.Red_F_\<G> (empty_typed ` N)" 

abbreviation Red_I where
  "Red_I N \<equiv> remove_types ` typed.Red_I_\<G> (empty_typed ` N)"

sublocale untyped_complete_calculus where 
  typed_bottom = "\<bottom>\<^sub>F" and typed_entails = typed.entails_\<G> and
  typed_inferences = typed.inferences and typed_Red_I = typed.Red_I_\<G> and
  typed_Red_F = typed.Red_F_\<G> and bottom = bottom and inferences = inferences and Red_F = Red_F and
  Red_I = Red_I and entails = entails
  by unfold_locales

end

end
