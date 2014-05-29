header "Setup of Environment for CAVA Model Checker"
theory CAVA_Base
  imports 
  "../../Collections/ICF/CollectionsV1"  (*-- {* Compatibility with ICF 1.0 *}*)
  Collections_Patch2

  "Statistics" (*-- {* Collecting statistics by instrumenting the formalization *}*)

  "CAVA_Code_Target" (*-- {* Code Generator Setup *}*)
begin

  (* TODO: Due to merging policies, this has to be repeated here.
    Remove once Automatic_Refinement has been patched! *)
  declare rmp_del_itypes[autoref_itype del]

  text {* Cleaning up the namespace a bit *}
  
  hide_type (open) Word.word
  no_notation Bit_Operations.bits_class.test_bit (infixl "!!" 100)

  text {* Some custom setup in cava, that does not match HOL defaults: *}
  declare Let_def[simp add]

end
