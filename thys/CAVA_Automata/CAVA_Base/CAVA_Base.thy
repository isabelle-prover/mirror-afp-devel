header "Setup of Environment for CAVA Model Checker"
theory CAVA_Base
  imports 
  "../../Collections/ICF/CollectionsV1"  (*-- {* Compatibility with ICF 1.0 *}*)
  "../../Collections/Refine_Dflt"      

  "Statistics" (*-- {* Collecting statistics by instrumenting the formalization *}*)

  "CAVA_Code_Target" (*-- {* Code Generator Setup *}*)
begin

(* Select-function that selects element from set *)
(* TODO: Move! Is select properly integrated into autoref? *)
  definition select where
    "select S \<equiv> if S={} then RETURN None else RES {Some s | s. s\<in>S}"

  text {* Cleaning up the namespace a bit *}
  
  hide_type (open) Word.word
  no_notation bits_class.test_bit (infixl "!!" 100)

  text {* Some custom setup in cava, that does not match HOL defaults: *}
  declare Let_def[simp add]

end
