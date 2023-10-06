(*  Title:      ML_Utils/attribute_util.ML
    Author:     Kevin Kappelmann

Utilities for attributes.
*)
signature ML_ATTRIBUTE_UTIL =
sig
  val apply_attribute : attribute -> Context.generic * thm -> Context.generic * thm

  val attribute_map_context : attribute -> Context.generic -> Context.generic
  val attribute_map_ctxt : attribute -> Proof.context -> Proof.context
end

structure ML_Attribute_Util : ML_ATTRIBUTE_UTIL =
struct

fun apply_attribute attr (context, thm) = swap (Thm.apply_attribute attr thm context)

fun attribute_map_context attr = Thm.attribute_declaration attr Drule.dummy_thm
val attribute_map_ctxt = Context.proof_map o attribute_map_context

end