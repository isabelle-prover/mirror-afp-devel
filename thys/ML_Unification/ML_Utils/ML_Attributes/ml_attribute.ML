(*  Title:      ML_Utils/ml_attribute.ML
    Author:     Kevin Kappelmann

Attributes from ML code.
*)
signature ML_ATTRIBUTE =
sig
  val get_thm : Context.generic -> thm
  val put_thm : thm -> Context.generic -> Context.generic

  val run_attribute : ML_Code_Util.code * Position.T -> attribute
  val run_mixed_attribute : ML_Code_Util.code * Position.T -> attribute
  val run_declaration_attribute : ML_Code_Util.code * Position.T -> attribute
  val run_map_context : ML_Code_Util.code * Position.T -> attribute
  val run_rule_attribute : ML_Code_Util.code * Position.T -> attribute
  val run_Krule_attribute : ML_Code_Util.code * Position.T -> attribute
end

structure ML_Attribute : ML_ATTRIBUTE =
struct

structure U = ML_Code_Util

structure Thm_Data = Generic_Data(
  type T = thm
  val empty = Drule.dummy_thm
  val merge = fst
)

val get_thm = Thm_Data.get
val put_thm = Thm_Data.put

fun run_attribute (code, pos) (context, thm) =
  let
    val context = put_thm thm context
    val (context_internal, thm_internal) = apply2 (U.read o U.internal_name) ("context", "thm")
    val code =
      U.read "Context.>> (fn" @ context_internal @ U.read "=>" @
      U.read "let val" @ thm_internal @ U.read "= ML_Attribute.get_thm" @ context_internal @
      U.read "val" @ U.tuple [thm_internal, context_internal] @ U.read "=" @
        U.read "Thm.apply_attribute" @ U.atomic code @ thm_internal @ context_internal @
      U.read "in ML_Attribute.put_thm" @ thm_internal @ context_internal @ U.read "end)"
    val context = ML_Context.expression pos code context
    val thm = get_thm context
  in (SOME context, SOME thm) end

fun run_mixed_attribute (code, pos) =
  let val code = U.read "Thm.mixed_attribute" @ U.atomic code
  in run_attribute (code, pos) end

fun run_declaration_attribute (code, pos) =
  let val code = U.read "Thm.declaration_attribute" @ U.atomic code
  in run_attribute (code, pos) end

fun run_map_context (code, pos) (context, _) =
  let val code = U.read "Thm.declaration_attribute" @ (U.atomic (U.read "K" @ U.atomic code))
  in run_attribute (code, pos) (context, Drule.dummy_thm) end

fun run_rule_attribute (code, pos) =
  let val code = U.read "Thm.rule_attribute []" @ U.atomic code
  in run_attribute (code, pos) end

fun run_Krule_attribute (code, pos) =
  let val code =
    U.read "Thm.rule_attribute []" @ (U.atomic (U.read "K" @ U.atomic code))
  in run_attribute (code, pos) end

val parse_code_pos = Scan.lift (Parse.position U.parse_code)

val _ = Theory.setup
  (Attrib.setup \<^binding>\<open>ML_attr\<close>
    (parse_code_pos >> run_attribute)
    "attribute as ML code" #>
  Attrib.setup \<^binding>\<open>ML_mattr\<close>
    (parse_code_pos >> run_mixed_attribute)
    "mixed attribute as ML code" #>
  Attrib.setup \<^binding>\<open>ML_dattr\<close>
    (parse_code_pos >> run_declaration_attribute)
    "declaration attribute as ML code" #>
  Attrib.setup \<^binding>\<open>ML_map_context\<close>
    (parse_code_pos >> run_map_context)
    "context only attribute as ML code" #>
  Attrib.setup \<^binding>\<open>ML_rattr\<close>
    (parse_code_pos >> run_rule_attribute)
    "rule attribute as ML code" #>
  Attrib.setup \<^binding>\<open>ML_Krattr\<close>
    (parse_code_pos >> run_Krule_attribute)
    "theorem only rule attribute as ML code")

end