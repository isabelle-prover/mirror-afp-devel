(*  Title:      ML_Typeclasses/eval_antiquotation.ML
    Author:     Kevin Kappelmann

Antiquotation for evaluation with string result.
*)
@{parse_entries (sig) PARSE_EVAL_ANTIQUOTATION_ARGS [parser]}

signature EVAL_ANTIQUOTATION_ARGS =
sig
  structure PA : PARSE_EVAL_ANTIQUOTATION_ARGS

  type args = (string context_parser) PA.entries
  val eval : args -> string context_parser
  val arg_parsers : (ML_Code_Util.code parser) PA.entries
end

structure Eval_Antiquotation_Args : EVAL_ANTIQUOTATION_ARGS =
struct

@{parse_entries (struct) PA [parser]}

type args = (string context_parser) PA.entries

fun eval entries = PA.get_parser entries

val arg_parsers = {
  parser = SOME (Parse_Util.nonempty_code (K "parser must not be empty"))
}

end

signature EVAL_ANTIQUOTATION =
sig
  structure Data : GENERIC_DATA
  where type T = Eval_Antiquotation_Args.args

  val get_args : Context.generic -> Eval_Antiquotation_Args.args
  val map_args : (Eval_Antiquotation_Args.args -> Eval_Antiquotation_Args.args) ->
    Context.generic -> Context.generic

  val get_parser : Context.generic -> string context_parser
  val map_parser : (string context_parser -> string context_parser) ->
    Context.generic -> Context.generic

  val eval : Context.generic -> string context_parser

  val binding : binding

  val parse_arg_entries : ML_Code_Util.code Eval_Antiquotation_Args.PA.entries parser
  val attribute : ML_Code_Util.code Eval_Antiquotation_Args.PA.entries * Position.T -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : string option -> local_theory -> local_theory

  val setup_antiquotation : theory -> theory
end

functor Eval_Antiquotation(
    structure FI : FUNCTOR_INSTANCE_BASE
    val init_args : Eval_Antiquotation_Args.args
  ) : EVAL_ANTIQUOTATION =
struct

structure EAA = Eval_Antiquotation_Args
structure PA = EAA.PA
structure FI = Functor_Instance(FI)
structure MCU = ML_Code_Util

structure Data = Generic_Data(
  type T = EAA.args
  val empty = init_args
  val merge = fst
)

val get_args = Data.get
val map_args = Data.map

val get_parser = PA.get_parser o get_args
val map_parser = map_args o PA.map_parser

fun eval context = get_args context |> EAA.eval

val binding = Binding.make (FI.prefix_id "eval", FI.pos)

val parse_arg_entries =
  let
    val parsers = EAA.arg_parsers
    val parse_value = PA.parse_entry (PA.get_parser parsers)
    val parse_entry = Parse_Key_Value.parse_entry PA.parse_key (K (Parse.$$$ ":")) parse_value
    val required_keys = []
    val default_entries = PA.empty_entries ()
  in PA.parse_entries_required Scan.repeat1 true required_keys parse_entry default_entries end

fun attribute (entries, pos) =
  let
    fun EAA_substructure_op substructure operation =
      MCU.flat_read ["Eval_Antiquotation_Args.", substructure, ".", operation]
    val code_PA_op = EAA_substructure_op "PA"
    val code_from_key = code_PA_op o PA.key_to_string
    fun code_from_entry (PA.parser c) = c
    val code_entries = PA.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code =
      FI.code_struct_op "map_args" @ MCU.atomic (code_PA_op "merge_entries" @
      MCU.atomic (code_PA_op "entries_from_entry_list" @ code_entries))
  in ML_Attribute.run_map_context (code, pos) end

val parse_attribute = (parse_arg_entries |> Parse_Util.position) >> attribute

val setup_attribute = Attrib.local_setup binding (Scan.lift (Parse.!!! parse_attribute)) o
  the_default ("configure eval antiquotation data " ^ enclose "(" ")" FI.long_name)

val setup_antiquotation =
  ML_Antiquotation.declaration binding (`(fst #> eval) #> (fn (parser, x) => parser x))
  (K (fn mk_code => pair ((K mk_code) #> pair "")))

end