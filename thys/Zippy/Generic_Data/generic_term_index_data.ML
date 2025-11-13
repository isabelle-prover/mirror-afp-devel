(*  Title:      Zippy/generic_term_index_data.ML
    Author:     Kevin Kappelmann

Term index stored in the generic context.
*)
@{parse_entries (sig) PARSE_GENERIC_TERM_INDEX_DATA_MODE [add, del]}

signature GENERIC_TERM_INDEX_DATA =
sig
  include HAS_LOGGER
  structure PM : PARSE_GENERIC_TERM_INDEX_DATA_MODE
  structure TI : TERM_INDEX

  type value
  val eq_value : value * value -> bool
  val pretty_value : Proof.context -> value -> Pretty.T

  type term_value = term * value
  val pretty_term_value : Proof.context -> term_value -> Pretty.T

  type index = term_value TI.term_index
  val pretty_index : Proof.context -> index -> Pretty.T

  structure Data : GENERIC_DATA
  where type T = index
  val get_index : Context.generic -> index
  val map_index : (index -> index) -> Context.generic -> Context.generic
  val pretty_Data : Proof.context -> Pretty.T

  val insert : term * value -> Context.generic -> Context.generic
  val delete : term * (term_value -> bool) -> Context.generic -> Context.generic

  val binding : Binding.binding
  val add_arg_parser : (string * ML_Code_Util.code, ML_Code_Util.code) Either.either list parser
  val del_arg_parser : (string * ML_Code_Util.code, ML_Code_Util.code) Either.either list parser
  val add_attribute : (string * ML_Code_Util.code, ML_Code_Util.code) Either.either list
    * Position.T -> attribute
  val del_attribute : (string * ML_Code_Util.code, ML_Code_Util.code) Either.either list
    * Position.T -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : (string, string) Either.either -> local_theory -> local_theory
end

functor Generic_Term_Index_Data(A :
  sig
    structure FI : FUNCTOR_INSTANCE_BASE
    val parent_logger : Logger.logger_binding
    structure TI : TERM_INDEX
    type value
    val eq_value : value * value -> bool
    val pretty_value : Proof.context -> value -> Pretty.T
  end) : GENERIC_TERM_INDEX_DATA =
struct

open A
structure FI = Functor_Instance(A.FI)
structure Show = SpecCheck_Show_Base
structure PU = Parse_Util
structure MCU = ML_Code_Util

val logger = Logger.setup_new_logger parent_logger FI.name

@{parse_entries (struct) PM [add, del]}

type term_value = term * value
fun pretty_term_value ctxt = Show.zip (Syntax.pretty_term ctxt) (pretty_value ctxt)

type index = term_value TI.term_index
fun pretty_index ctxt = TI.content #> Show.list (pretty_term_value ctxt)

val eq_insert = eq_snd eq_value
structure Data = Generic_Data(Term_Index_Generic_Data_Args(
  structure TI = TI
  type data = term_value
  val data_eq = eq_insert))

val get_index = Data.get
val map_index = Data.map
fun pretty_Data ctxt = get_index (Context.Proof ctxt) |> pretty_index ctxt

fun insert (t, value) context = map_index (fn ti =>
  let
    val ctxt = Context.proof_of context
    val term_value = (t, value)
    val key = TI.norm_term t
  in
    (@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.breaks [
        Pretty.block [Pretty.str "Inserting value ", pretty_value ctxt value],
        Pretty.block [Pretty.str "at key ", Syntax.pretty_term ctxt key, Pretty.str "."]
      ] |> Pretty.block |> Pretty.string_of);
    TI.insert (curry eq_insert term_value) (key, term_value) ti)
    handle Term_Index_Base.INSERT =>
      (@{log Logger.WARN} ctxt (fn _ =>
          Pretty.breaks [
          Pretty.block [Pretty.str "Value ", pretty_value ctxt value],
          Pretty.block [Pretty.str "already added at key ", Syntax.pretty_term ctxt key, Pretty.str "."]
        ] |> Pretty.block |> Pretty.string_of);
      ti)
  end) context

fun delete (t, select) context = map_index (fn ti =>
  let
    val ctxt = Context.proof_of context
    val key = TI.norm_term t
  in
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Deleting from key ", Syntax.pretty_term ctxt key
      ] |> Pretty.string_of);
    TI.delete select key ti)
    handle Term_Index_Base.DELETE =>
      (@{log Logger.WARN} (Context.proof_of context) (fn _ => Pretty.block [
        Pretty.str "No data for key ", Syntax.pretty_term ctxt key,
        Pretty.str " and given selector found."
      ] |> Pretty.string_of);
      ti)
  end) context

val binding = Binding.make (FI.id, FI.pos)

val add_arg_parser =
  (Args.parens (Parse.term --| Parse.$$$ "," -- PU.nonempty_code (K "value to add must not be empty"))
    >> Either.Left
  || PU.nonempty_code (K "data to add must not be empty") >> Either.Right)
  |> Scan.repeat1
val del_arg_parser =
  (Args.parens (Parse.term --| Parse.$$$ "," --
    PU.nonempty_code (K "selector for deletion must not be empty")) >> Either.Left
  || PU.nonempty_code (K "data for deletion must not be empty") >> Either.Right)
  |> Scan.repeat1

fun prepare_term context =
  Proof_Context.read_term_pattern (Context.proof_of context) #> ML_Syntax.print_term #> MCU.read

fun add_attribute (data, pos) (x as (context, _)) =
  let
    val args_code = map (Either.cases (fn (t, c) => MCU.tuple [prepare_term context t, c]) I) data
    val code = MCU.read "fold" @ FI.code_struct_op "insert" @ MCU.list args_code
  in ML_Attribute.run_map_context (code, pos) x end

fun del_attribute (data, pos) (x as (context, _)) =
  let
    val args_code = map (Either.cases (fn (t, c) => MCU.tuple [prepare_term context t, c]) I) data
    val code = MCU.read "fold" @ FI.code_struct_op "delete" @ MCU.list args_code
  in ML_Attribute.run_map_context (code, pos) x end

val parse_entries =
  let
    val parse_value = PM.parse_entry add_arg_parser del_arg_parser
    val parse_entry = Parse_Key_Value.parse_entry PM.parse_key (K (Parse.$$$ ":")) parse_value
    val default_entries = PM.empty_entries ()
  in PM.parse_entries_required Parse.and_list1 true [] parse_entry default_entries end

fun attribute (entries, pos) =
  let
    fun default_attr (context, thm) = (SOME context, SOME thm)
    val add_attr = PM.get_add_safe entries
      |> (fn SOME entries => add_attribute (entries, pos) | NONE => default_attr)
    val del_attr = PM.get_del_safe entries
      |> (fn SOME entries => del_attribute (entries, pos) | NONE => default_attr)
  in ML_Attribute_Util.apply_attribute del_attr #> add_attr end

val parse_attribute = PU.position parse_entries >> attribute
  || PU.position add_arg_parser >> add_attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  (Either.cases I (fn what => "configure " ^ what ^ " data " ^ enclose "(" ")" FI.long_name))
end
