(*  Title:      Zippy/context_parsers.ML
    Author:     Kevin Kappelmann

Customisable context parsers.
*)
@{parse_entries (sig) PARSE_CONTEXT_PARSERS_ARGS [add, del, default]}

signature CONTEXT_PARSERS =
sig
  structure Parsers_Data : GENERIC_TABLE_DATA
  where type key = Zippy_Identifier.id
  where type value = unit context_parser

  val get_parsers_table : Context.generic -> Parsers_Data.table

  structure Default_Data : GENERIC_DATA
  where type T = Parsers_Data.key option

  val pretty_Data : Proof.context -> Pretty.T

  val get_default : Context.generic -> Parsers_Data.key option
  val map_default : (Parsers_Data.key option -> Parsers_Data.key option) ->
    Context.generic -> Context.generic

  val insert : Parsers_Data.key * Parsers_Data.value -> Context.generic -> Context.generic
  val delete : Parsers_Data.key -> Context.generic -> Context.generic

  val binding : Binding.binding
  val add_arg_parser : ML_Code_Util.code list parser
  val del_arg_parser : ML_Code_Util.code list parser
  val default_arg_parser : ML_Code_Util.code option parser
  val add_attribute : ML_Code_Util.code list * Position.T -> attribute
  val del_attribute : ML_Code_Util.code list * Position.T -> attribute
  val default_attribute : ML_Code_Util.code option * Position.T -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : string option -> local_theory -> local_theory

  val parsers_separator : string
  (*returns list of parsers that were run*)
  val parse : Parsers_Data.key list context_parser
end

functor Context_Parsers(
    structure FI : FUNCTOR_INSTANCE_BASE
    val parent_logger : Logger.logger_binding
    val parsers_separator : string
  ) : CONTEXT_PARSERS =
struct

val logger = Logger.setup_new_logger parent_logger "Context_Parsers"

structure FI =  Functor_Instance(FI)
structure Id = Zippy_Identifier
structure MCU = ML_Code_Util
structure PU = Parse_Util
structure PKV = Parse_Key_Value
structure Show = SpecCheck_Show_Base

@{parse_entries (struct) PA [add, del, default]}

\<^functor_instance>\<open>struct_name: Parsers_Data
  functor_name: Generic_Table_Data
  id: \<open>FI.prefix_id "parsers_data"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    val parent_logger = logger
    type key = Id.id
    val pretty_key = Id.pretty
    val ord_key = Id.ord
    type value = unit context_parser
    val pretty_value = K (K (Pretty.str "<context parser>"))\<close>\<close>

val get_parsers_table = Parsers_Data.get_table

structure Default_Data = Generic_Data(
  type T = Parsers_Data.key option
  val empty = NONE
  val merge = fst)

fun pretty_Data ctxt = Show.record [
    ("default parser", Show.option Id.pretty (Default_Data.get (Context.Proof ctxt))),
    ("parsers: ", Parsers_Data.pretty_Data ctxt)
  ]

val get_default = Default_Data.get
fun map_default f context =
  let fun f' default = f default
    |> Option.mapPartial (fn key =>
      if Parsers_Data.Table.defined (get_parsers_table context) key
      then SOME key
      else (@{log Logger.WARN} (Context.proof_of context) (fn _ => Pretty.block [
            Pretty.str "Parser ", Id.pretty key, Pretty.str " not found. Keeping old default."
          ] |> Pretty.string_of);
        default))
  in Default_Data.map f' context end
val delete_default = map_default (K NONE)

val insert = Parsers_Data.insert

fun delete key context = context
  |> Parsers_Data.delete key
  |> (case Default_Data.get context of
      SOME key' => Id.eq (key', key) ? delete_default
    | NONE => I)

val binding = Binding.make (FI.id, FI.pos)

val add_arg_parser = Parsers_Data.add_arg_parser
val del_arg_parser = Parsers_Data.del_arg_parser
val default_arg_parser = PU.option (PU.nonempty_code (K "default key must not be empty"))

fun add_attribute (data, pos) =
  let val code = MCU.read "fold" @ FI.code_struct_op "insert" @ MCU.list data
  in ML_Attribute.run_map_context (code, pos) end

fun del_attribute (data, pos) =
  let val code = MCU.read "fold" @ FI.code_struct_op "delete" @ MCU.list data
  in ML_Attribute.run_map_context (code, pos) end

fun default_attribute (default, pos) =
  let
    val default = case default of
        NONE => MCU.read "NONE"
      | SOME key => MCU.read "SOME" @ MCU.atomic key
    val code = FI.code_struct_op "map_default" @ MCU.atomic (MCU.read "fn _ =>" @ default)
  in ML_Attribute.run_map_context (code, pos) end

val parse_entries =
  let
    val parse_value = PA.parse_entry add_arg_parser del_arg_parser default_arg_parser
    val parse_entry = PKV.parse_entry PA.parse_key (K (Parse.$$$ ":")) parse_value
    val default_entries = PA.empty_entries ()
  in PA.parse_entries_required Parse.and_list1 true [] parse_entry default_entries end

fun attribute (entries, pos) =
  let
    fun continue_attr (context, thm) = (SOME context, SOME thm)
    val add_attr = PA.get_add_safe entries
      |> (fn SOME entries => add_attribute (entries, pos) | NONE => continue_attr)
    val del_attr = PA.get_del_safe entries
      |> (fn SOME entries => del_attribute (entries, pos) | NONE => continue_attr)
    val default_attr = PA.get_default_safe entries
      |> (fn SOME default => default_attribute (default, pos) | NONE => continue_attr)
  in
    ML_Attribute_Util.apply_attribute del_attr
    #> ML_Attribute_Util.apply_attribute add_attr
    #> default_attr
  end

val parse_attribute = PU.position parse_entries >> attribute
  || PU.position add_arg_parser >> add_attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  the_default ("configure context parsers data " ^ enclose "(" ")" FI.long_name)

fun parse_key keys table = PKV.parse_key keys
  (Id.make NONE #> Option.filter (Parsers_Data.Table.defined table))

fun fail_undefined_key key = Scan.fail_with
  (fn _ => fn _ => "no parser registered for " ^ Id.quoted_string key)

fun parse_value table key = Parsers_Data.Table.lookup table key
  |> \<^if_none>\<open>fail_undefined_key key\<close>

fun parse_entry keys table = PKV.parse_entry' (Scan.lift (parse_key keys table))
  (K (Scan.succeed "")) (parse_value table)

val parsers_separator = parsers_separator

fun parse (args as (context, _)) = args |>
  let val table = get_parsers_table context
  in
    (case Default_Data.get context of
      NONE => Scan.succeed NONE
    | SOME key => PU.option' (parse_value table key >> pair key))
    -- (Scan.lift (PU.option (Parse.$$$ parsers_separator))
    :|-- (fn opt_sep =>
      let
        val string_from_key = Id.quoted_string
        val keys = Parsers_Data.Table.keys table |> map string_from_key
        val parse_list = case opt_sep of NONE => Parse.enum' | SOME _ => Parse.enum1'
      in
        PKV.parse_entries_required' Id.eq string_from_key false []
          (parse_list parsers_separator
            (parse_entry keys table |> Parse.!!!! |> Scan.unless (Scan.lift Parse.eof)))
      end))
    >> (fn (NONE, xs) => xs | (SOME x, xs) => x :: xs)
    >> map fst
  end

end