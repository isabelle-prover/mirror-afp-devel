(*  Title:      Transport_Infer/generic_ord_list_id_data.ML
    Author:     Kevin Kappelmann
*)
@{parse_entries (sig) PARSE_GENERIC_ORD_LIST_ID_DATA_MODE [add, del]}

signature GENERIC_ORD_LIST_ID_DATA_ARGS =
sig
  structure PM : PARSE_GENERIC_ORD_LIST_ID_DATA_MODE
  val arg_parsers : (ML_Code_Util.code list parser, ML_Code_Util.code list parser) PM.entries
end

structure Generic_Ord_List_Id_Data_Args : GENERIC_ORD_LIST_ID_DATA_ARGS =
struct
structure PU = Parse_Util

@{parse_entries (struct) PM [add, del]}

val arg_parsers = {
  add = SOME (PU.nonempty_code (K "data to add must not be empty") |> Scan.repeat1),
  del = SOME (PU.nonempty_code (K "id to delete must not be empty") |> Scan.repeat1)
}
end

signature GENERIC_ORD_LIST_ID_DATA =
sig
  include HAS_LOGGER
  structure FI : FUNCTOR_INSTANCE

  type id
  type data
  val morph_data : morphism -> data -> data

  type datas = data Ord_List.T
  structure Data : GENERIC_DATA
  where type T = datas

  val get_datas : Context.generic -> datas
  val map_datas : (datas -> datas) -> Context.generic -> Context.generic
  val insert_data : data -> Context.generic -> Context.generic
  val delete_id : id -> Context.generic -> Context.generic

  val pretty_datas : Proof.context -> Pretty.T

  val binding : Binding.binding

  val add_attribute : ML_Code_Util.code list * Position.T -> attribute
  val del_attribute : ML_Code_Util.code list * Position.T -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : (string, string) Either.either -> local_theory -> local_theory
end

(*precondition: equality on ord_data implies equality on (apply2 get_id #> eq_id)*)
functor Generic_Ord_List_Id_Data_Functor(
    structure FI : FUNCTOR_INSTANCE_BASE
    val parent_logger : Logger.logger_binding
    type data
    val morph_data : morphism -> data -> data
    val ord_data : data ord
    val pretty_data : Proof.context -> data -> Pretty.T
    type id
    val eq_id : id * id -> bool
    val pretty_id : Proof.context -> id -> Pretty.T
    val get_id : data -> id
  ) : GENERIC_ORD_LIST_ID_DATA =
struct

structure MCU = ML_Code_Util
structure PU = Parse_Util
structure GOLID = Generic_Ord_List_Id_Data_Args
structure PM = GOLID.PM
structure FI = Functor_Instance(FI)

val logger = Logger.setup_new_logger parent_logger FI.name

type id = id
type data = data
val morph_data = morph_data

type datas = data Ord_List.T

val eq_data_id = apply2 get_id #> eq_id
structure Data = Generic_Data(
  type T = datas
  val empty = []
  fun merge (xs, ys) = subtract eq_data_id xs ys |> curry (Ord_List.merge ord_data) xs)

fun get_datas context = Data.get context
  |> map (morph_data (Morphism.transfer_morphism'' context))
val map_datas = Data.map

fun insert_data data context =
  let val data = morph_data Morphism.trim_context_morphism data
  in
    Data.map (fn datas =>
      if member eq_data_id datas data
      then let val ctxt = Context.proof_of context
        in
          (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
              Pretty.str "Identifier ", pretty_id ctxt (get_id data), Pretty.str " already added."
            ] |> Pretty.string_of);
          datas)
        end
      else Ord_List.insert ord_data data datas) context
  end

fun delete_id id context =
  let val eq_id = apsnd get_id #> eq_id
  in
    Data.map (fn datas => if member eq_id datas id
      then remove eq_id id datas
      else let val ctxt = Context.proof_of context
        in
          (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
              Pretty.str "Identifier ", pretty_id ctxt id, Pretty.str " not found."
            ] |> Pretty.string_of);
          datas)
        end) context
  end

fun pretty_datas ctxt = get_datas (Context.Proof ctxt)
  |> map (pretty_data ctxt) |> Pretty.fbreaks |> Pretty.block

val binding = Binding.make (FI.id, FI.pos)

fun add_attribute (data, pos) =
  let val code = MCU.read "fold" @ FI.code_struct_op "insert_data" @ MCU.list data
  in ML_Attribute.run_map_context (code, pos) end

fun del_attribute (data, pos) =
  let val code = MCU.read "fold" @ FI.code_struct_op "delete_id" @ MCU.list data
  in ML_Attribute.run_map_context (code, pos) end

val parse_entries =
  let
    val parsers = GOLID.arg_parsers
    val parse_value = PM.parse_entry (PM.get_add parsers) (PM.get_del parsers)
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
  || PU.position (PM.get_add GOLID.arg_parsers) >> add_attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  (Either.cases I (fn what => "configure " ^ what ^ " data " ^ enclose "(" ")" FI.long_name))
end

functor Generic_Ord_List_Id_Data(A :
  sig
    structure FI : FUNCTOR_INSTANCE_BASE
    val parent_logger : Logger.logger_binding
    type data
    val morph_data : morphism -> data -> data
    val ord_data : data ord
    val pretty_data : Proof.context -> data -> Pretty.T
    val get_id : data -> Identifier.id
  end) = Generic_Ord_List_Id_Data_Functor(open A
  type id = Identifier.id
  val eq_id = Identifier.eq
  val pretty_id = K Identifier.pretty)
