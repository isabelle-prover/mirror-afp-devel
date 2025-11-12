(*  Title:      ML_Unification/unification_combine.ML
    Author:     Kevin Kappelmann

Combine a list of E-unifiers.
*)
@{parse_entries (sig) PARSE_UNIFICATION_COMBINE_MODE [add, del]}

signature UNIFICATION_COMBINE =
sig
  include HAS_LOGGER

  structure PM : PARSE_UNIFICATION_COMBINE_MODE

  type binding = binding
  val eq_binding : binding * binding -> bool
  val pretty_binding : binding -> Pretty.T

  type metadata
  val metadata : binding -> Prio.prio -> metadata
  val dest_metadata : metadata -> binding * Prio.prio
  val metadata_binding : metadata -> binding
  val metadata_prio : metadata -> Prio.prio
  val eq_metadata : metadata * metadata -> bool
  val pretty_metadata : metadata -> Pretty.T
  val default_metadata : binding -> metadata

  type eunif_data
  val eunif_data : metadata * Unification_Base.e_unifier -> eunif_data
  val dest_eunif_data : eunif_data -> metadata * Unification_Base.e_unifier
  val eunif_data_e_unifier : eunif_data -> Unification_Base.e_unifier
  val eunif_data_metadata : eunif_data -> metadata
  val pretty_eunif_data : eunif_data -> Pretty.T

  structure Table : TABLE
  where type key = Prio.prio
  type eunif_datas = eunif_data list Table.table
  (*storing the E-unifiers and metadata*)
  structure Data : GENERIC_DATA
  where type T = eunif_datas

  val get_eunif_datas : Context.generic -> eunif_datas
  val map_eunif_datas : (eunif_datas -> eunif_datas) -> Context.generic -> Context.generic
  val insert_eunif_data : eunif_data -> Context.generic -> Context.generic
  val delete_eunif_data : metadata -> Context.generic -> Context.generic

  val pretty_data : Proof.context -> Pretty.T

  val e_unify : Unification_Base.e_unifier

  val binding : Binding.binding

  val add_arg_parser : ML_Code_Util.code list parser
  val del_arg_parser : ML_Code_Util.code list parser
  val add_attribute : ML_Code_Util.code list * Position.T -> attribute
  val del_attribute : ML_Code_Util.code list * Position.T -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : string option -> local_theory -> local_theory
end

functor Unification_Combine(A :
  sig
    structure FI : FUNCTOR_INSTANCE_BASE
  end) : UNIFICATION_COMBINE =
struct

structure UCB = Unification_Combinator
structure UB = Unification_Base
structure PU = Parse_Util
structure MCU = ML_Code_Util
structure FI = Functor_Instance(A.FI)

val logger = Logger.setup_new_logger Unification_Base.logger FI.name

@{parse_entries (struct) PM [add, del]}

type binding = binding

val eq_binding = Binding.eq_name
val pretty_binding = Binding.pretty

datatype metadata = Metadata of binding * Prio.prio

fun metadata binding prio = Metadata (binding, prio)
fun dest_metadata (Metadata meta) = meta
fun metadata_binding (Metadata (binding, _)) = binding
fun metadata_prio (Metadata (_, prio)) = prio

val eq_metadata = eq_pair eq_binding Prio.eq o apply2 dest_metadata
fun pretty_metadata (Metadata (binding, prio))= Pretty.block [
    Pretty.str "Binding: ",
    pretty_binding binding,
    Pretty.str ", Priority: ",
    Prio.pretty prio
  ]

fun default_metadata binding = metadata binding Prio.MEDIUM

datatype eunif_data = EUnif_Data of metadata * UB.e_unifier

fun eunif_data (meta, unify) = EUnif_Data (meta, unify)
fun dest_eunif_data (EUnif_Data data) = data
fun eunif_data_metadata (EUnif_Data (meta, _)) = meta
fun eunif_data_e_unifier (EUnif_Data (_, unify)) = unify
val eunif_data_prio = eunif_data_metadata #> metadata_prio

val eq_eunif_data = eq_metadata o apply2 eunif_data_metadata
fun pretty_eunif_data (EUnif_Data (meta, _)) = pretty_metadata meta

structure Table = Table(type key = Prio.prio; val ord = rev_order o Prio.ord)
type eunif_datas = eunif_data list Table.table

(*invariant: data is sorted with respect to the priorities*)
structure Data = Generic_Data(
  type T = eunif_datas
  val empty = Table.empty
  val merge = Table.merge_list eq_eunif_data)

val get_eunif_datas = Data.get
val get_e_unifiers = map (eunif_data_e_unifier o snd) o Table.dest_list o get_eunif_datas
val map_eunif_datas = Data.map

fun insert_eunif_data data context =
  let val prio = eunif_data_prio data
  in
    Data.map (fn datas =>
      if member eq_eunif_data (Table.lookup_list datas prio) data
      then (@{log Logger.WARN} (Context.proof_of context) (fn _ => Pretty.block [
            Pretty.str "eunif data ",
            Pretty.enclose "(" ")" [pretty_eunif_data data],
            Pretty.str " already added."
          ] |> Pretty.string_of);
        datas)
      else Table.insert_list eq_eunif_data (prio, data) datas
    ) context
  end

fun delete_eunif_data metadata context =
  let val prio = metadata_prio metadata
  in
    Data.map (fn datas =>
      if member eq_metadata (Table.lookup_list datas prio |> map eunif_data_metadata) metadata
      then Table.remove_list (eq_metadata o apsnd eunif_data_metadata) (prio, metadata) datas
      else (@{log Logger.WARN} (Context.proof_of context) (fn _ => Pretty.block [
            Pretty.str "metadata ",
            Pretty.enclose "(" ")" [pretty_metadata metadata],
            Pretty.str " not found."
          ] |> Pretty.string_of);
        datas)
    ) context
  end

fun pretty_data ctxt = get_eunif_datas (Context.Proof ctxt)
  |> Table.dest_list
  |> map (pretty_eunif_data o snd)
  |> Pretty.fbreaks
  |> Pretty.block

fun e_unify unif binders ctxt tp env = Seq.make (fn _ =>
  (@{log Logger.DEBUG} ctxt (fn _ =>
    Pretty.block [
      Pretty.str "Combining E-unifiers for ",
      Unification_Util.pretty_unif_problem ctxt (apply2 (Envir_Normalisation.norm_term_unif env) tp)
    ] |> Pretty.string_of);
  UCB.concat_e_unifiers (get_e_unifiers (Context.Proof ctxt)) unif binders ctxt tp env) |> Seq.pull)

val binding = Binding.make (FI.prefix_id "ucombine", FI.pos)

val add_arg_parser = PU.nonempty_code (K "eunif_data to add must not be empty") |> Scan.repeat1
val del_arg_parser = PU.nonempty_code (K "data to delete must not be empty") |> Scan.repeat1

fun add_attribute (data, pos) =
  let val code = MCU.read "fold" @ FI.code_struct_op "insert_eunif_data" @ MCU.list data
  in ML_Attribute.run_map_context (code, pos) end

fun del_attribute (data, pos) =
  let val code = MCU.read "fold" @ FI.code_struct_op "delete_eunif_data" @ MCU.list data
  in ML_Attribute.run_map_context (code, pos) end

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
  the_default ("configure unification-combine data " ^ enclose "(" ")" FI.long_name)

end
