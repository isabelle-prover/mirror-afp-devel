(*  Title:      ML_Unification/unification_combine.ML
    Author:     Kevin Kappelmann

Combine a list of e-unifiers.
*)
@{parse_entries (sig) PARSE_UNIFICATION_COMBINE_ARGS
  [add, del]}

signature UNIFICATION_COMBINE =
sig
  include HAS_LOGGER

  structure PA : PARSE_UNIFICATION_COMBINE_ARGS

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
  val eunif_data : Unification_Base.e_unifier -> metadata -> eunif_data
  val dest_eunif_data : eunif_data -> Unification_Base.e_unifier * metadata
  val eunif_data_e_unifier : eunif_data -> Unification_Base.e_unifier
  val eunif_data_metadata : eunif_data -> metadata
  val pretty_eunif_data : eunif_data -> Pretty.T

  type eunif_datas = eunif_data list Prio.Table.table
  (*storing the e-unifiers and metadata*)
  structure Data : GENERIC_DATA

  val get_eunif_datas : Context.generic -> eunif_datas
  val map_eunif_datas : (eunif_datas -> eunif_datas) -> Context.generic -> Context.generic
  val insert_eunif_data : eunif_data -> Context.generic -> Context.generic
  val delete_eunif_data : metadata -> Context.generic -> Context.generic

  val pretty_data : Proof.context -> Pretty.T

  val e_unify : Unification_Base.e_unifier

  val binding : Binding.binding

  val arg_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser) PA.entries
  val attribute : (ML_Code_Util.code, ML_Code_Util.code) PA.entries * Position.T -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : string option -> local_theory -> local_theory
end

functor Unification_Combine(A : sig
  structure FIA : FUNCTOR_INSTANCE_ARGS
  end) : UNIFICATION_COMBINE =
struct

structure UCB = Unification_Combinator
structure UB = Unification_Base
structure FIU = Functor_Instance_Util(A.FIA)

val logger = Logger.setup_new_logger Unification_Base.logger FIU.FIA.full_name

@{parse_entries (struct) PA
  [add, del]}

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

datatype eunif_data = EUnif_Data of UB.e_unifier * metadata

fun eunif_data unify meta = EUnif_Data (unify, meta)
fun dest_eunif_data (EUnif_Data data) = data
fun eunif_data_e_unifier (EUnif_Data (unify, _)) = unify
fun eunif_data_metadata (EUnif_Data (_, meta)) = meta
val eunif_data_prio = eunif_data_metadata #> metadata_prio

val eq_eunif_data = eq_metadata o apply2 eunif_data_metadata
fun pretty_eunif_data (EUnif_Data (_, meta)) = pretty_metadata meta

type eunif_datas = eunif_data list Prio.Table.table

(*invariant: data is sorted with respect to the priorities*)
structure Data = Generic_Data(struct
  type T = eunif_datas
  val empty = Prio.Table.empty
  val merge = Prio.Table.merge_list eq_eunif_data
end)

val get_eunif_datas = Data.get
val get_e_unifiers = map (eunif_data_e_unifier o snd) o Prio.Table.dest_list o get_eunif_datas
val map_eunif_datas = Data.map

fun insert_eunif_data data context =
  let val prio = eunif_data_prio data
  in
    Data.map (fn datas =>
      if member eq_eunif_data (Prio.Table.lookup_list datas prio) data
      then (@{log Logger.WARN} (Context.proof_of context) (fn _ =>
        Pretty.block [
          Pretty.str "eunif data (",
          pretty_eunif_data data,
          Pretty.str ") already added."
        ] |> Pretty.string_of);
        datas)
      else Prio.Table.insert_list eq_eunif_data (prio, data) datas
    ) context
  end

fun delete_eunif_data metadata context =
  let val prio = metadata_prio metadata
  in
    Data.map (fn datas =>
      if member eq_metadata (Prio.Table.lookup_list datas prio |> map eunif_data_metadata) metadata
      then Prio.Table.remove_list (eq_metadata o apsnd eunif_data_metadata) (prio, metadata) datas
      else (@{log Logger.WARN} (Context.proof_of context) (fn _ =>
        Pretty.block [
          Pretty.str "metadata (",
          pretty_metadata metadata,
          Pretty.str ") not found."
        ] |> Pretty.string_of);
        datas)
    ) context
  end

fun pretty_data ctxt = get_eunif_datas (Context.Proof ctxt)
  |> Prio.Table.dest_list
  |> map (pretty_eunif_data o snd)
  |> Pretty.fbreaks
  |> Pretty.block

fun e_unify unif binders ctxt tp env =
  (@{log Logger.DEBUG} ctxt (fn _ =>
    Pretty.block [
      Pretty.str "Combining e-unifiers for ",
      Unification_Util.pretty_unif_problem ctxt (apply2 (Envir_Normalisation.norm_term_unif env) tp)
    ] |> Pretty.string_of);
  UCB.concat_e_unifiers (get_e_unifiers (Context.Proof ctxt)) unif binders ctxt tp env)

val binding = FIU.mk_binding_id_prefix "ucombine"

val arg_parsers = {
  add = SOME (Parse_Util.nonempty_code (K "eunif_data to add must not be empty")),
  del = SOME (Parse_Util.nonempty_code (K "eunif_data to delete must not be empty"))
}

val parse_arg_entries =
  let
    val parse_value = PA.parse_entry (PA.get_add arg_parsers) (PA.get_del arg_parsers)
    val parse_entry = Parse_Key_Value.parse_entry PA.parse_key Parse_Util.eq parse_value
  in PA.parse_entries_required Parse.and_list1 [] parse_entry (PA.empty_entries ()) end

fun attribute (entries, pos) =
  let
    fun default (context, _) = (SOME context, NONE)
    val run_code = ML_Attribute.run_map_context o rpair pos
    val add = case PA.get_add_safe entries of
        SOME c => FIU.code_struct_op "insert_eunif_data" @ ML_Code_Util.atomic c |> run_code
      | NONE => default
    val del = case PA.get_del_safe entries of
        SOME c => FIU.code_struct_op "delete_eunif_data" @ ML_Code_Util.atomic c |> run_code
      | NONE => default
  in ML_Attribute_Util.apply_attribute del #> add end

val parse_attribute = (parse_arg_entries |> Parse_Util.position) >> attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  the_default ("set unification-combine arguments (" ^ FIU.FIA.full_name ^ ")")

end
