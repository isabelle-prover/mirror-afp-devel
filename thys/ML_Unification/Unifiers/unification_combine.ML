(*  Title:      ML_Unification/unification_combine.ML
    Author:     Kevin Kappelmann

Combine a list of E-unifiers.
*)
signature UNIFICATION_COMBINE =
sig
  include HAS_LOGGER
  structure FI : FUNCTOR_INSTANCE

  type metadata
  val metadata : Identifier.id * Prio.prio -> metadata
  val dest_metadata : metadata -> Identifier.id * Prio.prio
  val get_metadata_id : metadata -> Identifier.id
  val get_metadata_prio : metadata -> Prio.prio
  val ord_metadata : metadata ord
  val pretty_metadata : metadata -> Pretty.T

  type eunif_data
  val eunif_data : metadata * Unification_Base.e_unifier -> eunif_data
  val dest_eunif_data : eunif_data -> metadata * Unification_Base.e_unifier
  val get_eunif_data_e_unifier : eunif_data -> Unification_Base.e_unifier
  val get_eunif_data_metadata : eunif_data -> metadata
  val ord_eunif_data : eunif_data ord
  val pretty_eunif_data : eunif_data -> Pretty.T

  structure Data : GENERIC_ORD_LIST_ID_DATA
  where type data = eunif_data

  val e_unify : Unification_Base.e_unifier

  val binding : Binding.binding
  val setup_attribute : string option -> local_theory -> local_theory
end

functor Unification_Combine_Functor(
    structure FI : FUNCTOR_INSTANCE_BASE
  ) : UNIFICATION_COMBINE =
struct

structure Id = Identifier
structure UCB = Unification_Combinator
structure UB = Unification_Base
structure Show = SpecCheck_Show_Base
structure FI = Functor_Instance(FI)

val logger = Logger.setup_new_logger UB.logger FI.name

datatype metadata = Metadata of Id.id * Prio.prio

val metadata = Metadata
fun dest_metadata (Metadata meta) = meta
fun get_metadata_id (Metadata (id, _)) = id
fun get_metadata_prio (Metadata (_, prio)) = prio

val ord_metadata = apply2 (dest_metadata #> swap)
  #> prod_ord (Prio.ord #> rev_order) Id.ord
fun pretty_metadata (Metadata (id, prio)) = Show.record [
    ("id", Identifier.pretty id),
    ("priority", Prio.pretty prio)
  ]

datatype eunif_data = EUnif_Data of metadata * Unification_Base.e_unifier

fun eunif_data (meta, unify) = EUnif_Data (meta, unify)
fun dest_eunif_data (EUnif_Data data) = data
fun get_eunif_data_e_unifier (EUnif_Data (_, unify)) = unify
fun get_eunif_data_metadata (EUnif_Data (meta, _)) = meta
val ord_eunif_data = ord_metadata o apply2 get_eunif_data_metadata
fun pretty_eunif_data (EUnif_Data (meta, _)) = pretty_metadata meta

\<^functor_instance>\<open>struct_name: Data
  functor_name: Generic_Ord_List_Id_Data
  id: \<open>FI.id\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    val parent_logger = logger
    type data = eunif_data
    val morph_data = K I
    val ord_data = ord_eunif_data
    val pretty_data = K pretty_eunif_data
    val get_id = get_eunif_data_metadata #> get_metadata_id\<close>\<close>

val get_e_unifiers = map get_eunif_data_e_unifier o Data.get_datas

fun e_unify unif binders ctxt tp env = Seq.make (fn _ =>
  (@{log Logger.DEBUG} ctxt (fn _ =>
    Pretty.block [
      Pretty.str "Combining E-unifiers for ",
      Unification_Util.pretty_unif_problem binders ctxt
        (apply2 (Same.commit (Envir_Normalisation.norm_term_unif env)) tp)
    ] |> Pretty.string_of);
  UCB.concat_e_unifiers (get_e_unifiers (Context.Proof ctxt)) unif binders ctxt tp env) |> Seq.pull)

val binding = Data.binding
val setup_attribute = Option.map Either.Left
  #> the_default (Either.Right "unification-combine")
  #> Data.setup_attribute

end
