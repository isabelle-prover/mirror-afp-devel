(*  Title:      ML_Unification/unification_hints.ML
    Author:     Kevin Kappelmann

Unification hints with arguments from context.
*)
@{parse_entries (sig) PARSE_UNIFICATION_HINTS_ARGS
  [concl_unifier, normalisers, prems_unifier]}

signature UNIFICATION_HINTS_ARGS =
sig
  structure PA : PARSE_UNIFICATION_HINTS_ARGS

  type args = (Unification_Base.unifier, Unification_Base.normalisers, Unification_Base.unifier)
    PA.entries

  val try_hints : args -> Unification_Hints_Base.hint_retrieval -> Unification_Base.unifier

  val arg_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser, ML_Code_Util.code parser)
    PA.entries
end

structure Unification_Hints_Args : UNIFICATION_HINTS_ARGS =
struct

structure UB = Unification_Base
structure EN = Envir_Normalisation
structure UHB = Unification_Hints_Base

@{parse_entries (struct) PA
  [concl_unifier, normalisers, prems_unifier]}

type args = (UB.unifier, UB.normalisers, UB.unifier) PA.entries

fun try_hints args retrieval =
  UHB.try_hints retrieval (PA.get_concl_unifier args) (PA.get_normalisers args)
    (PA.get_prems_unifier args)

val arg_parsers = {
  concl_unifier = SOME Unification_Parser.parse_unifier,
  normalisers = SOME Unification_Parser.parse_normalisers,
  prems_unifier = SOME Unification_Parser.parse_unifier
}

end

signature UNIFICATION_HINTS =
sig
  structure Data : GENERIC_DATA

  val get_args : Context.generic -> Unification_Hints_Args.args
  val map_args : (Unification_Hints_Args.args -> Unification_Hints_Args.args) ->
    Context.generic -> Context.generic

  val get_concl_unifier : Context.generic -> Unification_Base.unifier
  val map_concl_unifier : (Unification_Base.unifier -> Unification_Base.unifier) ->
    Context.generic -> Context.generic

  val get_normalisers : Context.generic -> Unification_Base.normalisers
  val map_normalisers : (Unification_Base.normalisers -> Unification_Base.normalisers) ->
    Context.generic -> Context.generic

  val get_prems_unifier : Context.generic -> Unification_Base.unifier
  val map_prems_unifier : (Unification_Base.unifier -> Unification_Base.unifier) ->
    Context.generic -> Context.generic

  val try_hints : Unification_Hints_Base.hint_retrieval -> Unification_Base.unifier

  val attribute : (ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code)
    Unification_Hints_Args.PA.entries * Position.T -> attribute
end

functor Unification_Hints(A : sig
    structure FIA : FUNCTOR_INSTANCE_ARGS
    val init_args : Unification_Hints_Args.args
  end) : UNIFICATION_HINTS =
struct

structure UHA = Unification_Hints_Args
structure PA = UHA.PA
structure FIU = Functor_Instance_Util(A.FIA)
structure MCU = ML_Code_Util

structure Data = Generic_Data(struct
  type T = UHA.args
  val empty = A.init_args
  val merge = fst
end)

val get_args = Data.get
val map_args = Data.map

val get_concl_unifier = PA.get_concl_unifier o get_args
val map_concl_unifier = map_args o PA.map_concl_unifier

val get_normalisers = PA.get_normalisers o get_args
val map_normalisers = map_args o PA.map_normalisers

val get_prems_unifier = PA.get_prems_unifier o get_args
val map_prems_unifier = map_args o PA.map_prems_unifier

fun try_hints retrieval binders ctxt  =
  UHA.try_hints (get_args (Context.Proof ctxt)) retrieval binders ctxt

fun attribute (entries, pos) =
  let
    fun code_PA_op operation = MCU.flat_read ["Unification_Hints_Args.PA.", operation]
    val code_from_key = code_PA_op o PA.key_to_string
    fun code_from_entry (PA.concl_unifier c) = c
      | code_from_entry (PA.normalisers c) = c
      | code_from_entry (PA.prems_unifier c) = c
    val code_entries = PA.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code =
      FIU.code_struct_op "map_args" @ MCU.atomic (code_PA_op "merge_entries" @
      MCU.atomic (code_PA_op "entries_from_entry_list" @ code_entries))
  in ML_Attribute.run_map_context (code, pos) end

end
