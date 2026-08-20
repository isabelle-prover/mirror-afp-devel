(*  Title:      ML_Unification/unify_assumption.ML
    Author:     Kevin Kappelmann

Assumption tactic with arguments from context.
*)
@{parse_entries (sig) PARSE_UNIFY_ASSUMPTION_ARGS [normalisers, unifier]}

signature UNIFY_ASSUMPTION_ARGS =
sig
  structure PA : PARSE_UNIFY_ASSUMPTION_ARGS

  type args = (Unification_Base.normalisers, Unification_Base.unifier) PA.entries
  val unify_assumption_tac : args -> Proof.context -> int -> tactic

  val arg_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser) PA.entries
end

structure Unify_Assumption_Args : UNIFY_ASSUMPTION_ARGS =
struct

@{parse_entries (struct) PA [normalisers, unifier]}

type args = (Unification_Base.normalisers, Unification_Base.unifier) PA.entries

fun unify_assumption_tac args ctxt =
  Unify_Assumption_Base.unify_assumption_tac (PA.get_normalisers args) (PA.get_unifier args) ctxt

val arg_parsers = {
  normalisers = SOME Unification_Parser.parse_normalisers,
  unifier = SOME Unification_Parser.parse_unifier
}

end

signature UNIFY_ASSUMPTION =
sig
  structure FI : FUNCTOR_INSTANCE

  structure Data : GENERIC_DATA
  where type T = Unify_Assumption_Args.args

  val get_args : Context.generic -> Unify_Assumption_Args.args
  val map_args : (Unify_Assumption_Args.args -> Unify_Assumption_Args.args) ->
    Context.generic -> Context.generic

  val get_normalisers : Context.generic -> Unification_Base.normalisers
  val map_normalisers : (Unification_Base.normalisers -> Unification_Base.normalisers) ->
    Context.generic -> Context.generic

  val get_unifier : Context.generic -> Unification_Base.unifier
  val map_unifier : (Unification_Base.unifier -> Unification_Base.unifier) ->
    Context.generic -> Context.generic

  val unify_assumption_tac : Proof.context -> int -> tactic

  val binding : binding

  val parse_arg_entries : (ML_Code_Util.code, ML_Code_Util.code) Unify_Assumption_Args.PA.entries
    parser
  val attribute : (ML_Code_Util.code, ML_Code_Util.code) Unify_Assumption_Args.PA.entries *
    Position.T -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : string option -> local_theory -> local_theory

  val parse_method : (Proof.context -> Method.method) context_parser
  val setup_method : string option -> local_theory -> local_theory
end

functor Unify_Assumption_Functor(A :
  sig
    structure FI : FUNCTOR_INSTANCE_BASE
    val init_args : Unify_Assumption_Args.args
  end) : UNIFY_ASSUMPTION =
struct

structure UAA = Unify_Assumption_Args
structure PA = UAA.PA

structure FI = Functor_Instance(A.FI)
structure MCU = ML_Code_Util

structure Data = Generic_Data(
  type T = UAA.args
  val empty = A.init_args
  val merge = fst)

val get_args = Data.get
val map_args = Data.map

val get_normalisers = PA.get_normalisers o get_args
val map_normalisers = map_args o PA.map_normalisers

val get_unifier = PA.get_unifier o get_args
val map_unifier = map_args o PA.map_unifier

fun unify_assumption_tac ctxt = UAA.unify_assumption_tac (get_args (Context.Proof ctxt)) ctxt

val binding = Binding.make (FI.id, FI.pos)

val parse_arg_entries =
  let
    val parse_value = PA.parse_entry (PA.get_normalisers UAA.arg_parsers)
      (PA.get_unifier UAA.arg_parsers)
    val parse_entry = Parse_Key_Value.parse_entry PA.parse_key (K (Parse.$$$ ":")) parse_value
  in PA.parse_entries_required Scan.repeat1 true [] parse_entry (PA.empty_entries ()) end

fun attribute (entries, pos) =
  let
    fun code_PA_op operation = MCU.flat_read ["Unify_Assumption_Args.PA.", operation]
    val code_from_key = code_PA_op o PA.key_to_string
    fun code_from_entry (PA.normalisers c) = MCU.atomic c
      | code_from_entry (PA.unifier c) = MCU.atomic c
    val code_entries = PA.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ code_from_entry v)
      |> MCU.list
    val code = FI.code_struct_op "map_args" @ MCU.atomic (code_PA_op "merge_entries" @
      MCU.atomic (code_PA_op "entries_from_entry_list" @ code_entries))
  in ML_Attribute.run_map_context (code, pos) end

val parse_attribute = (parse_arg_entries |> Parse_Util.position) >> attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  the_default ("configure unify-assumption data " ^ enclose "(" ")" FI.long_name)

val parse_method =
  Parse_Util.option (Parse.!!! parse_attribute)
  >> (fn opt_attr =>
    the_default I (Option.map ML_Attribute_Util.attribute_map_ctxt opt_attr)
    #> SIMPLE_METHOD' o unify_assumption_tac)
  |> Scan.lift

val setup_method = Method.local_setup binding parse_method o
  the_default ("solve first subgoal by assumption; with adjustable unifier " ^
    enclose "(" ")" FI.long_name)

end