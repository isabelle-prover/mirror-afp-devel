(*  Title:      ML_Unification/unify_fact.ML
    Author:     Kevin Kappelmann

Fact tactic tactic with arguments from context.
*)
@{parse_entries (sig) PARSE_UNIFY_FACT_ARGS
  [normalisers, unifier, facts]}
@{parse_entries (sig) PARSE_UNIFY_FACT_CONTEXT_ARGS
  [normalisers, unifier]}

@{parse_entries (sig) UNIFY_RESOLVE_CHAINED_MODES [insert, resolve, fact]}

signature UNIFY_FACT_ARGS =
sig
  structure PA : PARSE_UNIFY_FACT_ARGS
  structure PCA : PARSE_UNIFY_FACT_CONTEXT_ARGS

  val PCA_entries_from_PA_entries : ('a, 'b, 'c) PA.entries -> ('a, 'b) PCA.entries
  val PA_entries_from_PCA_entries : ('a, 'b) PCA.entries -> 'c -> ('a, 'b, 'c) PA.entries

  type args = (Unification_Base.normalisers, Unification_Base.unifier, thm list) PA.entries
  type context_args = (Unification_Base.normalisers, Unification_Base.unifier) PCA.entries

  val unify_fact_tac : args -> Proof.context -> int -> tactic
  val unify_fact_context_args_tac : context_args -> thm list -> Proof.context -> int -> tactic

  val arg_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser, thm list context_parser)
    PA.entries
end

structure Unify_Fact_Args : UNIFY_FACT_ARGS =
struct

@{parse_entries (struct) PA [normalisers, unifier, facts]}
@{parse_entries (struct) PCA [normalisers, unifier]}

fun PCA_entries_from_PA_entries {normalisers = normalisers, unifier = unifier,...} =
  {normalisers = normalisers, unifier = unifier}
fun PA_entries_from_PCA_entries {normalisers = normalisers, unifier = unifier} facts =
  {normalisers = normalisers, unifier = unifier, facts = SOME facts}

type args = (Unification_Base.normalisers, Unification_Base.unifier, thm list) PA.entries
type context_args = (Unification_Base.normalisers, Unification_Base.unifier) PCA.entries

fun unify_fact_tac args =
  Unify_Fact_Base.unify_fact_tac (PA.get_normalisers args) (PA.get_unifier args) (PA.get_facts args)

val unify_fact_context_args_tac = unify_fact_tac oo PA_entries_from_PCA_entries

val arg_parsers = {
  normalisers = SOME Unification_Parser.parse_normalisers,
  unifier = SOME Unification_Parser.parse_unifier,
  facts = SOME Parse_Util.thms
}

end

signature UNIFY_FACT =
sig
  structure Data : GENERIC_DATA

  val get_args : Context.generic -> Unify_Fact_Args.context_args
  val map_args : (Unify_Fact_Args.context_args -> Unify_Fact_Args.context_args) ->
    Context.generic -> Context.generic

  val get_normalisers : Context.generic -> Unification_Base.normalisers
  val map_normalisers : (Unification_Base.normalisers -> Unification_Base.normalisers) ->
    Context.generic -> Context.generic

  val get_unifier : Context.generic -> Unification_Base.unifier
  val map_unifier : (Unification_Base.unifier -> Unification_Base.unifier) ->
    Context.generic -> Context.generic

  val unify_fact_tac : thm list -> Proof.context -> int -> tactic

  val binding : binding

  val attribute : (ML_Code_Util.code, ML_Code_Util.code) Unify_Fact_Args.PCA.entries *
    Position.T -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : string option -> local_theory -> local_theory

  val parse_method : (Proof.context -> Method.method) context_parser
  val setup_method : string option -> local_theory -> local_theory
end

functor Unify_Fact(A : sig
    structure FIA : FUNCTOR_INSTANCE_ARGS
    val init_args : Unify_Fact_Args.context_args
  end) : UNIFY_FACT =
struct

structure UFA = Unify_Fact_Args
structure PCA = UFA.PCA
structure PA = UFA.PA

structure FIU = Functor_Instance_Util(A.FIA)
structure MCU = ML_Code_Util

structure Data = Generic_Data(struct
  type T = UFA.context_args
  val empty = A.init_args
  val merge = fst
end)

val get_args = Data.get
val map_args = Data.map

val get_normalisers = PCA.get_normalisers o get_args
val map_normalisers = map_args o PCA.map_normalisers

val get_unifier = PCA.get_unifier o get_args
val map_unifier = map_args o PCA.map_unifier

fun unify_fact_tac facts ctxt =
  UFA.unify_fact_context_args_tac (get_args (Context.Proof ctxt)) facts ctxt

val binding = FIU.mk_binding_id_prefix "ufact"

val parse_arg_entries =
  let
    val parsers = UFA.arg_parsers |> UFA.PCA_entries_from_PA_entries
    val parse_value = PCA.parse_entry (PCA.get_normalisers parsers) (PCA.get_unifier parsers)
    val parse_entry = Parse_Key_Value.parse_entry PCA.parse_key Parse_Util.eq parse_value
  in PCA.parse_entries_required Parse.and_list1 [] parse_entry (PCA.empty_entries ()) end

fun attribute (entries, pos) =
  let
    fun code_PCA_op operation = MCU.flat_read ["Unify_Fact_Args.PCA.", operation]
    val code_from_key = code_PCA_op o PCA.key_to_string
    fun code_from_entry (PCA.normalisers c) = MCU.atomic c
      | code_from_entry (PCA.unifier c) = MCU.atomic c
    val code_entries = PCA.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ code_from_entry v)
      |> MCU.list
    val code = FIU.code_struct_op "map_args" @ MCU.atomic (code_PCA_op "merge_entries" @
      MCU.atomic (code_PCA_op "entries_from_entry_list" @ code_entries))
  in ML_Attribute.run_map_context (code, pos) end

val parse_attribute = (parse_arg_entries |> Parse_Util.position) >> attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  the_default ("set unify-fact arguments (" ^ FIU.FIA.full_name ^ ")")

val parse_method =
  PA.get_facts UFA.arg_parsers
  -- ((Parse.where_ |-- parse_attribute) |> Parse.!!! |> Parse_Util.option |> Scan.lift)
  >> (fn (facts, opt_attr) =>
    the_default I (Option.map ML_Attribute_Util.attribute_map_ctxt opt_attr)
    #> Method_Util.METHOD_CONTEXT' (append facts #> unify_fact_tac))

val setup_method = Method.local_setup binding parse_method o
  the_default ("solve first subgoal by unification with a given fact; with adjustable unifier ("
    ^ FIU.FIA.full_name ^ ")")

end