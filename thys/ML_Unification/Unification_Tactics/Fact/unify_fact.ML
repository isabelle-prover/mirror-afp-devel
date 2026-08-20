(*  Title:      ML_Unification/unify_fact.ML
    Author:     Kevin Kappelmann

Fact tactic tactic with arguments from context.
*)
@{parse_entries (sig) PARSE_UNIFY_FACT_ARGS [normalisers, unifier, facts]}
@{parse_entries (sig) PARSE_UNIFY_FACT_CONFIG_ARGS [normalisers, unifier]}

@{parse_entries (sig) UNIFY_RESOLVE_CHAINED_MODES [insert, resolve, fact]}

signature UNIFY_FACT_ARGS =
sig
  structure PA : PARSE_UNIFY_FACT_ARGS
  structure PCA : PARSE_UNIFY_FACT_CONFIG_ARGS

  val PCA_entries_from_PA_entries : ('a, 'b, 'c) PA.entries -> ('a, 'b) PCA.entries
  val PA_entries_from_PCA_entries : ('a, 'b) PCA.entries -> 'c -> ('a, 'b, 'c) PA.entries

  type args = (Unification_Base.normalisers, Unification_Base.unifier, thm list) PA.entries
  type config_args = (Unification_Base.normalisers, Unification_Base.unifier) PCA.entries

  val unify_fact_tac : args -> Proof.context -> int -> tactic
  val unify_fact_config_args_tac : config_args -> thm list -> Proof.context -> int -> tactic

  val arg_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser,
    'a context_parser -> thm list context_parser) PA.entries
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
type config_args = (Unification_Base.normalisers, Unification_Base.unifier) PCA.entries

fun unify_fact_tac args =
  Unify_Fact_Base.unify_fact_tac (PA.get_normalisers args) (PA.get_unifier args) (PA.get_facts args)

val unify_fact_config_args_tac = unify_fact_tac oo PA_entries_from_PCA_entries

val arg_parsers = {
  normalisers = SOME Unification_Parser.parse_normalisers,
  unifier = SOME Unification_Parser.parse_unifier,
  facts = SOME (fn unless => Scan.repeats (Scan.unless unless Parse_Util.multi_thm))
}

end

signature UNIFY_FACT =
sig
  structure FI : FUNCTOR_INSTANCE

  structure Data : GENERIC_DATA
  where type T = Unify_Fact_Args.config_args

  val get_config_args : Context.generic -> Unify_Fact_Args.config_args
  val map_config_args : (Unify_Fact_Args.config_args -> Unify_Fact_Args.config_args) ->
    Context.generic -> Context.generic

  val get_normalisers : Context.generic -> Unification_Base.normalisers
  val map_normalisers : (Unification_Base.normalisers -> Unification_Base.normalisers) ->
    Context.generic -> Context.generic

  val get_unifier : Context.generic -> Unification_Base.unifier
  val map_unifier : (Unification_Base.unifier -> Unification_Base.unifier) ->
    Context.generic -> Context.generic

  val unify_fact_tac : thm list -> Proof.context -> int -> tactic

  val binding : binding

  val parse_arg_entries : (ML_Code_Util.code, ML_Code_Util.code) Unify_Fact_Args.PCA.entries parser
  val attribute : (ML_Code_Util.code, ML_Code_Util.code) Unify_Fact_Args.PCA.entries * Position.T ->
    attribute
  val parse_attribute : attribute parser
  val setup_attribute : string option -> local_theory -> local_theory

  val parse_method : (Proof.context -> Method.method) context_parser
  val setup_method : string option -> local_theory -> local_theory
end

functor Unify_Fact_Functor(A :
  sig
    structure FI : FUNCTOR_INSTANCE_BASE
    val init_args : Unify_Fact_Args.config_args
  end) : UNIFY_FACT =
struct

structure UFA = Unify_Fact_Args
structure PCA = UFA.PCA
structure PA = UFA.PA

structure FI = Functor_Instance(A.FI)
structure MCU = ML_Code_Util

structure Data = Generic_Data(
  type T = UFA.config_args
  val empty = A.init_args
  val merge = fst)

val get_config_args = Data.get
val map_config_args = Data.map

val get_normalisers = PCA.get_normalisers o get_config_args
val map_normalisers = map_config_args o PCA.map_normalisers

val get_unifier = PCA.get_unifier o get_config_args
val map_unifier = map_config_args o PCA.map_unifier

fun unify_fact_tac facts ctxt =
  UFA.unify_fact_config_args_tac (get_config_args (Context.Proof ctxt)) facts ctxt

val binding = Binding.make (FI.id, FI.pos)

val parse_arg_entry =
  let
    val parsers = UFA.arg_parsers |> UFA.PCA_entries_from_PA_entries
    val parse_value = PCA.parse_entry (PCA.get_normalisers parsers) (PCA.get_unifier parsers)
  in Parse_Key_Value.parse_entry PCA.parse_key (K (Parse.$$$ ":")) parse_value end
val parse_arg_entries =
  PCA.parse_entries_required Scan.repeat1 true [] parse_arg_entry (PCA.empty_entries ())

fun attribute (entries, pos) =
  let
    fun code_PCA_op operation = MCU.flat_read ["Unify_Fact_Args.PCA.", operation]
    val code_from_key = code_PCA_op o PCA.key_to_string
    fun code_from_entry (PCA.normalisers c) = MCU.atomic c
      | code_from_entry (PCA.unifier c) = MCU.atomic c
    val code_entries = PCA.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ code_from_entry v)
      |> MCU.list
    val code = FI.code_struct_op "map_config_args" @ MCU.atomic (code_PCA_op "merge_entries" @
      MCU.atomic (code_PCA_op "entries_from_entry_list" @ code_entries))
  in ML_Attribute.run_map_context (code, pos) end

val parse_attribute = (parse_arg_entries |> Parse_Util.position) >> attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  the_default ("configure unify-fact data " ^ enclose "(" ")" FI.long_name)

val parse_method =
  PA.get_facts UFA.arg_parsers (Scan.lift parse_arg_entry)
  -- ((Scan.option (Args.$$$ "use") |-- parse_attribute) |> Parse.!!! |> Parse_Util.option |> Scan.lift)
  >> (fn (facts, opt_attr) =>
    the_default I (Option.map ML_Attribute_Util.attribute_map_ctxt opt_attr)
    #> Method_Util.METHOD_CONTEXT' (append facts #> unify_fact_tac))

val setup_method = Method.local_setup binding parse_method o
  the_default ("solve first subgoal by unification with a given fact; with adjustable unifier " ^
    enclose "(" ")" FI.long_name)

end
