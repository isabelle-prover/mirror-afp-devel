(*  Title:      ML_Unification/unify_of.ML
    Author:     Kevin Kappelmann

OF attribute with arguments from context.
*)
@{parse_entries (sig) PARSE_UNIFY_OF_ARGS [normalisers, unifier, mode, rules]}
@{parse_entries (sig) PARSE_UNIFY_OF_CONFIG_ARGS [normalisers, unifier, mode]}
@{parse_entries (sig) PARSE_UNIFY_OF_MODES [resolve, fact]}

signature UNIFY_OF_ARGS =
sig
  structure PA : PARSE_UNIFY_OF_ARGS
  structure PCA : PARSE_UNIFY_OF_CONFIG_ARGS

  val PCA_entries_from_PA_entries : ('a, 'b, 'c, 'd) PA.entries -> ('a, 'b, 'c) PCA.entries
  val PA_entries_from_PCA_entries : ('a, 'b, 'c) PCA.entries -> 'd -> ('a, 'b, 'c, 'd) PA.entries

  structure PM : PARSE_UNIFY_OF_MODES
  type mode = PM.key
  val parse_mode : mode parser

  type args = (Unification_Base.normalisers, Unification_Base.unifier, mode, thm list)
    PA.entries
  type config_args = (Unification_Base.normalisers, Unification_Base.unifier, mode)
    PCA.entries

  val unify_OF : args -> Proof.context -> thm -> thm option
  val unify_OF_config_args : config_args -> thm list -> Proof.context -> thm -> thm option

  val unify_OF_attribute : args -> attribute
  val unify_OF_config_args_attribute : config_args -> thm list -> attribute

  val arg_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser, mode parser,
    'a context_parser -> thm list context_parser) PA.entries
end

structure Unify_OF_Args : UNIFY_OF_ARGS =
struct

structure URB = Unify_Resolve_Base

@{parse_entries (struct) PA [normalisers, unifier, mode, rules]}
@{parse_entries (struct) PCA [normalisers, unifier, mode]}

fun PCA_entries_from_PA_entries {normalisers = normalisers, unifier = unifier, mode = mode,...} =
  {normalisers = normalisers, unifier = unifier, mode = mode}
fun PA_entries_from_PCA_entries {normalisers = normalisers, unifier = unifier, mode = mode} rules =
  {normalisers = normalisers, unifier = unifier, mode = mode, rules = SOME rules}

@{parse_entries (struct) PM [resolve, fact]}
type mode = PM.key
val parse_mode = PM.parse_key

type args = (Unification_Base.normalisers, Unification_Base.unifier, mode, thm list)
  PA.entries
type config_args = (Unification_Base.normalisers, Unification_Base.unifier, mode)
  PCA.entries

fun gen_unify_of unify_OF_fn args =
  let val resolve_fn = case PA.get_mode args of
      PM.resolve _ => URB.unify_resolve_tac
    | PM.fact _ => URB.unify_resolve_atomic_tac
  in unify_OF_fn resolve_fn (PA.get_normalisers args) (PA.get_unifier args) (PA.get_rules args) end

val unify_OF = gen_unify_of Unify_OF_Base.unify_OF
val unify_OF_config_args = unify_OF oo PA_entries_from_PCA_entries

val unify_OF_attribute = gen_unify_of Unify_OF_Base.unify_OF_attribute
val unify_OF_config_args_attribute = unify_OF_attribute oo PA_entries_from_PCA_entries

val arg_parsers = {
  normalisers = SOME Unification_Parser.parse_normalisers,
  unifier = SOME Unification_Parser.parse_unifier,
  mode = SOME parse_mode,
  rules = SOME (fn unless => Scan.repeats (Scan.unless unless Parse_Util.multi_thm))
}

end

signature UNIFY_OF =
sig
  structure Data : GENERIC_DATA
  where type T = Unify_OF_Args.config_args

  val get_config_args : Context.generic -> Unify_OF_Args.config_args
  val map_config_args : (Unify_OF_Args.config_args -> Unify_OF_Args.config_args) ->
    Context.generic -> Context.generic

  val get_normalisers : Context.generic -> Unification_Base.normalisers
  val map_normalisers : (Unification_Base.normalisers -> Unification_Base.normalisers) ->
    Context.generic -> Context.generic

  val get_unifier : Context.generic -> Unification_Base.unifier
  val map_unifier : (Unification_Base.unifier -> Unification_Base.unifier) ->
    Context.generic -> Context.generic

  val get_mode : Context.generic -> Unify_OF_Args.mode
  val map_mode : (Unify_OF_Args.mode -> Unify_OF_Args.mode) ->
    Context.generic -> Context.generic

  val unify_OF : thm list -> Proof.context -> thm -> thm option
  val unify_OF_attribute : thm list -> attribute

  val binding : binding

  val parse_arg_entries : (ML_Code_Util.code, ML_Code_Util.code, Unify_OF_Args.mode)
    Unify_OF_Args.PCA.entries parser
  val set_args_attribute : (ML_Code_Util.code, ML_Code_Util.code, Unify_OF_Args.mode)
    Unify_OF_Args.PCA.entries * Position.T -> attribute
  val parse_set_args_attribute : attribute parser

  val parse_attribute : attribute context_parser
  val setup_attribute : string option -> local_theory -> local_theory
end

functor Unify_OF(A :
  sig
    structure FI : FUNCTOR_INSTANCE_BASE
    val init_args : Unify_OF_Args.config_args
  end) : UNIFY_OF =
struct

structure UOA = Unify_OF_Args
structure PCA = Unify_OF_Args.PCA
structure PA = Unify_OF_Args.PA
structure FI = Functor_Instance(A.FI)
structure MCU = ML_Code_Util

structure Data = Generic_Data(
  type T = UOA.config_args
  val empty = A.init_args
  val merge = fst)

val get_config_args = Data.get
val map_config_args = Data.map

val get_normalisers = PCA.get_normalisers o get_config_args
val map_normalisers = map_config_args o PCA.map_normalisers

val get_unifier = PCA.get_unifier o get_config_args
val map_unifier = map_config_args o PCA.map_unifier

val get_mode = PCA.get_mode o get_config_args
val map_mode = map_config_args o PCA.map_mode

fun unify_OF rules context =
  UOA.unify_OF_config_args (get_config_args (Context.Proof context)) rules context
fun unify_OF_attribute rules (context, thm) =
  UOA.unify_OF_config_args_attribute (get_config_args context) rules (context, thm)

val binding = Binding.make (FI.prefix_id "uOF", FI.pos)

val parse_arg_entry =
  let
    val parsers = UOA.arg_parsers |> UOA.PCA_entries_from_PA_entries
    val parse_value = PCA.parse_entry (PCA.get_normalisers parsers)
      (PCA.get_unifier parsers) (PCA.get_mode parsers)
  in Parse_Key_Value.parse_entry PCA.parse_key (K (Parse.$$$ ":")) parse_value end
val parse_arg_entries =
  PCA.parse_entries_required Scan.repeat1 true [] parse_arg_entry (PCA.empty_entries ())

fun set_args_attribute (entries, pos) =
  let
    fun UOA_substructure_op substructure operation =
      MCU.flat_read ["Unify_OF_Args.", substructure, ".", operation]
    val (code_PM_op, code_PCA_op) = apply2 UOA_substructure_op ("PM", "PCA")
    val code_from_key = code_PCA_op o PCA.key_to_string
    fun code_from_entry (PCA.normalisers c) = c
      | code_from_entry (PCA.unifier c) = c
      | code_from_entry (PCA.mode m) = code_PM_op "key" @ code_PM_op (UOA.PM.key_to_string m)
    val code_entries = PCA.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code =
      FI.code_struct_op "map_config_args" @ MCU.atomic (code_PCA_op "merge_entries" @
      MCU.atomic (code_PCA_op "entries_from_entry_list" @ code_entries))
  in ML_Attribute.run_map_context (code, pos) end

val parse_set_args_attribute = (parse_arg_entries |> Parse_Util.position) >> set_args_attribute

val parse_attribute =
  PA.get_rules UOA.arg_parsers (Scan.lift parse_arg_entry)
  :-- (fn [] => (parse_set_args_attribute |> Parse.!!!) >> SOME |> Scan.lift
        | _ => (Scan.option (Args.$$$ "use") |-- parse_set_args_attribute) |> Parse.!!! |> Parse_Util.option
          |> Scan.lift)
    (*if there are no rules, we update the arguments in the context*)
  >> (fn ([], SOME attr) => attr
    (*otherwise, we use the arguments but do not store them in the context*)
    | (rules, opt_attr) =>
        apfst (the_default I (Option.map ML_Attribute_Util.attribute_map_context opt_attr))
        #> unify_OF_attribute rules)

val setup_attribute = Attrib.local_setup binding parse_attribute o
  the_default ("apply theorem to arguments " ^ enclose "(" ")" FI.long_name)

end