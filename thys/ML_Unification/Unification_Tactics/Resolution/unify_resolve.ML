(*  Title:      ML_Unification/unify_resolve.ML
    Author:     Kevin Kappelmann

Unification-resolution tactics with arguments from context.
*)
@{parse_entries (sig) PARSE_UNIFY_RESOLVE_ARGS
  [normalisers, unifier, mode, chained, resolve_mode, rules]}

@{parse_entries (sig) PARSE_UNIFY_RESOLVE_CONTEXT_ARGS
  [normalisers, unifier, mode, chained]}

@{parse_entries (sig) PARSE_UNIFY_RESOLVE_MODES [any, every]}

@{parse_entries (sig) PARSE_UNIFY_RESOLVE_CHAINED_MODES [insert, resolve, fact]}

@{parse_entries (sig) PARSE_UNIFY_RESOLVE_RESOLVE_MODES [r, e, d, f]}

signature UNIFY_RESOLVE_ARGS =
sig
  include HAS_LOGGER

  structure PA : PARSE_UNIFY_RESOLVE_ARGS
  structure PCA : PARSE_UNIFY_RESOLVE_CONTEXT_ARGS

  val PCA_entries_from_PA_entries : ('a, 'b, 'c, 'd, 'e, 'f) PA.entries -> ('a, 'b, 'c, 'd) PCA.entries
  val PA_entries_from_PCA_entries : ('a, 'b, 'c, 'd) PCA.entries -> 'e -> 'f ->
    ('a, 'b, 'c, 'd, 'e, 'f) PA.entries

  structure PM : PARSE_UNIFY_RESOLVE_MODES
  type mode = PM.key
  val parse_mode : mode parser

  structure PCM : PARSE_UNIFY_RESOLVE_CHAINED_MODES
  type chained_mode = PCM.key
  val parse_chained_mode : chained_mode parser

  structure PRM : PARSE_UNIFY_RESOLVE_RESOLVE_MODES
  type resolve_mode = PRM.key
  val parse_resolve_mode : resolve_mode parser

  type args = (Unification_Base.normalisers, Unification_Base.unifier, mode, chained_mode,
    resolve_mode, thm list) PA.entries
  type context_args = (Unification_Base.normalisers, Unification_Base.unifier, mode,
    chained_mode) PCA.entries

  val unify_resolve_tac : args -> thm list -> Proof.context -> int -> tactic
  val unify_resolve_context_args_tac : context_args -> resolve_mode -> thm list -> thm list ->
    Proof.context -> int -> tactic

  val arg_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser, mode parser,
    chained_mode parser, resolve_mode parser, thm list context_parser) PA.entries
end

structure Unify_Resolve_Args : UNIFY_RESOLVE_ARGS =
struct

structure URB = Unify_Resolve_Base

val logger = Logger.setup_new_logger URB.logger "Unify_Resolve_Args"

@{parse_entries (struct) PA
  [normalisers, unifier, mode, chained, resolve_mode, rules]}
@{parse_entries (struct) PCA
  [normalisers, unifier, mode, chained]}

fun PCA_entries_from_PA_entries {normalisers = normalisers, unifier = unifier, mode = mode,
  chained = chained,...} =
  {normalisers = normalisers, unifier = unifier, mode = mode, chained = chained}
fun PA_entries_from_PCA_entries {normalisers = normalisers, unifier = unifier, mode = mode,
  chained = chained} resolve__mode rules = {normalisers = normalisers, unifier = unifier,
  mode = mode, chained = chained, resolve_mode = SOME resolve__mode, rules = SOME rules}

@{parse_entries (struct) PM [any, every]}
type mode = PM.key
val parse_mode = PM.parse_key

@{parse_entries (struct) PCM [insert, resolve, fact]}
type chained_mode = PCM.key
val parse_chained_mode = PCM.parse_key

@{parse_entries (struct) PRM [r, e, d, f]}
type resolve_mode = PRM.key
val parse_resolve_mode = PRM.parse_key

type args = (Unification_Base.normalisers, Unification_Base.unifier, mode, chained_mode,
  resolve_mode, thm list) PA.entries
type context_args = (Unification_Base.normalisers, Unification_Base.unifier, mode,
  chained_mode) PCA.entries

fun unify_resolve_tac args chained_facts ctxt i =
  let
    val norms = PA.get_normalisers args
    val unify = PA.get_unifier args
    val mode = PA.get_mode args
    val resolve_fn = (case (PA.get_resolve_mode args, mode) of
        (PRM.r _, PM.any _) => URB.unify_resolve_any_tac
      | (PRM.r _, PM.every _) => URB.unify_resolve_every_tac
        (*note: for e-resolution, we use the passed unifier to unify the conclusion
          as well as the premise of the elim-rule*)
      | (PRM.e _, PM.any _) => URB.unify_eresolve_any_tac norms unify
      | (PRM.e _, PM.every _) => URB.unify_eresolve_every_tac norms unify
      | (PRM.d _, PM.any _) => URB.unify_dresolve_any_tac
      | (PRM.d _, PM.every _) => URB.unify_dresolve_every_tac
      | (PRM.f _, PM.any _) => URB.unify_fresolve_any_tac
      | (PRM.f _, PM.every _) => URB.unify_fresolve_every_tac)
        norms unify
    val rules = PA.get_rules args
  in case PA.get_chained args of
      PCM.insert _ => (*insert chained facts*)
        (Tactic_Util.insert_tac chained_facts ctxt
        THEN' resolve_fn rules ctxt) i
    | cm => (*pre-process rules with chained facts*)
        let
          val process_rule_tac = (case cm of
              PCM.resolve _ => Unify_Resolve_Base.unify_resolve_every_tac
            | PCM.fact _ => Unify_Resolve_Base.unify_resolve_atomic_every_tac)
                norms unify chained_facts ctxt
            |> HEADGOAL
          fun add_rulesq (is_empty, rulesq) = case (is_empty, mode) of
              (true, PM.any _) => I
            | (true, PM.every _) => Seq.fail
            | _ => Seq.maps (fn rules => Seq.map (fn rule => rule :: rules) rulesq)
          fun process_rule rule = process_rule_tac rule
            |> General_Util.seq_is_empty
            |> tap (fn (true, _) => @{log Logger.WARN} ctxt (fn _ => Pretty.block [
                  Pretty.str "Could not use chained facts for rule ",
                  Thm.pretty_thm ctxt rule
                ] |> Pretty.string_of)
              | _ => ())
            |> add_rulesq
        in
          fold_rev process_rule rules (Seq.single [])
          |> Seq.lifts (fn rules => resolve_fn rules ctxt i)
        end
  end

val unify_resolve_context_args_tac = unify_resolve_tac ooo PA_entries_from_PCA_entries

val arg_parsers = {
  normalisers = SOME Unification_Parser.parse_normalisers,
  unifier = SOME Unification_Parser.parse_unifier,
  mode = SOME parse_mode,
  chained = SOME parse_chained_mode,
  resolve_mode = SOME parse_resolve_mode,
  rules = SOME (Parse_Util.nonempty_thms (K "must provide at least one rule to resolve"))
}

end

signature UNIFY_RESOLVE =
sig
  structure Data : GENERIC_DATA

  val get_args : Context.generic -> Unify_Resolve_Args.context_args
  val map_args : (Unify_Resolve_Args.context_args -> Unify_Resolve_Args.context_args) ->
    Context.generic -> Context.generic

  val get_normalisers : Context.generic -> Unification_Base.normalisers
  val map_normalisers : (Unification_Base.normalisers -> Unification_Base.normalisers) ->
    Context.generic -> Context.generic

  val get_unifier : Context.generic -> Unification_Base.unifier
  val map_unifier : (Unification_Base.unifier -> Unification_Base.unifier) ->
    Context.generic -> Context.generic

  val get_mode : Context.generic -> Unify_Resolve_Args.mode
  val map_mode : (Unify_Resolve_Args.mode -> Unify_Resolve_Args.mode) ->
    Context.generic -> Context.generic

  val get_chained : Context.generic -> Unify_Resolve_Args.chained_mode
  val map_chained : (Unify_Resolve_Args.chained_mode -> Unify_Resolve_Args.chained_mode) ->
    Context.generic -> Context.generic

  val unify_resolve_tac : Unify_Resolve_Args.resolve_mode -> thm list -> thm list -> Proof.context ->
    int -> tactic

  val binding : binding

  val attribute : (ML_Code_Util.code, ML_Code_Util.code, Unify_Resolve_Args.mode,
    Unify_Resolve_Args.chained_mode) Unify_Resolve_Args.PCA.entries * Position.T -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : string option -> local_theory -> local_theory

  val parse_method : (Proof.context -> Method.method) context_parser
  val setup_method : string option -> local_theory -> local_theory
end

functor Unify_Resolve(A : sig
    structure FIA : FUNCTOR_INSTANCE_ARGS
    val init_args : Unify_Resolve_Args.context_args
  end) : UNIFY_RESOLVE =
struct

structure URA = Unify_Resolve_Args
structure PCA = URA.PCA
structure PA = URA.PA
structure PRM = URA.PRM
structure FIU = Functor_Instance_Util(A.FIA)
structure MCU = ML_Code_Util

structure Data = Generic_Data(struct
  type T = URA.context_args
  val empty = A.init_args
  val merge = fst
end)

val get_args = Data.get
val map_args = Data.map

val get_normalisers = PCA.get_normalisers o get_args
val map_normalisers = map_args o PCA.map_normalisers

val get_unifier = PCA.get_unifier o get_args
val map_unifier = map_args o PCA.map_unifier

val get_mode = PCA.get_mode o get_args
val map_mode = map_args o PCA.map_mode

val get_chained = PCA.get_chained o get_args
val map_chained = map_args o PCA.map_chained

fun unify_resolve_tac resolve_mode rules facts ctxt =
  URA.unify_resolve_context_args_tac (get_args (Context.Proof ctxt)) resolve_mode rules facts
    ctxt

val binding = FIU.mk_binding_id_prefix "urule"

val parse_arg_entries =
  let
    val parsers = URA.arg_parsers |> URA.PCA_entries_from_PA_entries
    val parse_value = PCA.parse_entry (PCA.get_normalisers parsers)
      (PCA.get_unifier parsers) (PCA.get_mode parsers) (PCA.get_chained parsers)
    val parse_entry = Parse_Key_Value.parse_entry PCA.parse_key Parse_Util.eq parse_value
  in PCA.parse_entries_required Parse.and_list1 [] parse_entry (PCA.empty_entries ()) end

fun attribute (entries, pos) =
  let
    fun URA_substructure_op substructure operation =
      MCU.flat_read ["Unify_Resolve_Args.", substructure, ".", operation]
    val [code_PM_op, code_PCM_op, code_PCA_op] = map URA_substructure_op ["PM", "PCM", "PCA"]
    val code_from_key = code_PCA_op o PCA.key_to_string
    fun code_from_entry (PCA.normalisers c) = c
      | code_from_entry (PCA.unifier c) = c
      | code_from_entry (PCA.mode m) = code_PM_op "key" @ code_PM_op (URA.PM.key_to_string m)
      | code_from_entry (PCA.chained cm) = code_PCM_op "key" @ code_PCM_op (URA.PCM.key_to_string cm)
    val code_entries = PCA.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code =
      FIU.code_struct_op "map_args" @ MCU.atomic (code_PCA_op "merge_entries" @
      MCU.atomic (code_PCA_op "entries_from_entry_list" @ code_entries))
  in ML_Attribute.run_map_context (code, pos) end

val parse_attribute = (parse_arg_entries |> Parse_Util.position) >> attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  the_default ("set unify-resolution arguments (" ^ FIU.FIA.full_name ^ ")")

val parse_method =
  let val parse_resolve_mode = Scan.optional
    (Parse_Util.parenths (PA.get_resolve_mode URA.arg_parsers |> Parse.!!!))
    (PRM.key PRM.r)
  in
    Scan.lift parse_resolve_mode
    -- PA.get_rules URA.arg_parsers
    -- ((Parse.where_ |-- parse_attribute) |> Parse.!!! |> Parse_Util.option |> Scan.lift)
    >> (fn ((resolve_mode, rules), opt_attr) =>
      the_default I (Option.map ML_Attribute_Util.attribute_map_ctxt opt_attr)
      #> Method_Util.METHOD_CONTEXT' (unify_resolve_tac resolve_mode rules))
  end

val setup_method = Method.local_setup binding parse_method o
  the_default ("r/e/d/f-resolve rule(s) with first subgoal; with adjustable unifier ("
    ^ FIU.FIA.full_name ^ ")")

end