(*  Title:      ML_Unification/term_index_unification_hints.ML
    Author:     Kevin Kappelmann

Unification hints stored in term indexes.
*)
@{parse_entries (sig) PARSE_TERM_INDEX_UNIFICATION_HINTS_MODE
  [add, del]}

@{parse_entries (sig) PARSE_TERM_INDEX_UNIFICATION_HINTS_ARGS
  [concl_unifier, normalisers, prems_unifier, retrieval, hint_preprocessor, prio]}

@{parse_entries (sig) PARSE_TERM_INDEX_UNIFICATION_HINTS_CONTEXT_ARGS
  [concl_unifier, normalisers, prems_unifier, retrieval, hint_preprocessor]}

signature TERM_INDEX_UNIFICATION_HINTS_ARGS =
sig
  structure PA : PARSE_TERM_INDEX_UNIFICATION_HINTS_ARGS
  structure PCA : PARSE_TERM_INDEX_UNIFICATION_HINTS_CONTEXT_ARGS

  val PCA_entries_from_PA_entries : ('a, 'b, 'c, 'd, 'e, 'f) PA.entries ->
    ('a, 'b, 'c, 'd, 'e) PCA.entries
  val PA_entries_from_PCA_entries : ('a, 'b, 'c, 'd, 'e) PCA.entries -> 'f ->
    ('a, 'b, 'c, 'd, 'e, 'f) PA.entries
  val UHA_PA_entries_from_PCA_entries : ('a, 'b, 'c, 'd, 'e) PCA.entries ->
    ('a, 'b, 'c) Unification_Hints_Args.PA.entries

  structure PM : PARSE_TERM_INDEX_UNIFICATION_HINTS_MODE
  type mode = PM.key
  val parse_mode : mode parser

  type hint_prio = Unification_Hints_Base.unif_hint * Prio.prio
  val pretty_hint_prio : Proof.context -> hint_prio -> Pretty.T

  val retrieve_left : ('ti -> term -> hint_prio list) -> 'ti * 'ti -> term * term -> hint_prio list
  val retrieve_right : ('ti -> term -> hint_prio list) -> 'ti * 'ti -> term * term -> hint_prio list
  val retrieve_pair : ('ti -> term -> hint_prio list) -> 'ti * 'ti -> term * term -> hint_prio list
  val retrieve_sym : ('ti -> term * term -> hint_prio list) -> 'ti -> term * term -> hint_prio list

  val sort_hint_prios : hint_prio list -> hint_prio list
  val sorted_hint_seq_of_hint_prios : hint_prio list -> thm Seq.seq

  val mk_retrieval : ('ti -> term * term -> hint_prio list) -> (term * term -> term * term) ->
    'ti -> Unification_Hints_Base.hint_retrieval
  val mk_retrieval_left : ('ti -> term -> hint_prio list) -> Term_Normalisation.term_normaliser ->
    'ti * 'ti -> Unification_Hints_Base.hint_retrieval
  val mk_retrieval_right : ('ti -> term -> hint_prio list) -> Term_Normalisation.term_normaliser ->
    'ti * 'ti -> Unification_Hints_Base.hint_retrieval
  val mk_retrieval_pair : ('ti -> term -> hint_prio list) -> Term_Normalisation.term_normaliser ->
    'ti * 'ti -> Unification_Hints_Base.hint_retrieval
  val mk_retrieval_sym : ('ti -> term * term -> hint_prio list) -> Term_Normalisation.term_normaliser ->
    'ti -> Unification_Hints_Base.hint_retrieval
  val mk_retrieval_sym_pair : ('ti -> term -> hint_prio list) -> Term_Normalisation.term_normaliser ->
    'ti * 'ti -> Unification_Hints_Base.hint_retrieval

  type 'ti args = (Unification_Base.unifier, Unification_Base.normalisers, Unification_Base.unifier,
    'ti * 'ti -> Unification_Hints_Base.hint_retrieval, Unification_Hints_Base.hint_preprocessor,
    Prio.prio) PA.entries
  type 'ti context_args = (Unification_Base.unifier, Unification_Base.normalisers,
    Unification_Base.unifier, 'ti * 'ti -> Unification_Hints_Base.hint_retrieval,
    Unification_Hints_Base.hint_preprocessor) PCA.entries

  val arg_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser, ML_Code_Util.code parser,
    ML_Code_Util.code parser, ML_Code_Util.code parser, Prio.prio context_parser) PA.entries
end

structure Term_Index_Unification_Hints_Args : TERM_INDEX_UNIFICATION_HINTS_ARGS =
struct

structure UB = Unification_Base
structure EN = Envir_Normalisation
structure UHB = Unification_Hints_Base
structure UHA = Unification_Hints_Args
structure TUHP = Prio

@{parse_entries (struct) PA
  [concl_unifier, normalisers, prems_unifier, retrieval, hint_preprocessor, prio]}

@{parse_entries (struct) PCA
  [concl_unifier, normalisers, prems_unifier, retrieval, hint_preprocessor]}

fun PCA_entries_from_PA_entries {concl_unifier = concl_unifier, normalisers = normalisers,
  prems_unifier = prems_unifier, retrieval = retrieval, hint_preprocessor = hint_preprocessor,...} =
  {concl_unifier = concl_unifier, normalisers = normalisers, prems_unifier = prems_unifier,
    retrieval = retrieval, hint_preprocessor = hint_preprocessor}
fun PA_entries_from_PCA_entries {concl_unifier = concl_unifier, normalisers = normalisers,
  prems_unifier = prems_unifier, retrieval = retrieval, hint_preprocessor = hint_preprocessor} prio =
  {concl_unifier = concl_unifier, normalisers = normalisers, prems_unifier = prems_unifier,
    retrieval = retrieval, hint_preprocessor = hint_preprocessor, prio = SOME prio}

fun UHA_PA_entries_from_PCA_entries {concl_unifier = concl_unifier, normalisers = normalisers,
  prems_unifier = prems_unifier,...} =
  {concl_unifier = concl_unifier, normalisers = normalisers, prems_unifier = prems_unifier}

@{parse_entries (struct) PM
  [add, del]}
type mode = PM.key
val parse_mode = PM.parse_key

type hint_prio = UHB.unif_hint * TUHP.prio

fun pretty_hint_prio ctxt (hint, prio) = Pretty.block [
    UHB.pretty_hint ctxt hint,
    Pretty.enclose " (" ")" [Pretty.str "priority: ", Prio.pretty prio]
  ]

fun retrieve_left retrieve (ti,_) (t, _) = retrieve ti t
fun retrieve_right retrieve (_, ti) (_, t) = retrieve ti t

fun retrieve_pair retrieve (ti_lhs, ti_rhs) (tlhs, trhs) =
  retrieve ti_lhs tlhs @ retrieve ti_rhs trhs

fun interleave [] ys = ys
  | interleave xs [] = xs
  | interleave (x :: xs) (y :: ys) = x :: y :: interleave xs ys

fun retrieve_sym retrieve ti tp = interleave
  (retrieve ti tp)
  (retrieve ti (swap tp) |> map (apfst Unification_Hints_Base.symmetric_hint))

(*FIXME: use Prio.Table instead of sorted lists*)
val sort_hint_prios = sort (rev_order o Prio.ord o apply2 snd)

val sorted_hint_seq_of_hint_prios =
  sort_hint_prios #> Seq.of_list #> Seq.map fst

fun mk_retrieval f norm_terms ti _ _ tp _ =
  f ti (norm_terms tp) |> sorted_hint_seq_of_hint_prios

fun mk_retrieval_left retrieve = mk_retrieval (retrieve_left retrieve) o apfst
fun mk_retrieval_right retrieve = mk_retrieval (retrieve_right retrieve) o apsnd
fun mk_retrieval_pair retrieve = mk_retrieval (retrieve_pair retrieve) o apply2
fun mk_retrieval_sym retrieve = mk_retrieval (retrieve_sym retrieve) o apply2
fun mk_retrieval_sym_pair retrieve = mk_retrieval (retrieve_sym (retrieve_pair retrieve)) o apply2

type 'ti args = (UB.unifier, UB.normalisers, UB.unifier, 'ti * 'ti -> UHB.hint_retrieval,
  UHB.hint_preprocessor, TUHP.prio) PA.entries
type 'ti context_args = (UB.unifier, UB.normalisers, UB.unifier, 'ti * 'ti -> UHB.hint_retrieval,
  UHB.hint_preprocessor) PCA.entries

val arg_parsers = {
    concl_unifier = UHA.PA.get_concl_unifier_safe UHA.arg_parsers,
    normalisers = UHA.PA.get_normalisers_safe UHA.arg_parsers,
    prems_unifier = UHA.PA.get_prems_unifier_safe UHA.arg_parsers,
    retrieval = SOME (Parse_Util.nonempty_code (K "retrieval function must not be empty")),
    hint_preprocessor = SOME (Parse_Util.nonempty_code (K "hint preprocessor must not be empty")),
    prio = SOME Prio.parse
  }

end

signature TERM_INDEX_UNIFICATION_HINTS =
sig
  include HAS_LOGGER

  structure UH : UNIFICATION_HINTS

  (*underlying term index*)
  structure TI : TERM_INDEX
  structure Data : GENERIC_DATA

  type term_index = Term_Index_Unification_Hints_Args.hint_prio TI.term_index

  val get_retrieval : Context.generic -> term_index * term_index ->
    Unification_Hints_Base.hint_retrieval
  val map_retrieval : ((term_index * term_index -> Unification_Hints_Base.hint_retrieval) ->
    term_index * term_index -> Unification_Hints_Base.hint_retrieval) ->
    Context.generic -> Context.generic

  val get_hint_preprocessor : Context.generic -> Unification_Hints_Base.hint_preprocessor
  val map_hint_preprocessor : (Unification_Hints_Base.hint_preprocessor ->
    Unification_Hints_Base.hint_preprocessor) -> Context.generic -> Context.generic

  val get_indexes : Context.generic -> term_index * term_index
  val get_lhs_index : Context.generic -> term_index
  val get_rhs_index : Context.generic -> term_index

  val map_indexes : (term_index * term_index -> term_index * term_index) ->
    Context.generic -> Context.generic
  val map_lhs_index : (term_index -> term_index) -> Context.generic -> Context.generic
  val map_rhs_index : (term_index -> term_index) -> Context.generic -> Context.generic

  val pretty_indexes : Proof.context -> Pretty.T
  val pretty_lhs_index : Proof.context -> Pretty.T
  val pretty_rhs_index : Proof.context -> Pretty.T

  val add_hint_prio : Term_Index_Unification_Hints_Args.hint_prio -> Context.generic ->
    Context.generic

  val del_hint : Unification_Hints_Base.unif_hint -> Context.generic -> Context.generic

  val try_hints : Unification_Base.unifier

  val binding : binding

  val attribute : (Term_Index_Unification_Hints_Args.mode *
    ((ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code,
      ML_Code_Util.code, ML_Code_Util.code, Prio.prio)
      Term_Index_Unification_Hints_Args.PA.entries)) *
    Position.T -> attribute
  val parse_attribute : attribute context_parser
  val setup_attribute : string option -> local_theory -> local_theory
end

functor Term_Index_Unification_Hints(A : sig
  structure FIA : FUNCTOR_INSTANCE_ARGS
  structure TI : TERM_INDEX
  val init_args : (Term_Index_Unification_Hints_Args.hint_prio TI.term_index)
    Term_Index_Unification_Hints_Args.context_args
  end) : TERM_INDEX_UNIFICATION_HINTS =
struct

structure UHB = Unification_Hints_Base
structure TUHA = Term_Index_Unification_Hints_Args
structure TUHP = Prio
structure PA = TUHA.PA
structure PCA = TUHA.PCA
structure PM = TUHA.PM

structure FIU = Functor_Instance_Util(A.FIA)
structure TI = A.TI

structure MCU = ML_Code_Util
structure PU = Parse_Util

val logger = Logger.setup_new_logger Unification_Hints_Base.logger FIU.base_name

@{functor_instance struct_name = UH
  and functor_name = Unification_Hints
  and accessor = FIU.accessor
  and id = FIU.FIA.id
  and more_args = \<open>val init_args = TUHA.UHA_PA_entries_from_PCA_entries A.init_args\<close>}

fun are_hint_variants hp =
  let
    val ctp = apply2 Thm.cprop_of hp
    val match = Thm.first_order_match
  in can match ctp andalso can match (swap ctp) end

val term_index_data_eq = are_hint_variants o apply2 fst

type term_index = TUHA.hint_prio TI.term_index

structure Data = Generic_Data(Pair_Generic_Data_Args(
struct
  structure Data1 = Pair_Generic_Data_Args(
  struct
    structure Data1 =
    struct
      type T = term_index * term_index -> Unification_Hints_Base.hint_retrieval
      val empty = PCA.get_retrieval A.init_args
      val merge = fst
    end
    structure Data2 =
    struct
      type T = UHB.hint_preprocessor
      val empty = PCA.get_hint_preprocessor A.init_args
      val merge = fst
    end
  end)
  structure Data2 = Pair_Generic_Data_Args(
    structure Data1 = Term_Index_Generic_Data_Args(
    struct
      type data = TUHA.hint_prio
      structure TI = TI
      val data_eq = term_index_data_eq
    end)
    structure Data2 = Term_Index_Generic_Data_Args(
    struct
      type data = TUHA.hint_prio
      structure TI = TI
      val data_eq = term_index_data_eq
    end))
end))

val get_retrieval = fst o fst o Data.get
val map_retrieval = Data.map o apfst o apfst

val get_hint_preprocessor = snd o fst o Data.get
val map_hint_preprocessor = Data.map o apfst o apsnd

val get_indexes = snd o Data.get
val get_lhs_index = fst o get_indexes
val get_rhs_index = snd o get_indexes

val map_indexes = Data.map o apsnd
val map_lhs_index = map_indexes o apfst
val map_rhs_index = map_indexes o apsnd

fun pretty_index ctxt = TI.content
  #> TUHA.sort_hint_prios
  #> map (TUHA.pretty_hint_prio ctxt)
  #> Pretty.fbreaks
  #> Pretty.block

fun pretty_index' index_description ctxt = Pretty.fbreaks [
    index_description,
    get_lhs_index (Context.Proof ctxt) |> pretty_index ctxt
  ] |> Pretty.block

val pretty_lhs_index_description = Pretty.str "left-hand side index"
val pretty_rhs_index_description = Pretty.str "right-hand side index"

val pretty_lhs_index = pretty_index' pretty_lhs_index_description
val pretty_rhs_index = pretty_index' pretty_rhs_index_description

fun pretty_indexes ctxt = Pretty.fbreaks [
    pretty_lhs_index ctxt,
    pretty_rhs_index ctxt
  ] |> Pretty.block

val term_index_keys_from_hint =
  UHB.cdest_hint_concl #> apply2 (Thm.term_of #> TI.norm_term)

val pretty_spaced_block = Pretty.separate "" #> Pretty.block #> Pretty.string_of

fun msg_illegal_hint_format ctxt hint = pretty_spaced_block [
    Pretty.str "Illegal hint format for",
    UHB.pretty_hint ctxt hint
  ]

fun preprocess_hint context = get_hint_preprocessor context (Context.proof_of context)

fun add_hint_prio index_description get_index map_index key (hint, prio) context =
  let
    val ctxt = Context.proof_of context
    val is_hint_variant = curry are_hint_variants hint o fst
  in
    (@{log Logger.DEBUG} ctxt (fn _ => pretty_spaced_block [
        Pretty.str "Adding hint to",
        index_description,
        UHB.pretty_hint ctxt hint
      ]);
    TI.insert is_hint_variant (key, (hint, prio)) (get_index context)
    |> (fn ti => map_index (K ti) context))
    handle Term_Index_Base.INSERT =>
      (@{log Logger.WARN} ctxt
        (fn _ => pretty_spaced_block [
          Pretty.str "Hint",
          UHB.pretty_hint ctxt hint,
          Pretty.str "already added to",
          index_description
        ]);
      context)
    | TERM _ => (@{log Logger.WARN} ctxt (fn _ => msg_illegal_hint_format ctxt hint);
      context)
  end

val add_hint_prio_lhs = add_hint_prio pretty_lhs_index_description get_lhs_index map_lhs_index
val add_hint_prio_rhs = add_hint_prio pretty_rhs_index_description get_rhs_index map_rhs_index

fun add_hint_prio (hint, prio) context =
  let
    val hint = preprocess_hint context hint
    val (lhs_key, rhs_key) = term_index_keys_from_hint hint
  in
    add_hint_prio_lhs lhs_key (hint, prio) context
    |> add_hint_prio_rhs rhs_key (hint, prio)
  end

fun del_hint index_description get_index map_index key hint context =
  let
    val ctxt = Context.proof_of context
    val is_hint_variant = curry are_hint_variants hint o fst
  in
    (@{log Logger.DEBUG} ctxt (fn _ => pretty_spaced_block [
        Pretty.str "Deleting hint from",
        index_description,
        UHB.pretty_hint ctxt hint
      ]);
    TI.delete is_hint_variant key (get_index context)
    |> (fn ti => map_index (K ti) context))
    handle Term_Index_Base.DELETE =>
      (@{log Logger.WARN} ctxt
        (fn _ => pretty_spaced_block [
          Pretty.str "Hint ",
          UHB.pretty_hint ctxt hint,
          Pretty.str " not found in",
          index_description
        ]);
      context)
    | TERM _ => (@{log Logger.WARN} ctxt (fn _ => msg_illegal_hint_format ctxt hint);
      context)
  end

val del_hint_lhs = del_hint pretty_lhs_index_description get_lhs_index map_lhs_index
val del_hint_rhs = del_hint pretty_rhs_index_description get_rhs_index map_rhs_index

fun del_hint hint context =
  let
    val hint = preprocess_hint context hint
    val (lhs_key, rhs_key) = term_index_keys_from_hint hint
  in del_hint_lhs lhs_key hint context |> del_hint_rhs rhs_key hint end

val binding = FIU.mk_binding_id_prefix "uhint"

fun try_hints binders ctxt tp env = Seq.make (fn _ =>
  let
    val context = Context.Proof ctxt
    val _ = @{log Logger.DEBUG} ctxt (fn _ => pretty_spaced_block [
        Pretty.str "Trying unification hints",
        Binding.pretty binding,
        Pretty.str "for",
        Unification_Util.pretty_unif_problem ctxt tp
      ])
  in UH.try_hints (get_retrieval context (get_indexes context)) binders ctxt tp env |> Seq.pull end)

val default_entries = PA.empty_entries () |> fold PA.set_entry [PA.prio TUHP.MEDIUM]

fun parse_arg_entries mode =
  let
    val parsers = TUHA.arg_parsers
    val parse_value = PA.parse_entry (PA.get_concl_unifier parsers |> Scan.lift)
      (PA.get_normalisers parsers |> Scan.lift) (PA.get_prems_unifier parsers |> Scan.lift)
      (PA.get_retrieval parsers |> Scan.lift) (PA.get_hint_preprocessor parsers |> Scan.lift)
      (PA.get_prio parsers)
    val parse_entry = Parse_Key_Value.parse_entry' (Scan.lift PA.parse_key)
      (Scan.lift PU.eq) parse_value
  in
    PA.parse_entries_required' Parse.and_list1' [] parse_entry default_entries
    |> mode = PM.key PM.del ?
      PU.filter_cut' (is_none o PA.get_prio_safe) (K o K "Priority may not be specified for deletion.")
  end

fun attribute ((mode, entries), pos) =
  let
    fun update_index thm = Term_Util.no_dummy_pattern (Thm.prop_of thm) ? (
      case mode of
        PM.add _ => add_hint_prio (thm, PA.get_prio entries)
      | PM.del _ => del_hint thm)
    val PCA_entries = TUHA.PCA_entries_from_PA_entries entries
    val UHA_PA_entries = TUHA.UHA_PA_entries_from_PCA_entries PCA_entries
    val run_code = ML_Attribute.run_map_context o rpair pos
    fun default_code (context, _) = (SOME context, NONE)
    val map_retrieval = case PCA.get_retrieval_safe PCA_entries of
        SOME c => FIU.code_struct_op "map_retrieval" @ MCU.atomic (MCU.read "K" @ MCU.atomic c)
          |> run_code
      | NONE => default_code
    val map_hint_preprocessor = case PCA.get_hint_preprocessor_safe PCA_entries of
        SOME c => FIU.code_struct_op "map_hint_preprocessor" @ MCU.atomic (MCU.read "K" @ MCU.atomic c)
          |> run_code
      | NONE => default_code
  in
    ML_Attribute_Util.apply_attribute (Thm.declaration_attribute update_index)
    #> ML_Attribute_Util.apply_attribute (UH.attribute (UHA_PA_entries, pos))
    #> ML_Attribute_Util.apply_attribute map_retrieval
    #> map_hint_preprocessor
  end

val parse_attribute =
  (Scan.lift (Scan.optional TUHA.parse_mode (PM.key PM.add))
  :-- (fn mode => PU.optional' ((Scan.lift Parse.where_ |-- parse_arg_entries mode) |> Parse.!!!!)
    default_entries)
  |> PU.position')
  >> attribute

val setup_attribute = Attrib.local_setup binding (Parse.!!!! parse_attribute) o
  the_default ("set unification hints arguments (" ^ FIU.FIA.full_name ^ ")")

end
