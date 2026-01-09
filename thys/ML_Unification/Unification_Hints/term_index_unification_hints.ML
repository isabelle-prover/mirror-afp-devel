(*  Title:      ML_Unification/term_index_unification_hints.ML
    Author:     Kevin Kappelmann

Unification hints stored in term indexes.
*)
@{parse_entries (sig) PARSE_TERM_INDEX_UNIFICATION_HINTS_MODE [add, del, config]}
@{parse_entries (sig) PARSE_TERM_INDEX_UNIFICATION_HINTS_ADD_ARGS [prio]}
@{parse_entries (sig) PARSE_TERM_INDEX_UNIFICATION_HINTS_CONFIG_ARGS
  [concl_unifier, normalisers, prems_unifier, retrieval, hint_preprocessor]}

signature TERM_INDEX_UNIFICATION_HINTS_ARGS =
sig
  structure PM : PARSE_TERM_INDEX_UNIFICATION_HINTS_MODE
  structure PAA : PARSE_TERM_INDEX_UNIFICATION_HINTS_ADD_ARGS
  structure PCA : PARSE_TERM_INDEX_UNIFICATION_HINTS_CONFIG_ARGS

  val UHA_PA_entries_from_PCA_entries : ('a, 'b, 'c, 'd, 'e) PCA.entries ->
    ('a, 'b, 'c) Unification_Hints_Args.PA.entries

  type hint_prio = Unification_Hints_Base.unif_hint * Prio.prio
  val pretty_hint_prio : Proof.context -> hint_prio -> Pretty.T
  val transfer_hint_prio : theory -> hint_prio -> hint_prio

  val retrieve_left : (Proof.context -> 'ti -> term -> hint_prio list) -> Proof.context ->
    'ti * 'ti -> term * term -> hint_prio list
  val retrieve_right : (Proof.context -> 'ti -> term -> hint_prio list) -> Proof.context ->
    'ti * 'ti -> term * term -> hint_prio list
  val retrieve_pair : (Proof.context -> 'ti -> term -> hint_prio list) -> Proof.context ->
    'ti * 'ti -> term * term -> hint_prio list
  val retrieve_sym : (Proof.context -> 'ti -> term * term -> hint_prio list) -> Proof.context ->
    'ti -> term * term -> hint_prio list
  val retrieve_transfer : (Proof.context -> 'ti -> 't -> hint_prio list) ->
    Proof.context -> 'ti -> 't -> hint_prio list

  val sort_hint_prios : hint_prio list -> hint_prio list
  val sorted_hint_seq_of_hint_prios : hint_prio list -> thm Seq.seq

  val mk_retrieval : (Proof.context -> 'ti -> term * term -> hint_prio list) ->
    (term * term -> term * term) -> 'ti -> Unification_Hints_Base.hint_retrieval
  val mk_retrieval_left : (Proof.context -> 'ti -> term -> hint_prio list) ->
    Term_Normalisation.term_normaliser -> 'ti * 'ti -> Unification_Hints_Base.hint_retrieval
  val mk_retrieval_right : (Proof.context -> 'ti -> term -> hint_prio list) ->
    Term_Normalisation.term_normaliser -> 'ti * 'ti -> Unification_Hints_Base.hint_retrieval
  val mk_retrieval_pair : (Proof.context -> 'ti -> term -> hint_prio list) ->
    Term_Normalisation.term_normaliser -> 'ti * 'ti -> Unification_Hints_Base.hint_retrieval
  val mk_retrieval_sym : (Proof.context -> 'ti -> term * term -> hint_prio list) ->
    Term_Normalisation.term_normaliser -> 'ti -> Unification_Hints_Base.hint_retrieval
  val mk_retrieval_sym_pair : (Proof.context -> 'ti -> term -> hint_prio list) ->
    Term_Normalisation.term_normaliser -> 'ti * 'ti -> Unification_Hints_Base.hint_retrieval

  type 'ti config_args = (Unification_Base.unifier, Unification_Base.normalisers,
    Unification_Base.unifier, 'ti * 'ti -> Unification_Hints_Base.hint_retrieval,
    Unification_Hints_Base.hint_preprocessor) PCA.entries

  val add_arg_parsers : (Prio.prio context_parser) PAA.entries
  val config_arg_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser,
    ML_Code_Util.code parser, ML_Code_Util.code parser, ML_Code_Util.code parser) PCA.entries
end

structure Term_Index_Unification_Hints_Args : TERM_INDEX_UNIFICATION_HINTS_ARGS =
struct

structure UB = Unification_Base
structure EN = Envir_Normalisation
structure UHB = Unification_Hints_Base
structure UHA = Unification_Hints_Args
structure TUHP = Prio

@{parse_entries (struct) PM [add, del, config]}
@{parse_entries (struct) PAA [prio]}
@{parse_entries (struct) PCA
  [concl_unifier, normalisers, prems_unifier, retrieval, hint_preprocessor]}

fun UHA_PA_entries_from_PCA_entries {concl_unifier = concl_unifier, normalisers = normalisers,
  prems_unifier = prems_unifier,...} =
  {concl_unifier = concl_unifier, normalisers = normalisers, prems_unifier = prems_unifier}

type hint_prio = UHB.unif_hint * TUHP.prio

fun pretty_hint_prio ctxt (hint, prio) = Pretty.block [
    UHB.pretty_hint ctxt hint,
    Pretty.enclose " (" ")" [Pretty.str "priority: ", Prio.pretty prio]
  ]
fun transfer_hint_prio thy = apfst (Thm.transfer thy)

fun retrieve_left retrieve ctxt (ti,_) (t, _) = retrieve ctxt ti t
fun retrieve_right retrieve ctxt (_, ti) (_, t) = retrieve ctxt ti t

fun retrieve_pair retrieve ctxt (ti_lhs, ti_rhs) (tlhs, trhs) =
  retrieve ctxt ti_lhs tlhs @ retrieve ctxt ti_rhs trhs

fun interleave [] ys = ys
  | interleave xs [] = xs
  | interleave (x :: xs) (y :: ys) = x :: y :: interleave xs ys

fun retrieve_sym retrieve ctxt ti tp = interleave
  (retrieve ctxt ti tp)
  (retrieve ctxt ti (swap tp) |> map (apfst Unification_Hints_Base.symmetric_hint))

fun retrieve_transfer retrieve ctxt = map (transfer_hint_prio (Proof_Context.theory_of ctxt)) oo
  retrieve ctxt

(*FIXME: use priority queue instead of sorted lists?*)
val sort_hint_prios = sort (rev_order o Prio.ord o apply2 snd)

val sorted_hint_seq_of_hint_prios = sort_hint_prios #> Seq.of_list #> Seq.map fst

fun mk_retrieval retrieve norm_terms ti _ ctxt tp _ =
  retrieve ctxt ti (norm_terms tp) |> sorted_hint_seq_of_hint_prios

fun mk_retrieval_left retrieve = mk_retrieval (retrieve_left retrieve) o apfst
fun mk_retrieval_right retrieve = mk_retrieval (retrieve_right retrieve) o apsnd
fun mk_retrieval_pair retrieve = mk_retrieval (retrieve_pair retrieve) o apply2
fun mk_retrieval_sym retrieve = mk_retrieval (retrieve_sym retrieve) o apply2
fun mk_retrieval_sym_pair retrieve = mk_retrieval (retrieve_sym (retrieve_pair retrieve)) o apply2

type 'ti config_args = (UB.unifier, UB.normalisers, UB.unifier, 'ti * 'ti -> UHB.hint_retrieval,
  UHB.hint_preprocessor) PCA.entries

val add_arg_parsers = {
    prio = SOME Prio.parse
  }

val config_arg_parsers = {
    concl_unifier = UHA.PA.get_concl_unifier_safe UHA.arg_parsers,
    normalisers = UHA.PA.get_normalisers_safe UHA.arg_parsers,
    prems_unifier = UHA.PA.get_prems_unifier_safe UHA.arg_parsers,
    retrieval = SOME (Parse_Util.nonempty_code (K "retrieval function must not be empty")),
    hint_preprocessor = SOME (Parse_Util.nonempty_code (K "hint preprocessor must not be empty"))
  }

end

signature TERM_INDEX_UNIFICATION_HINTS =
sig
  include HAS_LOGGER
  structure FI : FUNCTOR_INSTANCE

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

  val parse_add_arg_entries : Prio.prio Term_Index_Unification_Hints_Args.PAA.entries context_parser
  val add_attribute : Prio.prio Term_Index_Unification_Hints_Args.PAA.entries -> attribute

  val del_attribute : attribute

  val parse_config_arg_entries : (ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code,
    ML_Code_Util.code, ML_Code_Util.code) Term_Index_Unification_Hints_Args.PCA.entries parser
  val config_attribute : (ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code,
      ML_Code_Util.code, ML_Code_Util.code) Term_Index_Unification_Hints_Args.PCA.entries
      * Position.T ->
    attribute

  val parse_attribute : attribute context_parser
  val setup_attribute : string option -> local_theory -> local_theory
end

functor Term_Index_Unification_Hints(A :
  sig
    structure FI : FUNCTOR_INSTANCE_BASE
    structure TI : TERM_INDEX
    val init_args : (Term_Index_Unification_Hints_Args.hint_prio TI.term_index)
      Term_Index_Unification_Hints_Args.config_args
  end) : TERM_INDEX_UNIFICATION_HINTS =
struct

structure UHB = Unification_Hints_Base
structure TUHA = Term_Index_Unification_Hints_Args
structure TUHP = Prio
structure PAA = TUHA.PAA
structure PCA = TUHA.PCA
structure PM = TUHA.PM
structure AU = ML_Attribute_Util

structure FI = Functor_Instance(A.FI)
structure TI = A.TI

structure MCU = ML_Code_Util
structure PU = Parse_Util

val logger = Logger.setup_new_logger Unification_Hints_Base.logger FI.name

\<^functor_instance>\<open>struct_name: UH
  functor_name: Unification_Hints_Functor
  path: FI.long_name
  id: FI.id
  more_args: \<open>val init_args = TUHA.UHA_PA_entries_from_PCA_entries A.init_args\<close>\<close>

val are_hint_variants = apply2 Thm.prop_of #> Term_Util.are_term_variants

val term_index_data_eq = are_hint_variants o apply2 fst

type term_index = TUHA.hint_prio TI.term_index

structure Data = Generic_Data(Pair_Generic_Data_Args(
  structure Data1 = Pair_Generic_Data_Args(
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
    end)
  structure Data2 = Pair_Generic_Data_Args(
    structure Data1 = Term_Index_Generic_Data_Args(
      type data = TUHA.hint_prio
      structure TI = TI
      val data_eq = term_index_data_eq)
    structure Data2 = Term_Index_Generic_Data_Args(
      type data = TUHA.hint_prio
      structure TI = TI
      val data_eq = term_index_data_eq))))

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

val pretty_spaced_block = Pretty.breaks #> Pretty.block #> Pretty.string_of

fun msg_illegal_hint_format ctxt hint = pretty_spaced_block [
    Pretty.str "Illegal hint format for",
    UHB.pretty_hint ctxt hint
  ]

fun preprocess_hint context = get_hint_preprocessor context (Context.proof_of context)

local fun add_hint_prio index_description get_index map_index key (hint, prio) context =
  let
    val ctxt = Context.proof_of context
    val is_hint_variant = curry are_hint_variants hint o fst
  in
    (@{log Logger.DEBUG} ctxt (fn _ => pretty_spaced_block [
        Pretty.str "Adding hint",
        UHB.pretty_hint ctxt hint,
        Pretty.str "to",
        index_description
      ]);
    TI.insert is_hint_variant (key, (Thm.trim_context hint, prio)) (get_index context)
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
in
val add_hint_prio_lhs = add_hint_prio pretty_lhs_index_description get_lhs_index map_lhs_index
val add_hint_prio_rhs = add_hint_prio pretty_rhs_index_description get_rhs_index map_rhs_index
end

fun add_hint_prio (hint, prio) context =
  let
    val hint = preprocess_hint context hint
    val (lhs_key, rhs_key) = term_index_keys_from_hint hint
  in
    add_hint_prio_lhs lhs_key (hint, prio) context
    |> add_hint_prio_rhs rhs_key (hint, prio)
  end

local fun del_hint index_description get_index map_index key hint context =
  let
    val ctxt = Context.proof_of context
    val is_hint_variant = curry are_hint_variants hint o fst
  in
    (@{log Logger.DEBUG} ctxt (fn _ => pretty_spaced_block [
        Pretty.str "Deleting hint",
        UHB.pretty_hint ctxt hint,
        Pretty.str "from",
        index_description
      ]);
    TI.delete is_hint_variant key (get_index context)
    |> (fn ti => map_index (K ti) context))
    handle Term_Index_Base.DELETE =>
      (@{log Logger.WARN} ctxt
        (fn _ => pretty_spaced_block [
          Pretty.str "Hint",
          UHB.pretty_hint ctxt hint,
          Pretty.str "not found in",
          index_description
        ]);
      context)
    | TERM _ => (@{log Logger.WARN} ctxt (fn _ => msg_illegal_hint_format ctxt hint);
      context)
  end
in
val del_hint_lhs = del_hint pretty_lhs_index_description get_lhs_index map_lhs_index
val del_hint_rhs = del_hint pretty_rhs_index_description get_rhs_index map_rhs_index
end

fun del_hint hint context =
  let
    val hint = preprocess_hint context hint
    val (lhs_key, rhs_key) = term_index_keys_from_hint hint
  in del_hint_lhs lhs_key hint context |> del_hint_rhs rhs_key hint end

val binding = Binding.make (FI.id, FI.pos)

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

val default_add_arg_entries = PAA.entries_from_entry_list [PAA.prio TUHP.MEDIUM]

val parse_add_arg_entries =
  let
    val parsers = TUHA.add_arg_parsers
    val parse_value = PAA.parse_entry (PAA.get_prio parsers)
    val parse_entry = Parse_Key_Value.parse_entry' (Scan.lift PAA.parse_key)
      (K (Scan.lift (Parse.$$$ ":"))) parse_value
  in PAA.parse_entries_required' Scan.repeat true [] parse_entry default_add_arg_entries end

fun add_attribute entries =
  let fun update thm = add_hint_prio (thm, PAA.get_prio entries)
  in Thm.declaration_attribute update end

val del_attribute = Thm.declaration_attribute del_hint

val parse_config_arg_entries =
  let
    val parsers = TUHA.config_arg_parsers
    val parse_value = PCA.parse_entry (PCA.get_concl_unifier parsers) (PCA.get_normalisers parsers)
      (PCA.get_prems_unifier parsers) (PCA.get_retrieval parsers) (PCA.get_hint_preprocessor parsers)
    val parse_entry = Parse_Key_Value.parse_entry PCA.parse_key (K (Parse.$$$ ":")) parse_value
    val default_entries = PCA.empty_entries ()
  in PCA.parse_entries_required Scan.repeat1 true [] parse_entry default_entries end

fun config_attribute (entries, pos) =
  let
    val UHA_PA_entries = TUHA.UHA_PA_entries_from_PCA_entries entries
    val run_code = ML_Attribute.run_map_context o rpair pos
    fun default_attr (context, _) = (SOME context, NONE)
    val map_retrieval = case PCA.get_retrieval_safe entries of
        SOME c => FI.code_struct_op "map_retrieval" @ MCU.atomic (MCU.read "K" @ MCU.atomic c)
          |> run_code
      | NONE => default_attr
    val map_hint_preprocessor = case PCA.get_hint_preprocessor_safe entries of
        SOME c => FI.code_struct_op "map_hint_preprocessor" @ MCU.atomic (MCU.read "K" @ MCU.atomic c)
          |> run_code
      | NONE => default_attr
  in
    AU.apply_attribute (UH.attribute (UHA_PA_entries, pos))
    #> AU.apply_attribute map_retrieval
    #> map_hint_preprocessor
  end

val parse_entries =
  let
    val parse_value = PM.parse_entry parse_add_arg_entries (Scan.succeed ())
      (Scan.lift parse_config_arg_entries)
    val parse_entry = Parse_Key_Value.parse_entry' (Scan.lift PM.parse_key)
      (K (Scan.lift (Scan.succeed ""))) parse_value
    val default_entries = PM.empty_entries ()
  in PM.parse_entries_required' Parse.and_list1' true [] parse_entry default_entries end

fun attribute (entries, pos) =
  let
    fun default_attr (context, thm) = (SOME context, SOME thm)
    val add_attr = PM.get_add_safe entries
      |> (fn SOME entries => add_attribute entries | NONE => default_attr)
    val del_attr = PM.get_del_safe entries
      |> (fn SOME _ => del_attribute | NONE => default_attr)
    val config_attr = PM.get_config_safe entries
      |> (fn SOME entries => config_attribute (entries, pos) | NONE => default_attr)
  in AU.apply_attribute config_attr #> AU.apply_attribute del_attr #> add_attr end

val parse_attribute = PU.position' parse_entries >> attribute
  || parse_add_arg_entries >> add_attribute

val setup_attribute = Attrib.local_setup binding (Parse.!!!! parse_attribute) o
  the_default ("configure unification hints data " ^ enclose "(" ")" FI.long_name)

end
