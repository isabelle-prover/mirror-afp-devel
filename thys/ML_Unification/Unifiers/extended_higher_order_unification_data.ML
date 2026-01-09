(*  Title:      ML_Unification/extended_higher_order_unification_data.ML
    Author:     Kevin Kappelmann
*)
@{parse_entries (sig) PARSE_EXTENDED_HIGHER_ORDER_UNIFICATION_DATA_ARGS
  [search_bound, results_bound, silence_bound_exceeded]}

signature EXTENDED_HIGHER_ORDER_UNIFICATION_DATA_ARGS =
sig
  structure PA : PARSE_EXTENDED_HIGHER_ORDER_UNIFICATION_DATA_ARGS
  type args = (int, int, bool) PA.entries

  val ho_unify : args -> Unification_Base.unifier

  val arg_parsers : (int parser, int parser, bool parser) PA.entries
end

structure Extended_Higher_Order_Unification_Data_Args : EXTENDED_HIGHER_ORDER_UNIFICATION_DATA_ARGS =
struct

@{parse_entries (struct) PA [search_bound, results_bound, silence_bound_exceeded]}

type args = (int, int, bool) PA.entries

fun ho_unify args binders ctxt tp env = Seq.make (fn _ =>
  let val ctxt = Tactic_Util.set_kernel_ho_unif_bound (PA.get_search_bound args) ctxt
    |> (PA.get_silence_bound_exceeded args ? Tactic_Util.silence_kernel_ho_bound_exceeded)
  in
    Higher_Order_Unification.unify binders ctxt tp env
    |> Seq.take (PA.get_results_bound args)
    |> Seq.pull
  end)

val arg_parsers = {
  search_bound = SOME Parse.int,
  results_bound = SOME Parse.int,
  silence_bound_exceeded = SOME Parse_Util.bool
}
end

signature EXTENDED_HIGHER_ORDER_UNIFICATION_DATA =
sig
  include HAS_LOGGER

  structure Data : GENERIC_DATA
  where type T = Extended_Higher_Order_Unification_Data_Args.args

  val get_args : Context.generic -> Data.T
  val map_args : (Data.T -> Data.T) -> Context.generic -> Context.generic
  val get_search_bound : Context.generic -> int
  val map_search_bound : (int -> int) -> Context.generic -> Context.generic
  val get_results_bound : Context.generic -> int
  val map_results_bound : (int -> int) -> Context.generic -> Context.generic
  val get_silence_bound_exceeded : Context.generic -> bool
  val map_silence_bound_exceeded : (bool -> bool) -> Context.generic -> Context.generic

  val ho_unify : Unification_Base.unifier

  val binding : Binding.binding
  val parse_arg_entries : Extended_Higher_Order_Unification_Data_Args.args parser
  val attribute : Extended_Higher_Order_Unification_Data_Args.args -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : string option -> local_theory -> local_theory
end

functor Extended_Higher_Order_Unification_Data(
    structure FI : FUNCTOR_INSTANCE_BASE
    val init_args : Extended_Higher_Order_Unification_Data_Args.args
    val parent_logger : Logger.logger_binding
  ) : EXTENDED_HIGHER_ORDER_UNIFICATION_DATA =
struct

val logger = Logger.setup_new_logger parent_logger "Extended_Higher_Order_Unification_Data"
structure FI = Functor_Instance(FI)

structure EHDA = Extended_Higher_Order_Unification_Data_Args
structure PA = EHDA.PA

structure Data = Generic_Data(
  type T = EHDA.args
  val empty = init_args
  val merge = fst)

val get_args = Data.get
val map_args = Data.map

val get_search_bound = PA.get_search_bound o get_args
val map_search_bound = map_args o PA.map_search_bound

val get_results_bound = PA.get_results_bound o get_args
val map_results_bound = map_args o PA.map_results_bound

val get_silence_bound_exceeded = PA.get_silence_bound_exceeded o get_args
val map_silence_bound_exceeded = map_args o PA.map_silence_bound_exceeded

fun ho_unify binders ctxt tp env = Seq.make (fn _ =>
  let
    val args = get_args (Context.Proof ctxt)
    val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Higher-order unifying with search bound ",
        SpecCheck_Show.int (PA.get_search_bound args),
        Pretty.str " and results bound ",
        SpecCheck_Show.int (PA.get_results_bound args)
      ] |> Pretty.string_of)
  in EHDA.ho_unify args binders ctxt tp env |> Seq.pull end)

val binding = Binding.make (FI.id, FI.pos)

val parse_arg_entries =
  let
    val parsers = EHDA.arg_parsers
    val parse_value = PA.parse_entry (PA.get_search_bound parsers) (PA.get_results_bound parsers)
      (PA.get_silence_bound_exceeded parsers)
    val parse_entry = Parse_Key_Value.parse_entry PA.parse_key (K (Parse.$$$ ":")) parse_value
  in PA.parse_entries_required Scan.repeat1 true [] parse_entry (PA.empty_entries ()) end

fun attribute entries = let val update = map_args (PA.merge_entries entries)
  in Thm.declaration_attribute (Library.K update) end

val parse_attribute = parse_arg_entries >> attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  the_default ("configure extended higher-order unification data " ^ enclose "(" ")" FI.long_name)

end

