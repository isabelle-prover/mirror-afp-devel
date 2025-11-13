(*  Title:      Zippy/extended_metis_data.ML
    Author:     Kevin Kappelmann
*)
@{parse_entries (sig) PARSE_EXTENDED_METIS_DATA_ARGS [runs, timeout]}

signature EXTENDED_METIS_DATA_ARGS =
sig
  structure PA : PARSE_EXTENDED_METIS_DATA_ARGS
  type run = (string list option * string option) * thm list
  val pretty_run : Proof.context -> run -> Pretty.T
  type runs = run list
  type args = (runs, real) PA.entries

  val metis_tac : (int -> Time.time -> (thm * thm Seq.seq) option) -> args -> Proof.context ->
    int -> tactic

  val parse_run : run context_parser
  val arg_parsers : (runs context_parser, real parser) PA.entries
end

structure Extended_Metis_Data_Args : EXTENDED_METIS_DATA_ARGS =
struct
structure Show = SpecCheck_Show

@{parse_entries (struct) PA [runs, timeout]}

type run = (string list option * string option) * thm list
fun pretty_run ctxt = Show.zip
  (Show.zip (Show.option (Show.list Show.string)) (Show.option Show.string))
  (Show.list (Show.thm ctxt))
type runs = run list
type args = (runs, real) PA.entries

fun metis_tac f_timeout args ctxt i state =
  let
    val timeout = the_default 0.0 (PA.get_timeout_safe args)
    fun mk_tac config = Metis_Tactic.metis_method config ctxt []
  in
    Seq.make (fn _ =>
      SELECT_GOAL (PARALLEL_CHOICE (List.map mk_tac (PA.get_runs args))) i state |> Seq.pull)
    |> General_Util.seq_with_timeout false f_timeout (K (seconds timeout))
  end

val parse_run = Scan.lift Metis_Tactic.parse_metis_options -- Parse_Util.thms

val arg_parsers = {
  runs = SOME (Parse.and_list1' parse_run),
  timeout = SOME Parse.real
}
end

signature EXTENDED_METIS_DATA =
sig
  include HAS_LOGGER

  structure Data : GENERIC_DATA
  where type T = Extended_Metis_Data_Args.args

  val get_args : Context.generic -> Data.T
  val map_args : (Data.T -> Data.T) -> Context.generic -> Context.generic
  val get_runs : Context.generic -> Extended_Metis_Data_Args.runs
  val map_runs : (Extended_Metis_Data_Args.runs -> Extended_Metis_Data_Args.runs) ->
    Context.generic -> Context.generic
  val get_timeout : Context.generic -> real
  val map_timeout : (real -> real) -> Context.generic -> Context.generic

  val metis_tac : Proof.context -> int -> tactic

  val binding : Binding.binding
  val parse_arg_entries : Extended_Metis_Data_Args.args context_parser
  val attribute : Extended_Metis_Data_Args.args -> attribute
  val parse_attribute : attribute context_parser
  val setup_attribute : string option -> local_theory -> local_theory
end

functor Extended_Metis_Data(
    structure FI : FUNCTOR_INSTANCE_BASE
    val init_args : Extended_Metis_Data_Args.args
    val parent_logger : Logger.logger_binding
  ) : EXTENDED_METIS_DATA =
struct

val logger = Logger.setup_new_logger parent_logger "Extended_Metis_Data"
structure FI = Functor_Instance(FI)

structure EBDA = Extended_Metis_Data_Args
structure PA = EBDA.PA
structure Show = SpecCheck_Show

structure Data = Generic_Data(
  type T = EBDA.args
  val empty = init_args
  val merge = fst)

val get_args = Data.get
val map_args = Data.map

val get_runs = PA.get_runs o get_args
val map_runs = map_args o PA.map_runs

val get_timeout = PA.get_timeout o get_args
val map_timeout = map_args o PA.map_timeout

fun f_timeout ctxt i state n time = (@{log Logger.WARN} ctxt (fn _ => Pretty.breaks [
    Pretty.block [Pretty.str "metis timeout at pull number ", Show.int n,
      Pretty.str " after ", Pretty.str (Time.print time), Pretty.str " seconds."],
    Pretty.block [Pretty.str "Called on subgoal ", Show.term ctxt (Thm.prem_of state i)],
    Pretty.str "Consider removing metis for this proof or increase/disable the timeout."
  ] |> Pretty.block0 |> Pretty.string_of);
  NONE)

fun metis_tac ctxt i state = EBDA.metis_tac (f_timeout ctxt i state)
  (get_args (Context.Proof ctxt)) ctxt i state

val binding = Binding.make (FI.id, FI.pos)

val parse_arg_entries =
  let
    val parsers = EBDA.arg_parsers
    val parse_value = PA.parse_entry (PA.get_runs parsers) (Scan.lift (PA.get_timeout parsers))
    val parse_entry = Parse_Key_Value.parse_entry' (Scan.lift PA.parse_key)
      (K (Scan.lift (Parse.$$$ ":"))) parse_value
  in PA.parse_entries_required' Scan.repeat1 true [] parse_entry (PA.empty_entries ()) end

fun attribute entries = let val update = map_args (PA.merge_entries entries)
  in Thm.declaration_attribute (Library.K update) end

val parse_attribute = parse_arg_entries >> attribute
  || PA.get_runs EBDA.arg_parsers >> (fn runs => Thm.declaration_attribute (K (map_runs (K runs))))

val setup_attribute = Attrib.local_setup binding (Parse.!!!! parse_attribute) o
  the_default ("configure extended metis data " ^ enclose "(" ")" FI.long_name)

end