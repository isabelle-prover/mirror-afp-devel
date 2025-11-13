(*  Title:      Zippy/extended_simp_data.ML
    Author:     Kevin Kappelmann
*)
@{parse_entries (sig) PARSE_EXTENDED_SIMP_DATA_ARGS [depth, timeout]}

signature EXTENDED_SIMP_DATA_ARGS =
sig
  structure PA : PARSE_EXTENDED_SIMP_DATA_ARGS
  type args = (int, real) PA.entries

  val wrap_simp_tac : (int -> Time.time -> (thm * thm Seq.seq) option) ->
    (Proof.context -> int -> tactic) -> args -> Proof.context -> int -> tactic

  val arg_parsers : (int parser, real parser) PA.entries
end

structure Extended_Simp_Data_Args : EXTENDED_SIMP_DATA_ARGS =
struct

@{parse_entries (struct) PA [depth, timeout]}

type args = (int, real) PA.entries

fun wrap_simp_tac f_timeout tac args ctxt i state =
  let
    val timeout = the_default 0.0 (PA.get_timeout_safe args)
    val ctxt = PA.get_depth_safe args
      |> Option.map (fn depth => Config.put Raw_Simplifier.simp_depth_limit depth ctxt)
      |> the_default ctxt
  in
    Seq.make (fn _ => tac ctxt i state |> Seq.pull)
    |> General_Util.seq_with_timeout false f_timeout (K (seconds timeout))
  end

val arg_parsers = {
  depth = SOME Parse.int,
  timeout = SOME Parse.real
}
end

signature EXTENDED_SIMP_DATA =
sig
  include HAS_LOGGER

  structure Data : GENERIC_DATA
  where type T = Extended_Simp_Data_Args.args

  val get_args : Context.generic -> Data.T
  val map_args : (Data.T -> Data.T) -> Context.generic -> Context.generic
  val get_depth : Context.generic -> int
  val map_depth : (int -> int) -> Context.generic -> Context.generic
  val get_timeout : Context.generic -> real
  val map_timeout : (real -> real) -> Context.generic -> Context.generic

  val wrap_simp_tac : (int -> Time.time -> (thm * thm Seq.seq) option) ->
    (Proof.context -> int -> tactic) -> Proof.context -> int -> tactic

  val binding : Binding.binding
  val parse_arg_entries : Extended_Simp_Data_Args.args parser
  val attribute : Extended_Simp_Data_Args.args -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : (string, string) Either.either -> local_theory -> local_theory
end

functor Extended_Simp_Data(
    structure FI : FUNCTOR_INSTANCE_BASE
    val init_args : Extended_Simp_Data_Args.args
    val parent_logger : Logger.logger_binding
  ) : EXTENDED_SIMP_DATA =
struct

val logger = Logger.setup_new_logger parent_logger "Extended_Simp_Data"
structure FI = Functor_Instance(FI)

structure ESDA = Extended_Simp_Data_Args
structure PA = ESDA.PA

structure Data = Generic_Data(
  type T = ESDA.args
  val empty = init_args
  val merge = fst)

val get_args = Data.get
val map_args = Data.map

val get_depth = PA.get_depth o get_args
val map_depth = map_args o PA.map_depth

val get_timeout = PA.get_timeout o get_args
val map_timeout = map_args o PA.map_timeout

fun wrap_simp_tac f_timeout tac ctxt = ESDA.wrap_simp_tac f_timeout tac
  (get_args (Context.Proof ctxt)) ctxt

val binding = Binding.make (FI.id, FI.pos)

val parse_arg_entries =
  let
    val parsers = ESDA.arg_parsers
    val parse_value = PA.parse_entry (PA.get_depth parsers) (PA.get_timeout parsers)
    val parse_entry = Parse_Key_Value.parse_entry PA.parse_key (K (Parse.$$$ ":")) parse_value
  in PA.parse_entries_required Scan.repeat1 true [] parse_entry (PA.empty_entries ()) end

fun attribute entries = let val update = map_args (PA.merge_entries entries)
  in Thm.declaration_attribute (Library.K update) end

val parse_attribute = parse_arg_entries >> attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  (Either.cases I (fn what => "configure " ^ what ^ " data " ^ enclose "(" ")" FI.long_name))
end