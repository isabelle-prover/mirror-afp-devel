(*  Title:      Zippy/extended_blast_data.ML
    Author:     Kevin Kappelmann
*)
@{parse_entries (sig) PARSE_EXTENDED_BLAST_DATA_ARGS [depth, timeout]}

signature EXTENDED_BLAST_DATA_ARGS =
sig
  structure PA : PARSE_EXTENDED_BLAST_DATA_ARGS
  type args = (int, real) PA.entries

  val blast_tac : (int -> Time.time -> (thm * thm Seq.seq) option) -> args -> Proof.context ->
    int -> tactic

  val arg_parsers : (int parser, real parser) PA.entries
end

structure Extended_Blast_Data_Args : EXTENDED_BLAST_DATA_ARGS =
struct

@{parse_entries (struct) PA [depth, timeout]}

type args = (int, real) PA.entries

fun blast_tac f_timeout args ctxt i state =
  let val timeout = the_default 0.0 (PA.get_timeout_safe args)
  in
    Seq.make (fn _ => Blast.depth_tac ctxt (PA.get_depth args) i state |> Seq.pull)
    |> General_Util.seq_with_timeout false f_timeout (K (seconds timeout))
  end

val arg_parsers = {
  depth = SOME Parse.int,
  timeout = SOME Parse.real
}
end

signature EXTENDED_BLAST_DATA =
sig
  include HAS_LOGGER

  structure Data : GENERIC_DATA
  where type T = Extended_Blast_Data_Args.args

  val get_args : Context.generic -> Data.T
  val map_args : (Data.T -> Data.T) -> Context.generic -> Context.generic
  val get_depth : Context.generic -> int
  val map_depth : (int -> int) -> Context.generic -> Context.generic
  val get_timeout : Context.generic -> real
  val map_timeout : (real -> real) -> Context.generic -> Context.generic

  val blast_tac : Proof.context -> int -> tactic

  val binding : Binding.binding
  val parse_arg_entries : Extended_Blast_Data_Args.args parser
  val attribute : Extended_Blast_Data_Args.args -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : string option -> local_theory -> local_theory
end

functor Extended_Blast_Data(
    structure FI : FUNCTOR_INSTANCE_BASE
    val init_args : Extended_Blast_Data_Args.args
    val parent_logger : Logger.logger_binding
  ) : EXTENDED_BLAST_DATA =
struct

val logger = Logger.setup_new_logger parent_logger "Extended_Blast_Data"
structure FI = Functor_Instance(FI)

structure EBDA = Extended_Blast_Data_Args
structure PA = EBDA.PA

structure Data = Generic_Data(
  type T = EBDA.args
  val empty = init_args
  val merge = fst)

val get_args = Data.get
val map_args = Data.map

val get_depth = PA.get_depth o get_args
val map_depth = map_args o PA.map_depth

val get_timeout = PA.get_timeout o get_args
val map_timeout = map_args o PA.map_timeout

fun f_timeout ctxt i state n time = (@{log Logger.WARN} ctxt (fn _ => Pretty.breaks [
    Pretty.block [Pretty.str "blast timeout at pull number ", SpecCheck_Show.int n,
      Pretty.str " after ", Pretty.str (Time.print time), Pretty.str " seconds."],
    Pretty.block [Pretty.str "Called on subgoal ", SpecCheck_Show.term ctxt (Thm.prem_of state i)],
    Pretty.str "Consider removing blast for this proof, increase/disable the timeout, or check for looping rules in the classical reasoner."
  ] |> Pretty.block0 |> Pretty.string_of);
  NONE)

fun blast_tac ctxt i state = EBDA.blast_tac (f_timeout ctxt i state)
  (get_args (Context.Proof ctxt)) ctxt i state

val binding = Binding.make (FI.id, FI.pos)

val parse_arg_entries =
  let
    val parsers = EBDA.arg_parsers
    val parse_value = PA.parse_entry (PA.get_depth parsers) (PA.get_timeout parsers)
    val parse_entry = Parse_Key_Value.parse_entry PA.parse_key (K (Parse.$$$ ":")) parse_value
  in PA.parse_entries_required Scan.repeat1 true [] parse_entry (PA.empty_entries ()) end

fun attribute entries = let val update = map_args (PA.merge_entries entries)
  in Thm.declaration_attribute (Library.K update) end

val parse_attribute = parse_arg_entries >> attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  the_default ("configure extended blast data " ^ enclose "(" ")" FI.long_name)

end