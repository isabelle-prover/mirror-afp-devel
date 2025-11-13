(*  Title:      Zippy/zippy_run_data.ML
    Author:     Kevin Kappelmann
*)
@{parse_entries (sig) PARSE_ZIPPY_RUN_DATA_ARGS [init, exec, post]}

signature ZIPPY_RUN_DATA_ARGS =
sig
  structure PA : PARSE_ZIPPY_RUN_DATA_ARGS
  val parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser, ML_Code_Util.code parser)
    PA.entries
end

structure Zippy_Run_Data_Args : ZIPPY_RUN_DATA_ARGS =
struct
structure MCU = ML_Code_Util

@{parse_entries (struct) PA [init, exec, post]}

val parsers = {
  init = SOME MCU.parse_code,
  exec = SOME MCU.parse_code,
  post = SOME MCU.parse_code}
end

signature ZIPPY_RUN_DATA =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  type container1
  type exec_config
  type data = ((@{ParaT_args} Zippy_Thm_State.state, container1) morph,
    exec_config -> (@{ParaT_args} container1, Zippy_Thm_State.state Seq.seq) morph,
    Zippy_Thm_State.state -> (@{ParaT_args} Zippy_Thm_State.state Seq.seq) emorph)
    Zippy_Run_Data_Args.PA.entries

  structure Data : GENERIC_DATA
  where type T = data

  val get_data : Context.generic -> Data.T
  val map_data : (Data.T -> Data.T) -> Context.generic -> Context.generic
  val get_init : Context.generic ->
    (@{ParaT_args} Zippy_Thm_State.state, container1) morph
  val map_init : ((@{ParaT_args} Zippy_Thm_State.state, container1) morph ->
      (@{ParaT_args} Zippy_Thm_State.state, container1) morph) ->
    Context.generic -> Context.generic
  val get_exec : Context.generic -> exec_config -> (@{ParaT_args} container1,
      Zippy_Thm_State.state Seq.seq) morph
  val map_exec : ((exec_config -> (@{ParaT_args} container1,
      Zippy_Thm_State.state Seq.seq) morph) -> exec_config ->
      (@{ParaT_args} container1, Zippy_Thm_State.state Seq.seq) morph) ->
    Context.generic -> Context.generic
  val get_post : Context.generic -> Zippy_Thm_State.state ->
    (@{ParaT_args} Zippy_Thm_State.state Seq.seq) emorph
  val map_post : ((Zippy_Thm_State.state -> (@{ParaT_args} Zippy_Thm_State.state Seq.seq) emorph) ->
      Zippy_Thm_State.state -> (@{ParaT_args} Zippy_Thm_State.state Seq.seq) emorph) ->
    Context.generic -> Context.generic

  val exec : exec_config -> (@{ParaT_args} Zippy_Thm_State.state, Zippy_Thm_State.state Seq.seq) morph
  type state
  val tac : exec_config -> state -> tactic

  val binding : Binding.binding
  val parse_arg_entries : (ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code)
    Zippy_Run_Data_Args.PA.entries parser
  val attribute : (ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code)
    Zippy_Run_Data_Args.PA.entries * Position.T -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : string option -> local_theory -> local_theory
  val parse_context_update : unit context_parser
end

functor Zippy_Run_Data(
    structure FI : FUNCTOR_INSTANCE_BASE
    structure Z : ZIPPY_BASE_BASE
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
    structure Seq_From_Monad : ZIPPY_SEQ_FROM_MONAD_MIXIN_BASE
    sharing type Seq_From_Monad.M.t = Z.M.t
    type exec_config
    val init_args : (
      (@{ParaT_args} Zippy_Thm_State.state, @{AllT_args} Z.Z1.ZM.container) Z.morph,
      exec_config -> (@{ParaT_args} @{AllT_args} Z.Z1.ZM.container,
        Zippy_Thm_State.state Seq.seq) Z.morph,
      Zippy_Thm_State.state -> (@{ParaT_args} Zippy_Thm_State.state Seq.seq) Z.emorph)
      Zippy_Run_Data_Args.PA.entries
  ) : ZIPPY_RUN_DATA =
struct
open Z

structure FI = Functor_Instance(FI)
structure ZRDA = Zippy_Run_Data_Args
structure PA = ZRDA.PA
structure MCU = ML_Code_Util

type container1 = @{AllT_args} Z.Z1.ZM.container
type exec_config = exec_config
type data = ((@{ParaT_args} Zippy_Thm_State.state, container1) morph,
  exec_config -> (@{ParaT_args} container1, Zippy_Thm_State.state Seq.seq) morph,
  Zippy_Thm_State.state -> (@{ParaT_args} Zippy_Thm_State.state Seq.seq) emorph)
  Zippy_Run_Data_Args.PA.entries

structure Data = Generic_Data(
  type T = data
  val empty = init_args
  val merge = fst)

val get_data = Data.get
val map_data = Data.map

val get_init = PA.get_init o get_data
val map_init = map_data o PA.map_init

val get_exec = PA.get_exec o get_data
val map_exec = map_data o PA.map_exec

val get_post = PA.get_post o get_data
val map_post = map_data o PA.map_post

local structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(M); open M
in
fun exec exec_config st = Ctxt.with_context get_init st
  >>= Ctxt.with_context (fn context => get_exec context exec_config)
  >>= Ctxt.with_context (fn context => get_post context st)
end
type state = @{AllT_args} Seq_From_Monad.state
fun tac exec_config s = exec exec_config #> Seq_From_Monad.seq_from_monad s

val binding = Binding.make (FI.id, FI.pos)

val parse_arg_entries =
  let
    val parsers = ZRDA.parsers
    val parse_value = PA.parse_entry (PA.get_init parsers) (PA.get_exec parsers) (PA.get_post parsers)
    val parse_entry = Parse_Key_Value.parse_entry PA.parse_key (K (Parse.$$$ ":")) parse_value
  in PA.parse_entries_required Scan.repeat1 true [] parse_entry (PA.empty_entries ()) end

fun attribute (entries, pos) =
  let
    fun struct_op operation = FI.struct_op operation |> MCU.read
    fun code_PA_op operation = MCU.read ("Zippy_Run_Data_Args.PA." ^ operation)
    val code_from_key = code_PA_op o PA.key_to_string
    fun code_from_entry (PA.init c) = c
      | code_from_entry (PA.exec c) = c
      | code_from_entry (PA.post c) = c
    val code_entries = PA.key_entry_entries_from_entries entries
      |> List.map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code =
      struct_op "map_data" @ MCU.atomic (code_PA_op "merge_entries" @
      MCU.atomic (code_PA_op "entries_from_entry_list" @ code_entries))
  in ML_Attribute.run_map_context (code, pos) end

val parse_attribute = Parse_Util.position parse_arg_entries >> attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  the_default ("configure exec data " ^ enclose "(" ")" FI.long_name)

val parse_context_update = Scan.lift parse_attribute
  :|-- (fn attr => Scan.depend (fn context =>
    Scan.succeed (ML_Attribute_Util.attribute_map_context attr context, ())))
end
