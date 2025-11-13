(*  Title:      Zippy/zippy_instance_subst_data.ML
    Author:     Kevin Kappelmann
*)
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_SUBST_DATA_MODES [asm, concl]}

signature ZIPPY_INSTANCE_SUBST_DATA_ARGS =
sig
  structure PM : PARSE_ZIPPY_INSTANCE_SUBST_DATA_MODES
  type mode = PM.key
  val parse_mode : mode parser
end

structure Zippy_Instance_Subst_Data_Args : ZIPPY_INSTANCE_SUBST_DATA_ARGS =
struct
@{parse_entries (struct) PM [asm, concl]}
type mode = PM.key
val parse_mode = PM.parse_key
end

functor Zippy_Instance_Subst_Data(
    structure FI : FUNCTOR_INSTANCE_BASE
    structure Z : ZIPPY_INSTANCE_TACTIC
    structure TI : TERM_INDEX
    val init_args : (Z.Tac_AAM.mk_meta,
      int -> @{AllT_args} Z.Base_Data.PAction.action,
      Z.Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z.ZLPC.Z2.zipper) Z.emorph,
      @{AllT_args} Z.Result_Action.mk_copy_update_data,
      @{AllT_args} Z.PResults.presultsq,
      thm * (term * (thm,
        Z.Tac_AAM.mk_meta,
        int -> @{AllT_args} Z.Base_Data.PAction.action,
        (Z.Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z.ZLPC.Z2.zipper) Z.emorph) list,
        @{AllT_args} Z.Result_Action.mk_copy_update_data,
        @{AllT_args} Z.PResults.presultsq)
        Zippy_Instance_Hom_Changed_Goals_Data_Args.PD.entries) -> bool)
        Zippy_Instance_Hom_Changed_Goals_Data_Args.PDC.entries
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
  ) =
struct
local structure FI =  Functor_Instance(FI)
in
structure Logging =
struct
  local structure Base = struct val parent_logger = Log.logger end
  in
  structure Asm = Zippy_Logger_Mixin_Base(open Base; val name = "Subst_Asm")
  structure Concl = Zippy_Logger_Mixin_Base(open Base; val name = "Subst_Concl")
  end
end

local open Z; open ZLPC
  structure Base = struct structure Z = Z; structure TI = TI; val init_args = init_args end
in
\<^functor_instance>\<open>struct_name: Asm
  functor_name: Zippy_Instance_Hom_Changed_Goals_Data
  FI_struct_name: FI_Hom_Changed_Goals_Data
  id: \<open>FI.prefix_id "subst_asm"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.concl_of
    val num_new_goals = Thm.nprems_of #> General_Util.succ
    structure Log = Logging.Asm\<close>\<close>
structure Asm = Asm.Hom_Changed_Goals_Data
\<^functor_instance>\<open>struct_name: Concl
  functor_name: Zippy_Instance_Hom_Changed_Goals_Data
  FI_struct_name: FI_Hom_Changed_Goals_Data
  id: \<open>FI.prefix_id "subst_concl"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.concl_of
    val num_new_goals = Thm.nprems_of #> General_Util.succ
    structure Log = Logging.Concl\<close>\<close>
structure Concl = Concl.Hom_Changed_Goals_Data

local
  open Zippy_Instance_Subst_Data_Args
  structure PMD = Zippy_Instance_Hom_Changed_Goals_Data_Args.PM
  val parse_mode_opt_default = Scan.optional (Args.parens (Parse.!!! PM.parse_key)) (PM.key PM.concl)
  fun gen_parse_attribute asm concl = parse_mode_opt_default
    :|-- (fn PM.asm _ => asm | PM.concl _ => concl)
  fun gen_setup_attribute binding what parse_attribute = Attrib.local_setup binding
    (Parse.!!! parse_attribute |> Scan.lift) o
    the_default ("configure " ^ what ^ " data " ^ enclose "(" ")" FI.long_name)
  fun gen_parse_method asm concl =
    let val parse = Scan.lift parse_mode_opt_default :|-- (fn PM.asm _ => asm | PM.concl _ => concl)
    in Parse.and_list1' parse >> K () end
in
val parse_attribute = gen_parse_attribute Asm.parse_attribute Concl.parse_attribute

val binding = Binding.make (FI.prefix_id "subst", FI.pos)
val setup_attribute = gen_setup_attribute binding "subst" parse_attribute

val parse_method = gen_parse_method Asm.parse_entry_context_update Concl.parse_entry_context_update
end
end
end
end
