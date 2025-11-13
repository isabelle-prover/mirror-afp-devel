(*  Title:      Zippy/zippy_instance_uresolves_data.ML
    Author:     Kevin Kappelmann
*)
functor Zippy_Instance_UResolves_Data(
    structure FI : FUNCTOR_INSTANCE_BASE
    structure Z : ZIPPY_INSTANCE_TACTIC
    structure TI : TERM_INDEX
    val init_args : (Unification_Base.normalisers,
      Unification_Base.unifier,
      Z.Tac_AAM.mk_meta,
      int -> @{AllT_args} Z.Base_Data.PAction.action,
      Z.Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z.ZLPC.Z2.zipper) Z.emorph,
      @{AllT_args} Z.Result_Action.mk_copy_update_data,
      @{AllT_args} Z.PResults.presultsq,
      thm * (term * (thm,
        Unification_Base.normalisers,
        Unification_Base.unifier,
        Z.Tac_AAM.mk_meta,
        int -> @{AllT_args} Z.Base_Data.PAction.action,
        (Z.Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z.ZLPC.Z2.zipper) Z.emorph) list,
        @{AllT_args} Z.Result_Action.mk_copy_update_data,
        @{AllT_args} Z.PResults.presultsq)
        Zippy_Instance_UResolve_Data_Args.PD.entries) -> bool)
        Zippy_Instance_UResolve_Data_Args.PDC.entries
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
  ) =
struct
local structure FI =  Functor_Instance(FI)
in
structure Logging =
struct
  local structure Base = struct val parent_logger = Log.logger end
  in
  structure Resolve = Zippy_Logger_Mixin_Base(open Base; val name = "Resolve")
  structure EResolve = Zippy_Logger_Mixin_Base(open Base; val name = "EResolve")
  structure DResolve = Zippy_Logger_Mixin_Base(open Base; val name = "DResolve")
  structure FResolve = Zippy_Logger_Mixin_Base(open Base; val name = "FResolve")
  end
end

local open Z; open ZLPC
  structure Base = struct structure Z = Z; structure TI = TI; val init_args = init_args end
in
\<^functor_instance>\<open>struct_name: Resolve
  functor_name: Zippy_Instance_UResolve_Data
  FI_struct_name: FI_UResolve_Data
  id: \<open>FI.prefix_id "resolve"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.concl_of
    val num_new_goals = Thm.nprems_of
    structure Log = Logging.Resolve\<close>\<close>
structure Resolve = Resolve.UResolve_Data

\<^functor_instance>\<open>struct_name: EResolve
  functor_name: Zippy_Instance_UResolve_Data
  FI_struct_name: FI_UResolve_Data
  id: \<open>FI.prefix_id "eresolve"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of #> General_Util.pred
    structure Log = Logging.EResolve\<close>\<close>
structure EResolve = EResolve.UResolve_Data

\<^functor_instance>\<open>struct_name: DResolve
  functor_name: Zippy_Instance_UResolve_Data
  FI_struct_name: FI_UResolve_Data
  id: \<open>FI.prefix_id "dresolve"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of
    structure Log = Logging.DResolve\<close>\<close>
structure DResolve = DResolve.UResolve_Data

\<^functor_instance>\<open>struct_name: FResolve
  functor_name: Zippy_Instance_UResolve_Data
  FI_struct_name: FI_UResolve_Data
  id: \<open>FI.prefix_id "fresolve"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of
    structure Log = Logging.FResolve\<close>\<close>
structure FResolve = FResolve.UResolve_Data

local open Zippy_Instance_Resolves_Data_Args
  val parse_mode_opt_default = Scan.optional (Args.parens (Parse.!!! PM.parse_key)) (PM.key PM.r)
in
val parse_attribute = parse_mode_opt_default
  :|-- (fn PM.r _ => Resolve.parse_attribute | PM.e _ => EResolve.parse_attribute
    | PM.d _ => DResolve.parse_attribute | PM.f _ => FResolve.parse_attribute)

val binding = Binding.make (FI.id, FI.pos)

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  Either.cases I (fn what => "configure " ^ what ^ " data " ^ enclose "(" ")" FI.long_name)

val parse_method =
  let val parse = Scan.lift parse_mode_opt_default
    :|-- (fn PM.r _ => Resolve.parse_entry_context_update | PM.e _ => EResolve.parse_entry_context_update
      | PM.d _ => DResolve.parse_entry_context_update | PM.f _ => FResolve.parse_entry_context_update)
  in Parse.and_list1' parse >> K () end
end
end
end
end
