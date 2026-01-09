(*  Title:      Zippy/zippy_instance_induction_data.ML
    Author:     Kevin Kappelmann
*)
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_INDUCTION_DATA_MODE [add, del, config]}
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_INDUCTION_DATA
  [insts, rule, arbitrary, taking, simp, facts, match, mk_meta, empty_action, updates, mk_cud,
  presultsq]}
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_INDUCTION_DATA_ADD_ARGS
  [insts, rule, arbitrary, taking, simp, facts, match, mk_meta, empty_action, default_update,
  updates, mk_cud, presultsq]}
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_INDUCTION_DATA_DEL_ARGS
  [insts, rule, arbitrary, taking, simp, facts]}
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_INDUCTION_DATA_CONFIG
  [simp, match, mk_meta, empty_action, default_update, mk_cud, presultsq]}

signature ZIPPY_INSTANCE_INDUCTION_DATA_ARGS =
sig
  structure PM : PARSE_ZIPPY_INSTANCE_INDUCTION_DATA_MODE
  structure PD : PARSE_ZIPPY_INSTANCE_INDUCTION_DATA
  structure PAA : PARSE_ZIPPY_INSTANCE_INDUCTION_DATA_ADD_ARGS
  structure PDA : PARSE_ZIPPY_INSTANCE_INDUCTION_DATA_DEL_ARGS
  structure PDC : PARSE_ZIPPY_INSTANCE_INDUCTION_DATA_CONFIG

  val PD_entries_from_PAA_entries : ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm) PAA.entries ->
    ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'k, 'l, 'm) PD.entries
  val PDA_entries_from_PAA_entries : ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm) PAA.entries ->
    ('a, 'b, 'c, 'd, 'e, 'f) PDA.entries
  val PDC_entries_from_PAA_entries : ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm) PAA.entries ->
    ('e, 'g, 'h, 'i, 'j, 'l, 'm) PDC.entries
  val induct_PD_entries_from_PD_entries : ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'l, 'm) PD.entries ->
    ('a, 'b, 'c, 'd, 'e, 'f, 'g) Induction_Data_Args.PD.entries

  val add_arg_parsers : (unit context_parser -> (Induction_Tactic_Base.def_inst option list,
      (term * term list) option list, ML_Code_Util.code option list)
      Cases_Data_Args.PIM.entry context_parser,
    thm context_parser,
    unit context_parser ->
      ((string * typ) list, term list * term list, ML_Code_Util.code)
        Cases_Data_Args.PIM.entry context_parser,
    unit context_parser -> Induction_Data_Args.taking context_parser,
    bool parser, thm list context_parser, ML_Code_Util.code parser,
    ML_Code_Util.code parser, ML_Code_Util.code parser, ML_Code_Util.code parser,
    (int * ML_Code_Util.code) list parser, ML_Code_Util.code parser,
    ML_Code_Util.code parser) PAA.entries
end

structure Zippy_Instance_Induction_Data_Args : ZIPPY_INSTANCE_INDUCTION_DATA_ARGS =
struct

structure IDA = Induction_Data_Args
structure HCGD = Zippy_Instance_Hom_Changed_Goals_Data_Args

@{parse_entries (struct) PM [add, del, config]}
@{parse_entries (struct) PD
  [insts, rule, arbitrary, taking, simp, facts, match, mk_meta, empty_action, updates, mk_cud, presultsq]}
@{parse_entries (struct) PAA
  [insts, rule, arbitrary, taking, simp, facts, match, mk_meta, empty_action, default_update, updates, mk_cud,
  presultsq]}
@{parse_entries (struct) PDA [insts, rule, arbitrary, taking, simp, facts]}
@{parse_entries (struct) PDC
  [simp, match, mk_meta, empty_action, default_update, mk_cud, presultsq]}

fun PD_entries_from_PAA_entries {insts, rule, arbitrary, taking, simp, facts, match, mk_meta,
  empty_action, updates, mk_cud, presultsq,...} =
  {insts = insts, rule = rule, arbitrary = arbitrary, taking = taking, simp = simp, facts = facts,
  match = match, mk_meta = mk_meta, empty_action = empty_action, updates = updates,
  mk_cud = mk_cud, presultsq = presultsq}
fun PDA_entries_from_PAA_entries {insts, rule, arbitrary, taking, simp, facts,...} =
  {insts = insts, rule = rule, arbitrary = arbitrary, taking = taking, simp = simp, facts = facts}
fun PDC_entries_from_PAA_entries {simp, match, mk_meta, empty_action, default_update, mk_cud,
  presultsq,...} = {simp = simp, match = match, mk_meta = mk_meta, empty_action = empty_action,
  default_update = default_update, mk_cud = mk_cud, presultsq = presultsq}
fun induct_PD_entries_from_PD_entries {insts, rule, arbitrary, taking, simp, facts, match,...} =
  {insts = insts, rule = rule, arbitrary = arbitrary, taking = taking, simp = simp, facts = facts,
  match = match}

val add_arg_parsers = {
  insts = SOME (IDA.PD.get_insts IDA.data_parsers),
  rule = SOME (IDA.PD.get_rule IDA.data_parsers),
  arbitrary = SOME (IDA.PD.get_arbitrary IDA.data_parsers),
  taking = SOME (IDA.PD.get_taking IDA.data_parsers),
  simp = SOME (IDA.PD.get_simp IDA.data_parsers),
  facts = SOME (IDA.PD.get_facts IDA.data_parsers),
  match = SOME (IDA.PD.get_match IDA.data_parsers),
  mk_meta = SOME (HCGD.PAA.get_mk_meta HCGD.add_arg_parsers),
  empty_action = SOME (HCGD.PAA.get_empty_action HCGD.add_arg_parsers),
  default_update = SOME (HCGD.PAA.get_default_update HCGD.add_arg_parsers),
  updates = SOME (HCGD.PAA.get_updates HCGD.add_arg_parsers),
  mk_cud = SOME (HCGD.PAA.get_mk_cud HCGD.add_arg_parsers),
  presultsq = SOME (HCGD.PAA.get_presultsq HCGD.add_arg_parsers)}

end

signature ZIPPY_INSTANCE_INDUCTION_DATA =
sig
  include ZIPPY_INSTANCE_TACTIC

  structure Induction_Data :
  sig
    structure Log : ZIPPY_LOGGER_MIXIN_BASE

    type config = (bool, Cases_Data_Args.match,
      Tac_AAM.mk_meta,
      int -> @{AllT_args} Base_Data.PAction.action,
      Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper) emorph,
      @{AllT_args} Result_Action.mk_copy_update_data,
      @{AllT_args} PResults.presultsq) Zippy_Instance_Induction_Data_Args.PDC.entries

    structure Config_Data : GENERIC_DATA
    where type T = config

    val get_config : Context.generic -> Config_Data.T
    val map_config : (Config_Data.T -> Config_Data.T) -> Context.generic -> Context.generic

    val get_simp : Context.generic -> bool
    val map_simp : (bool -> bool) -> Context.generic -> Context.generic

    val get_match : Context.generic -> Cases_Data_Args.match
    val map_match : (Cases_Data_Args.match -> Cases_Data_Args.match) ->
      Context.generic -> Context.generic

    val get_mk_meta : Context.generic -> Tac_AAM.mk_meta
    val map_mk_meta : (Tac_AAM.mk_meta -> Tac_AAM.mk_meta) ->
      Context.generic -> Context.generic

    val get_empty_action : Context.generic -> int -> @{AllT_args} Base_Data.PAction.action
    val map_empty_action : ((int -> @{AllT_args} Base_Data.PAction.action) ->
        int -> @{AllT_args} Base_Data.PAction.action) ->
      Context.generic -> Context.generic

    val get_default_update : Context.generic -> Base_Data.GCS.goal_pos ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper) emorph
    val map_default_update :
      ((Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper) emorph) ->
        Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper) emorph) ->
      Context.generic -> Context.generic

    val get_mk_cud : Context.generic -> @{AllT_args} Result_Action.mk_copy_update_data
    val map_mk_cud : (@{AllT_args} Result_Action.mk_copy_update_data ->
      @{AllT_args} Result_Action.mk_copy_update_data) -> Context.generic -> Context.generic

    val get_presultsq : Context.generic -> @{AllT_args} PResults.presultsq
    val map_presultsq : (@{AllT_args} PResults.presultsq ->
      @{AllT_args} PResults.presultsq) -> Context.generic -> Context.generic

    type data = (Induction_Data_Args.insts, thm option, Induction_Data_Args.arbitrary,
      Induction_Data_Args.taking, bool, thm list, Cases_Data_Args.match,
      Tac_AAM.mk_meta,
      int -> @{AllT_args} Base_Data.PAction.action,
      (Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper) emorph) list option,
      @{AllT_args} Result_Action.mk_copy_update_data,
      @{AllT_args} PResults.presultsq) Zippy_Instance_Induction_Data_Args.PD.entries

    val data_ord : data ord
    val eq_data : data * data -> bool
    val pretty_data : Proof.context -> data -> Pretty.T
    val map_data_thms : (thm -> thm) -> data -> data
    val transfer_data : theory -> data -> data

    structure Data : GENERIC_DATA
    where type T = data Ord_List.T

    type add_args = (Induction_Data_Args.insts, thm option, Induction_Data_Args.arbitrary,
      Induction_Data_Args.taking, bool, thm list, Cases_Data_Args.match,
      Tac_AAM.mk_meta,
      int -> @{AllT_args} Base_Data.PAction.action,
      Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper) emorph,
      (int * (Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper) emorph)) list option,
      @{AllT_args} Result_Action.mk_copy_update_data,
      @{AllT_args} PResults.presultsq) Zippy_Instance_Induction_Data_Args.PAA.entries

    val insert : data -> Context.generic -> Context.generic
    val insert_declaration_attribute : add_args -> thm -> Context.generic -> Context.generic
    val insert_declaration_attribute_context_defaults : add_args -> thm -> Context.generic ->
      Context.generic

    type del_args = (Induction_Data_Args.insts, thm option, Induction_Data_Args.arbitrary,
      Induction_Data_Args.taking, bool, thm list) Zippy_Instance_Induction_Data_Args.PDA.entries

    val delete : data -> Context.generic -> Context.generic
    val delete_declaration_attribute : del_args -> thm -> Context.generic -> Context.generic
    val delete_declaration_attribute_context_defaults : del_args -> thm -> Context.generic ->
      Context.generic

    val binding : Binding.binding
    val parse_add_arg_entries_attribute : ((Induction_Tactic_Base.def_inst option list,
      (term * term list) option list, ML_Code_Util.code option list) Cases_Data_Args.PIM.entry, thm,
      ((string * typ) list, term list * term list, ML_Code_Util.code) Cases_Data_Args.PIM.entry,
      Induction_Data_Args.taking, bool, thm list, ML_Code_Util.code, ML_Code_Util.code,
      ML_Code_Util.code, ML_Code_Util.code, (int * ML_Code_Util.code) list, ML_Code_Util.code,
      ML_Code_Util.code) Zippy_Instance_Induction_Data_Args.PAA.entries context_parser
    val parse_add_arg_entries : ((Induction_Tactic_Base.def_inst option list,
      (term * term list) option list, ML_Code_Util.code option list) Cases_Data_Args.PIM.entry, thm,
      ((string * typ) list, term list * term list, ML_Code_Util.code) Cases_Data_Args.PIM.entry,
      Induction_Data_Args.taking, bool, thm list, ML_Code_Util.code, ML_Code_Util.code,
      ML_Code_Util.code, ML_Code_Util.code, (int * ML_Code_Util.code) list, ML_Code_Util.code,
      ML_Code_Util.code) Zippy_Instance_Induction_Data_Args.PAA.entries context_parser

    structure Facts_Data_Internal : GENERIC_DATA

    val add_attribute : ((Induction_Tactic_Base.def_inst option list,
          (term * term list) option list, ML_Code_Util.code option list) Cases_Data_Args.PIM.entry,
        thm, ((string * typ) list, term list * term list, ML_Code_Util.code) Cases_Data_Args.PIM.entry,
        Induction_Data_Args.taking, bool, thm list, ML_Code_Util.code, ML_Code_Util.code,
        ML_Code_Util.code, ML_Code_Util.code, (int * ML_Code_Util.code) list, ML_Code_Util.code,
        ML_Code_Util.code) Zippy_Instance_Induction_Data_Args.PAA.entries * Position.T -> attribute

    val parse_del_arg_entries_attribute : ((Induction_Tactic_Base.def_inst option list,
      (term * term list) option list, ML_Code_Util.code option list) Cases_Data_Args.PIM.entry, thm,
      ((string * typ) list, term list * term list, ML_Code_Util.code) Cases_Data_Args.PIM.entry,
      Induction_Data_Args.taking, bool, thm list)
      Zippy_Instance_Induction_Data_Args.PDA.entries context_parser
    val parse_del_arg_entries : ((Induction_Tactic_Base.def_inst option list,
      (term * term list) option list, ML_Code_Util.code option list) Cases_Data_Args.PIM.entry, thm,
      ((string * typ) list, term list * term list, ML_Code_Util.code) Cases_Data_Args.PIM.entry,
      Induction_Data_Args.taking, bool, thm list)
      Zippy_Instance_Induction_Data_Args.PDA.entries context_parser

    val del_attribute : ((Induction_Tactic_Base.def_inst option list,
          (term * term list) option list, ML_Code_Util.code option list) Cases_Data_Args.PIM.entry,
        thm, ((string * typ) list, term list * term list, ML_Code_Util.code) Cases_Data_Args.PIM.entry,
        Induction_Data_Args.taking, bool, thm list)
        Zippy_Instance_Induction_Data_Args.PDA.entries * Position.T -> attribute

    val parse_config_arg_entries : (bool, ML_Code_Util.code,
      ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code,
      ML_Code_Util.code, ML_Code_Util.code) Zippy_Instance_Induction_Data_Args.PDC.entries parser
    val config_attribute : (bool, ML_Code_Util.code,
      ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code,
      ML_Code_Util.code, ML_Code_Util.code) Zippy_Instance_Induction_Data_Args.PDC.entries * Position.T ->
      attribute

    val parse_attribute : attribute context_parser
    val setup_attribute : string option -> local_theory -> local_theory

    val parse_add_context_update : unit context_parser
    val parse_del_context_update : unit context_parser
    val parse_config_context_update : unit context_parser
    val parse_entry_context_update : unit context_parser
    val parse_context_update : unit context_parser

    (* action data *)
    val tac_data_from_data : Base_Data.AMeta.metadata ->
      (Tac_AAM.mk_meta -> Induction_Data_Args.data -> @{AllT_args} ZLPC.Z4.zipper ->
        (@{ParaT_args} Base_Data.GFocus.focus, Tac_AAM.ztactic) morph) ->
      (@{AllT_args} Result_Action.mk_copy_update_data -> Result_Action.result ->
        @{AllT_args} Base_Data.PAction.action) option ->
      data -> @{AllT_args} Tac.data

    val paction_data_from_data : @{ParaT_args encl: "(" ")"} Exn.ME.exn ->
      Base_Data.AMeta.metadata ->
      (Tac_AAM.mk_meta -> Induction_Data_Args.data -> @{AllT_args} ZLPC.Z4.zipper ->
        (@{ParaT_args} Base_Data.GFocus.focus, Tac_AAM.ztactic) morph) ->
      (@{AllT_args} Result_Action.mk_copy_update_data -> Result_Action.result ->
        @{AllT_args} Base_Data.PAction.action) option ->
      data -> @{AllT_args} PAction.data

    val cons_action : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Base_Data.AMeta.metadata ->
      (Tac_AAM.mk_meta -> Induction_Data_Args.data -> @{AllT_args} ZLPC.Z4.zipper ->
        (@{ParaT_args} Base_Data.GFocus.focus, Tac_AAM.ztactic) morph) ->
      (@{AllT_args} Result_Action.mk_copy_update_data -> Result_Action.result ->
        @{AllT_args} Base_Data.PAction.action) option ->
      data -> Base_Data.GFocus.focus -> (@{ParaT_args} @{AllT_args} ZLPC.Z3.zipper,
        @{AllT_args} ZLPC.Z4.zipper) morph
    val cons_nth_action : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Base_Data.ACMeta.metadata ->
      (Tac_AAM.mk_meta -> Induction_Data_Args.data -> @{AllT_args} ZLPC.Z4.zipper ->
        (@{ParaT_args} Base_Data.GFocus.focus, Tac_AAM.ztactic) morph) ->
      (@{AllT_args} Result_Action.mk_copy_update_data -> Result_Action.result ->
        @{AllT_args} Base_Data.PAction.action) option ->
      Proof.context -> int -> data -> Base_Data.GFocus.focus ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z3.zipper, @{AllT_args} ZLPC.Z4.zipper) morph

    val cons_action_cluster : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Base_Data.ACMeta.metadata ->
      (Tac_AAM.mk_meta -> Induction_Data_Args.data -> @{AllT_args} ZLPC.Z4.zipper ->
        (@{ParaT_args} Base_Data.GFocus.focus, Tac_AAM.ztactic) morph) ->
      (@{AllT_args} Result_Action.mk_copy_update_data -> Result_Action.result ->
        @{AllT_args} Base_Data.PAction.action) option ->
      Proof.context -> (Base_Data.GFocus.focus * data) list ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper, @{AllT_args} ZLPC.Z3.zipper option) morph
  end
end

functor Zippy_Instance_Induction_Data(
    structure FI_Induction_Data : FUNCTOR_INSTANCE_BASE (*target path for Induction_Data*)
    structure Z : ZIPPY_INSTANCE_TACTIC
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
    val init_args : (bool, Cases_Data_Args.match,
      Z.Tac_AAM.mk_meta,
      int -> @{AllT_args} Z.Base_Data.PAction.action,
      Z.Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z.ZLPC.Z2.zipper) Z.emorph,
      @{AllT_args} Z.Result_Action.mk_copy_update_data,
      @{AllT_args} Z.PResults.presultsq) Zippy_Instance_Induction_Data_Args.PDC.entries
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_Base : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_LGoals : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_LGoals_Pos_Copy : ZIPPY_LOGGER_MIXIN_BASE
  ) : ZIPPY_INSTANCE_INDUCTION_DATA =
struct
open Z

structure AU = ML_Attribute_Util
structure MCU = ML_Code_Util
structure PU = Parse_Util
structure SShow = SpecCheck_Show

structure IDA = Induction_Data_Args
structure CDA = Cases_Data_Args
structure HCGD = Zippy_Instance_Hom_Changed_Goals_Data_Args

structure Induction_Data =
struct
structure FI = Functor_Instance(FI_Induction_Data)

local open Zippy_Instance_Induction_Data_Args ZLPC Base_Data
in

structure Log = Zippy_Logger_Mixin_Base(val parent_logger = Log.logger; val name = "Induction_Data")
open Log

type config = (bool, CDA.match,
  Tac_AAM.mk_meta,
  int -> @{AllT_args} Base_Data.PAction.action,
  Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper) emorph,
  @{AllT_args} Result_Action.mk_copy_update_data,
  @{AllT_args} PResults.presultsq) PDC.entries

structure Config_Data = Generic_Data(
  type T = config
  val empty = init_args
  val merge = fst)

val get_config = Config_Data.get
val map_config = Config_Data.map

val get_simp = PDC.get_simp o get_config
val map_simp = map_config o PDC.map_simp

val get_match = PDC.get_match o get_config
val map_match = map_config o PDC.map_match

val get_mk_meta = PDC.get_mk_meta o get_config
val map_mk_meta = map_config o PDC.map_mk_meta

val get_empty_action = PDC.get_empty_action o get_config
val map_empty_action = map_config o PDC.map_empty_action

val get_default_update = PDC.get_default_update o get_config
val map_default_update = map_config o PDC.map_default_update

val get_mk_cud = PDC.get_mk_cud o get_config
val map_mk_cud = map_config o PDC.map_mk_cud

val get_presultsq = PDC.get_presultsq o get_config
val map_presultsq = map_config o PDC.map_presultsq

type data = (IDA.insts, thm option, IDA.arbitrary, IDA.taking, bool, thm list, CDA.match,
  Tac_AAM.mk_meta,
  int -> @{AllT_args} Base_Data.PAction.action,
  (Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper) emorph) list option,
  @{AllT_args} Result_Action.mk_copy_update_data,
  @{AllT_args} PResults.presultsq) PD.entries

val data_ord = option_ord Thm.thm_ord o apply2 PD.get_rule
  ||| IDA.insts_ord o apply2 PD.get_insts
  ||| IDA.arbitrary_ord o apply2 PD.get_arbitrary
  ||| IDA.taking_ord o apply2 PD.get_taking
  ||| list_ord Thm.thm_ord o apply2 PD.get_facts
  ||| bool_ord o apply2 PD.get_simp

val eq_data = is_equal o data_ord
fun pretty_data ctxt data = SShow.record [
  ("rule", SShow.option (SShow.thm ctxt) (PD.get_rule data)),
  ("insts", IDA.pretty_insts ctxt (PD.get_insts data)),
  ("arbitrary", IDA.pretty_arbitrary ctxt (PD.get_arbitrary data)),
  ("taking", IDA.pretty_taking ctxt (PD.get_taking data)),
  ("facts", SShow.list (SShow.thm ctxt) (PD.get_facts data)),
  ("simp", SShow.bool (PD.get_simp data))
]
fun map_data_thms f = PD.map_rule (Option.map f) #> PD.map_facts (map f)
fun transfer_data thy = map_data_thms (Thm.transfer thy)

structure Data = Generic_Data(
  type T = data Ord_List.T
  val empty = []
  val merge = Ord_List.merge data_ord)

type add_args = (IDA.insts, thm option, IDA.arbitrary, IDA.taking, bool, thm list, CDA.match,
  Tac_AAM.mk_meta,
  int -> @{AllT_args} Base_Data.PAction.action,
  Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper) emorph,
  (int * (Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper) emorph)) list option,
  @{AllT_args} Result_Action.mk_copy_update_data,
  @{AllT_args} PResults.presultsq) PAA.entries

fun num_new_goals facts rule = Thm.nprems_of rule - length facts

fun insert args context = context |>
  let
    val nupdates = PD.get_updates args |> Option.map length
    val opt_rule = PD.get_rule args
    val facts = PD.get_facts args
    val num_new_goals = opt_rule |> Option.map (num_new_goals facts)
    val ctxt = Context.proof_of context
  in
    if num_new_goals <> nupdates
    then error (Pretty.breaks [
        Pretty.block [Pretty.str "Number of updates ",
          Pretty.enclose "(" ")" [SShow.option SShow.int nupdates]],
        Pretty.block [Pretty.str "does not match number of new goals ",
          Pretty.enclose "(" ")" [SShow.option SShow.int num_new_goals]],
        Pretty.block [Pretty.str "for theorem ", SShow.option (Thm.pretty_thm ctxt) opt_rule],
        Pretty.block [Pretty.str "and facts ", SShow.list (Thm.pretty_thm ctxt) facts]
      ] |> Pretty.block |> Pretty.string_of)
    else let val args = map_data_thms Thm.trim_context args
      in
        Data.map (fn data => if Ord_List.member data_ord data args
          then (@{log Logger.WARN} ctxt (fn _ => Pretty.breaks [
                Pretty.str "Similar induction data already added. Skipping insertion of",
                pretty_data ctxt args
              ] |> Pretty.block |> Pretty.string_of);
            data)
          else Ord_List.insert data_ord args data)
        end
    end

val prepare_attr_rule = Option.filter (Thm.is_dummy #> not)

fun insert_declaration_attribute args thm context =
  let
    val updates = PAA.get_updates args |> the_default []
    val ctxt = Context.proof_of context
    val (updates, rule) = case prepare_attr_rule thm of
        NONE => let val _ = if length updates > 0
            then @{log Logger.WARN} ctxt (fn _ =>
              "Passed updates will be ignored since no induction rule was passed.")
            else ()
          in (NONE, NONE) end
      | SOME rule =>
          let val updates = HCGD.mk_updates_default (num_new_goals (PAA.get_facts args)) rule
            (PAA.get_default_update args) updates ctxt
          in (SOME updates, SOME rule) end
  in
    PAA.map_updates (K updates) args |> PAA.map_rule_safe (K (SOME rule))
    |> PD_entries_from_PAA_entries |> (fn data => insert data context)
  end

fun add_args_context_defaults args = get_config
  #> (fn cargs => [PAA.simp (PDC.get_simp cargs),
    PAA.match (PDC.get_match cargs),
    PAA.mk_meta (PDC.get_mk_meta cargs),
    PAA.empty_action (PDC.get_empty_action cargs),
    PAA.default_update (PDC.get_default_update cargs),
    PAA.mk_cud (PDC.get_mk_cud cargs),
    PAA.presultsq (PDC.get_presultsq cargs)])
  #> PAA.entries_from_entry_list
  #> PAA.merge_entries args

fun insert_declaration_attribute_context_defaults args thm context =
  insert_declaration_attribute (add_args_context_defaults args context) thm context

type del_args = (IDA.insts, thm option, IDA.arbitrary, IDA.taking, bool, thm list) PDA.entries

fun delete args context = Data.map (fn data => if Ord_List.member data_ord data args
  then Ord_List.remove data_ord args data
  else let val ctxt = Context.proof_of context
    in
      (@{log Logger.WARN} ctxt (fn _ => Pretty.breaks [
          Pretty.str "Induction data", pretty_data ctxt args, Pretty.str "not found. Skipping deletion."
        ] |> Pretty.block |> Pretty.string_of);
      data)
    end) context

fun delete_declaration_attribute args thm =
  [PD.insts (PDA.get_insts args),
    PD.arbitrary (PDA.get_arbitrary args),
    PD.taking (PDA.get_taking args),
    PD.simp (PDA.get_simp args),
    PD.facts (PDA.get_facts args),
    PD.rule (prepare_attr_rule thm)]
  |> PD.entries_from_entry_list
  |> delete

fun del_args_context_defaults args = get_config
  #> (fn cargs => [PDA.simp (PDC.get_simp cargs)])
  #> PDA.entries_from_entry_list
  #> PDA.merge_entries args

fun delete_declaration_attribute_context_defaults args thm context =
  delete_declaration_attribute (del_args_context_defaults args context) thm context

val binding = Binding.make (FI.id, FI.pos)

fun gen_filter_arg_entries get_insts get_match_safe =
  let
    fun filter x = case (get_insts x, get_match_safe x) of
      (CDA.PIM.pat _, SOME _) => false | _ => true
    val filter_msg = "Match must only be passed when using patterns for instantiations."
  in PU.filter filter (K (PU.fail (K filter_msg))) end

val parse_insts_opt_args_sep = Scan.lift (Args.$$$ "use")

fun gen_parse_add_del_arg_entries parse_entries_required parse_entry default_entries map_insts_safe =
  let val unless = (parse_insts_opt_args_sep >> K ()) || (parse_entry >> K ())
  in
    Scan.optional (PAA.get_insts add_arg_parsers unless) (CDA.PIM.fix [])
    -- (Scan.option parse_insts_opt_args_sep
    :|-- (fn use => parse_entries_required (if is_some use then Scan.repeat1 else Scan.repeat)
      true [] parse_entry default_entries))
    >> (fn (insts, entries) => map_insts_safe (K (SOME insts)) entries)
  end

fun gen_parse_key keys key_to_string key_from_string except = Parse_Key_Value.parse_key
  (keys |> subtract (op =) except |> map key_to_string)
  (Option.composePartial (Option.filter (member (op =) except #> not), key_from_string))

fun gen_parse_add_arg_entries parse_rule =
  let
    val parsers = add_arg_parsers
    fun parse_value x = PAA.parse_entry Scan.fail
      (if parse_rule then PAA.get_rule parsers else Scan.fail)
      (PAA.get_arbitrary parsers parse_entry_unit) (PAA.get_taking parsers parse_entry_unit)
      (Scan.lift (PAA.get_simp parsers))
      (PAA.get_facts parsers) (Scan.lift (PAA.get_match parsers))
      (Scan.lift (PAA.get_mk_meta parsers)) (Scan.lift (PAA.get_empty_action parsers))
      (Scan.lift (PAA.get_default_update parsers)) (Scan.lift (PAA.get_updates parsers))
      (Scan.lift (PAA.get_mk_cud parsers)) (Scan.lift (PAA.get_presultsq parsers)) x
    and parse_key x = gen_parse_key PAA.keys PAA.key_to_string PAA.key_from_string
      (map PAA.key (PAA.insts :: (if parse_rule then [] else [PAA.rule]))) x
    and parse_entry x = Parse_Key_Value.parse_entry' (Scan.lift parse_key)
      (K (Scan.lift (Parse.$$$ ":"))) parse_value x
    and parse_entry_unit x = (parse_entry >> K ()) x
    val default_entries = PAA.entries_from_entry_list [PAA.updates [], PAA.facts [],
      PAA.arbitrary (CDA.PIM.fix []), PAA.taking []]
  in
    gen_parse_add_del_arg_entries PAA.parse_entries_required' parse_entry default_entries
      PAA.map_insts_safe
    |> gen_filter_arg_entries PAA.get_insts PAA.get_match_safe
  end
val parse_add_arg_entries_attribute = gen_parse_add_arg_entries false
val parse_add_arg_entries = gen_parse_add_arg_entries true

fun Args_substructure_op substructure operation =
  MCU.flat_read ["Zippy_Instance_Induction_Data_Args.", substructure, ".", operation]

structure Facts_Data_Internal = Generic_Data(
  type T = thm list
  val empty = []
  val merge = fst)

val code_bool = Value.print_bool #> MCU.read
val code_get_facts = FI.code_struct_op "Facts_Data_Internal.get"
fun gen_code_operation operation code_parse_op code_entries =
  let val [thm, context, get_facts] = map MCU.internal_name ["thm", "context", "get_facts"]
  in
    MCU.reads ["fn", thm, "=> fn", context, "=>"] @ FI.code_struct_op operation @
      MCU.atomic (code_parse_op "entries_from_entry_list" @ code_entries @
        MCU.read "|>" @ code_parse_op "map_facts" @
          MCU.atomic (MCU.reads ["fn", get_facts, "=>", get_facts, context])) @
      MCU.reads [thm, context]
  end

fun add_attribute (entries, pos) (context, thm) =
  let
    val code_PAA_op = Args_substructure_op "PAA"
    val code_from_key = code_PAA_op o PAA.key_to_string
    val context = Facts_Data_Internal.put (PAA.get_facts entries) context
    fun code_from_entry (PAA.simp b) = code_bool b
      | code_from_entry (PAA.insts insts) = IDA.code_insts insts
      | code_from_entry (PAA.arbitrary arbitrary) = IDA.code_arbitrary arbitrary
      | code_from_entry (PAA.taking taking) = IDA.code_taking taking
      | code_from_entry (PAA.facts _) = code_get_facts
      | code_from_entry (PAA.match c) = c
      | code_from_entry (PAA.mk_meta c) = c
      | code_from_entry (PAA.empty_action c) = c
      | code_from_entry (PAA.default_update c) = c
      | code_from_entry (PAA.updates updates) = MCU.option (SOME (HCGD.code_updates updates))
      | code_from_entry (PAA.mk_cud c) = c
      | code_from_entry (PAA.presultsq c) = c
      | code_from_entry (PAA.rule _) = error "rule may not be passed to add induction attribute"
    val code_entries = PAA.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code = gen_code_operation "insert_declaration_attribute_context_defaults" code_PAA_op code_entries
  in ML_Attribute.run_declaration_attribute (code, pos) (context, thm) end

fun gen_parse_del_arg_entries parse_rule =
  let
    val parsers = PDA_entries_from_PAA_entries add_arg_parsers
    fun parse_value x = PDA.parse_entry Scan.fail
      (if parse_rule then PDA.get_rule parsers else Scan.fail)
      (PDA.get_arbitrary parsers parse_entry_unit) (PDA.get_taking parsers parse_entry_unit)
      (Scan.lift (PDA.get_simp parsers)) (PDA.get_facts parsers) x
    and parse_key x = gen_parse_key PDA.keys PDA.key_to_string PDA.key_from_string
      (map PDA.key (PDA.insts :: (if parse_rule then [] else [PDA.rule]))) x
    and parse_entry x = Parse_Key_Value.parse_entry' (Scan.lift parse_key)
      (K (Scan.lift (Parse.$$$ ":"))) parse_value x
    and parse_entry_unit x = (parse_entry >> K ()) x
    val default_entries = PDA.entries_from_entry_list [PDA.facts [], PDA.arbitrary (CDA.PIM.fix []),
      PDA.taking []]
  in
    gen_parse_add_del_arg_entries PDA.parse_entries_required' parse_entry default_entries
      PDA.map_insts_safe
  end
val parse_del_arg_entries_attribute = gen_parse_del_arg_entries false
val parse_del_arg_entries = gen_parse_del_arg_entries true

fun del_attribute (entries, pos) (context, thm) =
  let
    val code_PDA_op = Args_substructure_op "PDA"
    val code_from_key = code_PDA_op o PDA.key_to_string
    val context = Facts_Data_Internal.put (PDA.get_facts entries) context
    fun code_from_entry (PDA.simp b) = code_bool b
      | code_from_entry (PDA.insts insts) = IDA.code_insts insts
      | code_from_entry (PDA.arbitrary arbitrary) = IDA.code_arbitrary arbitrary
      | code_from_entry (PDA.taking taking) = IDA.code_taking taking
      | code_from_entry (PDA.facts _) = code_get_facts
      | code_from_entry (PDA.rule _) = error "rule may not be passed to del induction attribute"
    val code_entries = PDA.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code = gen_code_operation "delete_declaration_attribute_context_defaults" code_PDA_op code_entries
  in ML_Attribute.run_declaration_attribute (code, pos) (context, thm) end

val parse_config_arg_entries =
  let
    val parsers = PDC_entries_from_PAA_entries add_arg_parsers
    val parse_value = PDC.parse_entry (PDC.get_simp parsers) (PDC.get_match parsers)
      (PDC.get_mk_meta parsers) (PDC.get_empty_action parsers) (PDC.get_default_update parsers)
      (PDC.get_mk_cud parsers) (PDC.get_presultsq parsers)
    val parse_entry = Parse_Key_Value.parse_entry PDC.parse_key (K (Parse.$$$ ":")) parse_value
    val default_entries = PDC.empty_entries ()
  in PDC.parse_entries_required Scan.repeat1 true [] parse_entry default_entries end

fun config_attribute (entries, pos) =
  let
    val code_PDC_op = Args_substructure_op "PDC"
    val code_from_key = code_PDC_op o PDC.key_to_string
    fun code_from_entry (PDC.simp b) = code_bool b
      | code_from_entry (PDC.match c) = c
      | code_from_entry (PDC.mk_meta c) = c
      | code_from_entry (PDC.empty_action c) = c
      | code_from_entry (PDC.default_update c) = c
      | code_from_entry (PDC.mk_cud c) = c
      | code_from_entry (PDC.presultsq c) = c
    val code_entries = PDC.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code =
      FI.code_struct_op "map_config" @ MCU.atomic (code_PDC_op "merge_entries" @
      MCU.atomic (code_PDC_op "entries_from_entry_list" @ code_entries))
  in ML_Attribute.run_map_context (code, pos) end

val parse_entries =
  let
    val parse_value = PM.parse_entry parse_add_arg_entries_attribute parse_del_arg_entries_attribute
      (Scan.lift parse_config_arg_entries)
    val parse_entry = Parse_Key_Value.parse_entry' (Scan.lift PM.parse_key) (K (Scan.succeed ""))
      parse_value
  in PM.parse_entries_required' Parse.and_list1' true [] parse_entry (PM.empty_entries ()) end

fun attribute (entries, pos) =
  let
    fun default_attr (context, thm) = (SOME context, SOME thm)
    val add_attr = PM.get_add_safe entries
      |> (fn SOME entries => add_attribute (entries, pos) | NONE => default_attr)
    val del_attr = PM.get_del_safe entries
      |> (fn SOME sel => del_attribute (sel, pos) | NONE => default_attr)
    val config_attr = PM.get_config_safe entries
      |> (fn SOME entries => config_attribute (entries, pos) | NONE => default_attr)
  in AU.apply_attribute config_attr #> AU.apply_attribute del_attr #> add_attr end

val parse_attribute = PU.position' parse_entries >> attribute
  || PU.position' parse_add_arg_entries_attribute >> add_attribute

val setup_attribute = Attrib.local_setup binding (Parse.!!!! parse_attribute) o
  the_default ("configure induction data " ^ enclose "(" ")" FI.long_name)

local
  fun run_attr attr (context, opt_thm) = (case opt_thm of
      NONE => AU.attribute_map_context attr context
    | SOME thm => AU.apply_attribute attr (context, thm) |> fst)
    |> rpair () |> Scan.succeed
  fun gen_add_del_attr_context_update attr map_rule_safe get_rule_safe parse_entries =
    PU.position' parse_entries
    :|-- (fn (entries, pos) => Scan.depend (fn context => run_attr
      (attr (map_rule_safe (K NONE) entries, pos)) (context, get_rule_safe entries)))
in
val parse_add_context_update = gen_add_del_attr_context_update
  add_attribute PAA.map_rule_safe PAA.get_rule_safe parse_add_arg_entries
val parse_del_context_update = gen_add_del_attr_context_update
  del_attribute PDA.map_rule_safe PDA.get_rule_safe parse_del_arg_entries
val parse_config_context_update = Scan.lift (PU.position parse_config_arg_entries)
  :|-- (fn parsed => Scan.depend (fn context => run_attr (config_attribute parsed) (context, NONE)))
end

val parse_entry_context_update =
  Scan.optional (Scan.lift PM.parse_key) (PM.key PM.add)
  :|-- (fn PM.add _ => parse_add_context_update | PM.del _ => parse_del_context_update
    | PM.config _ => parse_config_context_update)
val parse_context_update = Parse.and_list1' parse_entry_context_update >> K ()

(* action data *)

local open MU; open SC
  structure Base_Mixins = struct structure Exn = Exn; structure Co = Co; structure Ctxt = Ctxt end
  structure ZB = Zippy_Base(open Base_Mixins; structure Z = ZLPC; structure Log = Log_Base
    \<^imap>\<open>\<open>{i}\<close> => \<open>structure Show{i} = Show.Zipper{i}\<close>\<close>)
  structure ZL = Zippy_Lists(open Base_Mixins; structure Z = ZLPC)
  structure Goals = Zippy_Goals_Mixin_Base(open Mixin_Base1 Mixin_Base2)
  structure Goals_Pos = Zippy_Goals_Pos_Mixin_Base(open Goals; structure GPU = Base_Data.Tac_Res.GPU)
  structure Goals_Pos_Copy = Zippy_Goals_Pos_Copy_Mixin(Zippy_Goals_Pos_Copy_Mixin_Base(open Goals_Pos
    structure Copy = Mixin_Base3.Copy))
  structure LGoals_Pos_Copy = Zippy_Lists_Goals_Pos_Copy_Mixin(open Base_Mixins; structure Z = ZL
    structure GPC = Goals_Pos_Copy; structure Log = Log_LGoals_Pos_Copy; structure Log_Base = Log_Base
    structure Log_LGoals = Log_LGoals; \<^imap>\<open>\<open>{i}\<close> => \<open>structure Show{i} = Show.Zipper{i}\<close>\<close>)
in
fun tac_data_from_data meta tac opt_default_update_action data =
  let val result_action = case PD.get_updates data of
      NONE => (case opt_default_update_action of
        NONE => (fn x => fn y => fn z => Ctxt.with_ctxt (fn ctxt =>
          let
            val default_update = get_default_update (Context.Proof ctxt)
            val partition_update = Library.maps snd
              #> LGoals_Pos_Copy.partition_update_gcposs_gclusters_gclusters
                (List.map default_update #> ZB.update_zipper2)
          in Result_Action.changed_goals_action partition_update x y z end))
      | SOME default_update => default_update)
    | SOME updates => Result_Action.hom_changed_goals_action updates
  in
    {meta = meta,
    empty_action = PD.get_empty_action data,
    result_action = result_action (PD.get_mk_cud data),
    presultsq = PD.get_presultsq data,
    tac = tac (PD.get_mk_meta data) (induct_PD_entries_from_PD_entries data)}
  end

fun paction_data_from_data exn meta tac opt_default_update_action =
  tac_data_from_data meta tac opt_default_update_action #> Tac.paction_data_from_data exn

fun cons_action exn meta tac opt_default_update_action =
  paction_data_from_data exn meta tac opt_default_update_action #> Z.PAction.cons_action

fun cons_nth_action exn meta tac opt_default_update_action ctxt i data =
  let val meta = AMeta.metadata (
    Zippy_Identifier.suffix_name NONE (string_of_int i) (ACMeta.Id.getter meta),
    Lazy.lazy (fn _ => Pretty.breaks [
        Pretty.str (ACMeta.Descr.getter meta |> Lazy.force),
        Pretty.block [Pretty.str "Induction data: ",
          IDA.pretty_data ctxt (induct_PD_entries_from_PD_entries data)]
      ] |> Pretty.block |> Pretty.string_of))
  in cons_action exn meta tac opt_default_update_action data end

fun cons_action_cluster exn meta tac opt_default_update_action ctxt =
  map_index (Library.uncurry (fn i => apsnd (fn data => fn focus =>
    cons_nth_action exn meta tac opt_default_update_action ctxt i data focus >>> Up4.morph)))
  #> Node.cons3 exn meta
end
end
end
end