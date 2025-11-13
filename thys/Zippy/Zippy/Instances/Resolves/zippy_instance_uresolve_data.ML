(*  Title:      Zippy/zippy_instance_uresolve_data.ML
    Author:     Kevin Kappelmann
*)
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_URESOLVE_DATA_MODE [add, del, config]}
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_URESOLVE_DATA
  [rule, normalisers, unifier, mk_meta, empty_action, updates, mk_cud, presultsq]}
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_URESOLVE_DATA_ADD_ARGS
  [rule, normalisers, unifier, mk_meta, empty_action, default_update, updates, mk_cud, presultsq]}
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_URESOLVE_DATA_DEL_ARGS [rule, select]}
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_URESOLVE_DATA_CONFIG
  [normalisers, unifier, mk_meta, empty_action, default_update, mk_cud, presultsq, del_select]}

signature ZIPPY_INSTANCE_URESOLVE_DATA_ARGS =
sig
  structure PM : PARSE_ZIPPY_INSTANCE_URESOLVE_DATA_MODE
  structure PD : PARSE_ZIPPY_INSTANCE_URESOLVE_DATA
  structure PAA : PARSE_ZIPPY_INSTANCE_URESOLVE_DATA_ADD_ARGS
  structure PDA : PARSE_ZIPPY_INSTANCE_URESOLVE_DATA_DEL_ARGS
  structure PDC : PARSE_ZIPPY_INSTANCE_URESOLVE_DATA_CONFIG

  val PD_entries_from_PAA_entries : ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) PAA.entries ->
    ('a, 'b, 'c, 'd, 'e, 'g, 'h, 'i) PD.entries
  val PDA_entries_from_PAA_entries : ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) PAA.entries -> 'j ->
    ('a, 'j) PDA.entries
  val PDC_entries_from_PAA_entries : ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) PAA.entries -> 'j ->
    ('b, 'c, 'd, 'e, 'f, 'h, 'i, 'j) PDC.entries

  val add_arg_parsers : (thm context_parser, ML_Code_Util.code parser, ML_Code_Util.code parser,
    ML_Code_Util.code parser, ML_Code_Util.code parser, ML_Code_Util.code parser,
    (int * ML_Code_Util.code) list parser, ML_Code_Util.code parser, ML_Code_Util.code parser)
    PAA.entries
  val del_arg_parsers : (thm context_parser, ML_Code_Util.code parser) PDA.entries
  val config_data_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser,
    ML_Code_Util.code parser, ML_Code_Util.code parser, ML_Code_Util.code parser,
    ML_Code_Util.code parser, ML_Code_Util.code parser, ML_Code_Util.code parser) PDC.entries
end

structure Zippy_Instance_UResolve_Data_Args : ZIPPY_INSTANCE_URESOLVE_DATA_ARGS =
struct

structure PU = Parse_Util
structure UP = Unification_Parser
structure MCU = ML_Code_Util
structure HCGD = Zippy_Instance_Hom_Changed_Goals_Data_Args

@{parse_entries (struct) PM [add, del, config]}
@{parse_entries (struct) PD [rule, normalisers, unifier, mk_meta, empty_action, updates, mk_cud,
  presultsq]}
@{parse_entries (struct) PAA [rule, normalisers, unifier, mk_meta, empty_action, default_update,
  updates, mk_cud, presultsq]}
@{parse_entries (struct) PDA [rule, select]}
@{parse_entries (struct) PDC [normalisers, unifier, mk_meta, empty_action, default_update, mk_cud,
  presultsq, del_select]}

fun PD_entries_from_PAA_entries {rule, normalisers, unifier, mk_meta, empty_action, updates, mk_cud,
  presultsq,...} =
  {rule = rule, normalisers = normalisers, unifier = unifier, mk_meta = mk_meta,
  empty_action = empty_action, updates = updates, mk_cud = mk_cud, presultsq = presultsq}
fun PDA_entries_from_PAA_entries {rule,...} select = {rule = rule, select = SOME select}
fun PDC_entries_from_PAA_entries {mk_meta, normalisers, unifier, empty_action, default_update,
  mk_cud, presultsq,...} select =
  {normalisers = normalisers, unifier = unifier, mk_meta = mk_meta, empty_action = empty_action,
  default_update = default_update, mk_cud = mk_cud, presultsq = presultsq, del_select = SOME select}

val add_arg_parsers = {
  rule = SOME (HCGD.PAA.get_thm HCGD.add_arg_parsers),
  normalisers = SOME UP.parse_normalisers,
  unifier = SOME UP.parse_unifier,
  mk_meta = SOME (HCGD.PAA.get_mk_meta HCGD.add_arg_parsers),
  empty_action = SOME (HCGD.PAA.get_empty_action HCGD.add_arg_parsers),
  default_update = SOME (HCGD.PAA.get_default_update HCGD.add_arg_parsers),
  updates = SOME (HCGD.PAA.get_updates HCGD.add_arg_parsers),
  mk_cud = SOME (HCGD.PAA.get_mk_cud HCGD.add_arg_parsers),
  presultsq = SOME (HCGD.PAA.get_presultsq HCGD.add_arg_parsers)}

val del_arg_parsers = PDA_entries_from_PAA_entries add_arg_parsers
  (HCGD.PDA.get_select HCGD.del_arg_parsers)
val config_data_parsers = PDC_entries_from_PAA_entries add_arg_parsers
  (PDA.get_select del_arg_parsers)
end

signature ZIPPY_INSTANCE_URESOLVE_DATA =
sig
  include ZIPPY_INSTANCE_TACTIC

  structure UResolve_Data :
  sig
    type data = (thm,
      Unification_Base.normalisers,
      Unification_Base.unifier,
      Tac_AAM.mk_meta,
      int -> @{AllT_args} Base_Data.PAction.action,
      (Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper) emorph) list,
      @{AllT_args} Result_Action.mk_copy_update_data,
      @{AllT_args} PResults.presultsq) Zippy_Instance_UResolve_Data_Args.PD.entries

    val map_data_thms : (thm -> thm) -> data -> data
    val transfer_data : theory -> data -> data

    structure Data : GENERIC_TERM_INDEX_DATA
    where type value = data

    type config = (Unification_Base.normalisers,
      Unification_Base.unifier,
      Tac_AAM.mk_meta,
      int -> @{AllT_args} Base_Data.PAction.action,
      Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper) emorph,
      @{AllT_args} Result_Action.mk_copy_update_data,
      @{AllT_args} PResults.presultsq,
      thm * Data.term_value -> bool) Zippy_Instance_UResolve_Data_Args.PDC.entries

    structure Config_Data : GENERIC_DATA
    where type T = config

    val get_config : Context.generic -> Config_Data.T
    val map_config : (Config_Data.T -> Config_Data.T) -> Context.generic -> Context.generic

    val get_normalisers : Context.generic -> Unification_Base.normalisers
    val map_normalisers : (Unification_Base.normalisers -> Unification_Base.normalisers) ->
      Context.generic -> Context.generic

    val get_unifier : Context.generic -> Unification_Base.unifier
    val map_unifier : (Unification_Base.unifier -> Unification_Base.unifier) ->
      Context.generic -> Context.generic

    val get_mk_meta : Context.generic -> Tac_AAM.mk_meta
    val map_mk_meta : (Tac_AAM.mk_meta -> Tac_AAM.mk_meta) -> Context.generic -> Context.generic

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

    val get_del_select : Context.generic -> thm * Data.term_value -> bool
    val map_del_select : ((thm * Data.term_value -> bool) -> thm * Data.term_value -> bool) ->
      Context.generic -> Context.generic

    type add_args = (thm,
      Unification_Base.normalisers,
      Unification_Base.unifier,
      Tac_AAM.mk_meta,
      int -> @{AllT_args} Base_Data.PAction.action,
      Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper) emorph,
      (int * (Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper) emorph)) list,
      @{AllT_args} Result_Action.mk_copy_update_data,
      @{AllT_args} PResults.presultsq) Zippy_Instance_UResolve_Data_Args.PAA.entries

    val insert : data -> Context.generic -> Context.generic
    val insert_declaration_attribute : add_args -> thm -> Context.generic -> Context.generic
    val insert_declaration_attribute_context_defaults : add_args -> thm -> Context.generic ->
      Context.generic

    type del_args = (thm, thm * Data.term_value -> bool)
      Zippy_Instance_UResolve_Data_Args.PDA.entries

    val delete : del_args -> Context.generic -> Context.generic
    val delete_declaration_attribute : del_args -> thm -> Context.generic -> Context.generic
    val delete_declaration_attribute_context_defaults : del_args -> thm -> Context.generic ->
      Context.generic

    val binding : Binding.binding
    val parse_add_arg_entries_attribute : (thm, ML_Code_Util.code, ML_Code_Util.code,
      ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code, (int * ML_Code_Util.code) list,
      ML_Code_Util.code, ML_Code_Util.code) Zippy_Instance_UResolve_Data_Args.PAA.entries parser
    val add_attribute : (thm, ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code,
        ML_Code_Util.code, ML_Code_Util.code, (int * ML_Code_Util.code) list, ML_Code_Util.code,
        ML_Code_Util.code) Zippy_Instance_UResolve_Data_Args.PAA.entries * Position.T -> attribute

    val parse_del_arg_entries_attribute : (thm, ML_Code_Util.code)
      Zippy_Instance_UResolve_Data_Args.PDA.entries parser
    val del_attribute : (thm, ML_Code_Util.code) Zippy_Instance_UResolve_Data_Args.PDA.entries
      * Position.T -> attribute

    val parse_config_arg_entries : (ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code,
      ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code)
      Zippy_Instance_UResolve_Data_Args.PDC.entries parser
    val config_attribute : (ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code,
        ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code,
        ML_Code_Util.code) Zippy_Instance_UResolve_Data_Args.PDC.entries * Position.T -> attribute

    val parse_attribute : attribute parser
    val setup_attribute : (string, string) Either.either -> local_theory -> local_theory

    val parse_add_context_update : unit context_parser
    val parse_del_context_update : unit context_parser
    val parse_config_context_update : unit context_parser
    val parse_entry_context_update : unit context_parser
    val parse_context_update : unit context_parser

    (* action data *)
    val lookup_each_focused_data : ('a -> Data.term_value list) -> 'a list ->
      Base_Data.GFocus.focus -> (Base_Data.GFocus.focus * Data.value) list

    val tac_data_from_data : Base_Data.AMeta.metadata ->
      (Unification_Base.normalisers -> Unification_Base.unifier -> Tac_AAM.mk_meta -> thm ->
        @{AllT_args} ZLPC.Z4.zipper -> (@{ParaT_args} Base_Data.GFocus.focus,
        Tac_AAM.ztactic) morph) ->
      data -> @{AllT_args} Tac.data

    val paction_data_from_data : @{ParaT_args encl: "(" ")"} Exn.ME.exn ->
      Base_Data.AMeta.metadata ->
      (Unification_Base.normalisers -> Unification_Base.unifier -> Tac_AAM.mk_meta -> thm ->
        @{AllT_args} ZLPC.Z4.zipper -> (@{ParaT_args} Base_Data.GFocus.focus,
        Tac_AAM.ztactic) morph) ->
      data -> @{AllT_args} PAction.data

    val cons_action : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Base_Data.AMeta.metadata ->
      (Unification_Base.normalisers -> Unification_Base.unifier -> Tac_AAM.mk_meta -> thm ->
        @{AllT_args} ZLPC.Z4.zipper -> (@{ParaT_args} Base_Data.GFocus.focus,
        Tac_AAM.ztactic) morph) ->
      data -> Base_Data.GFocus.focus -> (@{ParaT_args} @{AllT_args} ZLPC.Z3.zipper,
        @{AllT_args} ZLPC.Z4.zipper) morph
    val cons_nth_action : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Base_Data.ACMeta.metadata ->
      (Unification_Base.normalisers -> Unification_Base.unifier -> Tac_AAM.mk_meta -> thm ->
        @{AllT_args} ZLPC.Z4.zipper -> (@{ParaT_args} Base_Data.GFocus.focus,
        Tac_AAM.ztactic) morph) ->
      Proof.context -> int -> data -> Base_Data.GFocus.focus ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z3.zipper, @{AllT_args} ZLPC.Z4.zipper) morph

    val cons_action_cluster : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Base_Data.ACMeta.metadata ->
      (Unification_Base.normalisers -> Unification_Base.unifier -> Tac_AAM.mk_meta -> thm ->
        @{AllT_args} ZLPC.Z4.zipper -> (@{ParaT_args} Base_Data.GFocus.focus,
        Tac_AAM.ztactic) morph) ->
      Proof.context -> (Base_Data.GFocus.focus * data) list ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper, @{AllT_args} ZLPC.Z3.zipper option) morph
  end
end


functor Zippy_Instance_UResolve_Data(
    structure FI_UResolve_Data : FUNCTOR_INSTANCE_BASE (*target path for UResolve_Data*)
    structure Z : ZIPPY_INSTANCE_TACTIC
    structure TI : TERM_INDEX
    val key_of_thm : thm -> term
    val num_new_goals : thm -> int
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
  ) : ZIPPY_INSTANCE_URESOLVE_DATA =
struct
open Z
structure AU = ML_Attribute_Util
structure MCU = ML_Code_Util
structure PU = Parse_Util
structure SShow = SpecCheck_Show
structure HCGD = Zippy_Instance_Hom_Changed_Goals_Data_Args

structure UResolve_Data =
struct
structure FI = Functor_Instance(FI_UResolve_Data)

local open Zippy_Instance_UResolve_Data_Args ZLPC Base_Data
in
type data = (thm,
  Unification_Base.normalisers,
  Unification_Base.unifier,
  Tac_AAM.mk_meta,
  int -> @{AllT_args} PAction.action,
  (GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z2.zipper) emorph) list,
  @{AllT_args} Result_Action.mk_copy_update_data,
  @{AllT_args} PResults.presultsq) PD.entries

fun eq_data data = Thm.eq_thm (apply2 PD.get_rule data)
fun pretty_data ctxt data = SShow.record [
    ("thm", Thm.pretty_thm ctxt (PD.get_rule data))
  ]
fun map_data_thms f = PD.map_rule f
fun transfer_data thy = map_data_thms (Thm.transfer thy)

\<^functor_instance>\<open>struct_name: Data
  functor_name: Generic_Term_Index_Data
  id: \<open>FI.prefix_id "data"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    val parent_logger = Log.logger
    structure TI = TI
    type value = data
    val eq_value = eq_data
    val pretty_value = pretty_data\<close>\<close>

type config = (Unification_Base.normalisers,
  Unification_Base.unifier,
  Tac_AAM.mk_meta,
  int -> @{AllT_args} PAction.action,
  GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z2.zipper) emorph,
  @{AllT_args} Result_Action.mk_copy_update_data,
  @{AllT_args} PResults.presultsq,
  thm * Data.term_value -> bool) PDC.entries

structure Config_Data = Generic_Data(
  type T = config
  val empty = init_args
  val merge = fst)

val get_config = Config_Data.get
val map_config = Config_Data.map

val get_normalisers = PDC.get_normalisers o get_config
val map_normalisers = map_config o PDC.map_normalisers

val get_unifier = PDC.get_unifier o get_config
val map_unifier = map_config o PDC.map_unifier

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

val get_del_select = PDC.get_del_select o get_config
val map_del_select = map_config o PDC.map_del_select

type add_args = (thm,
  Unification_Base.normalisers,
  Unification_Base.unifier,
  Tac_AAM.mk_meta,
  int -> @{AllT_args} PAction.action,
  GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z2.zipper) emorph,
  (int * (GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z2.zipper) emorph)) list,
  @{AllT_args} Result_Action.mk_copy_update_data,
  @{AllT_args} PResults.presultsq) PAA.entries

fun insert data context =
  let
    val data = map_data_thms Thm.trim_context data
    val thm = PD.get_rule data
    val num_new_goals = num_new_goals thm
    val nupdates = length (PD.get_updates data)
  in
    if num_new_goals <> nupdates
    then error (Pretty.breaks [
        Pretty.block [Pretty.str "Number of updates ",
          Pretty.enclose "(" ")" [SShow.int nupdates]],
        Pretty.block [Pretty.str "does not match number of new goals ",
          Pretty.enclose "(" ")" [SShow.int num_new_goals]],
        Pretty.block [Pretty.str "for theorem ", Thm.pretty_thm (Context.proof_of context) thm]
      ] |> Pretty.block |> Pretty.string_of)
    else Data.insert (key_of_thm thm, data) context
  end

fun insert_declaration_attribute args thm context =
  let val updates = HCGD.mk_updates_default num_new_goals thm (PAA.get_default_update args)
    (PAA.get_updates args) (Context.proof_of context)
  in
    PAA.map_updates (K updates) args |> PAA.map_rule_safe (K (SOME thm))
    |> PD_entries_from_PAA_entries |> (fn data => insert data context)
  end

fun add_args_context_defaults args = get_config
  #> (fn cargs => [PAA.normalisers (PDC.get_normalisers cargs),
    PAA.unifier (PDC.get_unifier cargs),
    PAA.mk_meta (PDC.get_mk_meta cargs),
    PAA.empty_action (PDC.get_empty_action cargs),
    PAA.default_update (PDC.get_default_update cargs),
    PAA.mk_cud (PDC.get_mk_cud cargs),
    PAA.presultsq (PDC.get_presultsq cargs)])
  #> PAA.entries_from_entry_list
  #> PAA.merge_entries args

fun insert_declaration_attribute_context_defaults args thm context =
  insert_declaration_attribute (add_args_context_defaults args context) thm context

type del_args = (thm, thm * Data.term_value -> bool) PDA.entries

fun delete args = let val thm = PDA.get_rule args
  in Data.delete (key_of_thm thm, curry (PDA.get_select args) thm) end

fun delete_declaration_attribute args thm = PDA.map_rule_safe (K (SOME thm)) args |> delete

fun del_args_context_defaults args = get_config
  #> (fn cargs => [PDA.select (PDC.get_del_select cargs)])
  #> PDA.entries_from_entry_list
  #> PDA.merge_entries args

fun delete_declaration_attribute_context_defaults args thm context =
  delete_declaration_attribute (del_args_context_defaults args context) thm context

val binding = Binding.make (FI.id, FI.pos)

fun gen_parse_key keys key_to_string key_from_string except = Parse_Key_Value.parse_key
  (keys |> subtract (op =) except |> map key_to_string)
  (Option.composePartial (Option.filter (member (op =) except #> not), key_from_string))

val parse_add_arg_entry_attribute =
  let
    val parsers = add_arg_parsers
    val parse_value = PAA.parse_entry Scan.fail (PAA.get_normalisers parsers)
      (PAA.get_unifier parsers) (PAA.get_mk_meta parsers) (PAA.get_empty_action parsers)
      (PAA.get_default_update parsers) (PAA.get_updates parsers) (PAA.get_mk_cud parsers)
      (PAA.get_presultsq parsers)
    val parse_key = gen_parse_key PAA.keys PAA.key_to_string PAA.key_from_string
      (map PAA.key [PAA.rule])
  in Parse_Key_Value.parse_entry parse_key (K (Parse.$$$ ":")) parse_value end

fun gen_parse_add_arg_entries_attribute repeat =
  PAA.parse_entries_required repeat true [] parse_add_arg_entry_attribute
  (PAA.entries_from_entry_list [PAA.updates []])

val parse_add_arg_entries_attribute = gen_parse_add_arg_entries_attribute Scan.repeat

fun Args_substructure_op substructure operation =
  MCU.flat_read ["Zippy_Instance_UResolve_Data_Args.", substructure, ".", operation]

fun add_attribute (entries, pos) =
  let
    val code_PAA_op = Args_substructure_op "PAA"
    val code_from_key = code_PAA_op o PAA.key_to_string
    fun code_from_entry (PAA.normalisers c) = c
      | code_from_entry (PAA.unifier c) = c
      | code_from_entry (PAA.mk_meta c) = c
      | code_from_entry (PAA.empty_action c) = c
      | code_from_entry (PAA.default_update c) = c
      | code_from_entry (PAA.updates updates) = HCGD.code_updates updates
      | code_from_entry (PAA.mk_cud c) = c
      | code_from_entry (PAA.presultsq c) = c
      | code_from_entry (PAA.rule _) = error "rule may not be passed to add attribute"
    val code_entries = PAA.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code = FI.code_struct_op "insert_declaration_attribute_context_defaults" @
      MCU.atomic (code_PAA_op "entries_from_entry_list" @ code_entries)
  in ML_Attribute.run_declaration_attribute (code, pos) end

val parse_del_arg_entry_attribute =
  let
    val parsers = del_arg_parsers
    val parse_value = PDA.parse_entry Scan.fail (PDA.get_select parsers)
    val parse_key = gen_parse_key PDA.keys PDA.key_to_string PDA.key_from_string (map PDA.key [PDA.rule])
  in Parse_Key_Value.parse_entry parse_key (K (Parse.$$$ ":")) parse_value end

fun gen_parse_del_arg_entries_attribute repeat =
  PDA.parse_entries_required repeat true [] parse_del_arg_entry_attribute (PDA.empty_entries ())

val parse_del_arg_entries_attribute = gen_parse_del_arg_entries_attribute Scan.repeat

fun del_attribute (entries, pos) =
  let
    val code_PDA_op = Args_substructure_op "PDA"
    val code_from_key = code_PDA_op o PDA.key_to_string
    fun code_from_entry (PDA.select c) = c
      | code_from_entry (PDA.rule _) = error "rule may not be passed to del attribute"
    val code_entries = PDA.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code = FI.code_struct_op "delete_declaration_attribute_context_defaults" @
      MCU.atomic (code_PDA_op "entries_from_entry_list" @ code_entries)
  in ML_Attribute.run_declaration_attribute (code, pos) end

val parse_config_arg_entries =
  let
    val parsers = config_data_parsers
    val parse_value = PDC.parse_entry (PDC.get_normalisers parsers) (PDC.get_unifier parsers)
      (PDC.get_mk_meta parsers) (PDC.get_empty_action parsers) (PDC.get_default_update parsers)
      (PDC.get_mk_cud parsers) (PDC.get_presultsq parsers) (PDC.get_del_select parsers)
    val parse_entry = Parse_Key_Value.parse_entry PDC.parse_key (K (Parse.$$$ ":")) parse_value
    val default_entries = PDC.empty_entries ()
  in PDC.parse_entries_required Scan.repeat1 true [] parse_entry default_entries end

fun config_attribute (entries, pos) =
  let
    val code_PDC_op = Args_substructure_op "PDC"
    val code_from_key = code_PDC_op o PDC.key_to_string
    fun code_from_entry (PDC.normalisers c) = c
      | code_from_entry (PDC.unifier c) = c
      | code_from_entry (PDC.mk_meta c) = c
      | code_from_entry (PDC.empty_action c) = c
      | code_from_entry (PDC.default_update c) = c
      | code_from_entry (PDC.mk_cud c) = c
      | code_from_entry (PDC.presultsq c) = c
      | code_from_entry (PDC.del_select c) = c
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
      parse_config_arg_entries
    val parse_entry = Parse_Key_Value.parse_entry PM.parse_key (K (Scan.succeed "")) parse_value
  in PM.parse_entries_required Parse.and_list1 true [] parse_entry (PM.empty_entries ()) end

fun attribute (entries, pos) =
  let
    fun default_attr (context, thm) = (SOME context, SOME thm)
    val add_attr = PM.get_add_safe entries
      |> (fn SOME entries => add_attribute (entries, pos) | NONE => default_attr)
    val del_attr = PM.get_del_safe entries
      |> (fn SOME entries => del_attribute (entries, pos) | NONE => default_attr)
    val config_attr = PM.get_config_safe entries
      |> (fn SOME entries => config_attribute (entries, pos) | NONE => default_attr)
  in AU.apply_attribute config_attr #> AU.apply_attribute del_attr #> add_attr end

val parse_attribute = PU.position parse_entries >> attribute
  || PU.position parse_add_arg_entries_attribute >> add_attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  (Either.cases I (fn what => "configure " ^ what ^ " data " ^ enclose "(" ")" FI.long_name))

fun parse_rules unless = Scan.repeats (Scan.unless unless Parse_Util.multi_thm)
  |> PU.nonempty_list (K "List of theorems must not be empty.")
val parse_thms_opt_args_sep = Scan.lift (Args.$$$ "use")

local
  fun run_attr attr = curry (swap #> AU.apply_attribute attr #> fst)
  fun gen_add_del_attr_context_update parse_entries_required parse_entry attr =
    let val unless = (parse_thms_opt_args_sep >> K ()) || (parse_entry >> K ())
    in
      PU.position' (parse_rules unless)
      -- (Scan.option parse_thms_opt_args_sep
      :|-- (fn use => parse_entries_required (if is_some use then Scan.repeat1 else Scan.repeat)))
      :|-- (fn ((thms, pos), entries) => Scan.depend (fn context =>
        fold (run_attr (attr (entries, pos))) thms context
        |> rpair () |> Scan.succeed))
    end
in
val parse_add_context_update = gen_add_del_attr_context_update
  (gen_parse_add_arg_entries_attribute #> Scan.lift) (Scan.lift parse_add_arg_entry_attribute)
  add_attribute
val parse_del_context_update = gen_add_del_attr_context_update
  (gen_parse_del_arg_entries_attribute #> Scan.lift) (Scan.lift parse_del_arg_entry_attribute)
  del_attribute
val parse_config_context_update = Scan.lift (PU.position parse_config_arg_entries)
  :|-- (fn parsed => Scan.depend (AU.attribute_map_context (config_attribute parsed)
    #> rpair () #> Scan.succeed))
end

val parse_entry_context_update =
  Scan.optional (Scan.lift PM.parse_key) (PM.key PM.add)
  :|-- (fn PM.add _ => parse_add_context_update | PM.del _ => parse_del_context_update
    | PM.config _ => parse_config_context_update)
val parse_context_update = Parse.and_list1' parse_entry_context_update >> K ()

(* action data *)
fun lookup_each_focused_data lookup x focus = GFocus.focused_data focus x
  |> maps (apsnd lookup #> (fn (i, datas) => List.map (snd #> pair (GFocus.single i)) datas))

fun tac_data_from_data meta tac data = {
  meta = meta,
  empty_action = PD.get_empty_action data,
  result_action = Result_Action.hom_changed_goals_action (PD.get_updates data) (PD.get_mk_cud data),
  presultsq = PD.get_presultsq data,
  tac = tac (PD.get_normalisers data) (PD.get_unifier data) (PD.get_mk_meta data) (PD.get_rule data)}

fun paction_data_from_data exn meta tac = tac_data_from_data meta tac
  #> Tac.paction_data_from_data exn

fun cons_action exn meta tac = paction_data_from_data exn meta tac #> Z.PAction.cons_action

fun cons_nth_action exn meta tac ctxt i data =
  let val meta = AMeta.metadata (
    Zippy_Identifier.suffix_name NONE (string_of_int i) (ACMeta.Id.getter meta),
    Lazy.lazy (fn _ => Pretty.breaks [
        Pretty.str (ACMeta.Descr.getter meta |> Lazy.force),
        Pretty.block [Pretty.str "Rule: ", Thm.pretty_thm ctxt (PD.get_rule data)]
      ] |> Pretty.block |> Pretty.string_of))
  in cons_action exn meta tac data end

local open MU.SC
in
fun cons_action_cluster exn meta tac ctxt =
  map_index (Library.uncurry (fn i => apsnd (fn data => fn focus =>
    cons_nth_action exn meta tac ctxt i data focus >>> Up4.morph)))
  #> Node.cons3 exn meta
end
end
end
end