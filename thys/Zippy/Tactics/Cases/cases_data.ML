(*  Title:      Zippy/cases_data.ML
    Author:     Kevin Kappelmann
*)
@{parse_entries (sig) PARSE_CASES_DATA_MODE [add, del, config]}
@{parse_entries (sig) PARSE_CASES_DATA [insts, rule, simp, facts, match]}
@{parse_entries (sig) PARSE_CASES_DATA_CONFIG [simp, match]}
@{parse_entries (sig) PARSE_CASES_DATA_INSTS_MODES [fix, pat, pred]}

signature CASES_DATA_ARGS =
sig
  structure PM : PARSE_CASES_DATA_MODE
  structure PD : PARSE_CASES_DATA
  structure PDC : PARSE_CASES_DATA_CONFIG
  structure PIM : PARSE_CASES_DATA_INSTS_MODES

  val PDC_entries_from_PD_entries : ('a, 'b, 'c, 'd, 'e) PD.entries -> ('c, 'e) PDC.entries

  type insts = (term option list, (term * term list) option list, (term -> bool) option list)
    PIM.entry
  val insts_ord : insts ord
  val pretty_insts : Proof.context -> insts -> Pretty.T

  type match = term Binders.binders -> Proof.context -> term * term -> Envir.env -> bool
  type data = (insts, thm option, bool, thm list, match) PD.entries
  val data_ord : data ord
  val eq_data : data * data -> bool
  val pretty_data : Proof.context -> data -> Pretty.T
  val map_data_thms : (thm -> thm) -> data -> data
  val transfer_data : theory -> data -> data

  type config = (bool, match) PDC.entries

  val parse_inst_fix : term option context_parser
  val parse_inst_pat : (term * term list) option context_parser
  val parse_inst_pred : ML_Code_Util.code option parser

  val data_parsers : (unit context_parser ->
      (term option list, (term * term list) option list, ML_Code_Util.code option list) PIM.entry
        context_parser,
    thm context_parser, bool parser, thm list context_parser, ML_Code_Util.code parser) PD.entries

  val print_insts_fix : term option list -> string
  val print_insts_pat : (term * term list) option list -> string
  val code_PIM_entry : ('a -> ML_Code_Util.code) -> ('b -> ML_Code_Util.code) ->
    ('c -> ML_Code_Util.code) -> ('a, 'b, 'c) PIM.entry -> ML_Code_Util.code
  val code_insts_pred : ML_Code_Util.code option list -> ML_Code_Util.code
  val code_insts :
    (term option list, (term * term list) option list, ML_Code_Util.code option list) PIM.entry ->
    ML_Code_Util.code
end

structure Cases_Data_Args : CASES_DATA_ARGS =
struct

structure PU = Parse_Util
structure Show = SpecCheck_Show
structure MCU = ML_Code_Util

@{parse_entries (struct) PM [add, del, config]}
@{parse_entries (struct) PD [insts, rule, simp, facts, match]}
@{parse_entries (struct) PDC [simp, match]}
@{parse_entries (struct) PIM [fix, pat, pred]}

fun PDC_entries_from_PD_entries {simp, match,...} = {simp = simp, match = match}

type insts = (term option list, (term * term list) option list, (term -> bool) option list)
  PIM.entry

fun term_ord tp = if Term_Util.are_term_variants tp then EQUAL else Term_Ord.fast_term_ord tp

fun insts_ord (PIM.fix x, PIM.fix y) = list_ord (option_ord term_ord) (x, y)
  | insts_ord (PIM.fix _, _) = LESS
  | insts_ord (_, PIM.fix _) = GREATER
  | insts_ord (PIM.pat x, PIM.pat y) =
      list_ord (option_ord (prod_ord term_ord (list_ord term_ord))) (x, y)
  | insts_ord (PIM.pat _, _) = LESS
  | insts_ord (_, PIM.pat _) = GREATER
  | insts_ord (PIM.pred x, PIM.pred y) = list_ord (option_ord (K EQUAL)) (x, y)
fun pretty_insts _ (PIM.pred x) = Show.list (Show.option (K (Pretty.str "<predicate>"))) x
  | pretty_insts ctxt (PIM.pat x) =
      Show.list (Show.option (Show.zip (Show.term ctxt) (Show.list (Show.term ctxt)))) x
  | pretty_insts ctxt (PIM.fix x) = Show.list (Show.option (Show.term ctxt)) x

type match = term Binders.binders -> Proof.context -> term * term -> Envir.env -> bool
type data = (insts, thm option, bool, thm list, match) PD.entries

val data_ord = option_ord Thm.thm_ord o apply2 PD.get_rule
  ||| insts_ord o apply2 PD.get_insts
  ||| list_ord Thm.thm_ord o apply2 PD.get_facts
  ||| bool_ord o apply2 PD.get_simp
val eq_data = is_equal o data_ord
fun pretty_data ctxt data = Show.record [
  ("rule", Show.option (Show.thm ctxt) (PD.get_rule data)),
  ("insts", pretty_insts ctxt (PD.get_insts data)),
  ("facts", Show.list (Show.thm ctxt) (PD.get_facts data)),
  ("simp", Show.bool (PD.get_simp data))
]
fun map_data_thms f = PD.map_rule (Option.map f) #> PD.map_facts (map f)
fun transfer_data thy = map_data_thms (Thm.transfer thy)

type config = (bool, match) PDC.entries

val parse_inst_pred = Parse.maybe ML_Code_Util.parse_code
fun maybe' scan = Scan.lift Parse.underscore >> K NONE || scan >> SOME
val parse_inst_pat = maybe' (PU.term_pattern >> rpair []
  || PU.parens' (Parse.!!!!
    (PU.term_pattern --| Scan.lift (Parse.$$$ ",") -- Scan.repeat1 PU.term_pattern)))
val parse_inst_fix = maybe' PU.term
fun parse_insts unless =
  Scan.lift (Scan.option (Args.parens PIM.parse_key))
  :|-- (fn opt_key =>
    let fun repeat_unless parse = (if is_none opt_key then Scan.repeat else Scan.repeat1)
      (Scan.unless unless parse)
    in case \<^if_none>\<open>PIM.key PIM.fix\<close> opt_key of
      PIM.fix _ => repeat_unless parse_inst_fix >> PIM.fix
    | PIM.pat _ => repeat_unless parse_inst_pat >> PIM.pat
    | PIM.pred _ => repeat_unless (Scan.lift parse_inst_pred) >> PIM.pred
    end)

val data_parsers = {
  insts = SOME parse_insts,
  rule = SOME PU.thm,
  simp = SOME PU.bool,
  facts = SOME (PU.nonempty_thms (K "must provide at least one fact")),
  match = SOME (PU.nonempty_code (K "match selector must not be empty"))
}

local open ML_Syntax
in
val print_insts_fix = print_list (print_option print_term)
val print_insts_pat = print_list (print_option (print_pair print_term (print_list print_term)))
end

fun code_PIM_op operation = MCU.flat_read ["Cases_Data_Args.PIM.", operation]
fun code_PIM_entry code_fix _ _ (PIM.fix x) = code_PIM_op "fix" @ MCU.atomic (code_fix x)
  | code_PIM_entry _ code_pat _ (PIM.pat x) = code_PIM_op "pat" @ MCU.atomic (code_pat x)
  | code_PIM_entry _ _ code_pred (PIM.pred x) = code_PIM_op "pred" @ MCU.atomic (code_pred x)
val code_insts_pred = List.map (Option.map MCU.atomic #> MCU.option) #> MCU.list
val code_insts = code_PIM_entry (print_insts_fix #> MCU.read) (print_insts_pat #> MCU.read)
  code_insts_pred
end

signature CASES_DATA_ARGS_TACTIC =
sig
  val cases_tac :
    (bool -> thm option -> term option list -> thm list -> Proof.context -> int -> tactic) ->
    Cases_Data_Args.data -> Proof.context -> int -> tactic
end

functor Cases_Data_Args_Tactic(Cases : CASES_TACTIC) : CASES_DATA_ARGS_TACTIC =
struct
open Cases_Data_Args
fun cases_tac cases_fixed_tac args =
  let fun app_args tac insts = tac (PD.get_simp args) (PD.get_rule args) insts (PD.get_facts args)
  in case PD.get_insts args of
    PIM.pred p => app_args Cases.cases_find_insts_tac p
  | PIM.pat p => app_args (fn x => Cases.cases_pattern_tac x (PD.get_match args)) p
  | PIM.fix p => app_args cases_fixed_tac p
  end
end

signature CASES_DATA =
sig
  include HAS_LOGGER

  structure Config_Data : GENERIC_DATA
  where type T = Cases_Data_Args.config

  val get_config : Context.generic -> Config_Data.T
  val map_config : (Config_Data.T -> Config_Data.T) -> Context.generic -> Context.generic

  val get_simp : Context.generic -> bool
  val map_simp : (bool -> bool) -> Context.generic -> Context.generic

  val get_match : Context.generic -> Cases_Data_Args.match
  val map_match : (Cases_Data_Args.match -> Cases_Data_Args.match) ->
    Context.generic -> Context.generic

  structure Data : GENERIC_DATA
  where type T = Cases_Data_Args.data Ord_List.T

  val insert : Cases_Data_Args.data -> Context.generic -> Context.generic
  val insert_declaration_attribute : Cases_Data_Args.data -> thm -> Context.generic -> Context.generic
  val insert_declaration_attribute_context_defaults : Cases_Data_Args.data -> thm ->
    Context.generic -> Context.generic

  val delete : Cases_Data_Args.data -> Context.generic -> Context.generic
  val delete_declaration_attribute : Cases_Data_Args.data -> thm -> Context.generic -> Context.generic
  val delete_declaration_attribute_context_defaults : Cases_Data_Args.data -> thm ->
    Context.generic -> Context.generic

  val binding : Binding.binding
  val parse_arg_entries_attribute : ((term option list, (term * term list) option list,
      ML_Code_Util.code option list) Cases_Data_Args.PIM.entry,
    thm, bool, thm list, ML_Code_Util.code) Cases_Data_Args.PD.entries context_parser
  val parse_arg_entries : ((term option list, (term * term list) option list,
      ML_Code_Util.code option list) Cases_Data_Args.PIM.entry,
    thm, bool, thm list, ML_Code_Util.code) Cases_Data_Args.PD.entries context_parser

  structure Facts_Data_Internal : GENERIC_DATA

  val add_attribute : ((term option list, (term * term list) option list,
        ML_Code_Util.code option list) Cases_Data_Args.PIM.entry,
      thm, bool, thm list, ML_Code_Util.code) Cases_Data_Args.PD.entries * Position.T -> attribute
  val del_attribute : ((term option list, (term * term list) option list,
        ML_Code_Util.code option list) Cases_Data_Args.PIM.entry,
      thm, bool, thm list, ML_Code_Util.code) Cases_Data_Args.PD.entries * Position.T -> attribute

  val parse_config_arg_entries : (bool, ML_Code_Util.code) Cases_Data_Args.PDC.entries parser
  val config_attribute : ((bool, ML_Code_Util.code) Cases_Data_Args.PDC.entries * Position.T) ->
    attribute

  val parse_attribute : attribute context_parser
  val setup_attribute : string option -> local_theory -> local_theory

  val parse_add_context_update : unit context_parser
  val parse_del_context_update : unit context_parser
  val parse_config_context_update : unit context_parser
  val parse_entry_context_update : unit context_parser
  val parse_context_update : unit context_parser
end

functor Cases_Data(
    structure FI : FUNCTOR_INSTANCE_BASE
    val init_args : Cases_Data_Args.config
    val parent_logger : Logger.logger_binding
  ) : CASES_DATA =
struct

val logger = Logger.setup_new_logger parent_logger "Cases_Data"
structure FI = Functor_Instance(FI)

open Cases_Data_Args
structure AU = ML_Attribute_Util
structure MCU = ML_Code_Util
structure PU = Parse_Util

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

structure Data = Generic_Data(
  type T = data Ord_List.T
  val empty = []
  val merge = Ord_List.merge data_ord)

fun insert args context = context |>
  let val args = map_data_thms Thm.trim_context args
  in
    Data.map (fn data => if Ord_List.member data_ord data args
      then let val ctxt = Context.proof_of context
        in
          (@{log Logger.WARN} ctxt (fn _ => Pretty.breaks [
              Pretty.str "Similar cases data already added. Skipping insertion of",
              pretty_data ctxt args
            ] |> Pretty.block |> Pretty.string_of);
          data)
        end
      else Ord_List.insert data_ord args data)
  end

val prepare_attr_rule = Option.filter (Thm.is_dummy #> not)
fun with_prepared_attr_rule f args thm = f (PD.map_rule_safe (K (SOME (prepare_attr_rule thm))) args)
val insert_declaration_attribute = with_prepared_attr_rule insert

fun data_context_defaults args = get_config
  #> (fn cargs => [PD.simp (PDC.get_simp cargs), PD.match (PDC.get_match cargs)])
  #> PD.entries_from_entry_list
  #> PD.merge_entries args

fun with_context_defaults f args thm context = f (data_context_defaults args context) thm context
val insert_declaration_attribute_context_defaults = with_context_defaults insert_declaration_attribute

fun delete args context = Data.map (fn data => if Ord_List.member data_ord data args
  then Ord_List.remove data_ord args data
  else let val ctxt = (Context.proof_of context)
    in
      (@{log Logger.WARN} ctxt (fn _ => Pretty.breaks [
          Pretty.str "Cases data", pretty_data ctxt args, Pretty.str "not found. Skipping deletion."
        ] |> Pretty.block |> Pretty.string_of);
      data)
    end) context
val delete_declaration_attribute = with_prepared_attr_rule delete
val delete_declaration_attribute_context_defaults = with_context_defaults delete_declaration_attribute

val binding = Binding.make (FI.prefix_id "cases", FI.pos)

val filter_arg_entries =
  let
    fun filter entries = case (PD.get_insts entries, PD.get_match_safe entries) of
      (PIM.pat _, SOME _) => false | _ => true
    val filter_msg = "Match must only be passed when using patterns for instantiations."
  in PU.filter filter (K (PU.fail (K filter_msg))) end

val parse_insts_opt_args_sep = Scan.lift (Args.$$$ "use")

fun gen_parse_key except = Parse_Key_Value.parse_key
  (PD.keys |> subtract (op =) except |> map PD.key_to_string)
  (Option.composePartial (Option.filter (member (op =) except #> not), PD.key_from_string))

fun gen_parse_arg_entries parse_rule =
  let
    val parsers = data_parsers
    val parse_value = PD.parse_entry Scan.fail
      (if parse_rule then PD.get_rule  parsers else Scan.fail)
      (Scan.lift (PD.get_simp parsers)) (PD.get_facts parsers) (Scan.lift (PD.get_match parsers))
    val parse_key = gen_parse_key (PD.key PD.insts :: (if parse_rule then [] else [PD.key PD.rule]))
    val parse_entry = Parse_Key_Value.parse_entry' (Scan.lift parse_key)
      (K (Scan.lift (Parse.$$$ ":"))) parse_value
    val unless = (parse_insts_opt_args_sep >> K ()) || (parse_entry >> K ())
    val default_entries = PD.entries_from_entry_list [PD.facts []]
  in
    Scan.optional (PD.get_insts data_parsers unless) (PIM.fix [])
    -- (Scan.option parse_insts_opt_args_sep
    :|-- (fn use => PD.parse_entries_required' (if is_some use then Scan.repeat1 else Scan.repeat)
      true [] parse_entry default_entries))
    >> (fn (insts, entries) => PD.map_insts_safe (K (SOME insts)) entries)
    |> filter_arg_entries
  end
val parse_arg_entries_attribute = gen_parse_arg_entries false
val parse_arg_entries = gen_parse_arg_entries true

fun Args_substructure_op substructure operation =
  MCU.flat_read ["Cases_Data_Args.", substructure, ".", operation]

structure Facts_Data_Internal = Generic_Data(
  type T = thm list
  val empty = []
  val merge = fst)

val code_bool = Value.print_bool #> MCU.read

fun gen_attribute operation (entries, pos) (context, thm) =
  let
    val code_PD_op = Args_substructure_op "PD"
    val code_from_key = code_PD_op o PD.key_to_string
    val context = Facts_Data_Internal.put (PD.get_facts entries) context
    fun code_from_entry (PD.simp b) = code_bool b
      | code_from_entry (PD.insts insts) = code_insts insts
      | code_from_entry (PD.facts _) = FI.code_struct_op "Facts_Data_Internal.get"
      | code_from_entry (PD.match c) = c
      | code_from_entry (PD.rule _) = error "rule may not be passed to cases attribute"
    val code_entries = PD.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code =
      let val [thm, context, get_facts] = map MCU.internal_name ["thm", "context", "get_facts"]
      in
        MCU.reads ["fn", thm, "=> fn", context, "=>"] @ FI.code_struct_op operation @
          MCU.atomic (code_PD_op "entries_from_entry_list" @ code_entries @
            MCU.read "|>" @ code_PD_op "map_facts" @
              MCU.atomic (MCU.reads ["fn", get_facts, "=>", get_facts, context])) @
          MCU.reads [thm, context]
      end
  in ML_Attribute.run_declaration_attribute (code, pos) (context, thm) end

val add_attribute = gen_attribute "insert_declaration_attribute_context_defaults"
val del_attribute = gen_attribute "delete_declaration_attribute_context_defaults"

val parse_config_arg_entries =
  let
    val parsers = PDC_entries_from_PD_entries data_parsers
    val parse_value = PDC.parse_entry (PDC.get_simp parsers) (PDC.get_match parsers)
    val parse_entry = Parse_Key_Value.parse_entry PDC.parse_key (K (Parse.$$$ ":")) parse_value
    val default_entries = PDC.empty_entries ()
  in PDC.parse_entries_required Scan.repeat1 true [] parse_entry default_entries end

fun config_attribute (entries, pos) =
  let
    val code_PDC_op = Args_substructure_op "PDC"
    val code_from_key = code_PDC_op o PDC.key_to_string
    fun code_from_entry (PDC.simp b) = code_bool b
      | code_from_entry (PDC.match c) = c
    val code_entries = PDC.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code =
      FI.code_struct_op "map_config" @ MCU.atomic (code_PDC_op "merge_entries" @
      MCU.atomic (code_PDC_op "entries_from_entry_list" @ code_entries))
  in ML_Attribute.run_map_context (code, pos) end

val parse_entries =
  let
    val parse_value = PM.parse_entry parse_arg_entries_attribute parse_arg_entries_attribute
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
  || PU.position' parse_arg_entries_attribute >> add_attribute

val setup_attribute = Attrib.local_setup binding (Parse.!!!! parse_attribute) o
  the_default ("configure cases data " ^ enclose "(" ")" FI.long_name)

local
  fun run_attr attr (context, opt_thm) = (case opt_thm of
      NONE => AU.attribute_map_context attr context
    | SOME thm => AU.apply_attribute attr (context, thm) |> fst)
    |> rpair () |> Scan.succeed
  fun gen_add_del_attr_context_update attr = PU.position' parse_arg_entries
    :|-- (fn (entries, pos) => Scan.depend (fn context => run_attr
      (attr (PD.map_rule_safe (K NONE) entries, pos)) (context, PD.get_rule_safe entries)))
in
val parse_add_context_update = gen_add_del_attr_context_update add_attribute
val parse_del_context_update = gen_add_del_attr_context_update del_attribute
val parse_config_context_update = Scan.lift (PU.position parse_config_arg_entries)
  :|-- (fn parsed => Scan.depend (fn context => run_attr (config_attribute parsed) (context, NONE)))
end

val parse_entry_context_update =
  Scan.optional (Scan.lift PM.parse_key) (PM.key PM.add)
  :|-- (fn PM.add _ => parse_add_context_update | PM.del _ => parse_del_context_update
    | PM.config _ => parse_config_context_update)
val parse_context_update = Parse.and_list1' parse_entry_context_update >> K ()

end