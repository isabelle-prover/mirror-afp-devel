(*  Title:      Zippy/induction_data.ML
    Author:     Kevin Kappelmann
*)
@{parse_entries (sig) PARSE_INDUCTION_DATA_MODE [add, del, config]}
@{parse_entries (sig) PARSE_INDUCTION_DATA [insts, rule, arbitrary, taking, simp, facts, match]}
@{parse_entries (sig) PARSE_INDUCTION_DATA_CONFIG [simp, match]}

signature INDUCTION_DATA_ARGS =
sig
  structure PM : PARSE_INDUCTION_DATA_MODE
  structure PD : PARSE_INDUCTION_DATA
  structure PDC : PARSE_INDUCTION_DATA_CONFIG

  val PDC_entries_from_PD_entries : ('a, 'b, 'c, 'd, 'e, 'f, 'g) PD.entries -> ('e, 'g) PDC.entries

  type insts = (Induction_Tactic_Base.def_inst option list, (term * term list) option list,
    (Term_Zipper.T -> bool) option list) Cases_Data_Args.PIM.entry
  val insts_ord : insts ord
  val pretty_insts : Proof.context -> insts -> Pretty.T

  type arbitrary = ((string * typ) list, term list * term list, Term_Zipper.T -> bool)
    Cases_Data_Args.PIM.entry
  val arbitrary_ord : arbitrary ord
  val pretty_arbitrary : Proof.context -> arbitrary -> Pretty.T

  type taking = term option list
  val taking_ord : taking ord
  val pretty_taking : Proof.context -> taking -> Pretty.T

  type data = (insts, thm option, arbitrary, taking, bool, thm list, Cases_Data_Args.match)
    PD.entries
  val data_ord : data ord
  val eq_data : data * data -> bool
  val pretty_data : Proof.context -> data -> Pretty.T
  val map_data_thms : (thm -> thm) -> data -> data
  val transfer_data : theory -> data -> data

  type config = (bool, Cases_Data_Args.match) PDC.entries

  val data_parsers : (unit context_parser -> (Induction_Tactic_Base.def_inst option list,
      (term * term list) option list, ML_Code_Util.code option list)
      Cases_Data_Args.PIM.entry context_parser,
    thm context_parser,
    unit context_parser ->
      ((string * typ) list, term list * term list, ML_Code_Util.code)
        Cases_Data_Args.PIM.entry context_parser,
    unit context_parser -> taking context_parser,
    bool parser, thm list context_parser, ML_Code_Util.code parser) PD.entries

  val print_def_insts : Induction_Tactic_Base.def_inst option list -> string
  val print_arbitrary_fix : (string * typ) list -> string
  val print_arbitrary_pat : term list * term list -> string

  val code_insts : (Induction_Tactic_Base.def_inst option list, (term * term list) option list,
      ML_Code_Util.code option list) Cases_Data_Args.PIM.entry -> ML_Code_Util.code
  val code_arbitrary : ((string * typ) list, term list * term list, ML_Code_Util.code)
      Cases_Data_Args.PIM.entry -> ML_Code_Util.code
  val code_taking : taking -> ML_Code_Util.code
end

structure Induction_Data_Args : INDUCTION_DATA_ARGS =
struct

structure PU = Parse_Util
structure PIM = Cases_Data_Args.PIM
structure Show = SpecCheck_Show
structure MCU = ML_Code_Util
structure CDA = Cases_Data_Args
structure IHB = Induction_Tactic_Base

@{parse_entries (struct) PM [add, del, config]}
@{parse_entries (struct) PD [insts, rule, arbitrary, taking, simp, facts, match]}
@{parse_entries (struct) PDC [simp, match]}

fun PDC_entries_from_PD_entries {simp, match,...} = {simp = simp, match = match}

type insts = (IHB.def_inst option list, (term * term list) option list, (Term_Zipper.T -> bool) option list)
  PIM.entry

fun term_ord tp = if Term_Util.are_term_variants tp then EQUAL else Term_Ord.fast_term_ord tp
val pred_ord = K EQUAL
val pretty_pred = Pretty.str "<predicate>"

fun insts_ord (PIM.fix x, PIM.fix y) = list_ord (option_ord (IHB.def_inst_ord term_ord)) (x, y)
  | insts_ord (PIM.fix _, _) = LESS
  | insts_ord (_, PIM.fix _) = GREATER
  | insts_ord (PIM.pat x, PIM.pat y) =
      list_ord (option_ord (prod_ord term_ord (list_ord term_ord))) (x, y)
  | insts_ord (PIM.pat _, _) = LESS
  | insts_ord (_, PIM.pat _) = GREATER
  | insts_ord (PIM.pred x, PIM.pred y) = list_ord (option_ord pred_ord) (x, y)
fun pretty_insts _ (PIM.pred x) = Show.list (Show.option (K pretty_pred)) x
  | pretty_insts ctxt (PIM.pat x) =
      Show.list (Show.option (Show.zip (Show.term ctxt) (Show.list (Show.term ctxt)))) x
  | pretty_insts ctxt (PIM.fix x) = Show.list (Show.option (IHB.pretty_def_inst ctxt)) x

type arbitrary = ((string * typ) list, term list * term list, Term_Zipper.T -> bool) CDA.PIM.entry
fun arbitrary_ord (PIM.fix x, PIM.fix y) =
      list_ord (prod_ord fast_string_ord Term_Ord.typ_ord) (x, y)
  | arbitrary_ord (PIM.fix _, _) = LESS
  | arbitrary_ord (_, PIM.fix _) = GREATER
  | arbitrary_ord (PIM.pat x, PIM.pat y) = let val patterns_ord = list_ord term_ord
     in prod_ord patterns_ord patterns_ord (x, y) end
  | arbitrary_ord (PIM.pat _, _) = LESS
  | arbitrary_ord (_, PIM.pat _) = GREATER
  | arbitrary_ord (PIM.pred x, PIM.pred y) = pred_ord (x, y)
fun pretty_arbitrary _ (PIM.pred _) = pretty_pred
  | pretty_arbitrary ctxt (PIM.pat x) = let val pretty_patterns = Show.list (Show.term ctxt)
     in Show.zip pretty_patterns pretty_patterns x end
  | pretty_arbitrary ctxt (PIM.fix x) = Show.list (Show.zip Show.string (Show.typ ctxt)) x

type taking = term option list
val taking_ord = list_ord (option_ord Term_Ord.fast_term_ord)
fun pretty_taking ctxt = Show.list (Show.option (Show.term ctxt))

type data = (insts, thm option, arbitrary, taking, bool, thm list, CDA.match) PD.entries

val data_ord = option_ord Thm.thm_ord o apply2 PD.get_rule
  ||| insts_ord o apply2 PD.get_insts
  ||| arbitrary_ord o apply2 PD.get_arbitrary
  ||| taking_ord o apply2 PD.get_taking
  ||| list_ord Thm.thm_ord o apply2 PD.get_facts
  ||| bool_ord o apply2 PD.get_simp
val eq_data = is_equal o data_ord
fun pretty_data ctxt data = Show.record [
  ("rule", Show.option (Show.thm ctxt) (PD.get_rule data)),
  ("insts", pretty_insts ctxt (PD.get_insts data)),
  ("arbitrary", pretty_arbitrary ctxt (PD.get_arbitrary data)),
  ("taking", pretty_taking ctxt (PD.get_taking data)),
  ("facts", Show.list (Show.thm ctxt) (PD.get_facts data)),
  ("simp", Show.bool (PD.get_simp data))
]
fun map_data_thms f = PD.map_rule (Option.map f) #> PD.map_facts (map f)
fun transfer_data thy = map_data_thms (Thm.transfer thy)

type config = (bool, CDA.match) PDC.entries

local fun maybe' scan = Scan.lift Parse.underscore >> K NONE || scan >> SOME
in
val parse_def_inst =
  (Scan.lift (Args.binding --| PU.eq) >> SOME) -- PU.term >> (IHB.with_eq #> SOME)
  || PU.parens' (Parse.!!!! PU.term) >> (curry IHB.without_eq NONE #> SOME)
  || maybe' PU.term >> Option.map (curry IHB.with_eq NONE)
end
fun parse_insts unless =
  Scan.lift (Scan.option (Args.parens PIM.parse_key))
  :|-- (fn opt_key =>
    let fun repeat_unless parse = (if is_none opt_key then Scan.repeat else Scan.repeat1)
      (Scan.unless unless parse)
    in case \<^if_none>\<open>PIM.key PIM.fix\<close> opt_key of
      PIM.fix _ => repeat_unless parse_def_inst >> PIM.fix
    | PIM.pat _ => repeat_unless CDA.parse_inst_pat >> PIM.pat
    | PIM.pred _ => repeat_unless (Scan.lift CDA.parse_inst_pred) >> PIM.pred
    end)

(* (string * typ) list, term list * term list, term -> bool *)
val parse_free = PU.term
  :|-- (fn t => Parse.!!!! (Scan.depend (fn context => Scan.succeed (context, Term.dest_Free t)
    handle TERM _ => PU.fail (fn _ => Pretty.block [
        Pretty.str "Expected a free variable but got ", Show.term (Context.proof_of context) t
      ] |> Pretty.string_of))))
fun parse_arbitrary_patterns repeat =
  repeat PU.term_pattern >> rpair []
  || PU.parens' (Parse.!!!! (let val parse_pats = Scan.repeat1 PU.term_pattern
    in parse_pats --| Scan.lift (Parse.$$$ ",") -- parse_pats end))

fun parse_arbitrary unless =
  Scan.lift (Scan.option (Args.parens PIM.parse_key))
  :|-- (fn opt_key =>
    let fun repeat_unless parse = (if is_none opt_key then Scan.repeat else Scan.repeat1)
      (Scan.unless unless parse)
    in case \<^if_none>\<open>PIM.key PIM.fix\<close> opt_key of
      PIM.fix _ => repeat_unless parse_free >> PIM.fix
    | PIM.pat _ => parse_arbitrary_patterns repeat_unless >> PIM.pat
    | PIM.pred _ => Scan.lift (ML_Code_Util.parse_code >> PIM.pred)
    end)

val data_parsers = {
  insts = SOME parse_insts,
  rule = SOME PU.thm,
  arbitrary = SOME parse_arbitrary,
  taking = SOME (fn unless => Scan.repeat1 (Scan.unless unless CDA.parse_inst_fix)),
  simp = SOME PU.bool,
  facts = SOME (PU.nonempty_thms (K "must provide at least one fact")),
  match = SOME (PU.nonempty_code (K "match selector must not be empty"))
}

local open ML_Syntax
in
val print_def_insts = print_list (print_option IHB.print_def_inst)
val print_arbitrary_fix = print_list (print_pair print_string print_typ)
val print_arbitrary_pat = let val print_pat = print_list print_term
  in print_pair print_pat print_pat end
end

val code_insts = CDA.code_PIM_entry (print_def_insts #> MCU.read) (CDA.print_insts_pat #> MCU.read)
  CDA.code_insts_pred
val code_arbitrary = CDA.code_PIM_entry (print_arbitrary_fix #> MCU.read)
  (print_arbitrary_pat #> MCU.read)
  I
val code_taking = CDA.print_insts_fix #> MCU.read
end

signature INDUCTION_DATA_ARGS_TACTIC =
sig
  val induct_tac : bool -> Induction_Data_Args.data -> Proof.context -> int -> tactic
end

functor Induction_Data_Args_Tactic(Induct : INDUCTION_TACTIC) : INDUCTION_DATA_ARGS_TACTIC =
struct
open Cases_Data_Args Induction_Data_Args
local fun induct_fixed_tac close_trivial simp opt_rule insts arbitrary =
  Induct.induct_tac close_trivial simp (Option.map single opt_rule) [insts] [arbitrary]
in
fun induct_tac close_trivial args ctxt i st = Seq.make (fn _ => PRIMSEQ (fn st =>
  let fun app_args tac insts arbitrary = tac close_trivial (PD.get_simp args) (PD.get_rule args)
    insts arbitrary (PD.get_taking args) (PD.get_facts args) ctxt i st
  in case (PD.get_insts args, PD.get_arbitrary args) of
    (PIM.fix insts, PIM.fix arbitrary) => app_args induct_fixed_tac insts arbitrary
  | (PIM.pat insts, PIM.pat arbitrary) => app_args
      (fn x => fn y => Induct.induct_pattern_tac x y (PD.get_match args)) insts arbitrary
  | (PIM.pred insts, PIM.pred arbitrary) => app_args Induct.induct_find_tac insts arbitrary
  | (PIM.fix insts, arbitrary) =>
      let
        val pred = case arbitrary of
            PIM.pat arbitrary =>
              Induct.prepare_patterns (PD.get_match args) NONE (SOME arbitrary) ctxt i st |> snd
          | PIM.pred arbitrary => arbitrary
        val arbitrary = Induct.prepare_preds NONE (SOME pred) ctxt i st |> snd
      in app_args induct_fixed_tac insts arbitrary end
  | (insts, PIM.fix arbitrary) =>
      let
        val pred = case insts of
            PIM.pat insts =>
              Induct.prepare_patterns (PD.get_match args) (SOME insts) NONE ctxt i st |> fst
          | PIM.pred insts => insts
        val instsq = Induct.prepare_preds (SOME pred) NONE ctxt i st |> fst
      in Seq.maps (fn insts => app_args induct_fixed_tac insts arbitrary) instsq end
  | (PIM.pred insts, PIM.pat arbitrary) =>
      Induct.prepare_patterns (PD.get_match args) NONE (SOME arbitrary) ctxt i st
      |> snd |> app_args Induct.induct_find_tac insts
  | (PIM.pat insts, PIM.pred arbitrary) =>
      Induct.prepare_patterns (PD.get_match args) (SOME insts) NONE ctxt i st
      |> fst |> (fn insts => app_args Induct.induct_find_tac insts arbitrary)
  end) st |> Seq.pull)
end
end

signature INDUCTION_DATA =
sig
  include HAS_LOGGER
  structure FI : FUNCTOR_INSTANCE

  structure Config_Data : GENERIC_DATA
  where type T = Induction_Data_Args.config

  val get_config : Context.generic -> Config_Data.T
  val map_config : (Config_Data.T -> Config_Data.T) -> Context.generic -> Context.generic

  val get_simp : Context.generic -> bool
  val map_simp : (bool -> bool) -> Context.generic -> Context.generic

  val get_match : Context.generic -> Cases_Data_Args.match
  val map_match : (Cases_Data_Args.match -> Cases_Data_Args.match) ->
    Context.generic -> Context.generic

  structure Data : GENERIC_DATA
  where type T = Induction_Data_Args.data Ord_List.T

  val insert : Induction_Data_Args.data -> Context.generic -> Context.generic
  val insert_declaration_attribute : Induction_Data_Args.data -> thm -> Context.generic -> Context.generic
  val insert_declaration_attribute_context_defaults : Induction_Data_Args.data -> thm ->
    Context.generic -> Context.generic

  val delete : Induction_Data_Args.data -> Context.generic -> Context.generic
  val delete_declaration_attribute : Induction_Data_Args.data -> thm -> Context.generic -> Context.generic
  val delete_declaration_attribute_context_defaults : Induction_Data_Args.data -> thm ->
    Context.generic -> Context.generic

  val binding : Binding.binding
  val parse_arg_entries_attribute : ((Induction_Tactic_Base.def_inst option list,
      (term * term list) option list, ML_Code_Util.code option list) Cases_Data_Args.PIM.entry,
    thm, ((string * typ) list, term list * term list, ML_Code_Util.code) Cases_Data_Args.PIM.entry,
    Induction_Data_Args.taking, bool, thm list, ML_Code_Util.code)
    Induction_Data_Args.PD.entries context_parser

  structure Facts_Data_Internal : GENERIC_DATA

  val add_attribute : ((Induction_Tactic_Base.def_inst option list,
        (term * term list) option list, ML_Code_Util.code option list) Cases_Data_Args.PIM.entry,
      thm, ((string * typ) list, term list * term list, ML_Code_Util.code) Cases_Data_Args.PIM.entry,
      Induction_Data_Args.taking, bool, thm list, ML_Code_Util.code)
      Induction_Data_Args.PD.entries * Position.T -> attribute
  val del_attribute : ((Induction_Tactic_Base.def_inst option list,
        (term * term list) option list, ML_Code_Util.code option list) Cases_Data_Args.PIM.entry,
      thm, ((string * typ) list, term list * term list, ML_Code_Util.code) Cases_Data_Args.PIM.entry,
      Induction_Data_Args.taking, bool, thm list, ML_Code_Util.code)
      Induction_Data_Args.PD.entries * Position.T -> attribute

  val parse_config_arg_entries : (bool, ML_Code_Util.code) Induction_Data_Args.PDC.entries parser
  val config_attribute : ((bool, ML_Code_Util.code) Induction_Data_Args.PDC.entries * Position.T) ->
    attribute

  val parse_attribute : attribute context_parser
  val setup_attribute : string option -> local_theory -> local_theory

  val parse_arg_entries : ((Induction_Tactic_Base.def_inst option list,
      (term * term list) option list, ML_Code_Util.code option list) Cases_Data_Args.PIM.entry,
    thm, ((string * typ) list, term list * term list, ML_Code_Util.code) Cases_Data_Args.PIM.entry,
    Induction_Data_Args.taking, bool, thm list, ML_Code_Util.code)
    Induction_Data_Args.PD.entries context_parser
  val parse_add_context_update : unit context_parser
  val parse_del_context_update : unit context_parser
  val parse_config_context_update : unit context_parser
  val parse_entry_context_update : unit context_parser
  val parse_context_update : unit context_parser
end

functor Induction_Data(
    structure FI : FUNCTOR_INSTANCE_BASE
    val init_args : Induction_Data_Args.config
    val parent_logger : Logger.logger_binding
  ) : INDUCTION_DATA =
struct

val logger = Logger.setup_new_logger parent_logger "Induction_Data"
structure FI = Functor_Instance(FI)

open Induction_Data_Args
structure AU = ML_Attribute_Util
structure MCU = ML_Code_Util
structure PU = Parse_Util
structure PIM = Cases_Data_Args.PIM

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
              Pretty.str "Similar induction data already added. Skipping insertion of",
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
          Pretty.str "Induction data", pretty_data ctxt args, Pretty.str "not found. Skipping deletion."
        ] |> Pretty.block |> Pretty.string_of);
      data)
    end) context
val delete_declaration_attribute = with_prepared_attr_rule delete
val delete_declaration_attribute_context_defaults = with_context_defaults delete_declaration_attribute

val binding = Binding.make (FI.id, FI.pos)

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
    fun parse_value x = PD.parse_entry Scan.fail
      (if parse_rule then PD.get_rule parsers else Scan.fail)
      (PD.get_arbitrary parsers parse_entry_unit) (PD.get_taking parsers parse_entry_unit)
      (Scan.lift (PD.get_simp parsers)) (PD.get_facts parsers) (Scan.lift (PD.get_match parsers)) x
    and parse_key x = gen_parse_key
      (PD.key PD.insts :: (if parse_rule then [] else [PD.key PD.rule])) x
    and parse_entry x = Parse_Key_Value.parse_entry' (Scan.lift parse_key)
      (K (Scan.lift (Parse.$$$ ":"))) parse_value x
    and parse_entry_unit x = (parse_entry >> K ()) x
    val unless = (parse_insts_opt_args_sep >> K ()) || (parse_entry >> K ())
    val default_entries = PD.entries_from_entry_list [PD.facts [], PD.arbitrary (PIM.fix []),
      PD.taking []]
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
  MCU.flat_read ["Induction_Data_Args.", substructure, ".", operation]

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
      | code_from_entry (PD.arbitrary arbitrary) = code_arbitrary arbitrary
      | code_from_entry (PD.taking taking) = code_taking taking
      | code_from_entry (PD.facts _) = FI.code_struct_op "Facts_Data_Internal.get"
      | code_from_entry (PD.match c) = c
      | code_from_entry (PD.rule _) = error "rule may not be passed to induction attribute"
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
  the_default ("configure induction data " ^ enclose "(" ")" FI.long_name)

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