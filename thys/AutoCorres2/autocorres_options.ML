(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

structure AutoCorres_Options = 
struct

(*
 * Option parsing for the autocorres command.
 * These options are documented in the README.md.
 *)

(*
 * Most fields are wrapped in option so that the parser can work out
 * whether they have been specified already.
 *
 *)

datatype unfold_constructor_bind = Always | Never | Selectors
fun unfold_constructor_bind_of_string str =
  case str of
    "Always" => Always
  | "Never" => Never
  | "Selectors" => Selectors
  | _ => error ("unexpected string " ^ quote str ^  ". Expecting (Always | Never | Selectors).")


@{record  \<open>datatype autocorres_options = Autocorres_options of {
  (* Do not lift heaps for these functions. *)
  no_heap_abs : string list option,
  (* In/Out parameter specs for these functions. *)
  in_out_parameters : ((string * ((string * ProgramInfo.parameter_kind) list)) list) option,
  in_out_globals: string list option,

  (* Make split heap on the level of fields not on the complete type *)
  addressable_fields: string list list option,
  ignore_addressable_fields_error: bool option,

  (* Skip heap lifting for the whole program. *)
  skip_heap_abs : bool option,

  (* Skip in-out parameter lifting for the whole program. *)
  skip_io_abs : bool option,

  (* Enable unsigned word abstraction for these functions. *)
  unsigned_word_abs : string list option,
  unsigned_word_abs_known_functions : bool option,

  (* Disable signed word abstraction for these functions. *)
  no_signed_word_abs : string list option,
  no_signed_word_abs_known_functions : bool option,
  (* Skip word abstraction for the whole program. *)
  skip_word_abs : bool option,

  (* Only lift to these monads. *)
  ts_rules : string list option,

  (* Force functions to be lifted to certain monads.
     The symtab is keyed on function name. *)
  ts_force : string Symtab.table,
  ts_force_known_functions : string option,

  (* Create some funky syntax for heap operations. *)
  heap_abs_syntax: bool option,

  (* Convert functions up to this phase *)
  phase: FunctionInfo.phase option,

  (* Only translate a subset of functions. *)
  scope: string list option,
  scope_depth: int option,

  (* Generate SIMPL wrappers that do not assert termination for the SIMPL.
   * Also generates ac_corres proofs minus the termination flag.
   * This option is for temporary CRefine compatibility. *)
  no_c_termination: bool option,

  (* Disable L1Peephole, L2Peephole and L2Opt rules. *)
  do_polish : bool option,
  L1_opt : FunctionInfo.stage option,
  L2_opt : FunctionInfo.stage option,
  HL_opt : FunctionInfo.stage option,
  WA_opt : FunctionInfo.stage option,

  (* Trace / Profile simplification rules. Note that some simplification is performed even with no_opt set. *)
  trace_opt : bool option,
  
  (* Define word{8,16,32,64} heaps even if the program does not use them. *)
  gen_word_heaps : bool option,

  keep_going : bool option,

  (* Change generated names for lifted_globals fields *)
  lifted_globals_field_prefix : string option,
  lifted_globals_field_suffix : string option,

  (* Change generated function names *)
  function_name_prefix : string option,
  function_name_suffix : string option,

  (* Generate theories (following call-graph and phases) to facilitate parallel processing *)
  single_threaded: bool option,
  unfold_constructor_bind: unfold_constructor_bind option,

 (* Base locale for all autocorres locales *)
  base_locale: (string * Position.T) option
}
\<close>}

(*
 * Blank set of options.
 *
 * Because we are using references, we need to construct a new set every
 * time; hence the dummy parameter.
 *)


val default_opts = make_autocorres_options {
    no_heap_abs = NONE,
    in_out_parameters = NONE,
    in_out_globals = NONE,
    skip_heap_abs = NONE,
    skip_io_abs = NONE,
    unsigned_word_abs = NONE,
    unsigned_word_abs_known_functions = NONE,
    no_signed_word_abs = NONE,
    no_signed_word_abs_known_functions = NONE,
    skip_word_abs = NONE,
    ts_rules = NONE,
    ts_force = Symtab.empty,
    ts_force_known_functions = NONE,
    heap_abs_syntax = NONE,
    phase = NONE,
    scope = NONE,
    scope_depth = NONE,
    no_c_termination = NONE,
    do_polish = NONE, 
    L1_opt = NONE,
    L2_opt = NONE,
    HL_opt = NONE,
    WA_opt = NONE,
    trace_opt = NONE,
    gen_word_heaps = NONE,
    keep_going = NONE,
    lifted_globals_field_prefix = NONE,
    lifted_globals_field_suffix = NONE,
    function_name_prefix = NONE,
    function_name_suffix = NONE,
    single_threaded = NONE,
    unfold_constructor_bind = NONE,
    addressable_fields = NONE,
    ignore_addressable_fields_error = NONE,
    base_locale = NONE
  }

structure Options_Theory = Theory_Data(
  type T = {options: autocorres_options, prog_info: ProgramInfo.prog_info} Symtab.table * autocorres_options option;
  val empty = (Symtab.empty, NONE);
  fun merge ((tab1, _), (tab2, _)) = (Symtab.merge (K true) (tab1, tab2), NONE);
)

fun get_current_options thy = Options_Theory.get thy |> snd
fun map_current_options f thy = Options_Theory.map (apsnd f) thy 

structure Options_Proof = AC_Proof_Data (
  type T = autocorres_options
  val init = fn thy => the_default default_opts (get_current_options thy)
)

val get_unfold_constructor_bind_opt = Options_Proof.get #> get_unfold_constructor_bind #> the_default Selectors 

(* Convert the given reference from "NONE" to "SOME x", emitting an
 * error if the value is already non-NONE. *)
fun none_to_some map_field new_value error_msg opt =
  let
    fun f x = case x of NONE => SOME new_value | SOME _ => error error_msg
  in
    map_field f opt
  end


(* get skipped phases *)
fun get_skips opt =
  let
    val io_abs = get_skip_io_abs opt = SOME false orelse is_some (get_in_out_parameters opt)
  in
    {skip_io_abs = not io_abs,
     skip_heap_abs = (get_skip_heap_abs opt = SOME true),
     skip_word_abs = (get_skip_word_abs opt = SOME true)} : FunctionInfo.skip_info
  end


(* Parsing expectations. *)
fun expect x y = !! (K (K ("autocorres: expected " ^ y ^ " after " ^ x)))

(* Generic parser for "NAME = THING" *)
fun named_option parser name elem_desc=
  Parse.reserved name |--
  expect (quote name) "\"=\"" (Parse.$$$ "=" |--
  expect "\"=\"" elem_desc parser)

(* Generic parser for "NAME = STRING ..." *)
val named_opt = named_option (Scan.repeat Parse.embedded)

(* Generic parser for "NAME = <nat>" *)
val nat_opt = named_option Parse.nat

(* Valid options. *)
val no_heap_abs_parser =
  named_opt "no_heap_abs" "function names" >>
  (fn funcs => none_to_some map_no_heap_abs funcs "autocorres: no_heap_abs option specified multiple times")



val parse_parameter_kind = Parse.embedded >> FunctionInfo.parameter_kind_from_string
val parse_in_out_param = Parse.embedded -- (Parse.$$$ ":" |-- parse_parameter_kind) 
val parse_in_out_list = Parse.$$$ "(" |-- (Parse.enum "," parse_in_out_param) --| Parse.$$$ ")"


val in_out_parameter_parser =
  named_option (Parse.and_list (Parse.embedded -- parse_in_out_list )) "in_out_parameters" "in / out parameters" >>
  (fn param_specs => none_to_some map_in_out_parameters param_specs "autocorres: in_out_parameters option specified miltiple times")

val in_out_globals_parser =
  named_opt "in_out_globals" "function names" >>
  (fn funcs => none_to_some map_in_out_globals funcs "autocorres: in_out_globals option specified multiple times")

val skip_heap_abs_parser =
  Parse.reserved "skip_heap_abs" >>
  (fn _ => none_to_some map_skip_heap_abs true "autocorres: skip_heap_abs option specified multiple times")

val skip_io_parser =
  Parse.reserved "skip_io_abs" >>
  (fn _ => none_to_some map_skip_io_abs true "autocorres: skip_io_abs option specified multiple times")

val ts_rules_parser =
  named_opt "ts_rules" "rule names" >>
  (fn rules => none_to_some map_ts_rules rules "autocorres: ts_rules option specified multiple times")

val scope_parser =
  named_opt "scope" "function names" >>
  (fn funcs => none_to_some map_scope funcs "autocorres: scope option specified multiple times")

val scope_depth_parser =
  nat_opt "scope_depth" "integer" >>
  (fn value => none_to_some map_scope_depth value "autocorres: scope option specified multiple times")

fun gen_phase_parser name map_field = 
    named_option (((Parse.reserved "CP" || Parse.reserved "L1" || Parse.reserved "L2" || Parse.reserved "HL" || 
         Parse.reserved "WA" || Parse.reserved "TS" || Parse.reserved "IO") 
         >> FunctionInfo.phase_of_string) 
       >> (fn value => none_to_some map_field value ("autocorres: " ^ name ^ "option specified multiple times"))) 
     name ("FuctionInfo " ^ name); 

val phase_parser = gen_phase_parser "phase" (map_phase)

fun stage_parser opt = 
    named_option (((Parse.reserved "RAW" || Parse.reserved "PEEP") 
         >> FunctionInfo.stage_of_string) >> opt)


val L1_opt_parser = stage_parser
      (fn value => none_to_some map_L1_opt value "autocorres: L1_opt option specified multiple times") 
     "L1_opt" "L1 maximal optimisation stage"; 

val L2_opt_parser = stage_parser
      (fn value => none_to_some map_L2_opt value "autocorres: L2_opt option specified multiple times") 
     "L2_opt" "L2 maximal optimisation stage"; 

val HL_opt_parser = stage_parser
      (fn value => none_to_some map_HL_opt value "autocorres: HL_opt option specified multiple times") 
     "HL_opt" "HL maximal optimisation stage"; 

val WA_opt_parser = stage_parser
      (fn value => none_to_some map_WA_opt value "autocorres: WA_opt option specified multiple times") 
     "WA_opt" "WA maximal optimisation stage"; 

val no_c_termination_parser =
  Parse.reserved "no_c_termination" >>
  (fn _ => none_to_some map_no_c_termination true "autocorres: no_c_termination option specified multiple times")

val ts_force_parser =
  ((Parse.reserved "ts_force" |--
      expect "\"ts_force\"" "rule name"
      (Parse.embedded :-- (fn name => expect name "\"=\"" (Parse.$$$ "="))) --
    Scan.repeat Parse.embedded)) >>
  (fn ((rule, _), funcs) => fn opt =>
    let
      fun upd v =
          fold (fn func => (fn table =>
              Symtab.update_new (func, rule) table
              handle Symtab.DUP _ =>
                error ("autocorres: function " ^ quote func
                    ^ " is already being forced to a particular type.")
              )) funcs v
    in
      map_ts_force upd opt
    end)

val ts_force_known_functions_parser =
  named_option Parse.embedded "ts_force_known_functions" "string" >>
  (fn name => none_to_some map_ts_force_known_functions name
                 "autocorres: ts_force_known_functions option specified multiple times")

val unsigned_word_abs_parser =
  named_opt "unsigned_word_abs" "function names" >>
  (fn funcs => none_to_some map_unsigned_word_abs funcs "autocorres: unsigned_word_abs option specified multiple times")

val unsigned_word_abs_known_functions_parser =
  Parse.reserved "unsigned_word_abs_known_functions" >>
  (fn _ => none_to_some map_unsigned_word_abs_known_functions true "autocorres: unsigned_word_abs_known_functions option specified multiple times")

val no_signed_word_abs_parser =
  named_opt "no_signed_word_abs" "function names" >>
  (fn funcs => none_to_some map_no_signed_word_abs funcs "autocorres: no_signed_word_abs option specified multiple times")

val no_signed_word_abs_known_functions_parser =
  Parse.reserved "no_signed_word_abs_known_functions" >>
  (fn _ => none_to_some map_no_signed_word_abs_known_functions true "autocorres: no_signed_word_abs_known_functions option specified multiple times")

val skip_word_abs_parser =
  Parse.reserved "skip_word_abs" >>
  (fn _ => none_to_some map_skip_word_abs true "autocorres: skip_word_abs option specified multiple times")

val heap_abs_syntax_parser =
  Parse.reserved "heap_abs_syntax" >>
  (fn _ => none_to_some map_heap_abs_syntax true "autocorres: heap_abs_syntax option specified multiple times")

val do_polish_parser =
  Parse.reserved "do_polish" >>
  (fn _ => none_to_some map_do_polish true "autocorres: do_polish option specified multiple times")

val trace_opt_parser =
  Parse.reserved "trace_opt" >>
  (fn _ => none_to_some map_trace_opt true "autocorres: trace_opt option specified multiple times")

val gen_word_heaps_parser =
  Parse.reserved "gen_word_heaps" >>
  (fn _ => none_to_some map_gen_word_heaps true "autocorres: gen_word_heaps option specified multiple times")

val keep_going_parser =
  Parse.reserved "keep_going" >>
  (fn _ => none_to_some map_keep_going true "autocorres: keep_going option specified multiple times")

val lifted_globals_field_prefix_parser =
  named_option Parse.embedded "lifted_globals_field_prefix" "string" >>
  (fn funcs => none_to_some map_lifted_globals_field_prefix funcs
                 "autocorres: lifted_globals_field_prefix option specified multiple times")

val lifted_globals_field_suffix_parser =
  named_option Parse.embedded "lifted_globals_field_suffix" "string" >>
  (fn funcs => none_to_some map_lifted_globals_field_suffix funcs
                 "autocorres: lifted_globals_field_suffix option specified multiple times")

val function_name_prefix_parser =
  named_option Parse.embedded "function_name_prefix" "string" >>
  (fn funcs => none_to_some map_function_name_prefix funcs
                 "autocorres: function_name_prefix option specified multiple times")

val function_name_suffix_parser =
  named_option Parse.embedded "function_name_suffix" "string" >>
  (fn funcs => none_to_some map_function_name_suffix funcs
                 "autocorres: function_name_suffix option specified multiple times")

val single_threaded_parser =
  Parse.reserved "single_threaded" >>
  (fn _ => none_to_some map_single_threaded true "autocorres: single_threaded option specified multiple times")

val unfold_constructor_bind_parser =
  named_option (Parse.embedded >> unfold_constructor_bind_of_string) 
    "unfold_constructor_bind" "Always | Never | Selectors"
  >> (fn exp => none_to_some map_unfold_constructor_bind exp
                 "autocorres: unfold_constroctur_bind  option specified multiple times")

val addressable_fields_parser =
  named_opt "addressable_fields" "field selections" >>
  (fn fields => none_to_some map_addressable_fields (map (space_explode ".") fields) "autocorres: addressable_fields option specified multiple times")

val ignore_addressable_fields_error_parser =
  Parse.reserved "ignore_addressable_fields_error" >>
  (fn _ => none_to_some map_ignore_addressable_fields_error true "autocorres: ignore_addressable_fields_error option specified multiple times")

val base_locale_parser =
  named_option Parse.name_position "base_locale" "string" >>
  (fn name_pos => none_to_some map_base_locale name_pos
                 "autocorres: base_locale option specified multiple times")

fun merge_in_out_parameters xs ys = AList.join (op =) (fn _ => AList.merge (op =) (op =)) (xs, ys)

fun merge_opt old new =
  let
    fun merge_o merge (NONE,   NONE)   = NONE 
      | merge_o merge (NONE,   SOME x) = SOME x
      | merge_o merge (SOME x, NONE  ) = SOME x
      | merge_o merge (SOME x, SOME y) = SOME (merge x y);

    fun override_o merge (NONE,   NONE)   = NONE 
      | override_o merge (NONE,   SOME x) = SOME x
      | override_o merge (SOME x, NONE  ) = NONE
      | override_o merge (SOME x, SOME y) = SOME (merge x y);

    fun merge_lists xs ys = duplicates (op =) (xs @ ys);
    fun take_fst x _ = x
    fun take_snd _ y = y

    fun get_opts prj o1 o2 = (prj o1, prj o2);

    val opt = make_autocorres_options {
      no_heap_abs         = merge_o merge_lists (get_opts get_no_heap_abs old new),
      in_out_parameters   = merge_o merge_in_out_parameters (get_opts get_in_out_parameters old new),
      in_out_globals      = merge_o merge_lists (get_opts get_in_out_globals old new),
      skip_heap_abs       = merge_o take_snd (get_opts get_skip_heap_abs old new),
      skip_io_abs         = merge_o take_snd (get_opts get_skip_io_abs old new),
      unsigned_word_abs   = merge_o merge_lists (get_opts get_unsigned_word_abs old new),
      unsigned_word_abs_known_functions = merge_o take_fst (get_opts get_unsigned_word_abs_known_functions old new),
      no_signed_word_abs  = merge_o merge_lists (get_opts get_no_signed_word_abs old new),
      no_signed_word_abs_known_functions = merge_o take_fst (get_opts get_no_signed_word_abs_known_functions old new),
      skip_word_abs       = merge_o take_snd (get_opts get_skip_word_abs old new),
      ts_rules            = merge_o merge_lists (get_opts get_ts_rules old new),
      ts_force            = Symtab.merge (K false) (get_ts_force old, get_ts_force new),
      ts_force_known_functions = merge_o take_fst (get_opts get_ts_force_known_functions old new),
      heap_abs_syntax     = merge_o take_fst (get_opts get_heap_abs_syntax old new),
      phase               = merge_o take_snd (get_opts get_phase old new),
      scope               = override_o take_snd (get_opts get_scope old new),
      scope_depth         = merge_o take_snd (get_opts get_scope_depth old new),
      no_c_termination    = merge_o take_fst (get_opts get_no_c_termination old new),
      do_polish           = merge_o take_snd (get_opts get_do_polish old new),
      L1_opt              = merge_o take_snd (get_opts get_L1_opt old new),
      L2_opt              = merge_o take_snd (get_opts get_L2_opt old new),
      HL_opt              = merge_o take_snd (get_opts get_HL_opt old new),
      WA_opt              = merge_o take_snd (get_opts get_WA_opt old new),
      trace_opt           = merge_o take_snd (get_opts get_trace_opt old new),
      gen_word_heaps      = merge_o take_fst (get_opts get_gen_word_heaps old new),
      keep_going          = merge_o take_snd (get_opts get_keep_going old new),
      lifted_globals_field_prefix = merge_o take_fst (get_opts get_lifted_globals_field_prefix old new),
      lifted_globals_field_suffix = merge_o take_fst (get_opts get_lifted_globals_field_suffix old new),
      function_name_prefix = merge_o take_fst (get_opts get_function_name_prefix old new),
      function_name_suffix = merge_o take_fst (get_opts get_function_name_suffix old new),
      single_threaded    = merge_o take_snd (get_opts get_single_threaded old new),
      unfold_constructor_bind = merge_o take_snd (get_opts get_unfold_constructor_bind old new),
      addressable_fields = merge_o take_fst (get_opts get_addressable_fields old new),
      ignore_addressable_fields_error = merge_o take_snd (get_opts get_ignore_addressable_fields_error old new),
      base_locale        = merge_o take_snd (get_opts get_base_locale old new)
      }
  in 
    opt
  end


fun upd_opts (opt:autocorres_options) scope phase :autocorres_options =
  opt |> map_scope (K (SOME scope)) |> map_phase (K (SOME phase))

local
  val option_parser =
    (no_heap_abs_parser ||
     in_out_parameter_parser ||
     in_out_globals_parser ||
     skip_heap_abs_parser ||
     ts_rules_parser ||
     ts_force_parser ||
     ts_force_known_functions_parser ||
     unsigned_word_abs_parser ||
     no_signed_word_abs_parser ||
     skip_word_abs_parser ||
     heap_abs_syntax_parser ||
     phase_parser ||
     scope_parser ||
     scope_depth_parser ||
     no_c_termination_parser ||
     do_polish_parser ||
     L1_opt_parser ||
     L2_opt_parser ||
     HL_opt_parser ||
     WA_opt_parser ||
     trace_opt_parser ||
     gen_word_heaps_parser ||
     keep_going_parser ||
     lifted_globals_field_prefix_parser ||
     lifted_globals_field_suffix_parser ||
     function_name_prefix_parser ||
     function_name_suffix_parser ||
     single_threaded_parser ||
     unfold_constructor_bind_parser ||
     addressable_fields_parser ||
     ignore_addressable_fields_error_parser ||
     base_locale_parser)
    |> !! (fn xs => K ("autocorres: unknown option " ^ quote (Parse.embedded (fst xs) |> #1)))

  val options_parser = Parse.list option_parser >> (fn opt_fns => fold I opt_fns)
in
val options_parser = 
  (Scan.optional (Parse.$$$ "[" |-- options_parser --| Parse.$$$ "]") I
      >> (fn f => f (default_opts)))
end

end
