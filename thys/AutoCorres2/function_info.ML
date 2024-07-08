(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Information about functions in the program we are translating,
 * and the call-graph between them.
 * To support incremental translation, we store the function information
 * for every intermediate phase as well.
 *)
signature FUNCTION_INFO2 =
sig
  (*** Basic data types ***)

  (* List of AutoCorres phases. *)
  datatype phase = CP (* Initial definition we get from the C parser *)
                 | L1 (* SimplConv *)
                 | L2 (* LocalVarExtract *)
                 | IO (* Remove local variable pointers and introduce in/out parameters *)
                 | HL (* HeapLift *) (* TODO: rename to HeapAbstract, Split Heap *)
                 | WA (* WordAbstract *)
                 | TS (* TypeStrengthen *);
  datatype parameter_kind = In | Out | In_Out | Data
  val parameter_kind_from_string : string -> parameter_kind
  val string_from_parameter_kind : parameter_kind -> string
  val phases: phase list;
  val string_of_phase : phase -> string;
  val phase_of_string : string -> phase;
  val phase_ord : phase * phase -> order;
  val next_phase : phase -> phase;
  type skip_info = {skip_io_abs: bool, skip_heap_abs: bool, skip_word_abs: bool}
  val info_phase : skip_info -> phase -> phase;
  val prev_phase : skip_info -> phase -> phase;
  val encode_phase : phase -> int;
  val decode_phase : int -> phase;
  structure Phasetab : TABLE; (* currently unused *)

  (* Each phase typically has the following stages *)
  datatype stage = RAW  (* Raw translation of program *) 
                 | PEEP (* Some peephole optimization *)
  val stages: stage list;
  val string_of_stage : stage -> string;
  val stage_of_string : string -> stage;
  val stage_ord : stage * stage -> order;
  val encode_stage : stage -> int;
  val decode_stage : int -> stage;


  (* Function info for a single phase. 
   * The function info is currently used as theory data as well as to store intermediate results
   * during autocorres transformations. It would be nice to clarify this and use proper
   * context data. This requires some refactoring of the way autocorres transforms and stores (intermediate)
   * results. For example the theorems like "definition" below, are now modelled as
   * Proof.context -> thm, to take the various views on a theorem in different locale / contexts
   * into account. This could become a simple "thm" when modelled as context data  
   * by using declarations / theorem-attributes where the infrastructure will take care to provide
   * the different views on the theorem by applying the right morphism. 
   * The current implementation with "Proof.context -> thm" 'notes' the theorem in a local theory and then
   * takes the resulting name as a reference that can be retrieved in various contexts.
   *
   * Similarily note that "const" currently is the external theory-level constant applied to
   * all locale parameters of the definition locale. Also here applying morphisms would be the
   * proper thing to do. When a constant is defined we will get a term back from the definition
   * command. This term can then be morphed to the correct instance in every locale.
   *
   * So at one point we should add a declaration attribute to the definition command or note command
   * that then takes care of applying morphisms to the data.
   *) 
  type var_info = ProgramAnalysis.var_info
  datatype function_info = Function_info of {
      (* Name of the function. *)
      name : string, (* locale independent, fix for all phases *)

      (* The translation phase for this definition. *)
      phase : phase, (* locale independent *)

      (* Constant for the function, which can be inserted as a call to the
       * function. Unlike "raw_const", this includes any locale parameters
       * required by the function *)
      const: term,   (* locale dependent *)

      (* Arguments of the function, in order, excluding measure variables. *)
      args : (string * (typ * var_info)) list,    (* locale independent, updated in L2 phase, type might change in WA*)
      locals: (string * (typ * var_info)) list,   (* locale independent, fix for all phases *)
      returns: (string * (typ * var_info)) list,  (* locale independent, fix for all phases *)
      in_out_parameters: (string * parameter_kind) list,
      (* Return type of the function ("unit" is used for void). *)
      return_type : typ,             (* locale independent, might change in WA pase *)

      (* Function calls. Direct (mutually) recursive calls go in rec_callees. *)
      callees : symset,              (* locale independent, may change in phases (due to dead code)*)
      rec_callees : symset,          (* locale independent, may change in phases (due to dead code)*)
      fun_ptr_dependencies : symset, 
      clique_fun_ptr_dependencies : symset, 
      clique : symset,               (* locale independent, fix in all phased*)

      (* Definition of the function. *)
      definition : thm lazy, (* locale dependent, phase dependent *)
      induct_thms: thm list lazy, (* locale dependent, phase dependent *)

      (* corres theorem for the function. (TrueI when phase = CP.) *)
      corres_thm : thm, (* locale dependent, phase dependent *)

      no_throw_thm: thm option, (* locale dependent, only updated in L1 *)

      (* Is this function actually being translated, or are we just
       * wrapping the SIMPL code? *)
      is_simpl_wrapper : bool, (* locale independent, phase independent *)

      (* Is this function generated by AutoCorres as a placeholder for
       * a function we didn't have the source code to? *)
      invented_body : bool  (* locale independent, phase independent *)
  };

  val make_function_info: {name: string, phase: phase, const:term,  
    args: (string * (typ * var_info)) list, 
    locals: (string * (typ * var_info)) list, 
    returns: (string * (typ * var_info)) list,
    in_out_parameters:  (string * parameter_kind) list,
    return_type: typ, callees: symset, rec_callees: symset, fun_ptr_dependencies: symset, 
    clique_fun_ptr_dependencies: symset, clique: symset, 
    definition : thm lazy, induct_thms : thm list lazy, corres_thm: thm, no_throw_thm: thm option, 
    is_simpl_wrapper: bool, invented_body : bool} -> function_info;

  (* Standard result sequence that is passed between stages *)
  type phase_results = (function_info Symtab.table) list;

  val dest_spec_monad_type: typ -> typ list * {exT: typ, resT:typ, stateT: typ}
  val dest_exn_monad_type : typ -> typ list * {exT: typ, resT:typ, stateT: typ}
  val dest_res_monad_type : typ -> typ list * {resT:typ, stateT: typ}

  val get_name             : function_info -> string;
  val get_phase            : function_info -> phase;
  val get_const            : function_info -> term;
  val get_raw_const        : function_info -> term; 
  val get_args             : function_info -> (string * (typ * ProgramAnalysis.var_info)) list;
  val get_args_without_outs: function_info -> (string * (typ * ProgramAnalysis.var_info)) list;
  val get_plain_args       : function_info -> (string * typ) list
  val get_fn_ptr_args_info: function_info -> (string * (int * (int CType.ctype * int CType.ctype list))) list
  val get_locals           : function_info -> (string * (typ * ProgramAnalysis.var_info)) list;
  val get_returns          : function_info -> (string * (typ * ProgramAnalysis.var_info)) list;
  val get_in_out_parameters: function_info -> (string * parameter_kind) list;
  val get_variables        : function_info -> (string * (typ * ProgramAnalysis.var_info)) list;
  val get_return_type      : function_info -> typ;
  val get_exit_type        : function_info -> typ;
  val get_exn_type         : function_info -> typ;
  val get_callees          : function_info -> symset;
  val get_rec_callees      : function_info -> symset;
  val get_fun_ptr_dependencies  : function_info -> symset;
  val get_clique_fun_ptr_dependencies  : function_info -> symset;
  val get_clique_recursion_fun_ptrs : function_info -> string list;
  val get_recursive_clique : function_info -> symset;
  val get_clique           : function_info -> symset;
  val get_first_clique     : function_info Symtab.table -> string list;
  val get_definition       : function_info -> thm;
  val get_induct_thms      : function_info -> thm list;
  val get_corres_thm       : function_info -> thm;
  val get_proper_corres_thm: function_info -> thm option;
  val get_no_throw_thm     : function_info -> thm option;
  val get_invented_body    : function_info -> bool;
  val get_is_simpl_wrapper : function_info -> bool;


  val map_name             : (string -> string) -> function_info -> function_info;
  val map_phase            : (phase -> phase) -> function_info -> function_info;
  val map_const            : (term -> term) -> function_info -> function_info;
  val map_args             : ((string * (typ * var_info)) list -> (string * (typ * var_info)) list) -> function_info -> function_info;
  val map_locals           : ((string * (typ * var_info)) list -> (string * (typ * var_info)) list) -> function_info -> function_info;
  val map_returns          : ((string * (typ * var_info)) list -> (string * (typ * var_info)) list) -> function_info -> function_info;
  val map_in_out_parameters: ((string * parameter_kind) list -> (string * parameter_kind) list) -> function_info -> function_info;
  val map_return_type      : (typ -> typ) -> function_info -> function_info;
  val map_callees          : (symset -> symset) -> function_info -> function_info;
  val map_rec_callees      : (symset -> symset) -> function_info -> function_info;
  val map_fun_ptr_dependencies  : (symset -> symset) -> function_info -> function_info;
  val map_clique_fun_ptr_dependencies  : (symset -> symset) -> function_info -> function_info;
  val map_clique           : (symset -> symset) -> function_info -> function_info;
  val map_definition       : (thm -> thm) -> function_info -> function_info;
  val map_induct_thms      : (thm list -> thm list) -> function_info -> function_info;
  val map_corres_thm       : (thm -> thm) -> function_info -> function_info;
  val map_no_throw_thm     : (thm option -> thm option) -> function_info -> function_info;
  val map_invented_body    : (bool -> bool) -> function_info -> function_info;
  val map_is_simpl_wrapper : (bool -> bool) -> function_info -> function_info;

  val set_lazy_definition  : thm lazy -> function_info -> function_info
  val set_lazy_induct_thms : thm list lazy -> function_info -> function_info
  val add_lazy_induct_thms : thm list lazy -> function_info -> function_info

  val merge : function_info -> function_info -> function_info;
  val empty_info : string -> phase -> function_info;
  val init_from_old : phase -> function_info -> function_info;
  val morph : Morphism.morphism -> function_info -> function_info;
  val transfer_call_graph_info: function_info -> function_info -> function_info;
  val transfer_call_graph_infos: function_info Symtab.table -> function_info Symtab.table -> function_info Symtab.table;
  val transfer_call_graph_infoss: function_info Symtab.table list -> function_info Symtab.table -> function_info Symtab.table
  (* Convenience getters. *)
  val is_function_recursive : function_info -> bool;
  val performs_indirect_calls : function_info -> bool;
  val all_callees : function_info -> symset;

  type call_graph_info = {
      (* Topologically sorted function calls, in dependency order.
       * Each sub-list represents one function or recursive function group. *)
      topo_sorted_functions : symset list,

      (* Table mapping raw_consts to functions. *)
      const_to_function : string Termtab.table,

      (* Table mapping each recursive function to its recursive function group.
       * Non-recursive functions do not appear in the table. *)
      recursive_group_of : symset Symtab.table
  };

  (* Group functions to facilitate parallel processing within the groups *)
  val group_independent_functions: function_info Symtab.table -> call_graph_info -> Symtab.key list list
  val group_cliques : call_graph_info -> string list list

  (* Calculate call-graph information.
   * Also updates the callees and rec_callees entries of its inputs,
   * which are assumed to have outdated callee info.
   *
   * Ideally, we'd also have a pre_function_info type that doesn't have
   * outdated callees, but dealing with ML records is annoying. *)
  val calc_call_graph : function_info Symtab.table -> call_graph_info * function_info Symtab.table;

  (* Update callees and rec_callees for the given recursive function group,
   * relative to a set of background functions (that must not contain the
   * given group).
   *
   * Returns a sequence of function groups in a valid topological order.
   * We return multiple groups because function calls can be removed by
   * dead code elimination and other transformations, which could cause
   * the original group to split.*)
  val recalc_callees : 
    function_info Symtab.table -> (* background *)
    function_info Symtab.table -> (* group *)
    function_info Symtab.table list;

  val reachable_direct_callees: function_info Symtab.table -> Symset.key list -> Symset.key Symset.set
end;

structure FunctionInfo : FUNCTION_INFO2 =
struct

type var_info = ProgramAnalysis.var_info;
type skip_info = {skip_io_abs: bool, skip_heap_abs: bool, skip_word_abs: bool}
datatype phase = CP | L1 | L2 | IO | HL | WA | TS;
val phases = [CP, L1, L2, IO, HL, WA, TS]

fun string_of_phase CP = "CP"
  | string_of_phase L1 = "L1"
  | string_of_phase L2 = "L2"
  | string_of_phase IO = "IO"
  | string_of_phase HL = "HL"
  | string_of_phase WA = "WA"
  | string_of_phase TS = "TS";

fun phase_of_string s = (case s of
      "CP" => CP
    | "L1" => L1
    | "L2" => L2
    | "IO" => IO
    | "HL" => HL
    | "WA" => WA
    | "TS" => TS); 

fun encode_phase CP = 0
  | encode_phase L1 = 1
  | encode_phase L2 = 2
  | encode_phase IO = 3
  | encode_phase HL = 4
  | encode_phase WA = 5
  | encode_phase TS = 6;

fun decode_phase 0 = CP
  | decode_phase 1 = L1
  | decode_phase 2 = L2
  | decode_phase 3 = IO
  | decode_phase 4 = HL
  | decode_phase 5 = WA
  | decode_phase 6 = TS;

val phase_ord = int_ord o apply2 encode_phase;

fun next_phase p = decode_phase (encode_phase p + 1);
fun prev_phase_raw p = decode_phase (encode_phase p - 1);

fun info_phase (skips as {skip_io_abs, skip_heap_abs, skip_word_abs}) phase = 
  case phase of
    IO => if skip_io_abs then info_phase skips L2 else IO
  | HL => if skip_heap_abs then info_phase skips IO else HL
  | WA => if skip_word_abs then info_phase skips HL else WA
  | _ => phase

fun prev_phase skips = info_phase skips o prev_phase_raw

datatype parameter_kind = In | Out | In_Out | Data

fun parameter_kind_from_string str = 
  case str of
    "in" => In
  | "out" => Out
  | "in_out" => In_Out
  | "data" => Data
  | _ => error ("parameter_kind_from_string: unexpected string" ^ quote str)

fun string_from_parameter_kind k =
  case k of
    In => "in"
  | Out => "out"
  | In_Out => "in_out"
  | Data => "data"

structure Phasetab = Table(
  type key = phase
  val ord = phase_ord);

datatype stage = RAW | PEEP
val stages = [RAW, PEEP];
  
fun string_of_stage RAW = "RAW"
  | string_of_stage PEEP = "PEEP"

fun stage_of_string s = (case s of 
    "RAW" => RAW
  | "PEEP" => PEEP);

fun encode_stage RAW = 0
  | encode_stage PEEP = 1;

fun decode_stage 0 = RAW
  | decode_stage 1 = PEEP;

val stage_ord = int_ord o apply2 encode_stage;

@{record \<open>datatype function_info = Function_info of {
  name             : string,
  phase            : phase,
  const            : term,
  args             : (string * (typ * ProgramAnalysis.var_info)) list,
  locals           : (string * (typ * ProgramAnalysis.var_info)) list,
  returns          : (string * (typ * ProgramAnalysis.var_info)) list,
  in_out_parameters : (string * parameter_kind) list,
  return_type      : typ,
  callees          : symset,
  rec_callees      : symset,
  fun_ptr_dependencies  : symset,
  clique_fun_ptr_dependencies : symset,
  clique           : symset,
  definition       : thm lazy,
  induct_thms      : thm list lazy,
  corres_thm       : thm,
  no_throw_thm     : thm option,
  invented_body    : bool,
  is_simpl_wrapper : bool
}\<close>
}

fun set_lazy_definition lazy_thm = map_definition (K lazy_thm)
val get_definition = get_definition #> Lazy.force
val map_definition = map_definition o Lazy.map 

fun set_lazy_induct_thms lazy_thms = map_induct_thms (K lazy_thms)
fun add_lazy_induct_thms lazy_thms = map_induct_thms 
     (fn thms => Lazy.lazy (fn () => Lazy.force lazy_thms @ Lazy.force thms))
val get_induct_thms = get_induct_thms #> Lazy.force
val map_induct_thms = map_induct_thms o Lazy.map

val map_definition' = map_definition

fun map_definition f info =
  let
    val info' = map_definition' f info
    val def' = get_definition info'
    val _ = if length (Thm.prems_of def') > 1 then
        error (@{make_string} def') else ()
  in
    info'
  end 
type phase_results = (function_info Symtab.table) list;

fun dummy_ctxt_thm ctxt = @{thm TrueI}

val fast_eq = Utils.fast_eq

fun merge 
  (Function_info {name = name1, phase = phase1, const = const1, 
    args = args1, locals = locals1, returns = returns1,
    in_out_parameters = in_out_parameters1,
    return_type = return_type1, callees = callees1, rec_callees =rec_callees1, 
    fun_ptr_dependencies = fun_ptr_dependencies1, 
    clique_fun_ptr_dependencies = clique_fun_ptr_dependencies1, 
    clique = clique1,
    definition = definition1, induct_thms = induct_thms1,  
    corres_thm = corres_thm1, no_throw_thm = no_throw_thm1,
    invented_body = invented_body1, is_simpl_wrapper = is_simpl_wrapper1
  })
  (Function_info {name = name2, phase = phase2, const = const2,
    args = args2, locals = locals2, returns = returns2, 
    in_out_parameters = in_out_parameters2,
    return_type = return_type2, callees = callees2, rec_callees =rec_callees2, 
    fun_ptr_dependencies = fun_ptr_dependencies2, 
    clique_fun_ptr_dependencies = clique_fun_ptr_dependencies2, clique = clique2,
    definition = definition2, induct_thms = induct_thms2,
    corres_thm = corres_thm2, no_throw_thm = no_throw_thm2,
    invented_body = invented_body2, is_simpl_wrapper = is_simpl_wrapper2
  }) =
let
  fun msg kind str = ("FunctionInfo.merge (" ^ name1 ^ ", " ^ name2 ^ "): " ^ 
    kind ^ " not mergable: "  ^ str ())
  val name = if name1 = name2 then name1 else error (msg "name" (fn _ => @{make_string} (name1, name2))) 
  val phase = if phase1 = phase2 then phase1 else error (msg "phase" (fn _ => @{make_string} (phase1, phase2)))
  val const = if const1 aconv const2 then const1 else error (msg "const" (fn _ => @{make_string} (const1, const2))) 
  val args = if args1 = args2 then args1 else error (msg "args" (fn _ => @{make_string} (args1, args2)))
  val locals = if locals1 = locals2 then locals1 else error (msg "locals" (fn _ => @{make_string} (locals1, locals2)))
  val returns = if returns1 = returns2 then returns1 else error (msg "returns" (fn _ => @{make_string} (returns1, returns2)))
  val in_out_parameters = if in_out_parameters1 = in_out_parameters2 then in_out_parameters1 else error (msg "in_out_parameters" (fn _ => @{make_string} (in_out_parameters1, in_out_parameters2)))
  val return_type = if return_type1 = return_type2 then return_type1
                    else error (msg "return_type" (fn _ => @{make_string} (return_type1, return_type2)))
  val callees = if fast_eq Symset.eq (callees1, callees2) then callees1 
                else error (msg "callees" (fn _ => @{make_string} (callees1, callees2)))
  val rec_callees = if fast_eq Symset.eq (rec_callees1, rec_callees2) then rec_callees1 
                    else error (msg "rec_callees" (fn _ => @{make_string} (rec_callees1, rec_callees2)))
  val fun_ptr_dependencies = if fast_eq Symset.eq (fun_ptr_dependencies1, fun_ptr_dependencies2) then fun_ptr_dependencies1 
                    else error (msg "fun_ptr_dependencies" (fn _ => @{make_string} (fun_ptr_dependencies1, fun_ptr_dependencies2)))
  val clique_fun_ptr_dependencies = if fast_eq Symset.eq (clique_fun_ptr_dependencies1, clique_fun_ptr_dependencies2) then fun_ptr_dependencies1 
                    else error (msg "clique_fun_ptr_dependencies" (fn _ => @{make_string} (clique_fun_ptr_dependencies1, clique_fun_ptr_dependencies2)))
  val clique = if fast_eq Symset.eq (clique1, clique2) then clique1 
                    else error (msg "clique" (fn _ => @{make_string} (clique1, clique2)))
  val definition = if Thm.eq_thm_prop (Lazy.force definition1, Lazy.force definition2) then definition1
                   else error (msg "definition" (fn _ => @{make_string} (Lazy.force definition1, Lazy.force definition2)))
  val induct_thms = if forall Thm.eq_thm_prop (Lazy.force induct_thms1 ~~ Lazy.force induct_thms2) then induct_thms1 
                   else error (msg "induct_thms" (fn _ => @{make_string} (Lazy.force induct_thms1, Lazy.force induct_thms2)))
  val corres_thm = if Thm.eq_thm_prop (corres_thm1, corres_thm2) then corres_thm1
                   else error (msg "corres_thm" (fn _ => @{make_string} (corres_thm1, corres_thm2)))
  val no_throw_thm = if eq_option Thm.eq_thm (no_throw_thm1, no_throw_thm2) then no_throw_thm1
                     else error (msg "no_throw_thm" (fn _ => @{make_string} (no_throw_thm1, no_throw_thm2)))
  val invented_body = if invented_body1 = invented_body2 then invented_body1 
                      else error (msg "invented_body" (fn _ => @{make_string} (invented_body1, invented_body2)))
  val is_simpl_wrapper = if is_simpl_wrapper1 = is_simpl_wrapper2 then is_simpl_wrapper1 
                      else error (msg "is_simpl_wrapper" (fn _ => @{make_string} (is_simpl_wrapper1, is_simpl_wrapper2))) 
in
  (Function_info {name = name, phase = phase, const = const, 
    args = args, locals = locals, returns = returns,
    in_out_parameters = in_out_parameters,
    return_type = return_type, callees = callees, rec_callees =rec_callees, 
    fun_ptr_dependencies = fun_ptr_dependencies, 
    clique_fun_ptr_dependencies = clique_fun_ptr_dependencies, 
    clique = clique,
    definition = definition, induct_thms = induct_thms, 
    corres_thm = corres_thm, no_throw_thm = no_throw_thm,
    invented_body = invented_body, is_simpl_wrapper = is_simpl_wrapper
  })
end

fun get_variables (Function_info {args, locals, returns, ...}) = args @ locals @ returns

fun get_plain_args (Function_info {args, ...}) = map (fn (n, (T, info)) => (n, T)) args

fun get_args_without_outs (Function_info {args, in_out_parameters, ...}) = 
  args |> filter_out (fn (n, _) => AList.lookup (op =) in_out_parameters n = SOME (Out))


fun get_fn_ptr_args_info (Function_info {args, ...}) =
  tag_list 1 args 
  |> map_filter (fn (idx, (name, (T, info))) => 
      case ProgramAnalysis.get_vtype info of
        CType.Ptr (CType.Function (retT, argTs)) => 
          let
          in 
            SOME (name, (idx, (retT, argTs)))
          end
      | _ => NONE)

val get_raw_const = head_of o get_const


fun dest_spec_monad_type T =
let
  val (argTs, mT) = strip_type T
  val \<^Type>\<open>spec_monad e a s\<close> = mT

in
  (argTs, {exT = e, resT = a, stateT = s})
end

fun dest_exn_monad_type T =
  let
    val (argTs, {exT, resT, stateT}) = dest_spec_monad_type T
    val \<^Type>\<open>option xT\<close> = exT
  in
    (argTs, {exT = xT, resT = resT, stateT = stateT})
  end

fun dest_res_monad_type T =
  let
    val (argTs, {exT, resT, stateT}) = dest_spec_monad_type T
    val \<^Type>\<open>unit\<close> = exT
  in
    (argTs, {resT = resT, stateT = stateT})
  end



fun get_exit_type (Function_info {const, ...}) = 
  let
    val (_, {exT, ...}) = dest_spec_monad_type (fastype_of const)
  in
    exT
  end

fun get_exn_type (Function_info {const, ...}) = 
  let
    val (_, {exT, ...}) = dest_exn_monad_type (fastype_of const)
  in
    exT
  end


fun get_first_clique info_tab = 
  case Symtab.dest info_tab of
    ((_, info)::_) => Symset.dest (get_clique info)
  | [] => []

fun is_function_recursive fi = 
    not (Symset.is_empty (get_rec_callees fi))
    orelse Symset.card (get_clique fi) > 1
    orelse Symset.contains (get_fun_ptr_dependencies fi) (get_name fi)
;

fun get_clique_recursion_fun_ptrs (Function_info {clique, clique_fun_ptr_dependencies, ...}) =
  Symset.dest clique |>  (filter (member (op =) (Symset.dest clique_fun_ptr_dependencies)))

fun get_recursive_clique fi = 
  if is_function_recursive fi then get_clique fi else Symset.empty


fun performs_indirect_calls (Function_info {phase, definition,...}) = 
 case phase of
   CP => exists_subterm (fn Const (@{const_name dynCall_exn}, _) => true | _ => false) (Thm.prop_of (Lazy.force definition))
  | _ => false

fun all_callees (Function_info { rec_callees, callees, fun_ptr_dependencies, ... }) = 
  Symset.union_sets [callees, rec_callees, fun_ptr_dependencies]


type call_graph_info = {
        topo_sorted_functions : symset list,
        const_to_function : string Termtab.table,
        recursive_group_of : symset Symtab.table
};



fun phase_of_infos infos = 
  case Symtab.dest infos of
    [] => CP
  | (_,info)::_ => get_phase info


fun fold_simpl_calls f t =
  case t of 
     Const (@{const_name "call_exn"}, _) $ init $ p $ return $ result_exn $ c => f p 
   | (u $ v) => fold_simpl_calls f u #> fold_simpl_calls f v
   | Abs (_, _, u) => fold_simpl_calls f u
   | _ => I


fun calc_call_graph fn_infos = let
  val const_to_function =
    Symtab.dest fn_infos
    |> map (fn (name, info) => (get_raw_const info, name))
    |> Termtab.make;

  val phase = phase_of_infos fn_infos;
  val fold_calls = 
    case phase of
      CP => fold_simpl_calls  
     | _ => Term.fold_aterms 


  (* Get a function's direct callees, based on the list of constants that appear
   * in its definition. *)
  fun get_direct_callees fn_info = let
    val body =
      get_definition fn_info 
      |> Thm.concl_of
      |> Utils.rhs_of_eq;
    in
      (* Ignore function bodies if we are using SIMPL wrappers. *)
      if get_is_simpl_wrapper fn_info then [] else
          fold_calls (fn t => fn a =>
                (Termtab.lookup const_to_function t
                |> Option.map single
                |> the_default []) @ a) body []
          |> distinct (op =)
    end;

  fun get_direct_and_fun_ptr_callees info = 
        ((get_direct_callees info) @ Symset.dest (get_fun_ptr_dependencies info)) 
        |> distinct (op =)
        |> filter (member (op =) (map fst (Symtab.dest fn_infos)))

  (* Call graph of all functions. *)
  val fn_direct_callees = fn_infos |> Symtab.map (K get_direct_callees) |> Symtab.map (K Symset.make)
  val fn_callees_lists = fn_infos |> Symtab.map (K get_direct_and_fun_ptr_callees);
  (* Add each function to its own callees to get a complete inverse *)
  val fn_callers_lists = flip_symtab (Symtab.map cons fn_callees_lists);

  val topo_sorted_functions =
        Topo_Sort.topo_sort {
          cmp = string_ord,
          graph = Symtab.lookup fn_callees_lists #> the,
          converse = Symtab.lookup fn_callers_lists #> the
        } (Symtab.keys fn_callees_lists |> sort_strings) (* FIXME: sort with depth in call-graph instead of string_ord should lead to smarter ordering of parallel partitions later on *)
        |> map Symset.make;

  fun is_recursive_singleton f =
        Symset.contains (Utils.the' ("is_recursive_singleton: " ^ f)
                                    (Symtab.lookup fn_direct_callees f)) f;

  val recursive_group_of =
        topo_sorted_functions
        |> maps (fn f_group =>
             (* Exclude non-recursive functions *)
             if Symset.card f_group = 1 andalso not (is_recursive_singleton (hd (Symset.dest f_group)))
             then []
             else Symset.dest f_group ~~ replicate (Symset.card f_group) f_group)
        |> Symtab.make;


  (* Now update callee info. *)
  fun maybe_symset NONE = Symset.empty
    | maybe_symset (SOME x) = x;
  val fn_infos' =
        fn_infos |> Symtab.map (fn f => let
          val (rec_callees, callees) =
                Symset.dest (Utils.the' ("not in fn_callees: " ^ f) (Symtab.lookup fn_direct_callees f))
                |> List.partition (Symset.contains (maybe_symset (Symtab.lookup recursive_group_of f)));
          val clique = case Symtab.lookup recursive_group_of f of
                         SOME s => s
                       | NONE => Symset.make [f]
          in map_callees (K (Symset.make callees)) o
             map_rec_callees (K (Symset.make rec_callees)) o 
             map_clique (K clique) end);
  in ({ topo_sorted_functions = topo_sorted_functions,
        const_to_function = const_to_function,
        recursive_group_of = recursive_group_of
      }, fn_infos')
  end;

fun partition_joined_group ignore part xss =
  let
    fun recurse (ys::yss) [] = yss@(part ys) 
      | recurse (ys::yss) (xs::xss) = if ignore xs then recurse ([]::yss@(part ys)@[xs]) xss
                                      else recurse ((ys@xs)::yss) xss
  in filter_out List.null (recurse [[]] xss)
  end;

val _ =
@{assert} ([[1, 2], [3, 4], [5, 6, 7]] = 
  partition_joined_group (fn xs => length xs > 1) (fn x => [x]) [[1, 2], [3], [4], [5, 6, 7]]);


fun group_independent deps xs =
  let
    fun recurse (ys::yss) [] = yss@[ys]
      | recurse (ys::yss) (x::xs) = 
          let
            val ds = deps x
          in 
            if exists (member (op =) ds) ys 
            then recurse ([x]::yss@[ys]) xs
            else recurse ((ys@[x])::yss) xs
          end  
  in
    recurse [[]] xs
  end;

val _ =
let 
  fun deps 4 = [3]
    | deps 6 = [1]
    | deps 7 = [5]
    | deps _ = []

in 
  @{assert} ([[1, 2, 3], [4, 5, 6], [7, 8, 9, 10]] = 
    group_independent deps [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
  
  @{assert} ([[1, 2], [3], [4], [5, 6, 7]] = 
     partition_joined_group (fn xs => length xs > 1)
       (group_independent deps) [[1, 2], [3], [4], [5, 6, 7]]);

  @{assert} ([[1, 2], [3, 4], [5, 6], [7]] =
     partition_joined_group (fn xs => length xs > 1)
       (group_independent deps) [[1, 2], [3, 4], [5], [6], [7]])
end

fun group_independent_functions infos {topo_sorted_functions, recursive_group_of,...} =
  let
    val is_recursive = Symtab.defined recursive_group_of
    fun ignore xs = exists is_recursive xs orelse length xs > 1
    fun deps f = (the  (Symtab.lookup infos f)) |> get_callees |> Symset.dest
    val fnss = partition_joined_group ignore (group_independent deps) (map Symset.dest topo_sorted_functions)
  in
    fnss
  end

fun group_cliques {topo_sorted_functions,...} = map Symset.dest topo_sorted_functions

  type call_graph_info = {
      (* Topologically sorted function calls, in dependency order.
       * Each sub-list represents one function or recursive function group. *)
      topo_sorted_functions : symset list,

      (* Table mapping raw_consts to functions. *)
      const_to_function : string Termtab.table,

      (* Table mapping each recursive function to its recursive function group.
       * Non-recursive functions do not appear in the table. *)
      recursive_group_of : symset Symtab.table
  };

fun recalc_callees base_infos fn_infos = let
  val base_consts =
        Symtab.dest base_infos
        |> map (fn (f, info) => (get_raw_const info, f))
        |> Termtab.make;
  (* restrict_fn_infos has the correct call graph,
   * but omits functions outside fn_infos *)
  val (call_graph, restrict_fn_infos) = calc_call_graph fn_infos;
  fun update_info f info = let
        val restrict_info = the (Symtab.lookup restrict_fn_infos f);
        (* Update calls into base_info *)
        val f_body = Thm.concl_of (get_definition info) |> Utils.rhs_of_eq;
        val base_callees' =
              if get_is_simpl_wrapper info then Symset.empty else
                Term.fold_aterms (fn t => fn a =>
                    (Termtab.lookup base_consts t
                     |> Option.map single
                     |> the_default []) @ a)
                    f_body []
                |> Symset.make;
        (* base_infos should not include fn_infos, otherwise this weird call would exist *)
        val () = assert (not (Symset.contains base_callees' f))
                   "FunctionInfo.recalc_base_callees";
        (* rec_callees has been recalculated *)
        val rec_callees' = get_rec_callees restrict_info;
        (* Some rec_callees may have become callees due to breaking recursive loops *)
        val callees' = Symset.union base_callees' (get_callees restrict_info);
        val clique' = get_clique restrict_info
        in info
           |> map_rec_callees (K rec_callees')
           |> map_callees (K callees')
           |> map_clique (K clique')
        end;
  in 
    group_independent_functions fn_infos call_graph |> map (fn group => 
      group
      |> map (fn f => (f, update_info f (the (Symtab.lookup fn_infos f))))
      |> Symtab.make)
  end;

val dummy_const = Bound 0;
val dummy_thm = Thm.trim_context (@{thm refl});
val dummy_typ = @{typ unit};

fun empty_info name phase = make_function_info {
         name = name,
         phase = phase,
         args = [],
         locals = [],
         returns = [],
         in_out_parameters = [],
         return_type = dummy_typ,
         const = dummy_const,
         callees = Symset.empty, 
         rec_callees = Symset.empty,
         fun_ptr_dependencies = Symset.empty, 
         clique_fun_ptr_dependencies = Symset.empty, 
         clique = Symset.insert name Symset.empty, 
         definition = Lazy.value dummy_thm,
         induct_thms = Lazy.value [],
         corres_thm = dummy_thm,
         no_throw_thm = NONE,
         is_simpl_wrapper = false,
         invented_body = false
       }


fun init_from_old phase old_info = 
 let
    val _ = @{assert} (not (Symset.is_empty (get_clique old_info))); 
    (* failure indicates issues with initialisation of the data *)
 in
  old_info 
  |> map_phase (K phase) 
  |> map_const (K dummy_const)
  |> map_definition (K dummy_thm)
  |> map_corres_thm (K dummy_thm)
  |> map_no_throw_thm (K NONE)
 end

local
  (* avoid morphing the global dummy theorem which was not produced in the locale *)
  fun thm_morph phi thm = 
    if pointer_eq (dummy_thm, thm) then dummy_thm else Morphism.thm phi thm
in 
fun morph phi info =
  info 
  |> map_const (Morphism.term phi) 
  |> map_definition (thm_morph phi)
  |> map_corres_thm (thm_morph phi)
  |> map_no_throw_thm (Option.map (thm_morph phi))
end

fun get_proper_corres_thm info =
  let
    val thm = get_corres_thm info
  in
    if pointer_eq (dummy_thm, thm) then NONE else SOME thm
  end


fun transfer_call_graph_info cg_info info =
  info 
  |> map_callees (K (get_callees cg_info))
  |> map_rec_callees (K (get_rec_callees cg_info))
  |> map_clique (K (get_clique cg_info))


fun transfer_call_graph_infos cg_infos infos =
  infos 
  |> fold (fn (name, cg_info) => Symtab.map_entry name (transfer_call_graph_info cg_info))
       (Symtab.dest cg_infos)

fun transfer_call_graph_infoss cg_infoss infos =
  infos 
  |> fold transfer_call_graph_infos
     cg_infoss

fun add_reachable_direct_callees infos fname S =
  case Symtab.lookup infos fname of 
     NONE => S
  |  SOME info => 
       let
         val direct_callees = Symset.union (get_callees info) (get_rec_callees info) |> Symset.insert fname
         val new_callees = Symset.subtract S direct_callees 
       in
         Symset.union S new_callees 
         |> fold (add_reachable_direct_callees infos) (Symset.dest new_callees) 
       end

fun reachable_direct_callees infos fnames = 
  Symset.empty |> fold (add_reachable_direct_callees infos) fnames

end; (* structure FunctionInfo *)
