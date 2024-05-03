(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Definition of context data.
 *)
signature AUTOCORRES_DATA = 
sig


  val get_phase_info: Context.generic -> string -> FunctionInfo.phase ->
        FunctionInfo.function_info Symtab.table option;
  val get_default_phase_info: Context.generic -> string -> FunctionInfo.phase ->
        FunctionInfo.function_info Symtab.table;
  val map_default_phase_info: string -> FunctionInfo.phase ->
        (FunctionInfo.function_info Symtab.table -> FunctionInfo.function_info Symtab.table) -> 
        Context.generic -> Context.generic;
  val map_default_info: string -> FunctionInfo.skip_info -> FunctionInfo.phase -> string ->
          (FunctionInfo.function_info -> FunctionInfo.function_info) -> 
          Context.generic -> Context.generic

  val get_function_info: Context.generic -> string -> FunctionInfo.phase -> Symtab.key -> 
        FunctionInfo.function_info option;
  val define_function_declaration:  {concealed_named_theorems:bool} ->
        string -> FunctionInfo.skip_info -> FunctionInfo.phase -> string -> thm -> local_theory -> local_theory;
  val corres_thm_attribute: string -> FunctionInfo.skip_info -> FunctionInfo.phase -> string -> attribute;
  val no_throw_thm_attribute: string -> FunctionInfo.skip_info -> FunctionInfo.phase -> string -> attribute;
  val induct_thms_declaration: string -> FunctionInfo.skip_info -> FunctionInfo.phase -> string -> thm list -> local_theory -> local_theory
  val corres_named_thms: FunctionInfo.phase -> string

  val impl_thm_name: ProgramInfo.prog_info -> FunctionInfo.phase -> string -> string
  val corres_thm_name: ProgramInfo.prog_info -> FunctionInfo.phase -> string -> string

  val definition_locale : Proof.context -> FunctionInfo.skip_info -> FunctionInfo.phase -> string -> string list -> string
  val corres_proof_locale : Proof.context -> FunctionInfo.skip_info -> FunctionInfo.phase -> string ->  string list -> string
  val phase_prefix : FunctionInfo.phase -> string

  (* Generate initial function_info from the C Parser's output. *)
  val init_function_info : FunctionInfo.skip_info -> ProgramInfo.prog_info -> theory -> (FunctionInfo.function_info Symtab.table * theory);

  val canonical_imports: theory -> ((string * term) list * xstring) list -> Expression.expression_i
  val mk_l1monadT : typ -> typ
  val mk_l2monadT : typ -> typ -> typ -> typ
  val dest_exn_monad_result_type : typ -> {exT: typ, resT: typ, stateT: typ}
  val dest_monad_type : typ -> {exT: typ, resT: typ, stateT: typ}
  val range_types_of_exn_monad: term -> {exT: typ, resT: typ, stateT: typ}
  val state_type_of_exn_monad: term -> typ 
  val res_type_of_exn_monad: term -> typ 
  val ex_type_of_exn_monad: term -> typ 

  val progenvN : string

  val global_impl_corres_bundle : FunctionInfo.phase -> string -> string
  val intern_global_impl_corres_bundle : theory -> FunctionInfo.phase -> xstring -> string
  val perhaps_intern_global_impl_corres_bundle : theory -> FunctionInfo.phase -> xstring -> string

  val global_corres_locale : FunctionInfo.phase -> string -> string
  val intern_global_corres_locale : theory -> FunctionInfo.phase -> xstring -> string
  val perhaps_intern_global_corres_locale : theory -> FunctionInfo.phase -> xstring -> string

  val final_corres_locale: string list -> string
  val intern_final_corres_locale: theory -> string list -> string

  val final_all_corres_locale: string -> string
  val intern_final_all_corres_locale: theory -> string -> string

  val final_all_impl_locale: string -> string
  val intern_final_all_impl_locale: theory -> string -> string

  val progenv_insts: Proof.context -> ProgramInfo.prog_info -> FunctionInfo.phase -> (string * term) list
  val dest_progenv_inst: term -> (string * typ)
  val progenv_insts_grouped_by_cty: {per_ctype:bool} -> Proof.context -> ProgramInfo.prog_info ->
        (string * (term * (FunctionInfo.phase * string * typ * typ list * int CType.ctype))) list list
  val progenv_names: Proof.context -> ProgramInfo.prog_info -> FunctionInfo.phase -> string list
  val get_progenv_for: Proof.context -> ProgramInfo.prog_info -> FunctionInfo.phase -> string -> string -> string * term
  val get_progenv_for_sig: Proof.context -> ProgramInfo.prog_info -> string -> FunctionInfo.phase ->
          typ * typ list -> (string * term) option
  val get_progenv_for_cty: Proof.context -> ProgramInfo.prog_info -> string -> FunctionInfo.phase ->
              int CType.ctype -> (string * term * (typ * typ list)) option
  val get_sig_for_fn_ptr: Proof.context -> ProgramInfo.prog_info -> string -> FunctionInfo.phase ->
              int CType.ctype -> (typ * typ list) option

  type fn_ptr_info = {idx: int, args: (string * typ) list, ret: (string * typ) list, ptr_val: string * typ, 
         prog_env: term}
  val retT_from_fn_ptr_info : fn_ptr_info -> typ

  val mk_fn_ptr_infos: Proof.context -> ProgramInfo.prog_info -> string -> 
        term list -> FunctionInfo.function_info -> (string * (FunctionInfo.phase -> fn_ptr_info)) list

  val add_definition_and_corres_proof_locales:
    ProgramInfo.prog_info -> string option ->
    FunctionInfo.function_info Symtab.table -> FunctionInfo.skip_info -> FunctionInfo.phase -> Symtab.key list -> theory -> string * local_theory
  val add_impl_locales: FunctionInfo.skip_info -> ProgramInfo.prog_info -> FunctionInfo.function_info Symtab.table -> FunctionInfo.phase -> (string * (term -> term)) list ->
          string list -> theory -> theory
  val add_final_corres_proof_locale: FunctionInfo.skip_info -> ProgramInfo.prog_info -> string list -> theory -> theory
  val add_final_all_impl_locale: ProgramInfo.prog_info -> string list -> theory -> theory
  val add_final_all_corres_locale: ProgramInfo.prog_info -> string list -> theory -> theory

  val prove_and_note_fun_ptr_intros: bool -> FunctionInfo.phase * FunctionInfo.phase -> ProgramInfo.prog_info ->
        (local_theory -> (term * string) * (term * string) -> (string * thm) list) -> 
        local_theory -> local_theory

  val add_global_corres_locale: FunctionInfo.phase * FunctionInfo.phase -> ProgramInfo.prog_info ->
        (FunctionInfo.phase -> term -> term -> term -> Proof.context -> ((term * Token.src list) * Proof.context) option) -> 
        theory -> theory

  structure FunctionInfo: GENERIC_DATA;

  val transfer_ac_slots: Proof.context -> Proof.context -> Proof.context
  val in_locale_result: xstring -> (local_theory -> 'a * local_theory) -> local_theory -> 'a * local_theory;
  val in_locale: xstring -> (local_theory -> local_theory) -> local_theory -> local_theory; 
  val in_theory_result: (theory -> 'a * theory) -> local_theory -> 'a * local_theory;
  val in_theory: (theory -> theory) -> local_theory -> local_theory;
  val in_theory_result': (local_theory -> 'a * local_theory) -> local_theory -> 'a * local_theory;
  val in_theory': (local_theory -> local_theory) -> local_theory -> local_theory;
end

structure AutoCorresData : AUTOCORRES_DATA =
struct


structure FI = FunctionInfo;

(* Function translation information.
 * This is needed for resuming incremental translations. *)
structure FunctionInfo = Generic_Data(
  type T = FunctionInfo.function_info Symtab.table
             FunctionInfo.Phasetab.table Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.join (fn filename => FunctionInfo.Phasetab.join (fn phase => 
    Symtab.join (fn name => (Utils.fast_merge (fn (info1, info2) => 
      (FunctionInfo.merge info1 info2))))));
)



val ac_slots = [AutoCorresTrace.transfer_trace_info, AutoCorres_Options.Options_Proof.transfer] 
val transfer_ac_slots = Utils.transfer_slots ac_slots
fun in_locale_result name = Utils.gen_in_locale_result ac_slots name
fun in_locale name = Utils.gen_in_locale ac_slots name
fun in_theory_result f = Utils.gen_in_theory_result ac_slots f
val in_theory = Utils.gen_in_theory ac_slots
fun in_theory_result' f = Utils.gen_in_theory_result' ac_slots f
val in_theory' = Utils.gen_in_theory' ac_slots


fun get_phase_info context filename phase =
  FunctionInfo.get context
  |> (fn file_tab => Symtab.lookup file_tab filename)
  |> Option.mapPartial (fn phase_tab => FI.Phasetab.lookup phase_tab phase)

fun get_default_phase_info context filename phase =
  case get_phase_info context filename phase of 
    SOME info => info 
  | NONE => Symtab.empty

fun map_default_phase_info filename phase = fn upd => fn context =>
  context 
  |> (FunctionInfo.map o Symtab.map_default (filename, FI.Phasetab.empty) o FI.Phasetab.map_default (phase, Symtab.empty)) upd

fun get_function_info context filename phase fname =
  FunctionInfo.get context
  |> (fn file_tab => Symtab.lookup file_tab filename)
  |> Option.mapPartial (fn phase_tab => FI.Phasetab.lookup phase_tab phase)
  |> Option.mapPartial (fn info_tab => Symtab.lookup info_tab fname) 

fun get_definition_clique ctxt skips phase filename clique =
 case clique of [] => []
 | name:: _ => 
    let
      (* Note that in the current construction the definition of a function is still made in a 
       * locale based on the clique-information of the previous phase.
       * In rare cases the clique might get split up in a phase due to dead-code elimination.
       *)
      val def_phase = case phase of FI.CP => FI.CP | _ => FI.prev_phase skips phase
    in
      case Option.map FI.get_clique (get_function_info (Context.Proof ctxt) filename def_phase name) of
        SOME clique => Symset.dest clique 
      | NONE => clique 
    end 

fun phase_prefix phase =
  FI.string_of_phase phase |> String.translate (str o Char.toLower) |> suffix "_"

(* Generate a L1 monad type. *)
fun mk_l1monadT stateT =
(* FIXME: use antiquotation *)
  Utils.gen_typ @{typ "'a L1_monad"} [stateT]

(* Make an L2 monad. *)
fun mk_l2monadT stateT retT exT =
  let
  in
(* FIXME: use antiquotation *)
    Utils.gen_typ @{typ "('a, 'b, 'c) exn_monad"} [exT, retT, stateT]
  end


val progenvN = "\<P>"

local

val l1_progenvN = progenvN
fun l1_progenvT stateT = @{typ "unit ptr"} --> mk_l1monadT stateT


fun dest_wordT (Type (@{type_name "word"}, [Type(@{type_name "signed"}, [T])])) = (true, Word_Lib.dest_binT T)
  | dest_wordT T = (false, Word_Lib.dest_wordT T)

fun abs_word_type opt T =
  case try dest_wordT T of
     SOME (true, _) => if ProgramInfo.get_signed_abs opt then @{typ int} else T
   | SOME (false,_) => if ProgramInfo.get_unsigned_abs opt then @{typ nat} else T
   | NONE => T

fun mk_progenvN name cty = progenvN ^ "_" ^ name ^ CType.tyname cty;
fun l2_progenvN phase cty = mk_progenvN (phase_prefix phase) cty;

fun mk_progenvT mk_monadT ctxt stateT abs_type (CType.Function (retT, argTs)) =
      let
        val retT' = abs_type (CalculateState.ctype_to_typ ctxt retT)
        val argTs' = map (abs_type o CalculateState.ctype_to_typ ctxt) argTs
        val monadT = mk_monadT stateT retT' HP_TermsTypes.c_exntype_ty
        val T = @{typ "unit ptr"} --> (argTs' ---> monadT)
      in
        (T, (retT', argTs'))
      end
  | mk_progenvT _ _ _ _ cty = error ("mk_progenvT: expecting function type got " ^ quote (@{make_string} cty))

val l2_progenvT = mk_progenvT mk_l2monadT 

 

fun ts_progenvT (monad_info: Monad_Types.monad_type) =
  let
    fun mk_monadT stateT resT exT = #typ_from_L2 monad_info {stateT=stateT, resT =  resT, exT = exT}
  in
    mk_progenvT mk_monadT
  end

(* FIXME: can we simplify the setup of progenv names ?  *)     
fun progenvN ctxt prog_info ts_monad_name phase cty =
  let
    val prog_name = ProgramInfo.get_prog_name prog_info 
    val naming = ProgramInfo.get_naming prog_info
    fun full_name base_name =
      Name_Space.full_name naming 
       (Binding.qualify false prog_name (Binding.name base_name)) 
  in             
    case phase of
      FI.CP => ProgramInfo.get_gamma prog_info |> dest_Const |> fst
    | FI.L1 => full_name l1_progenvN 
    | FI.L2 => full_name (l2_progenvN FI.L2 cty)
    | FI.IO => full_name (l2_progenvN FI.IO cty)
    | FI.HL => full_name (l2_progenvN FI.HL cty)
    | FI.WA => full_name (l2_progenvN FI.WA cty)
    | FI.TS => full_name (mk_progenvN (ts_monad_name |> suffix "_" ) cty)
    | _ => error ("progenvN not defined for phase " ^ quote (@{make_string} phase))
  end
fun get_stateT prog_info opt = 
 if ProgramInfo.get_heap_abs opt andalso not (ProgramInfo.get_skip_heap_abs opt)
 then the (ProgramInfo.get_lifted_globals_type prog_info)
 else ProgramInfo.get_globals_type prog_info
 
fun progenvT ctxt (prog_info: ProgramInfo.prog_info) ts_monad_name phase (cty, opt) =
  case phase of
    FI.CP => (ProgramInfo.get_gamma prog_info |> fastype_of, (dummyT, []))
  | FI.L1 => (l1_progenvT (ProgramInfo.get_state_type prog_info), (dummyT, []))
  | FI.L2 => l2_progenvT ctxt (ProgramInfo.get_globals_type prog_info) I cty
  | FI.IO => l2_progenvT ctxt (ProgramInfo.get_globals_type prog_info) I cty
  | FI.HL => l2_progenvT ctxt (get_stateT prog_info opt) I cty
  | FI.WA => l2_progenvT ctxt (get_stateT prog_info opt) (abs_word_type opt) cty
  | FI.TS => 
     case Symtab.lookup (Monad_Types.TSRules.get (Context.Proof ctxt)) ts_monad_name of
        SOME info => ts_progenvT info ctxt (get_stateT prog_info opt) (abs_word_type opt) cty
      | NONE => error ("progenvT monad_name undefined: " ^ quote ts_monad_name)
  | _ => error ("progenvT not defined for phase " ^ quote (@{make_string} phase))

fun progenv_inst' ctxt prog_info ts_monad_name phase (cty, opt) =
 let                                     
   val name = progenvN ctxt prog_info ts_monad_name phase cty
   val (T, (retT, argTs)) = progenvT ctxt prog_info ts_monad_name phase (cty, opt)
 in
  (Long_Name.base_name name, (Const (name, T), (phase, ts_monad_name, retT, argTs, cty)))
 end


fun progenv_inst ctxt prog_info ts_monad_name phase cty =
   let 
     val (n, (t, _)) = progenv_inst' ctxt prog_info ts_monad_name phase cty
   in  
     (n, t)
   end
         
fun ctype_of (retty, _, var_infos) = CType.Function (retty, map ProgramAnalysis.get_vtype var_infos)
in
fun progenv_insts' {per_ctype} ctxt (prog_info: ProgramInfo.prog_info) phase = 
  let
    val cse = ProgramInfo.get_csenv prog_info
    val fninfo = ProgramAnalysis.get_fninfo cse
    val fun_ptr_funs = ProgramAnalysis.get_functions_used_via_fun_ptr cse 
      |> map (fn fname => (fname, ctype_of (the (Symtab.lookup fninfo fname))))
    val grouped = Utils.buckets (fn ((_, cty1), (_, cty2)) => cty1 = cty2) fun_ptr_funs
    val fun_ptr_parameter_types = ProgramAnalysis.all_fun_ptr_parameter_types cse
    val method_ptr_types = ProgramAnalysis.all_method_fun_ptr_types cse
    val fun_opts = ProgramInfo.get_fun_options prog_info
    fun options_of_group [] = error ("progenv_insts': empty function group")
      | options_of_group ((n, cty)::fs) =
        let
          val names = n::map fst fs
          val options = map fun_opts names |> distinct (op =)
        in 
          case options of 
            [opt] => (cty, opt)
          | _ => error ("progenv_insts': function group has different options " ^ @{make_string} (names, options))
        end
     
    val ts_monad_names = if phase = FI.TS 
          then Monad_Types.TSRules.get (Context.Proof ctxt) |> Symtab.keys 
          else [""]
    val fun_types = map options_of_group grouped
    val decl_only_types = fun_ptr_parameter_types @ method_ptr_types 
        |> sort_distinct (CType.ctype_ord int_ord)
        |> filter_out (member (fn (t, (t', _)) => t = t') fun_types)
        |> map (rpair (ProgramInfo.get_fun_options prog_info ""))
  in
    fun_types @ decl_only_types
    |> map (fn (cty, opt) => 
        map (fn mn => progenv_inst' ctxt prog_info mn phase (cty,opt)) ts_monad_names) 
    |> flat 
    |> distinct (fn ((n, (_, (_, _, _, _, cty1))), (m, (_,(_, _, _, _, cty2)))) => n = m andalso if per_ctype then cty1 = cty2 else true)
  end

fun progenv_insts_grouped_by_cty per_ctype ctxt prog_info =
  let
    val all = map (progenv_insts' per_ctype ctxt prog_info) FI.phases |> flat
    val cty_eq = (op =) o apply2 (#5 o #2 o #2)
  in
    group_by cty_eq all
  end

fun progenv_insts ctxt (prog_info: ProgramInfo.prog_info) phase =
  map (fn (n, (t, _)) => (n, t)) (progenv_insts' {per_ctype=false} ctxt prog_info phase)


fun get_progenv_for ctxt (prog_info: ProgramInfo.prog_info) phase ts_monad_name fname = 
  let
    val cse = ProgramInfo.get_csenv prog_info
    val fninfo = ProgramAnalysis.get_fninfo cse
    val all = progenv_insts ctxt prog_info phase
    fun check inst = if member (op =) all inst then inst else 
       error ("get_progenv_for no environment for function " ^ quote fname)
  in
    case Symtab.lookup fninfo fname |> Option.map ctype_of of
      SOME cty => 
         check (progenv_inst ctxt prog_info ts_monad_name phase 
                  (cty, ProgramInfo.get_fun_options prog_info fname)) 
     | _ => error ("get_progenv_for: undefined function " ^ quote fname)
  end

fun get_progenv_for_sig ctxt (prog_info: ProgramInfo.prog_info) ts_monad_name phase (retT, argTs) = 
  let
    val all = progenv_insts' {per_ctype=false} ctxt prog_info phase
    fun match (n, (t, (phase', ts_monad_name', retT', argTs', cty))) =
      if member (op =) [FI.CP, FI.L1] phase orelse 
         (retT' = retT andalso argTs' = argTs andalso 
            (phase <> FI.TS orelse ts_monad_name' = ts_monad_name))
      then SOME (n, t) 
      else NONE
  in
    get_first match all
  end

fun get_progenv_for_cty ctxt (prog_info: ProgramInfo.prog_info) ts_monad_name phase cty = 
  let
    val all = progenv_insts' {per_ctype=false} ctxt prog_info phase
    fun match (n, (t, (phase', ts_monad_name', retT', argTs', cty'))) =
      if member (op =) [FI.CP, FI.L1] phase orelse  
         (cty = cty' andalso 
           (phase <> FI.TS orelse ts_monad_name' = ts_monad_name))
      then SOME (n, t, (retT', argTs')) 
      else NONE
  in
    get_first match all
  end

fun dest_progenv_inst (Const(n, T)) = (n, T)
  | dest_progenv_inst t = raise TERM ("dest_progenv_insts: unexpected term", [t])


fun get_sig_for_fn_ptr ctxt (prog_info: ProgramInfo.prog_info) ts_monad_name phase cty =
  get_progenv_for_cty ctxt prog_info ts_monad_name phase cty 
  |> Option.map (#3)


fun mk_positional_args pargTs =
  tag_list 0 pargTs
  |> map (fn (idx, (cT, T)) => (NameGeneration.positional_name false "in" idx cT, T))



type fn_ptr_info = {
  idx: int, 
  args: (string * typ) list, 
  ret: (string * typ) list, 
  ptr_val: (string * typ), 
  prog_env: term}



fun get_fn_ptr_param_info ctxt (prog_info: ProgramInfo.prog_info) ts_monad_name (pname, idx) (cretT, cargTs) phase =
  let
    val cty = CType.Function (cretT, cargTs)
    val (retT, argTs) = the (get_sig_for_fn_ptr ctxt prog_info ts_monad_name phase cty)
    val prog_env = get_progenv_for_cty ctxt prog_info ts_monad_name phase cty |> the |> #2 
    val args = if member (op =) [FI.CP, FI.L1] phase then [] else mk_positional_args (cargTs ~~ argTs) 
    val ret = if retT = @{typ unit} then [] else [(string_of_int (length args), retT)]
    val ptr_val = (pname, @{typ "unit ptr"})
  in
   {idx = idx, args = args, ret = ret, ptr_val = ptr_val, prog_env = prog_env}
  end

fun mk_fn_ptr_infos ctxt prog_info ts_monad_name fargs finfo =
   FI.get_fn_ptr_args_info finfo |> map (fn (n, (idx, (cretT, cargTs))) =>
    let
      val n' = case try (nth fargs) (idx - 1) of SOME (Free (n', _)) => n' | _ => n 
    in
      (NameGeneration.ensure_varname n, 
         fn phase => get_fn_ptr_param_info ctxt prog_info ts_monad_name  
          (n', idx) (cretT, cargTs) phase) 
    end)

fun retT_from_fn_ptr_info {ret,...} = 
  case ret of
    [] => @{typ unit}
  | [(_, retT)] => retT
  | _ => error ("retT_from_fn_ptr_info: multiple return values unsupported")

end

val corresN = "corres"
val definitionN = "definition"
val implN = "impl"

fun progenv_names ctxt prog_info phase = map fst (progenv_insts ctxt prog_info phase)

 
fun global_impl_corres_bundle phase filename = filename ^ "_" ^ phase_prefix phase  ^ implN ^ "_" ^ corresN;

fun intern_global_impl_corres_bundle thy phase filename =
  NameGeneration.intern_bundle thy (global_impl_corres_bundle phase filename)

fun perhaps_intern_global_impl_corres_bundle thy phase filename =
 the_default filename (try (intern_global_impl_corres_bundle thy phase) filename)

fun global_corres_locale phase filename = filename ^ "_" ^ phase_prefix phase  ^ corresN;

fun intern_global_corres_locale thy phase filename =
  NameGeneration.intern_locale thy (global_corres_locale phase filename)

fun perhaps_intern_global_corres_locale thy phase filename =
 the_default filename (try (intern_global_corres_locale thy phase) filename)


fun final_corres_locale clique = corresN ^ "_" ^ (space_implode "_" clique);
fun intern_final_corres_locale thy clique =
  NameGeneration.intern_locale thy (final_corres_locale clique)

fun final_all_corres_locale filename = filename ^ "_all_" ^ corresN;
fun intern_final_all_corres_locale thy filename =
  NameGeneration.intern_locale thy (final_all_corres_locale filename)

fun final_all_impl_locale filename = filename ^ "_all_" ^  implN;
fun intern_final_all_impl_locale thy filename =
  NameGeneration.intern_locale thy (final_all_impl_locale filename)

fun gen_implementation_locale infer_clique ctxt skips phase filename clique =
 let
   val def_clique = if infer_clique then get_definition_clique ctxt skips phase filename clique else clique
   val thy = Proof_Context.theory_of ctxt
 in
   case phase of
     FI.CP => NameGeneration.intern_impl_clique_locale_name thy def_clique
   | _  => NameGeneration.maybe_intern_locale thy (phase_prefix phase ^ implN ^ "_" ^ (space_implode "_" def_clique))
 end

val implementation_locale = gen_implementation_locale true

fun gen_definition_locale infer_clique ctxt skips phase filename clique =
 let
   val def_clique = if infer_clique then get_definition_clique ctxt skips phase filename clique else clique
   val thy = Proof_Context.theory_of ctxt
 in
   case phase of
     FI.CP => NameGeneration.intern_impl_clique_locale_name thy def_clique
   | _  => NameGeneration.maybe_intern_locale thy (phase_prefix phase ^ definitionN ^ "_" ^ (space_implode "_" def_clique))
 end

val definition_locale = gen_definition_locale true;

fun gen_corres_proof_locale infer_clique ctxt skips phase filename clique =
  let
    val def_clique = if infer_clique then get_definition_clique ctxt skips phase filename clique else clique
    val thy = Proof_Context.theory_of ctxt
  in
    case phase of
      FI.CP => error ("corres_proof_locale: not defined for CP")
    | _ => NameGeneration.maybe_intern_locale thy (phase_prefix phase ^ corresN ^ "_" ^ (space_implode "_" def_clique))
  end

val corres_proof_locale = gen_corres_proof_locale true;

fun canonical_imports thy is =
  let
    val vars = is |> map #1 |> flat |> map #1 |> distinct (op =)
  in
    (map (fn (insts, loc) => HPInter.import insts thy loc) is, map HPInter.for_clause vars)
  end

local
  structure HP = HPInter;
  fun performs_indirect_calls thy filename clique =
    map_filter (get_function_info (Context.Theory thy) filename FI.CP) clique 
    |> exists (FI.performs_indirect_calls)
in



fun requires_progenv thy prog_info finfos clique = 
  let
    val csenv = ProgramInfo.get_csenv prog_info
    val filename = ProgramInfo.get_prog_name prog_info
    val all_addressed_funs = ProgramAnalysis.get_all_addressed_funs csenv 
    val reachable_funs = FI.reachable_direct_callees finfos clique |> Symset.dest
    val result = exists (member (op =) all_addressed_funs) reachable_funs orelse 
          exists (ProgramAnalysis.has_fun_ptr_parameters csenv) reachable_funs orelse
          performs_indirect_calls thy filename reachable_funs
 in
   result
 end

fun add_alias_locale super name thy = 
  thy 
  |> HP.add_locale (Binding.name name) (Binding.name name) (canonical_imports thy [([], super)]) []
  ||> Local_Theory.exit_global
  |> (fn (name, thy) => thy |> HP.immediate_global_sublocale super name)
  

fun add_definition_and_corres_proof_locales (prog_info:ProgramInfo.prog_info) base_locale_opt
  finfos skips phase clique thy =
  let 
    val prev_phase = FI.prev_phase skips phase
    val csenv = ProgramInfo.get_csenv prog_info
    val has_methods = exists (member (op =) (ProgramInfo.get_method_callers prog_info)) clique
    val filename = ProgramInfo.get_prog_name prog_info
    val ctxt = Proof_Context.init_global thy
    val def_clique = get_definition_clique ctxt skips phase filename clique
    val all_addressed_funs = ProgramAnalysis.get_all_addressed_funs csenv 
    val is_addressed = exists (member (op =) all_addressed_funs) clique
    val requires_progenv = requires_progenv thy prog_info finfos 
    val clique_has_fn_ptr_calls = requires_progenv clique
    val uses_globals = exists (ProgramAnalysis.uses_globals csenv) clique

    fun get_referenced_funs fname = 
     the_list (Symtab.lookup finfos fname) |> map (fn info => 
        Symset.union (FI.get_callees info) (FI.get_fun_ptr_dependencies info)) 
        |> Symset.union_sets |> Symset.dest

    val referenced_other_funs = map get_referenced_funs clique
      |> flat |> distinct (op =) |> filter_out (member (op =) clique)

    val defL = definition_locale ctxt skips phase filename clique
    val defLs = map (gen_definition_locale false ctxt skips phase filename o single) clique
    val imports_def =
      (if is_some base_locale_opt then [([], the base_locale_opt)] else []) @
      (if uses_globals then [([], NameGeneration.intern_globals_locale_name thy filename)] else []) @
      (if phase = FI.L1 
          then if clique_has_fn_ptr_calls 
               then [([], NameGeneration.intern_impl_clique_locale_name thy def_clique)]
               else [] 
          else []) @
      map (fn fname => ([], gen_implementation_locale false ctxt skips phase filename [fname])) 
        referenced_other_funs
    val corresL = corres_proof_locale ctxt skips phase filename clique
    val corresLs = map (gen_corres_proof_locale false ctxt skips phase filename o single) clique
    fun dep_corres name = corres_proof_locale ctxt skips phase filename [name]
    fun dep_corres_l1 name = corres_proof_locale ctxt skips FI.L1 filename [name]
    val imports_corres =
      (if has_methods andalso phase <> FI.IO then [([], intern_global_corres_locale thy phase filename)] else []) @
      map (fn l => ([], l)) (
         [implementation_locale ctxt skips prev_phase filename clique] @ 
         map dep_corres referenced_other_funs @ 
         (if phase = FI.L2 then map dep_corres_l1 referenced_other_funs else [])) @
      map (fn l => ([], l)) (
         [defL])
  in
    thy 
    |> HP.add_locale (Binding.name defL) (Binding.name defL)
        (canonical_imports thy imports_def) 
        []
    ||> Local_Theory.exit_global 
    |> (fn (defL, thy) => thy |> length clique > 1 ? fold (add_alias_locale defL) defLs)
    |> (fn thy => thy 
    |> HP.add_locale (Binding.name corresL) (Binding.name corresL)
        (canonical_imports thy imports_corres) 
        [])
    ||> (member (op =) [FI.HL, FI.WA, FI.TS] phase andalso is_addressed) ? Bundle.unbundle [perhaps_intern_global_impl_corres_bundle thy phase filename]
    ||> Local_Theory.exit_global                                                             
    |> (fn (corresL, thy) => thy 
    |> length clique > 1 ? fold (add_alias_locale corresL) corresLs
    |> Named_Target.init [] corresL
    |> pair corresL)
  end

val add_definition_and_corres_proof_locales = fn prog_info => fn base_locale_opt => fn finfos => fn phase => fn prev_phase => fn clique => fn thy =>
 let
   val ctxt = Proof_Context.init_global thy
 in
   thy |> Utils.timeap_msg 1 ctxt (fn _ => "definition and corres locales " ^ @{make_string} clique) (
      add_definition_and_corres_proof_locales prog_info base_locale_opt finfos phase prev_phase clique)
 end


fun add_final_corres_proof_locale skips (prog_info:ProgramInfo.prog_info) clique thy =
  let
    val ctxt = Proof_Context.init_global thy
    val loc = final_corres_locale clique
    val locs = map (final_corres_locale o single) clique
    val skip_word_abs = exists (ProgramInfo.get_skip_word_abs o ProgramInfo.get_fun_options prog_info) clique
    val skip_heap_abs = exists (ProgramInfo.get_skip_heap_abs o ProgramInfo.get_fun_options prog_info) clique
    val skip_io_abs = exists (ProgramInfo.skip_in_out_abs o ProgramInfo.get_fun_options prog_info) clique
    val phases = drop 1 FI.phases 
      |> filter_out (fn phase => skip_word_abs andalso phase = FI.WA)
      |> filter_out (fn phase => skip_heap_abs andalso phase = FI.HL)      
      |> filter_out (fn phase => skip_io_abs andalso phase = FI.IO)
    val imports = map (fn phase => ([], 
           corres_proof_locale ctxt skips phase (ProgramInfo.get_prog_name prog_info) clique)) phases
  in
    thy
    |> HP.add_locale (Binding.name loc) (Binding.name loc)
        (canonical_imports thy imports) 
        []
    ||> Local_Theory.exit_global
    |> (fn (loc, thy) => thy
    |> length clique > 1 ? fold (add_alias_locale loc) locs)
  end

fun add_final_all_impl_locale (prog_info:ProgramInfo.prog_info) all_funs thy =
  let
    val ctxt = Proof_Context.init_global thy
    val filename = ProgramInfo.get_prog_name prog_info
    val allL = final_all_impl_locale filename
    val imports = all_funs 
      |> map (fn fname => ([],
        gen_implementation_locale false ctxt {skip_io_abs=false,skip_heap_abs=false,skip_word_abs=false}\<comment> \<open>irrelevant because infer_clique=false\<close>
          FI.TS filename [fname]))
  in
    thy
    |> HP.add_locale (Binding.name allL) (Binding.name allL)
       (canonical_imports thy imports)
       []
    |> snd
    |> Local_Theory.exit_global
  end

fun add_final_all_corres_locale (prog_info:ProgramInfo.prog_info) all_funs thy =
  let
    val filename = ProgramInfo.get_prog_name prog_info
    val allL = final_all_corres_locale filename
    val imports = all_funs 
      |> map (fn fname => ([], final_corres_locale [fname]))
  in
    thy
    |> HP.add_locale (Binding.name allL) (Binding.name allL)
       (canonical_imports thy imports)
       []
    |> snd
    |> Local_Theory.exit_global
  end


end


fun impl_thm_name prog_info phase name =
  ProgramInfo.get_mk_fun_name prog_info phase "" name ^ "_" ^ implN

fun corres_thm_name prog_info phase name =
  ProgramInfo.get_mk_fun_name prog_info phase "" name ^ "_" ^ "corres"

fun default_info filename skips phase name context = 
  case phase of 
    FI.CP => FI.empty_info name phase 
  | phase => (case get_function_info context filename (FI.prev_phase skips phase) name of
                SOME info => FI.init_from_old phase info
             | NONE => FI.init_from_old phase (default_info filename skips (FI.prev_phase skips phase) name context));

fun map_default_info filename skips phase name = fn upd => fn context =>
  let
    val default_info = default_info filename skips phase name context
    val context = context 
      |> (FunctionInfo.map o Symtab.map_default (filename, FI.Phasetab.empty) o FI.Phasetab.map_default (phase, Symtab.empty) o 
         Symtab.map_default (name, default_info)) upd
  in  
    context
  end

fun dest_sumT (Type (@{type_name sum}, [T1, T2])) = (T1, T2)
  | dest_sumT T = raise TYPE ("dest_sumT", [T], []);

fun range_types_of_exn_monad monad = monad |> fastype_of |> FI.dest_exn_monad_type |> snd
    

val state_type_of_exn_monad = #stateT o range_types_of_exn_monad
val res_type_of_exn_monad = #resT o range_types_of_exn_monad
val ex_type_of_exn_monad = #exT o range_types_of_exn_monad


fun dest_exn_monad_result_type T =
   FI.dest_exn_monad_type T |> snd


fun dest_monad_type \<^Type>\<open>spec_monad E A S\<close> = {exT = E, resT = A, stateT = S}
  | dest_monad_type \<^Type>\<open>option A\<close> = {exT = @{typ unit}, resT = A, stateT = @{typ unit}} \<comment> \<open>option monad\<close>
  | dest_monad_type T = {exT = @{typ unit},  resT = T, stateT = @{typ unit}} \<comment> \<open>pure\<close>


fun strip_monad_type T = strip_type T |> apsnd dest_monad_type
val range_monad_type = strip_monad_type #> snd

val range_monad = fastype_of #> range_monad_type


  
fun chop_while P xs = 
 let
   fun chop goods [] = (rev goods, [])
     | chop goods (x::xs) = if P x then chop (x::goods) xs else (rev goods, x::xs)
 in
   chop [] xs
 end 
  
fun corres_named_thms phase =
  case phase of
    FI.L1 => @{named_theorems AutoCorres.l1_corres}
  | FI.L2 => @{named_theorems AutoCorres.l2_corres}
  | FI.IO => @{named_theorems AutoCorres.io_corres}
  | FI.HL => @{named_theorems AutoCorres.hl_corres}
  | FI.WA => @{named_theorems AutoCorres.wa_corres}
  | FI.TS => @{named_theorems AutoCorres.ts_corres}
  | _ => error ("corres_named_thms not defined for phase: " ^ @{make_string} phase)
                                   
fun add_corres_thm phase thm =
  Named_Theorems.add_thm (corres_named_thms phase) thm
  #> Named_Theorems.add_thm @{named_theorems AutoCorres.ac_corres} thm
  #> phase = FI.IO ? (fn context => context |> 
       Synthesize_Rules.add_rule @{synthesize_rules_name refines_in_out} {only_schematic_goal = false}
         (Utils.guess_binding_of_thm (Context.proof_of context) thm) 10 thm)



fun def_named_thms phase =
  case phase of                                                       
    FI.L1 => @{lazy_named_theorems AutoCorres.l1_def}
  | FI.L2 => @{lazy_named_theorems AutoCorres.l2_def}
  | FI.IO => @{lazy_named_theorems AutoCorres.io_def}
  | FI.HL => @{lazy_named_theorems AutoCorres.hl_def}
  | FI.WA => @{lazy_named_theorems AutoCorres.wa_def}
  | FI.TS => @{lazy_named_theorems AutoCorres.ts_def}
  | _ => error ("def_named_thms not defined for phase: " ^ @{make_string} phase)


val is_theory = Context.cases (K true) (Named_Target.is_theory)



fun add_def name def phi context =
  if not (is_theory context) then
    let    
    in
       context
       |> Lazy_Named_Theorems.add_lazy_thm name def [] phi 
    end
  else context
                     
fun add_def_thm concealed phase thm phi =
  if concealed then I else
  add_def (def_named_thms phase) thm phi
  #> add_def @{lazy_named_theorems AutoCorres.ac_def} thm phi

fun timeit_declaration level msg spec f =
  Local_Theory.declaration spec (fn phi => fn context =>
    Utils.timeap_msg level (Context.proof_of context) msg (f phi) context)

fun timeit_declaration_attribute level msg f =
  Thm.declaration_attribute (fn thm => fn context =>
    Utils.timeap_msg level (Context.proof_of context) msg (f thm) context)

fun phase_msg kind phase descr name = fn _ => kind ^ " " ^ descr ^ " (" ^ (FI.string_of_phase phase) ^ ") "  ^ name 

val attrib_msg = phase_msg "ATTRIBUTE"

fun corres_thm_attribute filename skips phase name = 
  timeit_declaration_attribute 3 (attrib_msg phase "corres" name) (fn thm => fn context => 
    let
      val thm = case phase of FI.L2 => CLocals.unfolded_with [filename, name] (Context.proof_of context) thm | _ => thm
      val new_info = FI.map_corres_thm (K (Thm.trim_context thm))
    in
      context 
      |> map_default_info filename skips phase name new_info
      |> add_corres_thm phase thm
    end)

fun no_throw_thm_attribute filename skips phase name = 
  timeit_declaration_attribute 3 (attrib_msg phase "no_throw" name) (fn thm => 
    let
      val new_info = FI.map_no_throw_thm (K (SOME (Thm.trim_context thm)))
    in
      map_default_info filename skips phase name new_info
    end)

fun induct_thms_declaration filename skips phase name = 
  fn thms => timeit_declaration 3 (attrib_msg phase "induct" name) {pervasive=true, syntax=false, pos=\<^here>} (fn phi => fn context =>
    let
      val thms = map Thm.trim_context thms
      val thms = Lazy.lazy (fn () => (map (Morphism.thm phi) thms))
      val new_info = FI.set_lazy_induct_thms thms
    in
      context |> map_default_info filename skips phase name new_info
    end
  )

fun init_function_info skips (prog_info: ProgramInfo.prog_info) thy =                            
  case get_phase_info (Context.Theory thy) (ProgramInfo.get_prog_name prog_info) FI.CP of
    SOME infos => (infos, thy)
  | NONE => 
    let
      val lthy = Named_Target.theory_init thy
      val filename = ProgramInfo.get_prog_name prog_info;
      val csenv = ProgramInfo.get_csenv prog_info;
    
      (* Get information about a single function. *)
      fun gen_fn_info name (return_ctype, proto, carg_list) lthy = 
        let
          (* function options *)
          val skips = ProgramInfo.get_skips prog_info name
           
          (* Convert C Parser return type into a HOL return type. *)
          val has_body_spec =  exists (fn StmtDeclDatatype.gcc_attribs _ => false | _ => true) 
               (these (Symtab.lookup (ProgramAnalysis.function_specs csenv) name))
          val return_type =
            if return_ctype = Absyn.Void then
              @{typ unit}
            else
              CalculateState.ctype_to_typ lthy return_ctype;
      
       
          (* Convert arguments into a list of (name, HOL type) pairs. *)
          fun make_var v = 
            (ProgramAnalysis.get_mname v |> MString.dest,
             (CalculateState.ctype_to_typ lthy (ProgramAnalysis.get_vtype v), v))
           
          val args = map make_var carg_list;
          val locals = map make_var (ProgramAnalysis.get_locals csenv name) |> distinct (op =)
          val returns = if return_ctype = Absyn.Void then []
            else map make_var (ProgramAnalysis.get_return_vars csenv name)
          (*
           * Get constant, type signature and definition of the function.
           *
           * The definition may not exist if the function is declared "extern", but
           * never defined. In this case, we replace the body of the function with
           * what amounts to a "fail" command. Any C body is a valid refinement of
           * this, allowing our abstraction to succeed.
           *)
          val const = HP_TermsTypes.mk_fun_ptr lthy (ProgramInfo.get_prog_name prog_info) name;
          val myvars_typ = ProgramInfo.get_state_type prog_info;
          val retvar_name = NameGeneration.return_var_name |> MString.dest
          val undef_thm = 
            if return_ctype = Absyn.Void then
                Thm.instantiate (TVars.make [((("'a", 0), ["HOL.type"]), Thm.ctyp_of lthy myvars_typ)], Vars.empty)
                                 @{thm undefined_function_body_def}
            else 
              let
                val ret_upd = HPInter.raw_abs_update_actual_locvar myvars_typ lthy retvar_name
              in 
                Utils.inst_args lthy [Thm.cterm_of lthy ret_upd] @{thm init_return_undefined_function_body_def}
              end
       
          val (definition, invented) = if proto andalso not has_body_spec then (undef_thm, true) else
                  (Proof_Context.get_thm lthy (Long_Name.implode [Long_Name.localN, name ^ "_body_def"]), false)
                   handle ERROR _ => (undef_thm, true);

          val clique = these (ProgramAnalysis.get_clique csenv name)
          val fun_ptr_dependencies = 
            ProgramAnalysis.get_indirect_fun_ptr_dependencies csenv name
          val clique_fun_ptr_dependencies =
              map (ProgramAnalysis.get_indirect_fun_ptr_dependencies csenv) clique |> flat |> distinct (op =)
          val in_out_parameters = ProgramInfo.get_fun_options prog_info name |> ProgramInfo.get_in_out_parameters
          fun upd_info existing_info = 
            existing_info 
              (* existing_info is either default_info or already complete_info (including call-graph-info) 
               * so we only overwrite what stays invariant in both cases *) 
            |> FI.map_args (K args)
            |> FI.map_locals (K locals)
            |> FI.map_returns (K returns)
            |> FI.map_in_out_parameters (K in_out_parameters)
            |> FI.map_return_type (K return_type)
            |> FI.map_const (K const)
            |> FI.map_definition (K definition)
            |> FI.map_is_simpl_wrapper (K false)
            |> FI.map_invented_body (K invented)
            |> FI.map_fun_ptr_dependencies (K (Symset.make fun_ptr_dependencies))
            |> FI.map_clique_fun_ptr_dependencies (K (Symset.make clique_fun_ptr_dependencies))
            |> FI.map_clique (K (Symset.make clique)) 
        in 
          lthy |> Local_Theory.declaration {pervasive=true, syntax=false, pos=\<^here>} (fn phi => 
              map_default_info filename skips FI.CP name (FI.morph phi o upd_info))
        end
      
      val parser_infos = ProgramAnalysis.get_fninfo csenv |> Symtab.dest
      val lthy = lthy 
        |> fold (fn (name, data as (_, is_proto, _)) => 
               in_locale (definition_locale lthy skips FI.CP filename [name]) (gen_fn_info name data)) 
           parser_infos
  
      val raw_simpl_infos = get_phase_info (Context.Proof lthy) filename FI.CP |> the
      (* We discard the call graph info here.
       * After calling init_function_info, we often want to change some of the entries,
       * which usually requires recalculating it anyway. *)
      val (_, cg_infos) = FI.calc_call_graph raw_simpl_infos;

      val lthy = lthy |> Local_Theory.declaration {pervasive=true, syntax=false,pos=\<^here>} (fn phi => 
        let
        in 
          map_default_phase_info filename FI.CP (Symtab.map (fn name => fn info => 
           info
           |> FI.transfer_call_graph_info (the (Symtab.lookup cg_infos name)) 
           |> FI.morph phi))
        end)
  
      val infos = get_phase_info (Context.Proof lthy) filename FI.CP |> the        
    in
      (infos, Local_Theory.exit_global lthy)
    end;

(* We use a (pervasive) declaration instead of an attribute for definitions to ensure that the
   global versions of the definitions are stored in the FunctionInfo of the theory. 
   This information is used to determine what has already been processed. 
*)
fun define_function_declaration {concealed_named_theorems} filename skips phase name =
  let  
    (* locale parameters are Frees whereas regular parameters are Vars *)              
    fun split_lhs_args t = strip_comb t |> apsnd (chop_while (fn Free _ => true | _ => false))
    fun mk_arg_info (t, info) = let val (n,T) = Utils.dest_name_type t in (n, (T, info)) end;
  in
    fn def => timeit_declaration 3 (attrib_msg phase "def" name) {pervasive=true, syntax=false, pos=\<^here>} (fn phi => fn context =>
      let
        val def = safe_mk_meta_eq def |> Drule.zero_var_indexes
        val info = default_info filename skips phase name context
        val lhs = def |> Thm.prop_of |> Utils.lhs_of_eq 
        val (head, (locale_args, regular_args)) = split_lhs_args lhs
        val arg_var_infos = (if phase = FI.IO then FI.get_args_without_outs info else FI.get_args info)  
          |> map (#2 o #2)
        val def' = Thm.trim_context def
        val def' = Lazy.lazy (fn () => Morphism.thm phi def')
        val lhs' = list_comb (head, locale_args) |> Morphism.term phi
        val new_info = FI.set_lazy_definition def'
          #> FI.map_const (K lhs')
          #> (if phase <> FI.L1 then FI.map_args (K (map mk_arg_info (regular_args ~~ arg_var_infos))) else I)
          #> phase <> FI.L1 ? FI.map_return_type (K (#resT (range_monad head)))
      in
        context |> map_default_info filename skips phase name new_info |> add_def_thm concealed_named_theorems phase def phi
      end)  
  end

fun add_impl_locale prog_info finfos phase ts_monads name thy =
  let                              
    val filename = ProgramInfo.get_prog_name prog_info 
    val ctxt = Proof_Context.init_global thy;
    val skips = ProgramInfo.get_skips prog_info name
    val fun_ptr_funs = ProgramAnalysis.get_all_addressed_funs (ProgramInfo.get_csenv prog_info)
    val fun_impl_loc = gen_implementation_locale false ctxt skips phase filename [name]

    val def_loc = definition_locale ctxt skips phase filename [name];

    val clique = get_definition_clique ctxt skips phase filename [name];

    val clique_fun_ptr_funs = clique |> (filter (member (op =) fun_ptr_funs))

    val imports = [([], def_loc)] 
    val imports = canonical_imports thy imports

    fun refine_def lthy =
      let
        val finfo = get_function_info (Context.Proof lthy) filename phase name |> the
        val clique_recs = FI.get_clique_recursion_fun_ptrs finfo
      in
        if null clique_recs then lthy
        else  
          let
            val def = FI.get_definition finfo
            val def_name = ProgramInfo.get_mk_fun_name prog_info phase "impl_" name ^ "_def"
           
            val fun_ptr_simps = Named_Theorems.get lthy \<^named_theorems>\<open>fun_ptr_simps\<close> @ 
                  @{thms map_of_default_default_conv}
            val simp_ctxt = put_simpset HOL_ss lthy
                  addsimps (fun_ptr_simps @  @{thms list_all_simps case_prod_conv} )
            val def' = def |> Conv.fconv_rule (Simplifier.asm_full_rewrite simp_ctxt)
          in 
            lthy |> Utils.define_lemma' (Binding.name def_name) [define_function_declaration {concealed_named_theorems=false} filename skips phase name] def' |> snd
          end 
      end 
                                                                                          
    fun assumes assume_ctxt name = 
      if member (op =) fun_ptr_funs name 
      then
        let
          fun penv (ts_monad_name, lift) =
                (get_progenv_for ctxt prog_info phase ts_monad_name name |> snd , lift)
            
          val monads = if null ts_monads then [("", I)] else ts_monads
          val Ps = map penv monads
          val p = HP_TermsTypes.mk_fun_ptr assume_ctxt (ProgramInfo.get_prog_name prog_info) name

          fun eq (P, lift) = 
            let         
              val local_name = ProgramInfo.get_mk_fun_name prog_info phase "" name

              val p = HP_TermsTypes.mk_fun_ptr assume_ctxt (ProgramInfo.get_prog_name prog_info) name
              val c = Proof_Context.read_const {proper=true, strict=false} assume_ctxt local_name
            in                                                     
              (HOLogic.Trueprop $ (HOLogic.eq_const dummyT $
                 (P $ p) $ lift c), 
               [])
            end
          
          val known_function = 
           ( \<^instantiate>\<open>known_function = \<open>HP_TermsTypes.known_function assume_ctxt\<close> and p = p 
             in prop \<open>known_function p\<close> for known_function::"unit ptr \<Rightarrow> bool"\<close>, [])

          val assume_eq = ((Binding.name (impl_thm_name prog_info phase name), 
                         @{attributes [fun_ptr_simps]}), map eq Ps)
          val assume_known = ((Binding.empty, @{attributes [known_function]}), [known_function])
        in 
          [assume_eq] @ [assume_known]
        end
      else ([])
    val assume_ctxt = (* Enter hypothetical context only once for the clique (performance) *)
      if null clique_fun_ptr_funs then ctxt 
      else Utils.timeap_msg 3 ctxt (phase_msg "impl locale" phase "assume_ctxt" name) (Expression.cert_declaration imports I []) ctxt 
           |> #2 |> #2
    val clique_assumes = map (assumes assume_ctxt) clique_fun_ptr_funs |> flat
  in
    thy
    |> HPInter.add_locale (Binding.name fun_impl_loc) (Binding.name fun_impl_loc)
        imports
        [Element.Assumes clique_assumes]
    |> snd
    |> Utils.timeap_msg 3 ctxt (phase_msg "impl locale" phase "refine" name) refine_def 
    |> Local_Theory.exit_global
  end

val add_impl_locale = fn prog_info => fn finfos => fn phase => fn ts_monads => fn name => fn thy =>
 let
   val ctxt = Proof_Context.init_global thy
 in
   thy |> Utils.timeap_msg 1 ctxt (phase_msg "impl locale" phase "total" name) (
      add_impl_locale prog_info finfos phase ts_monads name)
 end

fun add_impl_locales skips prog_info finfos phase ts_monad_name clique thy = 
  let
    val filename = ProgramInfo.get_prog_name prog_info 
    val ctxt = Proof_Context.init_global thy;
    fun imports thy = map (fn name => ([], (gen_implementation_locale false ctxt skips phase filename [name]))) clique 
        |> canonical_imports thy
    val cliqueL = implementation_locale (Proof_Context.init_global thy) skips phase (ProgramInfo.get_prog_name prog_info) clique
  in
    thy 
    |> fold (add_impl_locale prog_info finfos phase ts_monad_name) clique
    |> length clique > 1 ? (fn thy => thy 
        |> HPInter.add_locale (Binding.name cliqueL) (Binding.name cliqueL) (imports thy) [] 
        |> snd |> Local_Theory.exit_global)
  end


fun pairs xs ys =
  map (fn x => map (pair x) ys) xs 

fun pull_tag [] = ("", [])
  | pull_tag ((t,x)::xs) = (t, x :: map snd xs)

fun prove_and_note_fun_ptr_intros persistent (prev_phase, phase) prog_info mk_thm lthy =
  let
    val all_insts = progenv_insts_grouped_by_cty {per_ctype=false} lthy prog_info
    fun phase_insts phase = filter (fn inst => #1 (#2 (#2 inst)) = phase) 
            #> map (fn inst => ((#1 o #2) inst, (#2 o #2 o #2) inst))
    val paired_insts = map (fn insts => pairs (phase_insts prev_phase insts) (phase_insts phase insts)) all_insts |> flat |> flat
    fun get_monad_type_attribs "" = ("", [])
      | get_monad_type_attribs monad_type = 
            Monad_Types.get_monad_type monad_type (Context.Proof lthy) 
            |> Option.map (fn mt => (#name mt, Monad_Types.add_call_rule_attribs (Context.Proof lthy) mt {only_schematic_goal = true}
                                         (Binding.make ("fun_ptr_corres",\<^here>)) (if persistent then 10 else 20)
                               |> map (Attrib.internal \<^here> o K)))
            |> the_default ("", [])

    (* theorem name is meaningless in bundles or proof-context, we note for the attributes *)
    fun note (attrs, thms) lthy  =
      if persistent 
      then Local_Theory.note ((Binding.empty, attrs), thms) lthy |> snd 
      else lthy |> fold (fn thm => Thm.proof_attributes (map (Attrib.attribute lthy) attrs) thm #> snd) thms

    fun notes lthy =
      let
        val thmss = map (mk_thm lthy) paired_insts |> flat |> group_by ((op =) o (apply2 fst)) |> map pull_tag 
         |> map (apfst get_monad_type_attribs)
      in 
        lthy |> fold (fn ((name, attrs), thms) =>
          note ((@{attributes [fun_ptr_intros]}@attrs), thms)) thmss
      end

  in
    lthy |> notes
  end


fun add_global_corres_locale (prev_phase, phase) prog_info mk_prop thy =
  if not (ProgramInfo.has_method_fun_ptrs prog_info) then thy else
  let
    val ctxt = Proof_Context.init_global thy
    val all_insts = progenv_insts_grouped_by_cty {per_ctype=phase=FI.L2} ctxt prog_info
    fun phase_insts phase = filter (fn inst => #1 (#2 (#2 inst)) = phase) 
            #> map (fn inst => ((#1 o #2) inst, (#2 o #2 o #2) inst))

    val paired_insts = map (fn insts => pairs (phase_insts prev_phase insts) (phase_insts phase insts)) all_insts |> flat |> flat
    val prog_name = ProgramInfo.get_prog_name prog_info
    val locale_name = global_corres_locale phase prog_name
    val locale_binding = Binding.make (locale_name, \<^here>)

    val known_function = HP_TermsTypes.known_function ctxt
    fun make_prop ((P_prev, _), (P, _)) = 
      let
        val ([p], ctxt1) = Utils.fix_variant_frees [("p", @{typ "unit ptr"})] ctxt
      in 
        mk_prop phase p P_prev P ctxt1 |> Option.map (fn ((prop, attrs), ctxt2) =>
          let 
            val prop1 = \<^infer_instantiate>\<open>P = "prop" and p = p and known_function = known_function 
              in prop \<open>known_function p \<Longrightarrow> PROP P\<close>\<close> ctxt |> Thm.cterm_of ctxt
            val final_prop = Utils.export_prop {closed=true} ctxt2 ctxt prop1 |> Thm.term_of
          in
            (final_prop, attrs)
          end)
      end
    fun make_assm (prop, attrs) = ((Binding.empty, attrs @ @{attributes [known_function_corres]}), [(prop, [])])
    val assms = map_filter (Option.map make_assm o make_prop) paired_insts
  in
    thy 
    |> HPInter.add_locale locale_binding locale_binding ([], []) [Element.Assumes assms]
    |> snd |> Local_Theory.exit_global
  end


end (* structure AutoCorresData *)




