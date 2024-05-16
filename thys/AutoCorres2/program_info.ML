(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Functions for extracting information from the C parser in a format more
 * convenient for us to work with.
 *)
structure ProgramInfo =
struct

type parameter_kind = FunctionInfo.parameter_kind

@{record \<open>datatype function_options = Function_options of {
  heap_abs         : bool,
  signed_abs       : bool,
  unsigned_abs     : bool,
  skip_heap_abs    : bool,
  skip_word_abs    : bool,
  in_out_globals : bool,
  in_out_parameters : (string * parameter_kind) list option
}\<close>
}

val default_fun_options = make_function_options {
  heap_abs=true, 
  signed_abs=true, 
  unsigned_abs=false, 
  skip_heap_abs = false, 
  skip_word_abs = false,
  in_out_globals = false,
  in_out_parameters = NONE}

fun skip_in_out_abs opts = is_none (get_in_out_parameters opts)
val get_in_out_parameters_raw = get_in_out_parameters
fun get_in_out_parameters opts = the_default [] (get_in_out_parameters_raw opts)

fun is_in_out_parameter opts name = is_some (AList.lookup (op =) (get_in_out_parameters opts) name)
fun has_in_out_parameters opts = not (null (get_in_out_parameters opts))
fun parameter_kind opts name = (AList.lookup (op =) (get_in_out_parameters opts) name)


(* Program information type. *)
@{record \<open>datatype prog_info = Prog_info of 
{
  mk_fun_name: FunctionInfo.phase -> string -> string -> string,
  dest_fun_name: FunctionInfo.phase -> string -> string -> string,
  fun_options: string -> function_options,

  (* C environment from the C parser *)
  csenv : ProgramAnalysis.csenv,

  prog_name : string,
  naming: Name_Space.naming,
  method_callers: string list,

  state_type : typ,
  globals_type : typ,
  lifted_globals_type : typ option,
  gamma : term,

  var_getters : term Symtab.table,
  var_setters : term Symtab.table,
  globals_getter : term,

  global_var_getters : term Symtab.table,
  global_var_setters : term Symtab.table,
  t_hrs_getter : term,
  t_hrs_setter : term
}\<close>
}

(* Internal name of the "globals variable" in the "myvars" record. *)
val globals_record = "globals'"

(* Get skipped phases function options *)
fun get_skips prog_info fname = let
  val fopt = get_fun_options prog_info fname
  in {skip_io_abs = skip_in_out_abs fopt, 
      skip_heap_abs = get_skip_heap_abs fopt, 
      skip_word_abs = get_skip_word_abs fopt} :
    FunctionInfo.skip_info
  end

(*
 * Get the HOL constant names for the getter/setter for variable
 * "varname" of the record "record_typ".
 *)
fun get_record_getter_setter ctxt record_typ varname =
let
  val consts = Proof_Context.consts_of ctxt;
  val getter_varname = varname |> Consts.intern consts;
  val setter_varname = varname ^ Record.updateN |> Consts.intern consts;
  val getter_term = Const (getter_varname, record_typ --> dummyT)
        |> Syntax.check_term ctxt
  val setter_term = Const (setter_varname, [dummyT, dummyT] ---> record_typ)
        |> Syntax.check_term ctxt
in
   (getter_term, setter_term)
end

(*
 * Extract useful information about the given local variable from the
 * c-parser "vinfo" structure.
 *)
fun get_local_variable_info ctxt state_typ csenv_var =
let
  val munged_name = ProgramAnalysis.get_mname csenv_var;
  val pretty_name = ProgramAnalysis.srcname csenv_var;
  val hol_type = CalculateState.ctype_to_typ ctxt (ProgramAnalysis.get_vtype csenv_var)
  val (getter, setter) = get_record_getter_setter
      ctxt state_typ (HoarePackage.varname (MString.dest munged_name))
in
  (munged_name, pretty_name, hol_type, getter, setter)
end

(*
 * Extract useful information about the given global variable from the
 * c-parser "vinfo" structure.
 *)
fun get_global_variable_info ctxt csenv_var =
let
  val munged_name = ProgramAnalysis.get_mname csenv_var;
  val pretty_name = ProgramAnalysis.srcname csenv_var;
  val hol_type = CalculateState.ctype_to_typ ctxt (ProgramAnalysis.get_vtype csenv_var)
in
  (munged_name, pretty_name, hol_type)
end

(* Given a record field name, guess the original variable name. *)
fun guess_var_name x =
  case (Long_Name.base_name x) of
      "globals" => globals_record
    | "locals" => "locals"
    | x => NameGeneration.un_varname x

(* Given a record field updater function, guess the original variable name. *)
fun guess_var_name_from_setter x =
  Long_Name.base_name x |> unsuffix Record.updateN |> guess_var_name

fun guess_var_name_type_from_record_setter_term setter =
let
  (* We have a term of the form (Const "foo_'_update"). Extract the name
   * of the constant. *)
  val (setter_name, setter_type) = Term.dest_Const setter

  (* Guess the variable name by stripping off the suffix. *)
  val var_name = (guess_var_name_from_setter setter_name)
    handle Fail _ => (Utils.invalid_term "local variable update function" setter)

  (* Get the variable type: @{typ "(TYPE --> X) --> X --> X"} *)
  val var_type = dest_Type setter_type |> snd |> hd |> dest_Type |> snd |> hd
in
  (var_name, var_type)
end

fun guess_var_name_type_from_setter_term t =
  case HPInter.name_type_from_local_var_update t of
    SOME (Const (n,_), T) => (guess_var_name n, T)
  | NONE => guess_var_name_type_from_record_setter_term t
                     
fun dest_var_update t =
 case HPInter.dest_local_var_update' t of
   SOME (n, T, upd, SOME s) => SOME ((NameGeneration.map_named guess_var_name n, T), upd, s)
 | _ => (case t of 
          (Const var $ upd $ s) => 
          let 
            val (n,  T) = guess_var_name_type_from_record_setter_term (Const var)
          in SOME ((NameGeneration.Named n, T), upd, s)end
         | _ => NONE)
    
 
(*                   
 * Demangle a name mangled by the C parser.
 *)
fun demangle_ret_and_tmp s =
  let
    val s = NameGeneration.rmUScoreSafety s
  in
    if s = MString.dest (NameGeneration.return_var_name) then 
      SOME "ret"
    else 
      NameGeneration.dest_tmp (MString.mk s) |> Option.map (fn (_, n) =>  
        "ret" ^ (if n > 1 then string_of_int n else ""))
  end
fun demangle_name (prog_info: prog_info) m =
    case demangle_ret_and_tmp m of
      (* Return variable for function f *)
      SOME n => n
      (* Ordinary variable. Look up the original name in csenv. *)
    | NONE =>
        let
          fun lookup k v = Symtab.lookup v k
        in
          (* Don't bother checking if we're asked to demangle an unmangled name
             (e.g. a global), just default to the input. *)
          ProgramAnalysis.get_mangled_vars (get_csenv prog_info)
            |> lookup m |> Option.map (hd #> ProgramAnalysis.srcname)
            |> the_default m
        end

(*
 * Extract details from the c-parser about the given program.
 *)
fun get_prog_info thy fun_options mk_fun_name dest_fun_name cfilename : prog_info =
  let
    val ctxt = Proof_Context.init_global thy
    val csenv = CalculateState.get_csenv thy cfilename |> the;
    val prog_name = cfilename |> Path.explode |> Path.split_ext |> fst |> Path.file_name

    (* Get the type of the state record and the globals record. *)
    val globals_type =  Proof_Context.read_typ ctxt NameGeneration.global_rcd_name
    val locals_type = IsabelleTermsTypes.localsT
    val styargs = [globals_type, locals_type, @{typ exit_status}]
    val state_type = Proof_Context.cert_typ ctxt
              (Type("CProof.state", styargs))

    (* Get the gamma variable, mapping function numbers to function bodies in
     * SIMPL. *)
    val gamma = HP_TermsTypes.mk_gamma ctxt prog_name

    (*
     * Return a Const term of the local-variable getters/setters for the given
     * variable name.
     *
     * For instance, if "x" was passed in, we might return:
     *     SOME (Const ("Kernel_C.myvars.x_'", "globals myvars => nat"))
     *)
    val var_getters = Record.get_recT_fields thy state_type
      |> fst
      |> map (fn (x, T) => (guess_var_name x, Const (x, state_type --> T)))
      |> filter_out (fn (n, _) => n = "locals")
      |> Symtab.make
    val var_setters = Record.get_recT_fields thy state_type
      |> fst
      |> map (fn (x, T) => (guess_var_name x,
          Const (x ^ Record.updateN, (T --> T) --> state_type --> state_type)))
      |> filter_out (fn (n, _) => n = "locals")
      |> Symtab.make

    (* Get the "globals" getter from "myvars". *)
    val globals_getter = Proof_Context.cert_term ctxt 
      (Const (@{const_name "globals"}, state_type --> globals_type))

    (* Get global getters/setters. *)
    val global_var_getters = Record.get_recT_fields thy globals_type
      |> fst
      |> map (fn (x, T) => (guess_var_name x, Const (x, globals_type --> T)))
      |> Symtab.make
    val global_var_setters = Record.get_recT_fields thy globals_type
      |> fst
      |> map (fn (x, T) => (guess_var_name x,
          Const (x ^ Record.updateN, (T --> T) --> globals_type --> globals_type)))
      |> Symtab.make

    (* Get the "t_hrs_'" getter/setter from "myvars". *)
    val t_hrs_getter = case (Symtab.lookup global_var_getters "t_hrs") of
        SOME x => x
      | NONE => raise Utils.InvalidInput "'globals' doesn't appear to have a \"t_hrs_'\" field."
    val t_hrs_setter = case (Symtab.lookup global_var_setters "t_hrs") of
        SOME x => x
      | NONE => raise Utils.InvalidInput "'globals' doesn't appear to have a \"t_hrs_'\" field."
    val method_callers = ProgramAnalysis.method_callers csenv
  in
    make_prog_info
    {
      mk_fun_name = mk_fun_name,
      dest_fun_name = dest_fun_name,
      fun_options = fun_options,
      csenv = csenv,

      prog_name = prog_name,
      naming = Sign.naming_of thy,
      method_callers = method_callers,

      state_type = state_type,
      globals_type = globals_type,
      lifted_globals_type = NONE,
      gamma = gamma,

      var_getters = var_getters,
      var_setters = var_setters,
      globals_getter = globals_getter,

      global_var_getters = global_var_getters,
      global_var_setters = global_var_setters,
      t_hrs_getter = t_hrs_getter,
      t_hrs_setter = t_hrs_setter
    }
  end

fun has_method_fun_ptrs prog_info = not (null (get_method_callers prog_info))

fun all_var_getters ctxt (prog_info: prog_info) state = 
  let
    fun get_type (Const (_, T)) = range_type T
    val basic_getters = get_var_getters prog_info |> Symtab.dest 
      |> map (fn (name, t) => (name, ((t $ state), get_type t)))
    val locvars = HPInter.all_locvars ctxt state
  in               
    basic_getters @ locvars
  end


fun get_var_value ctxt (prog_info: prog_info) loc_ref state =
 case loc_ref of
   NameGeneration.Named name =>
     (case try (HPInter.get_actual_locvar ctxt (NameGeneration.Named (Hoare.varname name))) state of
        SOME (x, _) => x
      | _ => (case Symtab.lookup (get_var_getters prog_info) name of
               SOME get => get $ state
             | NONE => error ("get_var_value: undefined variable " ^ quote name)))  
 | p => HPInter.get_actual_locvar ctxt p state |> fst  


(* Is the given term the "t_hrs_'" constant? *)
fun is_t_hrs_const (prog_info : prog_info) t =
  (t = get_t_hrs_getter prog_info)
fun is_t_hrs_update_const (prog_info : prog_info) t =
  (t = get_t_hrs_setter prog_info)

end
