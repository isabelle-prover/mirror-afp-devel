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

  val define_function: {concealed_named_theorems: bool} ->
        string -> FunctionInfo.skip_info -> FunctionInfo.phase -> string -> 
        (thm -> Context.generic -> Context.generic)
  val define_function_attribute: {concealed_named_theorems: bool} ->
      string -> FunctionInfo.skip_info -> FunctionInfo.phase -> string -> attribute
  val corres_thm: string -> FunctionInfo.skip_info -> FunctionInfo.phase -> string -> 
        (thm -> Context.generic -> Context.generic)
  val corres_thm_attribute: string -> FunctionInfo.skip_info -> FunctionInfo.phase -> string -> attribute;
  val no_throw_thm_attribute: string -> FunctionInfo.skip_info -> FunctionInfo.phase -> string -> attribute;
  val corres_named_thms: FunctionInfo.phase -> string

  val corres_thm_name: ProgramInfo.prog_info -> FunctionInfo.phase -> string -> string

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

  datatype Fun_Kind = Spec_Monad | Option | Reader | Pure
  val dest_monad: typ -> Fun_Kind * typ * typ list
  val kind_of: typ -> Fun_Kind
  val has_error: typ -> bool
  val fixpoint_type: typ -> bool
  val mk_default: typ -> term

  val progenvN : string

  val def_named_thms: FunctionInfo.phase -> string

  val options_of_in_out_params: ProgramInfo.prog_info -> FunctionInfo.in_out_fun_ptr_spec ->
        ProgramInfo.function_options

  val norm_kind: {only_type: bool} ->  FunctionInfo.parameter_kind -> FunctionInfo.parameter_kind

  type fn_ptr_info = {idx: int,  ptr_val: string * typ, 
          in_out_spec: FunctionInfo.in_out_fun_ptr_spec,fname:string}

  val name_args: term list -> (string * term) list
  val mk_fn_ptr_infos: Proof.context -> ProgramInfo.prog_info -> {ts_monad_name:string} -> 
        term list -> FunctionInfo.function_info -> (string * (FunctionInfo.phase -> fn_ptr_info)) list

  structure FunctionInfo: GENERIC_DATA;

  val transfer_ac_slots: Proof.context -> Proof.context -> Proof.context
  val in_locale_result: xstring -> (local_theory -> 'a * local_theory) -> local_theory -> 'a * local_theory;
  val in_locale: xstring -> (local_theory -> local_theory) -> local_theory -> local_theory; 
  val in_theory_result: (theory -> 'a * theory) -> local_theory -> 'a * local_theory;
  val in_theory: (theory -> theory) -> local_theory -> local_theory;
  val in_theory_result': (local_theory -> 'a * local_theory) -> local_theory -> 'a * local_theory;
  val in_theory': (local_theory -> local_theory) -> local_theory -> local_theory;
  val d1: bool Unsynchronized.ref
  val d2: bool Unsynchronized.ref

  val monad_args_def: thm -> thm
end

structure AutoCorresData : AUTOCORRES_DATA  =
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



val ac_slots = [
  AutoCorresTrace.transfer_trace_info, 
  AutoCorresTrace.ProfileConv.transfer', 
  AutoCorres_Options.Options_Proof.transfer]

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

fun get_definition_clique ctxt prog_info skips phase filename clique =
 case clique of [] => []
 | name:: _ => 
    let
      (* Note that in the current construction the definition of a function is still made in a 
       * locale based on the clique-information of the previous phase.
       * In rare cases the clique might get split up in a phase due to dead-code elimination.
       *)
      val def_phase = case phase of FI.CP => FI.CP | _ => FI.prev_phase skips phase
      val info_opt = get_function_info (Context.Proof ctxt) filename def_phase name
    in
      case Option.map FI.get_clique (get_function_info (Context.Proof ctxt) filename def_phase name) of
        SOME clique => Symset.dest clique 
      | NONE => these (ProgramAnalysis.get_clique (ProgramInfo.get_csenv prog_info) 
          (name))
    end 

fun string_of_phase phase = FI.string_of_phase phase |> String.translate (str o Char.toLower)
fun phase_prefix phase =
  string_of_phase phase |> suffix "_"

fun phase_prefix' phase =
 if (phase = FI.TS) then "" else phase_prefix phase
 
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

fun norm_kind {only_type=true} (FI.Keep_Ptr) = FI.Data (* should have same effect on type of program environemnt *)
  | norm_kind _ x = x


fun options_of_in_out_params prog_info =
  let
    val opt0 = ProgramInfo.get_fun_options prog_info "" 
    fun options_of_params ({param_kinds, might_exit,...}:FI.in_out_fun_ptr_spec) = opt0 
      |> ProgramInfo.map_in_out_parameters (K (SOME (map (pair "") (map fst param_kinds))))
      |> ProgramInfo.map_might_exit (K might_exit)
  in options_of_params end

type fn_ptr_info = {
  idx: int, 
  ptr_val: (string * typ), 
  in_out_spec: FI.in_out_fun_ptr_spec, fname:string}


fun in_out_fn_ptr_param_spec prog_info fname pname (cretT, cargTs) = (
  case ProgramInfo.get_in_out_fun_ptr_params  (ProgramInfo.get_fun_options prog_info fname) of
    [] => FI.default_fun_ptr_params (CType.Function (cretT, cargTs))
  | ps => case AList.lookup (op =) ps pname of
              NONE => FI.default_fun_ptr_params  (CType.Function (cretT, cargTs))
            | some => some)

fun get_fn_ptr_param_info ctxt (prog_info: ProgramInfo.prog_info) fname ts_monad_name (pname, pname_orig, idx) (cretT, cargTs) phase =
  let
    val in_out_spec =  (the (in_out_fn_ptr_param_spec prog_info fname pname_orig (cretT, cargTs)))
    val ptr_val = (pname, @{typ "unit ptr"})
  in
   {idx = idx, ptr_val = ptr_val, in_out_spec = in_out_spec, fname=fname}:fn_ptr_info
  end

val name_args = map (fn t => (Term.term_name t, t)) 

fun mk_fn_ptr_infos ctxt prog_info ts_monad_name fargs finfo =
   FI.get_fn_ptr_args_info finfo |> map (fn (n, (idx, srcname, (cretT, cargTs))) =>
    let
      val n' = case try (nth fargs) (idx - 1) of SOME (Free (n', _)) => n' | _ => n
      val fname = FI.get_name finfo
    in
      (NameGeneration.ensure_varname n, 
         fn phase => get_fn_ptr_param_info ctxt prog_info fname ts_monad_name  
          (n', srcname, idx) (cretT, cargTs) phase) 
    end)


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

  
val d1 = Unsynchronized.ref false
val d2 = Unsynchronized.ref false

end



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
    FI.L1 => @{named_theorems AutoCorres.l1_def}
  | FI.L2 => @{named_theorems AutoCorres.l2_def}
  | FI.IO => @{named_theorems AutoCorres.io_def}
  | FI.HL => @{named_theorems AutoCorres.hl_def}
  | FI.WA => @{named_theorems AutoCorres.wa_def}
  | FI.TS => @{named_theorems AutoCorres.ts_def}
  | _ => error ("def_named_thms not defined for phase: " ^ @{make_string} phase)

fun add_def name def context =
  context
  |> Named_Theorems.add_thm name def  

fun add_def_thm concealed phase thm =
  if concealed orelse phase = FI.CP then I else
  add_def (def_named_thms phase) thm 
  #> add_def @{named_theorems AutoCorres.ac_def} thm

fun timeit_declaration level msg spec f =
  Local_Theory.declaration spec (fn phi => fn context =>
    Utils.timeap_msg level (Context.proof_of context) msg (f phi) context)

fun timeit_declaration_attribute level msg f =
  Thm.declaration_attribute (fn thm => fn context =>
    Utils.timeap_msg level (Context.proof_of context) msg (f thm) context)

fun phase_msg kind phase descr name = fn _ => kind ^ " " ^ descr ^ " (" ^ (FI.string_of_phase phase) ^ ") "  ^ name 

val attrib_msg = phase_msg "ATTRIBUTE"

fun corres_thm filename skips phase name thm context = 
  let
    val thm = case phase of FI.L2 => CLocals.unfolded_with [filename, name] (Context.proof_of context) thm | _ => thm
    val new_info = FI.map_corres_thm (K (Thm.trim_context thm))
  in
    context 
    |> map_default_info filename skips phase name new_info
    |> add_corres_thm phase thm
  end

fun corres_thm_attribute filename skips phase name = 
  timeit_declaration_attribute 3 (attrib_msg phase "corres" name) (corres_thm filename skips phase name)

fun no_throw_thm_attribute filename skips phase name = 
  timeit_declaration_attribute 3 (attrib_msg phase "no_throw" name) (fn thm => 
    let
      val new_info = FI.map_no_throw_thm (K (SOME (Thm.trim_context thm)))
    in
      map_default_info filename skips phase name new_info
    end)

fun init_function_info skips (prog_info: ProgramInfo.prog_info) thy =                            
  case get_phase_info (Context.Theory thy) (ProgramInfo.get_prog_name prog_info) FI.CP of
    SOME infos => (infos, thy)
  | NONE => 
    let
      val lthy = Named_Target.theory_init thy
      val filename = ProgramInfo.get_prog_name prog_info;
      val csenv = ProgramInfo.get_csenv prog_info;
      (* Get information about a single function. *)
      fun gen_fn_info name (return_ctype, proto, carg_list) lthy0 = 
        let
          val lthy = HPInter.enter_scope filename name lthy0
          (* function options *)
          val skips = ProgramInfo.get_skips prog_info name
          (* Convert C Parser return type into a HOL return type. *)
          val has_body_spec =  exists (fn AstDatatype.gcc_attribs _ => false | _ => true) 
               (these (Symtab.lookup (ProgramAnalysis.function_specs csenv) name))
          val return_type =
            if return_ctype = Absyn.Void then
              @{typ unit}
            else
              CalculateState.ctype_to_typ {bitint_padding=true} lthy return_ctype;
          (* Convert arguments into a list of (name, HOL type) pairs. *)
          fun make_var v = 
            (ProgramAnalysis.get_mname v |> MString.dest,
             (CalculateState.ctype_to_typ {bitint_padding=true} lthy (ProgramAnalysis.get_vtype v), v))
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
                  (Proof_Context.get_thm lthy (name ^ "_body_def"), false)
                   handle ERROR _ => (undef_thm, true);
          val clique = these (ProgramAnalysis.get_clique csenv name)
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
            |> FI.map_clique (K (Symset.make clique)) 
        in 
          lthy |> Local_Theory.declaration {pervasive=true, syntax=false, pos=\<^here>} (fn phi => 
              map_default_info filename skips FI.CP name (FI.morph phi o upd_info))
        end
      
      val parser_infos = ProgramAnalysis.get_fninfo csenv |> Symtab.dest
      val lthy = lthy 
        |> fold (fn (name, data as (_, is_proto, _)) => 
                (Utils.timeit_msg 1 lthy (fn _ => "gen_fn_info: " ^ name ^ ":") (fn _=> 
                  gen_fn_info name data))) 
           parser_infos
  
      val raw_simpl_infos = get_phase_info (Context.Proof lthy) filename FI.CP |> the
      (* We discard the call graph info here.
       * After calling init_function_info, we often want to change some of the entries,
       * which usually requires recalculating it anyway. *)
      val (_, cg_infos) = Utils.timeit_msg 1 lthy (fn _ => "calc_call_graph:") (fn _ => 
        FI.calc_call_graph raw_simpl_infos);
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

val Type(spec_monad_name, _) = @{typ "('e::default, 'b, 's) spec_monad"}
val Type(option_name, _) = @{typ "'a option"}
datatype Fun_Kind = Spec_Monad | Option | Reader | Pure

(* FIXME: avoid strings globals lifted_globals here *)
fun is_stateT (Type(n, _))= is_some (try (unprefix "globals") (Long_Name.base_name n)) orelse is_some (try (unprefix "lifted_globals") (Long_Name.base_name n))
  | is_stateT _ = false

fun kind_of T =     
  let 
    val (argTs, resT) = strip_type T
    val kind = case resT of Type(n, _) => 
     if (n = spec_monad_name) then Spec_Monad 
     else if (n = option_name) then Option
     else if not (null argTs) andalso is_stateT (List.last argTs) then Reader
     else Pure
  in kind end

fun dest_monad T =
  let
    val (argTs, resT) = strip_type T
    val kind = kind_of T

    val (monadT, paramTs) = 
      case kind of
       Spec_Monad => (resT, argTs)
      | Pure => (resT, argTs)
      | _ => let val (argTs', stateT) = split_last argTs in (stateT --> resT, argTs') end
  in (kind, monadT, paramTs) end

fun dest_optionT \<^Type>\<open>option T\<close> = T
fun mk_default T =
  let
    val (argTs, resT) = strip_type T
    val default_val = 
      case kind_of T of
         Option =>\<^instantiate>\<open>'a = \<open>dest_optionT resT\<close> in term \<open>None\<close>\<close>
      | Spec_Monad =>\<^instantiate>\<open>'a = resT in term \<open>\<top>::'a::top\<close>\<close>
      | _ => \<^instantiate>\<open>'a = resT in term \<open>undefined\<close>\<close>
  in
    default_val |> fold_rev (fn T => fn x => Abs ("_", T, x)) argTs
  end

fun has_error T = member (op =) [Spec_Monad, Option] (kind_of T)
fun fixpoint_type T = has_error T

val meta_fun_cong = @{lemma "f \<equiv> g \<Longrightarrow> f x \<equiv> g x" by auto}
val Var (x_name, xT) = meta_fun_cong |> Thm.concl_of |> Term.strip_comb |> #2 |> hd |> Term.strip_comb |> #2 |> hd


fun meta_fun_cong_named maxidx n = Drule.infer_instantiate @{context} [(x_name, Thm.cterm_of @{context} (Var ((n,maxidx + 1), xT)))] meta_fun_cong 


fun arg_def n eq_thm = 
    let
      val maxidx = Thm.maxidx_of eq_thm
      val rule = meta_fun_cong_named maxidx n
      val inst = rule OF [eq_thm]
    in inst |> Drule.zero_var_indexes end

fun args_def ns eq_thm =
  eq_thm |> fold arg_def ns

fun monad_args_def eq_thm = 
  let
    val rhs = Thm.cconcl_of eq_thm |> Utils.crhs_of_eq
    val T = Thm.typ_of_cterm rhs
    val names = Utils.abs_names (Thm.term_of rhs)
    val (argTs, _) = Term.strip_type T
    val arity = length argTs
    val kind = kind_of T
    val n = 
      (case kind of 
        Spec_Monad => arity 
      | Pure => arity 
      | Option => arity - 1 
      | Reader => arity - 1)
    val names' = take n names
    val dummy_names = map (fn i => "x" ^ string_of_int i) (length names' + 1 upto n)
    val res = args_def (names' @ dummy_names) (safe_mk_meta_eq eq_thm)
  in
    res
  end

local
    fun split_lhs_args t = strip_comb t
    fun mk_arg_info (t, info) = let val (n,T) = Utils.dest_name_type t in (n, (T, info)) end
in
fun define_function {concealed_named_theorems} filename skips phase name def0 context =
  let
    val def = if phase = FI.CP then def0 else monad_args_def def0 |> Drule.zero_var_indexes
    val info = default_info filename skips phase name context
    val lhs = def |> Thm.prop_of |> Utils.lhs_of_eq 
    val (head, args) = split_lhs_args lhs
    val arg_var_infos = (if phase = FI.IO then FI.get_args_without_outs info else FI.get_args info)  
      |> map (#2 o #2)
    val def' = Thm.trim_context def
    val lhs' = head
    val const = if phase = FI.CP then HP_TermsTypes.mk_fun_ptr (Context.proof_of context) filename name else lhs'
    val new_info = FI.map_definition (K def')
      #> FI.map_const (K const)
      #> (if not (member (op =) [FI.CP, FI.L1] phase) then FI.map_args (K (map mk_arg_info (args ~~ arg_var_infos))) else I) 
      #> not (member (op =) [FI.CP, FI.L1] phase) ? FI.map_return_type (K (#resT (range_monad head)))
      #> phase = FI.CP ? FI.map_invented_body (K false)
  in
    context |> map_default_info filename skips phase name new_info |> add_def_thm concealed_named_theorems phase def
  end

fun define_function_attribute concealed_named_theorems filename skips phase name =
    timeit_declaration_attribute 3 (attrib_msg phase "def" name) 
      (define_function concealed_named_theorems filename skips phase name )  
end

end (* structure AutoCorresData *)
