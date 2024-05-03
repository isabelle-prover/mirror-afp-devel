(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * The top-level "autocorres" command.
 *)
structure AutoCorres =
struct


val verbose_msg = Utils.verbose_msg;

(* Get all that the given function depends on, up to "depth" functions deep. *)
fun get_function_deps get_callees roots depth =
let
  fun get_calleess fns = Symset.union_sets (fns :: map get_callees (Symset.dest fns))
in
  funpow depth get_calleess (Symset.make roots)
end

fun fixpoint eq iter x =
  let
    val y = iter x
  in
    if eq y x then y else fixpoint eq iter y
  end 

fun all_reachable finfos funs =
  let
    fun callees f =
      case Symtab.lookup finfos f of 
        NONE => Symset.empty
      | SOME info => FunctionInfo.all_callees info
    fun iter x = fold Symset.union (map callees (Symset.dest x)) x
    fun eq x y = (Symset.dest x = Symset.dest y)
  in
   funs |> Symset.make |> fixpoint eq iter |> Symset.dest
  end

(* Combined parser. *)
val autocorres_parser : (AutoCorres_Options.autocorres_options * string) parser =
  (* Options *)
   AutoCorres_Options.options_parser --
  (* Filename *)
  Parse.embedded

val init_autocorres_parser : (AutoCorres_Options.autocorres_options * string) parser =
  (* Options *)
  AutoCorres_Options.options_parser --
  (* Filename *)
  Parse.embedded

val final_autocorres_parser : (string) parser =
  (* Filename *)
  Parse.embedded


(* build_tasks calculates the "build-dependencies" of C-functions in the various phases of
 * autocorrres. To build a function in phase X it depends on all callees in the same phase and on
 * itsself in phase (X - 1). We identify a tasks by a string encoding: 
 *    <function_name>_<phase_name>_<cfile_name>
 *
 * The result is a list of tuples:
 *    (name, (imports, (scope, phase)))
 *  - name: string as described above
 *  - imports: list of names it depends on
 *  - (scope, phase) are the options for autocorres to build the function in a particular phase.
 *      (scope is a singleton list containing the function name)
 *  - an artificial final theory "autocorres_final_<cfile_name>" will be added to include all the
 *    root functions.
 * Note that the task list is complete and does not consider what might already be built. 
 *)
fun build_tasks finfos cfile skips max_phase =
  let

    fun get_rec_callees (finfos: FunctionInfo.function_info Symtab.table) f =
      let
        val info = case (Symtab.lookup finfos f) of SOME i => i | NONE => error ("function " ^ f ^ " undefined");
        val rec_callees =  Symset.dest (FunctionInfo.get_recursive_clique info);
      in rec_callees end

    fun get_callees (finfos: FunctionInfo.function_info Symtab.table) f =
      let
        val info = case (Symtab.lookup finfos f) of SOME i => i | NONE => error ("function " ^ f ^ " undefined");
        val callees =  Symset.dest 
             (Symset.subtract (FunctionInfo.get_recursive_clique info)
                (Symset.union_sets [FunctionInfo.get_callees info, FunctionInfo.get_fun_ptr_dependencies info]));

      in callees end

    fun fixpoint_rec_callees  (finfos: FunctionInfo.function_info Symtab.table) fs =
      let 
        val fs' = union (op =) fs (map (get_rec_callees finfos) fs |> flat |> distinct (op =))
        val new = subtract (op =) fs fs'
      in 
        if null new then fs' else fixpoint_rec_callees finfos fs'
      end

    fun group (finfos: FunctionInfo.function_info Symtab.table) f =
      let
        val info = case (Symtab.lookup finfos f) of SOME i => i | NONE => error ("function " ^ f ^ " undefined");
        val rec_callees =  Symset.dest (FunctionInfo.get_recursive_clique info);
      in 
        if null rec_callees then [f] else fixpoint_rec_callees finfos (f::rec_callees) |> sort_strings
      end

    val group_name = space_implode "_";

    fun theory_name_group (finfos: FunctionInfo.function_info Symtab.table) cfile g phase =
          space_implode "_" [group_name g, FunctionInfo.string_of_phase phase, cfile]

    fun theory_name (finfos: FunctionInfo.function_info Symtab.table) cfile phase f = 
      theory_name_group finfos cfile (group finfos f) phase

    fun theory_content finfos cfile f phase =
      let
        val scope = group finfos f
        val callees = scope |> map (get_callees finfos) |> flat |> distinct (op =);
        val f_prev = if phase = FunctionInfo.L1 then "" else theory_name finfos cfile (FunctionInfo.prev_phase skips phase) f;
        val imports = (if f_prev = "" then [] else [f_prev]) @ map (theory_name finfos cfile phase) callees;

      in
        (theory_name finfos cfile phase f,
         (imports,
          (scope,
           phase)))
      end

    fun theory_final_name cfile = "autocorres_final_" ^ cfile 
    fun theory_final_content finfos cfile groups =
      let
        val name = theory_final_name cfile
        val imports = groups |> map (fn g => theory_name_group finfos cfile g max_phase) 

      in
        (name, (imports, ([], FunctionInfo.TS)))
      end

    fun mk_thys finfos cfile =
      let
        val groups = finfos |> Symtab.dest |> map (group finfos o fst) |> distinct (op =)
        val phases = FunctionInfo.phases |> drop 1 |> take (FunctionInfo.encode_phase max_phase)  
        fun mk phase = 
              groups 
              |> map (fn g =>  
                   (theory_content finfos cfile (hd g) phase))
        val final = (theory_final_content finfos cfile groups)
      in
        final::(phases |> map mk |> flat)
      end
  in
     mk_thys finfos cfile
  end

fun forall2 p [] = true
  | forall2 p [_] = true
  | forall2 p (x::y::xs) = p x y andalso forall2 p (y::xs);

fun existing_info lthy filename =
  let
    val existing_phases = Symtab.lookup (AutoCorresData.FunctionInfo.get (Context.Proof lthy)) filename

    val get_existing_optional_phase =
        case existing_phases of
            NONE => (fn phase => SOME Symtab.empty)
          | SOME phases => FunctionInfo.Phasetab.lookup phases 

    fun get_existing_phase phase =
         Option.getOpt (get_existing_optional_phase phase, Symtab.empty)

  in get_existing_phase end

 
fun add_progenv_decls phase prog_info filename thy =
  let
    fun decl_from_inst (base_name, Const (full_name, T)) =
      let
        val prog_name = ProgramInfo.get_prog_name prog_info
        val b = Binding.make (base_name, \<^here>) |> Binding.qualify false prog_name
      in
        ((b, T), Mixfix.NoSyn)
      end

    val ctxt = Proof_Context.init_global thy
    val decls = map decl_from_inst (AutoCorresData.progenv_insts ctxt prog_info phase)
    fun declare_progenv decl thy =
      let
        val (p, thy) = Theory.specify_const decl thy
      in
        thy
      end
    val globloc = NameGeneration.intern_globals_locale_name thy filename 

  in
    thy 
    |> fold declare_progenv decls
  end


fun add_progenv_corres_bundle (prev_phase, phase) prog_info filename thy = 
  let
    val mk_thm = case phase of 
          FunctionInfo.HL => HeapLift.mk_L2Tcorres_fun_ptr_thm prog_info ([], [])
        | FunctionInfo.WA => WordAbstract.mk_corresTA_fun_ptr_thm prog_info ([], [])
        | FunctionInfo.TS => TypeStrengthen.mk_corresTS_fun_ptr_thm prog_info ([], [])
        | _ => error ("add_progenv_corres_bundle: undefined phase: " ^ @{make_string} phase) 
    val name = AutoCorresData.global_impl_corres_bundle phase filename
  in
    thy 
    |> Bundle.init (Binding.make (name, \<^here>))
    |> AutoCorresData.prove_and_note_fun_ptr_intros true (prev_phase, phase) prog_info (mk_thm)
    |> Local_Theory.exit_global
  end


fun L1_fn_ptr_corres p Gamma P ctxt =
  let
    val prop = \<^infer_instantiate>\<open>p = p and G = Gamma and P = P in prop\<open>L1corres True G (P p) (Call p)\<close>\<close> ctxt
  in
    SOME ((prop, []), ctxt) 
  end

fun L2_fn_ptr_corres prog_info p P_L1 (P_L2 as Const (_, T)) ctxt =
  let
    val (ptrT::argTs, retT) = strip_type T
    val {exT = errT, resT =  resT, ...} = AutoCorresData.dest_exn_monad_result_type retT
    val args = map_index (fn (i, T) => ("in'" ^ @{make_string} i ^ "'", T)) argTs
    val res = (@{make_string} (length args), resT)
    val vars = LocalVarExtract.make_set args
    val precond = LocalVarExtract.mk_precond ctxt prog_info Free vars
    val (_::args', ctxt1) = Utils.fix_variant_frees ([res] @ args) ctxt
    val return_xf = LocalVarExtract.mk_xf ctxt prog_info (LocalVarExtract.make_set [res])
    val except_xf = LocalVarExtract.mk_xf ctxt prog_info (LocalVarExtract.exn_var)

    val L2 = betapplys(P_L2, p::args')
    val L1 = betapplys(P_L1, [p])
    val prop = \<^infer_instantiate>\<open>st = \<open>ProgramInfo.get_globals_getter prog_info\<close> and 
      ret_xf = return_xf and ex_xf = except_xf and L2 = L2 and L1 = L1 and pre = precond in
      prop\<open>L2corres st ret_xf ex_xf pre L2 L1\<close>\<close> ctxt1
  in
    SOME ((prop, []), ctxt1)
  end

fun HL_fn_ptr_corres HL_setup p (P_prev as Const (_, T_prev)) (P as Const (Pname, T)) ctxt =
  let
    val (ptrT::argTs, ret_prevT) = strip_type T_prev
    val stateT = T |> strip_type |> fst |> split_last |> snd
    val args = map (fn T => ("x", T)) argTs
    val st = #lift_fn_full (#heap_info HL_setup)
    val (args', ctxt1) = Utils.fix_variant_frees args ctxt
    val P_prev' = betapplys(P_prev, p::args')
    val P' = betapplys(P, p::args')
    val prop = \<^infer_instantiate>\<open>st = st and P = P' and P_prev = P_prev' in prop \<open>L2Tcorres st P P_prev\<close>\<close> ctxt1
  in
    SOME ((prop, @{attributes [consumes 1]}), ctxt1)
  end


fun WA_fn_ptr_corres opt p (P_prev as Const (_, T_prev)) (P as Const (Pname, T)) ctxt =
  let
    val unsigned_word_abs = the_default false (AutoCorres_Options.get_unsigned_word_abs_known_functions opt)
    val no_signed_word_abs = the_default false (AutoCorres_Options.get_no_signed_word_abs_known_functions opt)
    val WA_rules = 
      (if unsigned_word_abs then WordAbstract.word_abs else []) @ 
      (if no_signed_word_abs then [] else WordAbstract.sword_abs)
    val (ptrT::prev_argTs, mprevT) = strip_type T_prev
    val {resT = ret_prevT, ...} = AutoCorresData.dest_exn_monad_result_type mprevT

    val (_ :: argTs, mT) = strip_type T
    val {resT = retT, ...} = AutoCorresData.dest_exn_monad_result_type mT

    val prev_args = map (fn T => ("x", T)) prev_argTs
    val args = map (fn T => ("y", T)) argTs

    fun matches xT yT t =
      let val ([dT], rT) = strip_type (fastype_of t) 
      in if dT = xT andalso rT = yT then SOME t else NONE end


    fun abs_fun xT yT = 
      if xT = yT then
         \<^Const>\<open>id xT\<close>
       else
         the (get_first (matches xT yT o #abs_fn) WA_rules)

    val rt = abs_fun ret_prevT retT
    val (prev_args, ctxt1) = Utils.fix_variant_frees (prev_args) ctxt
    val (args, ctxt2) = Utils.fix_variant_frees (args) ctxt1


    fun abs_var (x as Free (_, xT), y as Free (_, yT)) = 
      \<^infer_instantiate>\<open>x = x and y = y and f = \<open>abs_fun xT yT\<close> in term \<open>abs_var y f x\<close>\<close> ctxt2

    val abs_conj = Utils.mk_conj_list (map abs_var (prev_args ~~ args))

    val P_prev = betapplys(P_prev, [p] @ prev_args)
    val P = betapplys(P, [p] @ args)
    val prop = \<^infer_instantiate>\<open>Pre = abs_conj and rt = rt and P_prev = P_prev and P = P in 
      prop\<open>corresTA (\<lambda>s. Pre) rt id P P_prev\<close>\<close> ctxt2
  in
    SOME ((prop, []), ctxt2)
  end
  handle Option => NONE


fun TS_fn_ptr_corres opt p (P_prev as Const (_, T_prev)) (P as Const (Pname, T)) ctxt =
  let
    val target_monad_name = the_default "exit" (AutoCorres_Options.get_ts_force_known_functions opt)
    val (ptrT::prev_argTs, mprevT) = strip_type T_prev
    val {exT = ex_prevT, resT= ret_prevT,stateT} = AutoCorresData.dest_exn_monad_result_type mprevT

    val args = map (fn T => ("x", T)) prev_argTs
    val (s::args, ctxt') = Utils.fix_variant_frees ([("s", stateT)] @ args) ctxt
    val mt = Monad_Types.get_monad_type target_monad_name (Context.Proof ctxt) |> the
    val lift = #lift (#refines_nondet mt)
    val relator = (case ex_prevT of
          \<^Type>\<open>c_exntype _\<close> => Monad_Types.relator_from_c_exntype (#refines_nondet mt)
         | _ => #relator (#refines_nondet mt))
    val old = betapplys (P_prev, p::args)
    val new = betapplys (P, p::args)
    val resT = AutoCorresData.res_type_of_exn_monad old
    val exT = AutoCorresData.ex_type_of_exn_monad old
    val corres = (
     \<^instantiate>\<open>
         's = stateT and 'a = resT and 'f = exT and 'x = dummyT and 'e = dummyT and 'b = dummyT and 
         s = \<open>s\<close> and old = old and lift=\<open>Utils.dummy lift\<close> and 
         new = new and relator=\<open>Utils.dummy relator\<close>
       in 
         prop \<open>refines old (lift new) s s (rel_prod relator (=))\<close> 
       for s::'s and old::\<open>('f, 'a, 's) exn_monad\<close> and 
           lift::\<open>'x \<Rightarrow> ('e::default, 'b, 's) spec_monad\<close> and new::'x and
           relator::\<open>('f, 'a) xval \<Rightarrow> ('e::default, 'b) exception_or_result \<Rightarrow> bool\<close>\<close> 
       |> Utils.infer_types_simple ctxt) handle ERROR _ => raise TERM ("", [])
    val synth_rule_attrib = Attrib.internal \<^here> (K (Monad_Types.add_call_rule_attrib mt {only_schematic_goal=false} Binding.empty 6))
  in
    SOME ((corres, @{attributes [consumes 1]} @ [synth_rule_attrib]), ctxt')
  end
  handle TYPE _ => NONE | TERM _ => NONE

fun add_corres_locale HL_setup_opt opt (prev_phase, phase) prog_info filename thy =
  if phase = FunctionInfo.HL andalso is_none HL_setup_opt then thy 
  else
    let
      fun prop FunctionInfo.L1 = L1_fn_ptr_corres
        | prop FunctionInfo.L2 = L2_fn_ptr_corres prog_info
        | prop FunctionInfo.HL = HL_fn_ptr_corres (the HL_setup_opt)
        | prop FunctionInfo.WA = WA_fn_ptr_corres opt
        | prop FunctionInfo.TS = TS_fn_ptr_corres opt
    in
      AutoCorresData.add_global_corres_locale (prev_phase, phase) prog_info prop thy
    end

fun fun_options opt fname =
  let
    val {skip_io_abs, skip_heap_abs, skip_word_abs} = AutoCorres_Options.get_skips opt
    val heap_abs = not (skip_heap_abs orelse member (op =) (these (AutoCorres_Options.get_no_heap_abs opt)) fname)
    val signed_abs = not (skip_word_abs orelse member (op =) (these (AutoCorres_Options.get_no_signed_word_abs opt)) fname)
    val unsigned_abs = (not skip_word_abs) andalso member (op =) (these (AutoCorres_Options.get_unsigned_word_abs opt)) fname
    val in_out_globals =  (not skip_io_abs) andalso member (op =) (these (AutoCorres_Options.get_in_out_globals opt)) fname
    val in_out_params = AList.lookup (op =) (these (AutoCorres_Options.get_in_out_parameters opt)) fname |> these
    val in_out_params_opt = if skip_io_abs then NONE else SOME in_out_params

  in
    ProgramInfo.make_function_options {heap_abs = heap_abs, signed_abs = signed_abs, unsigned_abs = unsigned_abs,
      skip_heap_abs = skip_heap_abs, skip_word_abs = skip_word_abs,
      in_out_parameters = in_out_params_opt, in_out_globals = in_out_globals}
  end

fun check_options thy cfilename opt =
  let
    val csenv = the (CalculateState.get_csenv thy cfilename)
    val all_functions = ProgramAnalysis.get_functions csenv
    val method_callers = ProgramAnalysis.method_callers csenv
    val in_out_globals = these (AutoCorres_Options.get_in_out_globals opt)
    val in_out_parameters = these (AutoCorres_Options.get_in_out_parameters opt)
    val skip_in_out_phase = null in_out_globals andalso null in_out_parameters
    val check_in_out_globals = if skip_in_out_phase then () else
      let
        val in_out_globals = AutoCorres_Options.get_in_out_globals opt |> these |> sort fast_string_ord
        val unknown_functions = in_out_globals |> filter_out (member (op =) all_functions)
        val _ = if null unknown_functions then () else 
          warning ("unknown functions for option in_out_globals: " ^ @{make_string} unknown_functions)
        val known_in_out_globals = in_out_globals |> filter_out (member (op =) unknown_functions)
        val all_callers = maps (ProgramAnalysis.get_final_callers csenv) known_in_out_globals 
          |> sort_distinct fast_string_ord
        val missing_in_out_globals = all_callers |> filter_out (member (op =) known_in_out_globals)
        val _ = null missing_in_out_globals orelse
           error ("missing calling functions in in_out_globals: " ^ @{make_string} missing_in_out_globals) 
      in () end
    val check_in_out_params = if skip_in_out_phase then () else
     let
       val in_out_params = these (AutoCorres_Options.get_in_out_parameters opt)
       val funs = map fst in_out_params
       val unknown_functions = funs |> filter_out (member (op =) all_functions)
       val _ = if null unknown_functions then () else  
          warning ("unknown functions for option in_out_params: " ^ @{make_string} unknown_functions)
       val known_in_out_params = in_out_params |> filter_out (member (fn (b, a) => fst b = a) unknown_functions) 
       fun check (fname, in_outs) = 
         let
           val params = these (ProgramAnalysis.get_params fname csenv)
           fun get_info n = find_first (fn info => ProgramAnalysis.srcname info = n) params 
           val unknown_params = in_outs |> filter (is_none o get_info o fst)
           val _ = null unknown_params orelse
             error ("in_out_params: unknown parameters of function " ^ quote fname ^ ": " ^ @{make_string} unknown_params)
           fun is_ptr_type n = get_info n |> the |> ProgramAnalysis.get_vtype |> CType.ptr_type
           val non_ptr_params = in_outs |> filter_out (is_ptr_type o fst)
           val _ = null non_ptr_params orelse
             error ("in_out_params: not a pointer parameter of function " ^ quote fname ^ ": " ^ @{make_string} non_ptr_params)
         in () 
         end
       val _ = map check known_in_out_params
     in
       ()
     end
     val check_method_known_functions = if null method_callers then () else
       let
         val target_known_functions = the_default "exit" (AutoCorres_Options.get_ts_force_known_functions opt)
         val _ = writeln ("C-style method invocations detected in functions: " ^ @{make_string} method_callers)
         val _ = 
           if target_known_functions <> "exit" then 
             warning ("all potential function pointer instances for 'C-style object methods' must fit into (forced) target monad for known functions: " ^ 
               quote target_known_functions) 
           else ()
         val ts_force = AutoCorres_Options.get_ts_force opt
         fun ts fname = the_default "exit" (Symtab.lookup ts_force fname)
         val ts_rules = Monad_Types.get_ordered_rules [] (Context.Theory thy)
         fun ts_index rule_name = find_index (fn x => #name x = rule_name) ts_rules
         fun check_ts_fun fname = 
           let 
             val fi = ts_index (ts fname)
             val ki = ts_index target_known_functions
           in
             if fi < ki then
                error ("ts monad " ^ quote (ts fname) ^ " for function " ^ quote fname ^ 
                  " must be contained in monad " ^ quote target_known_functions ^ " for function pointers of known functions")
             else ()
           end
        val _ = map check_ts_fun method_callers
        val unsigned_word_abs = AutoCorres_Options.get_unsigned_word_abs opt
        val unsigned_word_abs_known_functions = AutoCorres_Options.get_unsigned_word_abs opt
        val no_signed_word_abs = AutoCorres_Options.get_no_signed_word_abs opt
        val no_signed_word_abs_known_functions = AutoCorres_Options.get_no_signed_word_abs opt
        val _ = 
          if is_none unsigned_word_abs andalso is_none unsigned_word_abs_known_functions andalso
             is_none no_signed_word_abs andalso is_none no_signed_word_abs_known_functions then () 
          else
            warning ("Make sure that word abstraction options for all functions that may be called via 'C-style object methods' must be" ^ 
                     "compatible with word abstraction options for known_functions!")
       in
        ()
       end
  in
    ()
  end

fun finalise prog_info skips keep_going existing_ts (cliques, thy) =
  let
    val filename = ProgramInfo.get_prog_name prog_info
    val info_phase = FunctionInfo.info_phase skips
  in
    thy |> fold (fn clique => fn thy =>
    let
      val loc = AutoCorresData.intern_final_corres_locale thy clique

      val lthy = Named_Target.init [] loc thy
      val [simpl_info, l1_info, l2_info, io_info, hl_info, wa_info, ts_info] = 
        map (
             AutoCorresData.get_default_phase_info (Context.Proof lthy) filename o 
             info_phase)
         [FunctionInfo.CP, FunctionInfo.L1, FunctionInfo.L2, FunctionInfo.IO, FunctionInfo.HL, FunctionInfo.WA, FunctionInfo.TS]
    
      val ops = the (In_Out_Parameters.Data.get (NameGeneration.global_rcd_name) lthy)
      (* Put together final ac_corres theorems.
       * TODO: we should also store these as theory data. *) 
      fun prove_ac_corres fn_name =
      let
        fun get_corres_thm name (info:FunctionInfo.function_info Symtab.table) = 
          let
            val thm = FunctionInfo.get_corres_thm (the (Symtab.lookup info name))
              handle Option => raise SimplConv.FunctionNotFound name
          in Thm.transfer' lthy thm end;
    
        fun simplified ctxt thms = Simplifier.simplify ((Raw_Simplifier.clear_simpset ctxt) addsimps thms)
        val l1_thm = get_corres_thm fn_name l1_info
        val l2_thm = get_corres_thm fn_name l2_info |> CLocals.folded_with [filename, fn_name] lthy
                     (* If in-out lifting was disabled, we use a placeholder *)
        val io_thm = if #skip_io_abs skips then
                       @{thm IOcorres_trivial_from_local_var_extract} OF [l2_thm] 
                     else
                       get_corres_thm fn_name io_info |> #refines_to_IOcorres_conv ops lthy

                     (* If heap lifting was disabled, we use a placeholder *)
        val hl_thm = if #skip_heap_abs skips then @{thm L2Tcorres_trivial_from_in_out_parameters} OF [io_thm] 
                     else get_corres_thm fn_name hl_info 
    
                     (* Placeholder for when word abstraction is disabled *)
        val wa_thm = if #skip_word_abs skips then @{thm corresTA_trivial_from_heap_lift} OF [hl_thm]
                     else get_corres_thm fn_name wa_info
        val ts_thm = get_corres_thm fn_name ts_info
              |> simplified lthy @{thms refines_eq_convs}
                   
      in let
           fun inst_ac_rule rule = try (fn rule => rule OF [l1_thm, l2_thm, io_thm, hl_thm, wa_thm, ts_thm]) rule
           val final_thm = the (get_first inst_ac_rule @{thms ac_corres_chain_sims}) 
           (* Remove fluff, like "f o id", that gets introduced by the HL and WA placeholders *)
           val final_thm' = Simplifier.simplify (put_simpset AUTOCORRES_SIMPSET lthy) final_thm

         in SOME final_thm' end
         handle THM _ =>
             (Utils.THM_non_critical keep_going
                  ("autocorres: failed to prove ac_corres theorem for " ^ fn_name)
                  0 [l1_thm, l2_thm, io_thm, hl_thm, wa_thm, ts_thm];
              NONE) 
      end
    
      val ts_info_todos = Symtab.dest ts_info 
          |> filter_out (fn (k,p) => not (member (op =) clique k) orelse Symtab.defined existing_ts k)

      val _ = verbose_msg 0 lthy (fn _ => "Doing final autocorres proof for: " ^ Utils.commas (map fst ts_info_todos) ^ 
                " in locale " ^ loc)

      val ac_corres_thms = ts_info_todos
            |> map fst 
            |> Par_List.map (fn f => Option.map (pair f) (prove_ac_corres f))
            |> List.mapPartial I
      val ac_corres_attrib = map (Attrib.attribute lthy) @{attributes [ac_corres]}

      val lthy = lthy 
        |> fold (fn (f, thm) =>
             Utils.define_lemma (Binding.name (ProgramInfo.get_mk_fun_name prog_info FunctionInfo.TS "" f ^ "_ac_corres")) 
                ac_corres_attrib thm #> snd)
             ac_corres_thms 
        
    in Local_Theory.exit_global lthy end) cliques
  end

(*
 * Worker for the autocorres command. opt is already merged by parallel_autocorres.
 *)
fun do_autocorres parallel (opt : AutoCorres_Options.autocorres_options) filename prog_info HL_setup_opt thy = 
  AutoCorresUtil.timeit_msg 1 (Proof_Context.init_global thy) (fn _ => "autocorres") (fn () =>
let

  val globals_locale = NameGeneration.intern_globals_locale_name thy filename  
 

  val lthy = case try (Named_Target.init [] globals_locale) thy of
                 SOME lthy => lthy
               | NONE => error ("autocorres: no such locale: " ^ globals_locale)
  val lthy = lthy |> AutoCorres_Options.Options_Proof.map (K opt)
  val all_simpl_info = AutoCorresData.get_phase_info (Context.Proof lthy) filename FunctionInfo.CP |> the

  (* Fetch program information from the C-parser output. *)
  val all_simpl_functions = Symset.make (Symtab.keys all_simpl_info)


  (* Process autocorres options. *)
  val keep_going = AutoCorres_Options.get_keep_going opt = SOME true

  val _ = if not (AutoCorres_Options.get_unsigned_word_abs opt = NONE) andalso not (AutoCorres_Options.get_skip_word_abs opt = NONE) then
              error "autocorres: unsigned_word_abs and skip_word_abs cannot be used together."
          else if not (AutoCorres_Options.get_no_signed_word_abs opt = NONE) andalso not (AutoCorres_Options.get_skip_word_abs opt = NONE) then
              error "autocorres: no_signed_word_abs and skip_word_abs cannot be used together."
          else ()

  val _ = if not (AutoCorres_Options.get_no_heap_abs opt = NONE) andalso not (AutoCorres_Options.get_skip_heap_abs opt = NONE) then
              error "autocorres: no_heap_abs and skip_heap_abs cannot be used together."
          else ()
  val no_heap_abs = these (AutoCorres_Options.get_no_heap_abs opt)

  val skips = AutoCorres_Options.get_skips opt
  (* Resolve rule names for ts_rules and ts_force. *)
  val ts_force = Symtab.map (K (fn name => Monad_Types.get_monad_type name (Context.Proof lthy)
                                  |> the handle Option => Monad_Types.error_no_such_mt name))
                            (AutoCorres_Options.get_ts_force opt)
  val ts_rules = Monad_Types.get_ordered_rules (these (AutoCorres_Options.get_ts_rules opt)) (Context.Proof lthy)
  (* heap_abs_syntax defaults to off. *)
  val heap_abs_syntax = AutoCorres_Options.get_heap_abs_syntax opt = SOME true

  (* maximal phase to translate functions *)
  val max_phase = the_default FunctionInfo.TS (AutoCorres_Options.get_phase opt)

  (* (Finished processing options.) *)

  val prev_phase = FunctionInfo.prev_phase skips 

  val phases = FunctionInfo.phases
  val todo_phases = phases 
       |> take (FunctionInfo.encode_phase max_phase) 
       |> drop 1
       |> #skip_heap_abs skips ? filter_out (fn phase => phase = FunctionInfo.HL)
       |> #skip_word_abs skips ? filter_out (fn phase => phase = FunctionInfo.WA)
 
  val existing_infos = map (existing_info lthy filename) phases
  fun info infos phase = nth infos (FunctionInfo.encode_phase phase)
  val existing_info = info existing_infos

  fun keyset finfo = finfo |> Symtab.keys |> Symset.make
 
  fun verbose_phase_info str info = phases 
      |> map (fn phase => verbose_msg 1 lthy (fn _ => str ^ " " ^ FunctionInfo.string_of_phase phase ^ ": " ^
           @{make_string} (Symtab.keys (info phase))))

  val _ = verbose_phase_info "existing_info" existing_info;
  
  val _ = @{assert} (forall (fn p =>
      Symset.subset (keyset (existing_info p), keyset (existing_info (prev_phase p)))) todo_phases);


  (* Skip functions that have already been translated. *)
  val already_translated = Symset.make (Symtab.keys (existing_info max_phase))

  (* Determine which functions should be translated.
   * If "scope" is not specified, we translate all functions.
   * Otherwise, we translate only "scope"d functions and their direct callees
   * (which are translated using a trivial wrapper so that they can be called). *)
  val (functions_to_translate, functions_to_wrap) =
    case AutoCorres_Options.get_scope opt of
        NONE => (all_simpl_functions, Symset.empty)
      | SOME fs =>
        let
          val scope_depth = the_default 2 (AutoCorres_Options.get_scope_depth opt)
          val get_deps = get_function_deps (fn f =>
                           the_default Symset.empty (Option.map FunctionInfo.all_callees (Symtab.lookup all_simpl_info f)))
          val funcs = get_deps fs scope_depth
          val funcs_callees =
            Symset.subtract (Symset.union already_translated funcs) (get_deps (Symset.dest funcs) 1)
        in (funcs, funcs_callees) end

  (* If a function has no SIMPL body, we will not wrap its body;
   * instead we create a dummy definition and translate it via the usual process. *)
  val undefined_functions =
        Symset.filter (fn f => FunctionInfo.get_invented_body (the (Symtab.lookup all_simpl_info f))) functions_to_wrap
  val functions_to_wrap = Symset.subtract undefined_functions functions_to_wrap
  val functions_to_translate = Symset.union undefined_functions functions_to_translate

  val _ = verbose_msg 0 lthy (fn _ => "autocorres scope: selected " ^ Int.toString (Symset.card functions_to_translate) ^ " function(s): " ^ 
            Utils.commas (Symset.dest functions_to_translate) ^ "\n" ^
            "autocorres scope: wrapping " ^ Int.toString (Symset.card functions_to_wrap) ^ " function(s): " ^
            Utils.commas (Symset.dest functions_to_wrap));

  val nothing_todo =  Symset.is_empty (Symset.subtract already_translated functions_to_translate) 

  val _ = if nothing_todo then error ("All functions in scope are already translated (cf. option 'fresh').") 
   else ()
  (* We will process these functions... *)
  val functions_to_process = Symset.union functions_to_translate functions_to_wrap
  (* ... and ignore these functions. *)
  val functions_to_ignore = Symset.subtract functions_to_process all_simpl_functions

  (* Disallow referring to functions that don't exist or are excluded from processing. *)
  val funcs_in_options =
        these (AutoCorres_Options.get_no_heap_abs opt)
        @ these (AutoCorres_Options.get_unsigned_word_abs opt)
        @ these (AutoCorres_Options.get_no_signed_word_abs opt)
        @ these (AutoCorres_Options.get_scope opt)
        @ Symtab.keys (AutoCorres_Options.get_ts_force opt)
        |> Symset.make

  val invalid_functions =
        Symset.subtract all_simpl_functions funcs_in_options
  val ignored_functions =
        Symset.subtract (Symset.union invalid_functions functions_to_process) funcs_in_options
  val _ =
    if Symset.card invalid_functions > 0 then
      error ("autocorres: no such function(s): " ^ commas (Symset.dest invalid_functions))
    else if Symset.card ignored_functions > 0 andalso not parallel then
      warning ("autocorres: cannot configure translation for excluded function(s): " ^
             commas (Symset.dest ignored_functions))
    else
      ()



  (* Only translate "scope" functions and their direct callees. *)
  val simpl_info =
        Symtab.dest all_simpl_info
        |> List.mapPartial (fn (name, info) =>
             if Symset.contains functions_to_translate name orelse Symset.contains already_translated name then
               (* we leave already translated function in, otherwise their callee information is stripped out
                * of the functions_to_translate *)
               SOME (name, FunctionInfo.map_is_simpl_wrapper (K false) info)
             else if Symset.contains functions_to_wrap name then
               SOME (name, FunctionInfo.map_is_simpl_wrapper (K true) info)
      
             else
               NONE)
        |> Symtab.make


  (* Recalculate callees after "scope" restriction. *)
  val (simpl_call_graph, simpl_info) = FunctionInfo.calc_call_graph simpl_info
  (* Check that recursive function groups are all lifted to the same monad. *)
  val _ = #topo_sorted_functions simpl_call_graph
          |> map (TypeStrengthen.compute_lift_rules ts_rules ts_force o Symset.dest)

  (* Disable heap lifting for all un-translated functions. *)
  val no_heap_abs = Symset.union (Symset.make no_heap_abs) functions_to_wrap

  (* Disable word abstraction for all un-translated functions. *)
  val unsigned_word_abs = these (AutoCorres_Options.get_unsigned_word_abs opt) |> Symset.make
  val no_signed_word_abs = these (AutoCorres_Options.get_no_signed_word_abs opt) |> Symset.make
  val conflicting_unsigned_abs_fns =
        Symset.subtract functions_to_translate unsigned_word_abs

  val _ = if parallel orelse Symset.is_empty conflicting_unsigned_abs_fns then () else
            error ("autocorres: Functions marked 'unsigned_word_abs' but excluded from 'scope': "
                   ^ commas (Symset.dest conflicting_unsigned_abs_fns))

  val no_signed_word_abs = Symset.union no_signed_word_abs functions_to_wrap

  val do_polish = the_default true (AutoCorres_Options.get_do_polish opt)
  val L1_opt = the_default FunctionInfo.PEEP (AutoCorres_Options.get_L1_opt opt)
  val L2_opt = the_default FunctionInfo.PEEP (AutoCorres_Options.get_L2_opt opt)
  val HL_opt = the_default FunctionInfo.PEEP (AutoCorres_Options.get_HL_opt opt)
  val WA_opt = the_default FunctionInfo.PEEP (AutoCorres_Options.get_WA_opt opt)

  val trace_opt = AutoCorres_Options.get_trace_opt opt = SOME true
  val gen_word_heaps = AutoCorres_Options.get_gen_word_heaps opt = SOME true

  (* Any function that was declared in the C file (but never defined) should
   * stay in the nondet-monad unless explicitly instructed by the user to be
   * something else. *)
  val ts_force = let
    val invented_functions =
      functions_to_process
      (* Select functions with an invented body. *)
      |> Symset.filter (Symtab.lookup simpl_info #> the #> FunctionInfo.get_invented_body)
      (* Ignore functions which already have a "ts_force" rule applied to them. *)
      |> Symset.subtract (Symset.make (Symtab.keys ts_force))
      |> Symset.dest
  in
    (* Use the most general monadic type allowed by the user. *)
    fold (fn n => Symtab.update_new (n, List.last ts_rules)) invented_functions ts_force
  end

  (* Prefixes/suffixes for generated names. *)
  val make_lifted_globals_field_name = let
    val prefix = case AutoCorres_Options.get_lifted_globals_field_prefix opt of
                     NONE => ""
                   | SOME p => p
    val suffix = case AutoCorres_Options.get_lifted_globals_field_suffix opt of
                     NONE => "_''"
                   | SOME s => s
  in fn f => prefix ^ f ^ suffix end

  fun do_phase' empty phase translate lthy = 
    if FunctionInfo.encode_phase phase <= FunctionInfo.encode_phase max_phase then
       (verbose_msg 1 lthy (fn _ => "Processing phase: " ^ FunctionInfo.string_of_phase phase); translate lthy)
    else (verbose_msg 1 lthy (fn _ => "Skipping phase: " ^ FunctionInfo.string_of_phase phase); empty lthy)

  val do_phase = do_phase' (fn lthy => ([], lthy))

  val base_locale_opt = AutoCorres_Options.get_base_locale opt
    |> Option.map (Locale.check thy)

  (* Do the translation. *)
  val (simpl_call_graph, _) = FunctionInfo.calc_call_graph simpl_info;
  val cliques = FunctionInfo.group_cliques simpl_call_graph
  val _ = verbose_msg 0 lthy (fn _ => "cliques: " ^ @{make_string} cliques)

  val (l1_cliques, lthy) = lthy |> do_phase FunctionInfo.L1 (
        SimplConv.translate
            skips
            base_locale_opt
            prog_info 
            (AutoCorres_Options.get_no_c_termination opt <> SOME true)
            L1_opt trace_opt parallel
            cliques);

  val (l2_cliques, lthy) = lthy |> do_phase FunctionInfo.L2 (
        LocalVarExtract.translate
            skips
            base_locale_opt
            prog_info  
            L2_opt trace_opt parallel 
            l1_cliques);
  (* When skip_io_abs / skip_heap_abs / skip_word_abs is set, we just pass the results from the previous
   * phase to the next phase. Function prove_ac_corres will then reflect these steps as 
   * identity transformations in the final proof. By passing the results to the final phase, 
   * we ensure that polishing
   * of the body and the final definition of the function is done.
   *)

  val (io_cliques, lthy) = lthy |> do_phase FunctionInfo.IO (fn lthy =>
    if #skip_io_abs skips
    then (l2_cliques, lthy)
    else lthy |>
      In_Out_Parameters.translate
        skips
        base_locale_opt
        prog_info
        parallel
        l2_cliques);

  val ((hl_cliques, maybe_heap_info), lthy) = 
    lthy |> do_phase' (fn lthy => (([], NONE), lthy)) FunctionInfo.HL (fn lthy =>
        if #skip_heap_abs skips
        then ((io_cliques, NONE), lthy)
        else 
          let
            val (hl_groups, lthy) = lthy |> HeapLift.translate
               skips
               base_locale_opt
               prog_info
               (the HL_setup_opt) no_heap_abs
               heap_abs_syntax keep_going
               HL_opt trace_opt parallel
               io_cliques

          in 
            ((hl_groups, SOME (#heap_info (the HL_setup_opt))), lthy)
          end);

  val (wa_cliques, lthy) = lthy |> do_phase FunctionInfo.WA  (fn lthy =>
        if #skip_word_abs skips
        then (hl_cliques, lthy) \<comment> \<open>c.f. previous comment on heap_lift phase\<close>  
        else lthy |> WordAbstract.translate skips base_locale_opt prog_info
               maybe_heap_info  
               unsigned_word_abs no_signed_word_abs
               WA_opt trace_opt parallel
               hl_cliques);

  val (ts_cliques, lthy) = lthy |> do_phase FunctionInfo.TS (
        TypeStrengthen.translate
            skips
            base_locale_opt
            ts_rules ts_force prog_info
            keep_going do_polish
            (wa_cliques))
  val thy = lthy |> Local_Theory.exit_global
    |> AutoCorresTrace.ProfileConv.transfer lthy
in
  (ts_cliques, thy)
end);

(* the final theory has no scope just combines everything *)
fun final_task (_, (_, (scope, _))) = null scope

fun spawn_autocorres filename prog_info HL_setup opts tasks thy =
  let
     val ctxt = Proof_Context.init_global thy
     fun trace s = Utils.timing_msg 1 ctxt (fn () => "autocorres scheduler: " ^ s ()) 

     fun depends name = 
       case AList.lookup (op =) tasks name of
         NONE => []
       | SOME (imports, _) => imports
 
     fun ac (t as (name, (imports, (scope, phase)))) (cliques, thy)  =
       if final_task t then (cliques, thy)
       else
         let
           val opts' = AutoCorres_Options.upd_opts opts scope phase 
           val _ = trace (fn () => "doing autocorres for: " ^ name)
         in do_autocorres true opts' filename prog_info HL_setup thy end

     fun join results = 
      let 
        val (cliquess, thys) = split_list results 
      in (flat cliquess |> distinct (op =), Context.join_thys thys) end

     val results = Utils.map_reduce trace I fst depends ac join tasks ([], thy)

     val final_task_name = fst (hd (filter final_task tasks))
  in
    case AList.lookup (op =) results final_task_name of 
      SOME res => res
    | NONE => error ("parallel autocorres failed in building the theories")
  end


fun is_initialized filename thy =
  Symtab.defined (fst (AutoCorres_Options.Options_Theory.get thy)) filename 

fun get_prog_info thy filename =
  the (Symtab.lookup (fst (AutoCorres_Options.Options_Theory.get thy)) filename) |> #prog_info


fun check_addressable_field thy xnames =
  let
    val ctxt = Proof_Context.init_global thy
    fun ensure_C_names [] = error ("addressable_fields: expecting structure name and at least one field name")
      | ensure_C_names [x] = (x,[]) (* x must be a array type *)
      | ensure_C_names (x::xs) = 
         (NameGeneration.ensure_C_struct_name x,  map NameGeneration.ensure_C_field_name xs)

    val (record_name, field_names) = ensure_C_names xnames


    val record_info = RecursiveRecordPackage.get_info thy
    fun select field (recordT, field_infos) =
      let
        val Type(record_name, _) = recordT     
      in
        case Symtab.lookup record_info record_name of
          SOME {fields,...} => (case find_first (fn (xn, T) => Long_Name.base_name xn = field) fields of 
                                  SOME (field_name, T) => (T, field_infos @ [(field_name, T)])
                                | NONE => error ("unknown field " ^ quote field ^ " for " ^ quote record_name))
        | NONE => error ("unknown struct type: " ^ quote record_name)
      end

    val T = \<^try>\<open>Proof_Context.read_typ ctxt record_name catch _ => error ("unknown struct type: " ^ quote record_name)\<close>
    val _ = if null field_names andalso not (TermsTypes.is_array_type T) then error ("not an array type: " ^ quote (Syntax.string_of_typ ctxt T))
            else ()
    val (_, fields) =  (T, []) |> fold select field_names  
  in
    (T, fields)
  end
    
fun check_addressable_fields ignore_addressable_fields_error thy prog_info xnames =
 let
   val ctxt = Proof_Context.init_global thy
   val record_info = RecursiveRecordPackage.get_info thy
   fun merge_fields (fs as ((T, _)::_) ) = (T, distinct (op =) (map snd fs))  
   val singles = map (check_addressable_field thy) xnames |> group_by (fn ((T1, _), (T2, _)) => T1 = T2) 
     |> map merge_fields   

   fun all_fields (Type(record_name, _)) = Symtab.lookup record_info record_name |> the |> #fields

   fun suffixes sfxs field = 
     let
        val sfxs' = map_filter (fn (f::fs) => if f = field  then SOME fs else NONE | _ => NONE) sfxs
     in
       if null sfxs' then NONE else SOME (field, sfxs') 
     end

   fun expand_fields (prefix:(string*typ) list) (addressable_sfxs: (string*typ) list list) (T:typ): (string*typ) list list = 
     case addressable_sfxs of [[]] => [[]] | _ =>
     let
       val all = all_fields T
       val (addressable, not_addressable) = Utils.split_map_filter (suffixes addressable_sfxs) all
       val not_addressable' = map (fn (field as (_, fieldT), sfxs) => expand_fields (prefix @ [field]) sfxs fieldT) addressable
     in
       ( map (fn field => prefix @ [field]) not_addressable @  flat not_addressable')
     end 
   fun select_field (Type(record_name, _)) field = 
         Symtab.lookup record_info record_name |> the |> #fields 
         |> find_first (fn (long, ty) => Long_Name.base_name long = field)
         |> the
   fun filter_intermediate_arrays [] = []
     | filter_intermediate_arrays [x] = [x]
     | filter_intermediate_arrays (x::xs) = x :: filter_out (fn (ty, fld) => fld = "") xs       

   fun expand_type ty [] = []
     | expand_type ty (x::xs) = 
          (case x of 
            ProgramAnalysis.Field f => 
              let val (long, ty') = select_field ty f in (ty, long)::expand_type ty' xs end
          | ProgramAnalysis.Array_Index => 
              (case ty of
                 \<^Type>\<open>ptr ty'\<close> => expand_type ty' xs 
               | _ => let val ty' = TermsTypes.element_type ty in (ty, "")::expand_type ty' xs end))  

   val addressed_types = ProgramAnalysis.get_addressed_types (ProgramInfo.get_csenv prog_info) 
        |> Absyn.CTypeTab.dest
        |> map_filter (fn (cty, selectors) => 
            let
              val ty = CalculateState.ctype_to_typ ctxt cty
            in 
              if forall null selectors then 
                NONE
              else 
                SOME (map (filter_intermediate_arrays o expand_type ty) selectors)
            end) 
        |> flat |> flat

   val addressable_fields = singles |> map (fn (T, addressable) => 
        (T, 
         {not_addressable = expand_fields [] addressable T |> filter_out null, 
         addressable = addressable |> filter_out null}))
 
   fun find_addressable_field (ty, fld) = AList.lookup (op =) addressable_fields ty 
     |> Option.mapPartial (fn {addressable, ...} => 
          if null addressable andalso fld="" then 
            SOME ty 
          else
            get_first (fn flds => AList.lookup (op =) flds fld) addressable)

   val missing_fields = addressed_types |> filter_out (is_some o find_addressable_field)
   
   fun pretty (arr_ty, "") = Pretty.quote (Syntax.pretty_typ ctxt arr_ty)
     | pretty (struct_ty, fld) = 
         Pretty.block [
           Syntax.pretty_typ ctxt struct_ty, Pretty.str "." , 
           Pretty.str (Long_Name.base_name fld)]
  
   val trace = if ignore_addressable_fields_error then warning else error
   val _ = if null missing_fields then () else
       trace (Pretty.string_of (Pretty.big_list "These fields should be made addressable (for lifting into the split heap): " 
             (map pretty (missing_fields))))
 in
   addressable_fields
 end

fun do_init_autocorres (opt : AutoCorres_Options.autocorres_options) cfilename store_opt thy =
  let
    val filename = cfilename |> Path.explode |> Path.split_ext |> fst |> Path.file_name
  (* Ensure that the filename has already been parsed by the C parser. *)
    val csenv = case CalculateState.get_csenv thy cfilename of
          NONE => error ("Filename '" ^ cfilename ^ "' has not been parsed by the C parser yet.")
        | SOME x => x
    val globals_locale = NameGeneration.intern_globals_locale_name thy filename
  (* Prefixes/suffixes for generated names. *)
    fun gen_make_function_name phase ext = 
      let
        val phase_prefix = 
          case phase of 
               FunctionInfo.TS => "" 
             | FunctionInfo.CP => ""
             | _ => FunctionInfo.string_of_phase phase |> String.translate (str o Char.toLower) |> suffix "_"
        val prefix = 
          case phase of 
            FunctionInfo.CP => "" 
          | _ => (case AutoCorres_Options.get_function_name_prefix opt of
                         NONE => ""
                       | SOME p => p)
        val suffix =  
          case phase of 
            FunctionInfo.CP => "" 
          | _ => (case AutoCorres_Options.get_function_name_suffix opt of
                         NONE => "'"
                       | SOME s => s)
      in (fn name => phase_prefix ^ ext ^ prefix ^ name ^ suffix, 
          fn full_name => full_name |> unsuffix suffix |> unprefix phase_prefix |> unprefix ext |> unprefix prefix)
      end
    fun make_function_name phase ext name = fst (gen_make_function_name phase ext) name
    fun dest_function_name phase ext full_name = snd (gen_make_function_name phase ext) full_name

    val _ = check_options thy cfilename opt
    val thy = thy |> AutoCorres_Options.map_current_options (K (SOME opt))
  in
    if is_initialized filename thy 
    then 
      let
        val prog_info = get_prog_info thy filename
        val fun_opts = fun_options opt
        val prog_info = prog_info |> ProgramInfo.map_fun_options (K fun_opts)
        val HL_setup_opt = Symtab.lookup (HeapLiftBase.HeapInfo.get thy) filename
        val prog_info = (case HL_setup_opt of 
            SOME HL_setup =>
              prog_info |> ProgramInfo.map_lifted_globals_type 
                 (K (SOME (#globals_type (#heap_info HL_setup))))
          | NONE => prog_info)
      in
        ((prog_info, HL_setup_opt), thy)
      end
    else
      let   
        val prog_info = ProgramInfo.get_prog_info thy (fun_options opt) make_function_name dest_function_name cfilename

        val skips = AutoCorres_Options.get_skips opt
        val (_, thy) = thy |> AutoCorresData.init_function_info skips prog_info

        val ctxt = Proof_Context.init_global thy
        val params = HP_TermsTypes.globals_stack_heap_raw_state_params HP_TermsTypes.State ctxt
        val [hrs, hrs_upd,  S] = map Utils.dummy_schematic 
               [#hrs params, #hrs_upd params, #S params] 
        val params_globals = HP_TermsTypes.globals_stack_heap_raw_state_params HP_TermsTypes.Globals ctxt
        val [hrs_globals, hrs_upd_globals] = map Utils.dummy_schematic
               [#hrs params_globals, #hrs_upd params_globals]       
        val expr = ([(@{locale L2_heap_raw_state}, ((NameGeneration.global_ext_type, false),
             (Expression.Positional (map SOME ([
               hrs_globals, hrs_upd_globals,
               hrs, hrs_upd, S, ProgramInfo.get_globals_getter prog_info])), [])))], []) 
     
        val thy = thy |> Named_Target.theory_init
          |> Interpretation.global_interpretation expr []
          |> Proof.global_terminal_proof ((Method.Basic (fn ctxt =>  SIMPLE_METHOD (
              (Locale.intro_locales_tac {strict = false, eager = true} ctxt [] THEN 
                 ALLGOALS (asm_full_simp_tac (ctxt addsimps 
                   @{thms hrs_mem_def hrs_mem_update_def hrs_htd_def hrs_htd_update_def case_prod_unfold}))))), 
              Position.no_range), NONE) 
          |> Local_Theory.exit_global
   
        val lthy = Named_Target.init [] globals_locale thy
                   |> AutoCorres_Options.Options_Proof.map (K opt)

        val all_simpl_infos = AutoCorresData.get_phase_info (Context.Proof lthy) filename FunctionInfo.CP |> the
     
        (* heap_abs_syntax defaults to off. *)
        val heap_abs_syntax = AutoCorres_Options.get_heap_abs_syntax opt = SOME true
     
        (* Prefixes/suffixes for generated names. *)
        val make_lifted_globals_field_name = 
          let
            val prefix = case AutoCorres_Options.get_lifted_globals_field_prefix opt of
                           NONE => ""
                         | SOME p => p
            val suffix = case AutoCorres_Options.get_lifted_globals_field_suffix opt of
                           NONE => "_''"
                         | SOME s => s
           in fn f => prefix ^ f ^ suffix end;

        val gen_word_heaps = AutoCorres_Options.get_gen_word_heaps opt = SOME true
        val ignore_addressable_fields_error = AutoCorres_Options.get_ignore_addressable_fields_error opt = SOME true
        val addressable_fields = AutoCorres_Options.get_addressable_fields opt |> these 
          |> check_addressable_fields ignore_addressable_fields_error thy prog_info

        val (prog_info, HL_setup, lthy) = 
          if AutoCorres_Options.get_skip_heap_abs opt = SOME true then (prog_info, NONE, lthy) 
          else
            let
              val (HL_setup, lthy) = lthy |> HeapLiftBase.prepare_heap_lift filename prog_info addressable_fields 
                    all_simpl_infos make_lifted_globals_field_name gen_word_heaps heap_abs_syntax
              val prog_info = prog_info |> ProgramInfo.map_lifted_globals_type 
                    (K (SOME (#globals_type (#heap_info HL_setup))))
            in (prog_info, SOME HL_setup, lthy) end
        val opt' = if store_opt then opt else AutoCorres_Options.default_opts

        val skips = AutoCorres_Options.get_skips opt
        fun info_phase_pair phase = (FunctionInfo.prev_phase skips phase, phase)

        val thy = lthy 
          |> Local_Theory.exit_global 
          |> AutoCorres_Options.Options_Theory.map (apfst (Symtab.update (filename, {options=opt', prog_info = prog_info})))
          |> add_progenv_decls FunctionInfo.L1 prog_info filename
          |> add_corres_locale HL_setup opt (info_phase_pair FunctionInfo.L1) prog_info filename
          |> add_progenv_decls FunctionInfo.L2 prog_info filename
          |> add_corres_locale HL_setup opt (info_phase_pair FunctionInfo.L2) prog_info filename
          |> add_progenv_decls FunctionInfo.IO prog_info filename
          |> add_progenv_decls FunctionInfo.HL prog_info filename
          |> add_corres_locale HL_setup opt (info_phase_pair FunctionInfo.HL) prog_info filename
          |> add_progenv_corres_bundle (info_phase_pair FunctionInfo.HL) prog_info filename
          |> add_progenv_decls FunctionInfo.WA prog_info filename
          |> add_progenv_corres_bundle (info_phase_pair FunctionInfo.WA) prog_info filename
          |> add_corres_locale HL_setup opt (info_phase_pair FunctionInfo.WA) prog_info filename
          |> add_progenv_decls FunctionInfo.TS prog_info filename
          |> add_progenv_corres_bundle (info_phase_pair FunctionInfo.TS) prog_info filename
          |> add_corres_locale HL_setup opt (info_phase_pair FunctionInfo.TS) prog_info filename

      in ((prog_info, HL_setup), AutoCorres_Options.map_current_options (K NONE) thy) end
  end  

fun is_finalised filename thy =
  Locale.defined thy (NameGeneration.maybe_intern_locale thy (AutoCorresData.final_all_impl_locale filename))

fun final_autocorres prog_info funs thy =
  thy 
  |> AutoCorresData.add_final_all_impl_locale prog_info funs
  |> AutoCorresData.add_final_all_corres_locale prog_info funs

fun final_autocorres_cmd cfilename thy =
  let
    val start = Timing.start ();
    val filename = cfilename |> Path.explode |> Path.split_ext |> fst |> Path.file_name
    val prog_info = if is_initialized filename thy then
                       ProgramInfo.get_prog_info thy (K ProgramInfo.default_fun_options) (K (K I)) (K (K I)) cfilename
                    else 
                       error ("final_autocorres: autocorres not yet run on: " ^ quote cfilename)

   val all_functions = ProgramAnalysis.get_non_proto_and_body_spec_functions (ProgramInfo.get_csenv prog_info)

   val opt = case AutoCorres_Options.get_current_options thy of SOME opt => opt
    | NONE => AutoCorres_Options.default_opts
   val skips = AutoCorres_Options.get_skips opt
   val translated_functions = all_functions |>
         filter (Locale.defined thy o 
           AutoCorresData.definition_locale (Proof_Context.init_global thy) skips FunctionInfo.TS filename o 
           single) 
   val thy = if not (is_finalised filename thy) 
     then final_autocorres prog_info translated_functions thy
     else error ("final_autocorres: autocorres already finalized for: " ^ quote cfilename)
  in
    thy
    before (Utils.timing_msg' 1 (Proof_Context.init_global thy) (fn _ => "final-autocorres") start)
  end

fun parallel_autocorres (opt : AutoCorres_Options.autocorres_options) cfilename thy =
  let
    val start = Timing.start ();
    val filename = cfilename |> Path.explode |> Path.split_ext |> fst |> Path.file_name
    val opt = case Symtab.lookup (fst (AutoCorres_Options.Options_Theory.get thy)) filename of
           NONE => opt
         | SOME {options=opt', ...} => AutoCorres_Options.merge_opt opt' opt;
    val ((prog_info, HL_setup), thy) = do_init_autocorres opt cfilename false thy
    val globals_locale = NameGeneration.intern_globals_locale_name thy filename  

    val _ = verbose_msg 0 (Proof_Context.init_global thy) (fn _ => "options: " ^ @{make_string} opt)
    val single_threaded = AutoCorres_Options.get_single_threaded opt = SOME true  (* single threaded defaults to off. *)

    val skips = AutoCorres_Options.get_skips opt
    val keep_going = AutoCorres_Options.get_keep_going opt = SOME true       
    val max_phase = the_default FunctionInfo.TS (AutoCorres_Options.get_phase opt)
    val existing_ts = existing_info (Proof_Context.init_global thy) filename FunctionInfo.TS

    val thy =
       (if single_threaded then
          do_autocorres false opt filename prog_info HL_setup (thy)
       else
          let
            val lthy = Named_Target.init [] globals_locale thy
  
            val all_simpl_infos = AutoCorresData.get_phase_info (Context.Proof lthy) filename FunctionInfo.CP |> the
            val scope = these (AutoCorres_Options.get_scope opt)
            val reachable = if null scope then Symtab.keys all_simpl_infos  
              else all_reachable all_simpl_infos (these (AutoCorres_Options.get_scope opt))
 
            fun in_scope (t as (_, (_, (scope, _)))) = final_task t orelse subset (op =) (scope, reachable);
 
            val phase_info = existing_info lthy filename
 
            fun not_already_existing (t as (_, (_, (scope, phase)))) = final_task t orelse  
                  not (subset (op =) (scope, phase_info phase |> Symtab.keys))
   
            fun adjust_imports defined (name, (imports, (scope, phase))) = 
              let 
                val imports' = filter (member (op =) defined) imports
              in (name, (imports', (scope, phase))) end 
 
            val tasks = build_tasks all_simpl_infos filename skips max_phase 
                 |> filter in_scope
                 |> filter not_already_existing
                 |> (fn tasks => map (adjust_imports (map fst tasks)) tasks)
 
            val _ = Utils.timing_msg 1 lthy (fn () => "tasks: " ^ @{make_string} tasks)
            val _ = @{assert} (final_task (hd tasks))
 
          in case tasks of
               (_::_) => spawn_autocorres filename prog_info HL_setup opt tasks thy 
             | _ => error ("All functions in scope are already translated (cf. option 'fresh').") 
               
          end)
       |> finalise prog_info skips keep_going existing_ts
 
   val all_functions = ProgramAnalysis.get_non_proto_and_body_spec_functions (ProgramInfo.get_csenv prog_info)
 
   val all_functions_translated =
       forall (Locale.defined thy o 
         AutoCorresData.definition_locale (Proof_Context.init_global thy) skips FunctionInfo.TS filename o 
         single) 
      all_functions
 
   val thy = 
     if all_functions_translated then 
        if is_finalised filename thy then
          (warning ("autocorres already finalised for: " ^ quote cfilename); thy) 
        else 
          final_autocorres prog_info all_functions thy
     else 
       thy
  in
    thy
    before (Utils.timing_msg' 1 (Proof_Context.init_global thy) (fn _ => "autocorres (parallel)") start)
  end
     
end