(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Rewrite L1 specifications to reduce the use of exception constructs.
 * These code transformations currently do not properly deal with recursive procedures.
 * This step is left for the "Type-Strenghthening" phase. Note that due to the encoding
 * of recursive procedures with a measure parameter, with a 'fail' when the measure is
 * exceeded, these will end up at least in the option-monad.
 *)
structure ExceptionRewrite =
struct


(*
 * States what control flow a block of code exhibits.
 *
 * NoThrow and NoReturn states that the block never/always throws exceptions.
 *
 * AlwaysFail states that the block always fails (with no return states); this
 * can be converted into either NoThrow or NoReturn at will.
 *
 * UnknownExc states that we just don't know what the block of code does.
 *)
datatype exc_status =
    NoThrow of thm
  | NoReturn of thm
  | AlwaysFail of thm
  | UnknownExc

(* Convert a "always_fail" theorem into a "no_throw" or "no_return" theorem. *)
fun fail_to_nothrow t = @{thm alwaysfail_nothrow} OF [t]
fun fail_to_noreturn t = @{thm alwaysfail_noreturn} OF [t]


(*
 * Anonymize "uninteresting" parts of a L1 program to make caching more efficient.
 *
 * Structure of the program is retained, but everything else becomes bogus.
 *)
fun anon  term =
  case term of
      (Const (@{const_name "L1_skip"}, _)) => @{term L1_skip}
    | (Const (@{const_name "L1_modify"}, _) $ _) => @{term "L1_modify m"}
    | (Const (@{const_name "L1_guard"}, _) $ _) => @{term "L1_guard g"}
    | (Const (@{const_name "L1_init"}, _) $ _) => @{term "L1_init i"}
    | (Const (@{const_name "L1_spec"}, _) $ _) => @{term "L1_spec s"}
    | (Const (@{const_name "L1_assume"}, _) $ _) => @{term "L1_assume s"}
    | (Const (@{const_name "L1_throw"}, _)) => @{term "L1_throw"}
    | (Const (@{const_name "L1_fail"}, _)) => @{term "L1_fail"}
    | (Const (@{const_name "L1_call"}, _) $ _ $ body $ _ $ _) =>
        @{term "L1_call"} $ Free ("a", dummyT) $ anon  body $ Free ("b", dummyT) $ Free ("c", dummyT)
    | (Const (@{const_name "L1_condition"}, _) $ _ $ lhs $ rhs) =>
        @{term "L1_condition"} $ Free ("C", dummyT) $ anon  lhs $ anon  rhs
    | (Const (@{const_name "L1_seq"}, _) $ lhs $ rhs) =>
        @{term "L1_seq"} $ anon  lhs $ anon  rhs
    | (Const (@{const_name "L1_catch"}, _) $ lhs $ rhs) =>
        @{term "L1_catch"} $ anon  lhs $ anon  rhs
    | (Const (@{const_name "L1_while"}, _) $ _ $ body) =>
        @{term "L1_while"} $ Free ("C", dummyT) $ anon  body
    | (Const (@{const_name "stack_heap_state.with_fresh_stack_ptr"}, _) $ _ $ _ $ _ $ _ $ n $ init $ Abs (_,_, bdy)) =>
        @{term "stack_heap_state.with_fresh_stack_ptr"} $ Free("a", dummyT) $ Free("b", dummyT) $ 
          Free("c", dummyT) $ Free ("d", dummyT) $ Free ("n", dummyT) $ Free ("init", dummyT) $ anon bdy
    | x => x

structure Exc_Table = struct
  val empty = Termtab.empty
  fun lookup t k = Termtab.lookup t (anon  k)
  fun update (k, v) t = Termtab.update (anon  k, v) t
end

fun thm_cache name (f:term -> thm) = Fun_Cache.create name 
  (fn tab => @{make_string} (Termtab.dest tab)) Exc_Table.empty Exc_Table.lookup Exc_Table.update f

fun exn_cache name (f:term -> exc_status) = Fun_Cache.create name 
  (fn tab => @{make_string} (Termtab.dest tab)) Exc_Table.empty Exc_Table.lookup Exc_Table.update f


(*
 * Prove "always_progress" on a block of code.
 *)
fun always_progress term =
  case term of
      (Const (@{const_name "L1_skip"}, _)) => @{thm L1_skip_always_progress}
    | (Const (@{const_name "L1_modify"}, _) $ _) => @{thm L1_modify_always_progress}
    | (Const (@{const_name "L1_guard"}, _) $ _) => @{thm L1_guard_always_progress}
    | (Const (@{const_name "L1_init"}, _) $ _) => @{thm L1_init_always_progress}
    | (Const (@{const_name "L1_spec"}, _) $ _) => @{thm L1_spec_always_progress}
    | (Const (@{const_name "L1_throw"}, _)) => @{thm L1_throw_always_progress}
    | (Const (@{const_name "L1_fail"}, _)) => @{thm L1_fail_always_progress}
    | (Const (@{const_name "L1_call"}, _) $ _ $ body $ _ $ _) =>
        @{thm L1_call_always_progress} OF [always_progress body] 
        (* note that this will usually fail, as we currently do not do any bookeeping and propagation  
         * of empty_fail for functions (compared to no_throws where we do this) 
         *)
    | (Const (@{const_name "L1_condition"}, _) $ _ $ lhs $ rhs) =>
        @{thm L1_condition_always_progress} OF [always_progress lhs, always_progress rhs]
    | (Const (@{const_name "L1_seq"}, _) $ lhs $ rhs) =>
        @{thm L1_seq_always_progress} OF [always_progress lhs, always_progress rhs]
    | (Const (@{const_name "L1_catch"}, _) $ lhs $ rhs) =>
        @{thm L1_catch_always_progress} OF [always_progress lhs, always_progress rhs]
    | (Const (@{const_name "L1_while"}, _) $ _ $ body) =>
        @{thm L1_while_always_progress} OF [always_progress body]
    | x => Utils.invalid_term "L1_term" x
val always_progress = fn () => thm_cache @{binding "L1 exception rewrite: always_progress"} always_progress


fun is_callee callee thm =
  let
    fun dest_callee ( c $ _) = c
      | dest_callee x = x
      
    val c = dest_callee callee
    val @{term_pat "Trueprop (no_throw _ (?x _))"} = Envir.eta_contract (Thm.prop_of thm)
  in
    x = c
  end
  handle Bind => false

fun get_callee_thm callee_thms callee = find_first (is_callee callee) callee_thms

(*
 * Determine what control flow the given block of code exhibits.
 *)
fun throws_exception ctxt empty_fail callee_thms term =
  case term of
      (Const (@{const_name "L1_skip"}, _)) =>
        NoThrow @{thm L1_skip_nothrow}
    | (Const (@{const_name "L1_modify"}, _) $ _) =>
        NoThrow @{thm L1_modify_nothrow}
    | (Const (@{const_name "L1_guard"}, _) $ _) =>
        NoThrow @{thm L1_guard_nothrow}
    | (Const (@{const_name "L1_call"}, _) $ _ $ callee $ _ $ _) =>
        (case get_callee_thm callee_thms callee of
           NONE => (warning ("no no_throws theorem for : " ^ @{make_string} callee); UnknownExc)
         | SOME callee_thm => NoThrow (@{thm L1_call_nothrow} OF [callee_thm]))
    | (Const (@{const_name "L1_init"}, _) $ _) =>
        NoThrow @{thm L1_init_nothrow}
    | (Const (@{const_name "L1_spec"}, _) $ _) =>
        NoThrow @{thm L1_spec_nothrow}
    | (Const (@{const_name "L1_assume"}, _) $ _) =>
        NoThrow @{thm L1_assume_nothrow}
    | (Const (@{const_name "L1_throw"}, _)) =>
        NoReturn @{thm L1_throw_noreturn}
    | (Const (@{const_name "L1_fail"}, _)) =>
        AlwaysFail @{thm L1_fail_alwaysfail}

    | (Const (@{const_name "L1_while"}, _) $ _ $ body) =>
       (case (throws_exception ctxt empty_fail callee_thms body) of
           NoThrow thm => NoThrow (@{thm L1_while_nothrow} OF [thm])
         | _ => UnknownExc)

    | (Const (@{const_name "L1_condition"}, _) $ _ $ lhs $ rhs) =>
        (case (throws_exception ctxt empty_fail callee_thms lhs, throws_exception ctxt empty_fail callee_thms rhs) of
            (AlwaysFail lhs_thm, AlwaysFail rhs_thm) =>
              AlwaysFail (@{thm L1_condition_alwaysfail} OF [lhs_thm, rhs_thm])
          | (NoThrow lhs_thm, NoThrow rhs_thm) =>
              NoThrow (@{thm L1_condition_nothrow} OF [lhs_thm, rhs_thm])
          | (NoReturn lhs_thm, NoReturn rhs_thm) =>
              NoReturn (@{thm L1_condition_noreturn} OF [lhs_thm, rhs_thm])

          | (NoThrow lhs_thm, AlwaysFail rhs_thm) =>
              NoThrow (@{thm L1_condition_nothrow} OF [lhs_thm, fail_to_nothrow rhs_thm])
          | (NoReturn lhs_thm, AlwaysFail rhs_thm) =>
              NoReturn (@{thm L1_condition_noreturn} OF [lhs_thm, fail_to_noreturn rhs_thm])
          | (AlwaysFail lhs_thm, NoThrow rhs_thm) =>
              NoThrow (@{thm L1_condition_nothrow} OF [fail_to_nothrow lhs_thm, rhs_thm])
          | (AlwaysFail lhs_thm, NoReturn rhs_thm) =>
              NoReturn (@{thm L1_condition_noreturn} OF [fail_to_noreturn lhs_thm, rhs_thm])

          | (_, _) => UnknownExc)

    | (Const (@{const_name "L1_seq"}, _) $ lhs $ rhs) =>
        (case (throws_exception ctxt empty_fail callee_thms lhs, throws_exception ctxt empty_fail callee_thms rhs,
            SOME (empty_fail lhs) handle Utils.InvalidInput _ => NONE) of
            (AlwaysFail lhs_thm, _, _) =>
              AlwaysFail (@{thm L1_seq_alwaysfail_lhs} OF [lhs_thm])
          | (NoThrow lhs_thm, AlwaysFail rhs_thm, SOME ef) =>
              AlwaysFail (@{thm L1_seq_alwaysfail_rhs} OF [ef, lhs_thm, rhs_thm])
          | (NoThrow lhs_thm, AlwaysFail rhs_thm, _) =>
              NoThrow (@{thm L1_seq_nothrow} OF [lhs_thm, fail_to_nothrow rhs_thm])
          | (NoReturn lhs_thm, _, _) =>
              NoReturn (@{thm L1_seq_noreturn_lhs} OF [lhs_thm])
          | (_, NoReturn rhs_thm, _) =>
              NoReturn (@{thm L1_seq_noreturn_rhs} OF [rhs_thm])
          | (NoThrow lhs_thm, NoThrow rhs_thm, _) =>
              NoThrow (@{thm L1_seq_nothrow} OF [lhs_thm, rhs_thm])
          | (_, _, _) =>
              UnknownExc)

    | (Const (@{const_name "L1_catch"}, _) $ lhs $ rhs) =>
        (case (throws_exception ctxt empty_fail callee_thms lhs, throws_exception ctxt empty_fail callee_thms rhs,
            SOME (empty_fail lhs) handle Utils.InvalidInput _ => NONE) of
            (AlwaysFail lhs_thm, _, _) =>
              AlwaysFail (@{thm L1_catch_alwaysfail_lhs} OF [lhs_thm])
          | (NoReturn lhs_thm, AlwaysFail rhs_thm, SOME ef) =>
              AlwaysFail (@{thm L1_catch_alwaysfail_rhs} OF [ef, lhs_thm, rhs_thm])
          | (NoReturn lhs_thm, AlwaysFail rhs_thm, _) =>
              NoReturn (@{thm L1_catch_noreturn} OF [lhs_thm, fail_to_noreturn rhs_thm])
          | (NoReturn lhs_thm, NoReturn rhs_thm, _) =>
              NoReturn (@{thm L1_catch_noreturn} OF [lhs_thm, rhs_thm])
          | (NoThrow lhs_thm, _, _) =>
              NoThrow (@{thm L1_catch_nothrow_lhs} OF [lhs_thm])
          | (_, NoThrow rhs_thm, _) =>
              NoThrow (@{thm L1_catch_nothrow_rhs} OF [rhs_thm])
          | (_, _, _) =>
              UnknownExc)
    | other =>
       let
         val {init, c, ...} = with_fresh_stack_ptr.match ctxt other
         val Abs (p, pT, bdy) = c
       in
         case throws_exception ctxt empty_fail callee_thms bdy of
           NoThrow bdy_thm => 
               NoThrow (hd (Named_Theorems.get ctxt @{named_theorems no_throw_with_fresh_stack_ptr} |> Utils.OFs [bdy_thm]))
         | NoReturn bdy_thm => 
               NoReturn (hd (Named_Theorems.get ctxt @{named_theorems no_return_with_fresh_stack_ptr} |> Utils.OFs [bdy_thm]))
         | _ => UnknownExc
 
       end handle Match =>  UnknownExc
val throws_exception = (fn ctxt => fn empty_fail => fn callee_thms => 
       exn_cache @{binding "L1 exception rewrite: throws_exception"} (throws_exception ctxt empty_fail callee_thms)) 


(*
 * Simprocs.
 *)

(*
 * L1_condition simplification procedure.
 *
 * Most conversions to non-exception form are trivial rewrites. The one exception
 * is "L1_condition", which _does_ have a simple conversion which causes exponential
 * blow-up in code size in the worst case.
 *
 * We hence use this complex simproc to determine if we are in a safe situation or not.
 * If so, we perform the rewrite. Otherwise, we just leave the exceptions in place.
 *)
fun l1_condition_simproc throws_exception redex =
let
  val result = 
  case Thm.term_of redex of
      (Const (@{const_name "L1_catch"}, _)
          $ (Const (@{const_name "L1_seq"}, _)
            $ (Const (@{const_name "L1_condition"}, _) $ _ $ cond_lhs $ cond_rhs)
            $ seq_rhs)
        $ exc) =>
      let
        
        val cond_lhs_res = throws_exception cond_lhs
        val cond_rhs_res = throws_exception cond_rhs
        val exc_res = throws_exception exc
        val seq_rhs_is_short = case seq_rhs of
            (Const (@{const_name "L1_skip"}, _)) => true
          | (Const (@{const_name "L1_throw"}, _)) => true
          | (Const (@{const_name "L1_fail"}, _)) => true
          | _ => false
      in
        case (cond_lhs_res, cond_rhs_res, exc_res, seq_rhs_is_short) of
            (NoThrow l, NoThrow r, _, _) =>
              SOME (@{thm L1_catch_seq_cond_nothrow} OF [l, r])
          | (NoThrow l, AlwaysFail r, _, _) =>
              SOME (@{thm L1_catch_seq_cond_nothrow} OF [l, fail_to_nothrow r])
          | (AlwaysFail l, NoThrow r, _, _) =>
              SOME (@{thm L1_catch_seq_cond_nothrow} OF [fail_to_nothrow l, r])
          | (AlwaysFail l, AlwaysFail r, _, _) =>
              SOME (@{thm L1_catch_seq_cond_nothrow} OF [fail_to_nothrow l, fail_to_nothrow r])

          (* L1_catch_cond_seq can cause exponential blowup: the
           * following cases are safe, because one side will always
           * cause "seq_rhs" to be stripped away. *)
          | (NoReturn _, _, _, _) =>
              SOME (@{thm L1_catch_cond_seq})
          | (_, NoReturn _, _, _) =>
              SOME (@{thm L1_catch_cond_seq})
          | (AlwaysFail _, _, _, _) =>
              SOME (@{thm L1_catch_cond_seq})
          | (_, AlwaysFail _, _, _) =>
              SOME (@{thm L1_catch_cond_seq})

          (* Only duplicating something tiny. *)
          | (_, _, _, true) =>
              SOME (@{thm L1_catch_cond_seq})

          (* The exception handler doesn't return. *)
          | (_, _, NoReturn thm, _) =>
              SOME (@{thm L1_catch_seq_cond_noreturn_ex} OF [thm])
          | (_, _, AlwaysFail thm, _) =>
              SOME (@{thm L1_catch_seq_cond_noreturn_ex} OF [fail_to_noreturn thm])

          (* May cause duplication of "rhs_seq" which we don't want,
           * so we don't optimise in this case. *)
          | _ => NONE
      end
    | _ => NONE
in
  result
end
fun nothrow_simproc throws_exception redex =
  case Thm.term_of redex of
      (Const (@{const_name "no_throw"}, _)
          $ Abs (_, _, Const (@{const_name True}, _))
          $ body) =>
        (case throws_exception body of
            NoThrow thm => SOME thm
          | AlwaysFail thm => SOME (fail_to_nothrow thm)
          | _ => NONE)
    | _ => NONE

fun noreturn_simproc throws_exception redex =
  case Thm.term_of redex of
      (Const (@{const_name "no_return"}, _)
          $ Abs (_, _, Const (@{const_name True}, _))
          $ body) =>
        (case throws_exception body of
            NoReturn thm => SOME thm
          | AlwaysFail thm => SOME (fail_to_noreturn thm)
          | _ => NONE)
    | _ => NONE

fun alwaysfail_simproc throws_exception redex =
  case Thm.term_of redex of
      (Const (@{const_name "always_fail"}, _)
          $ Abs (_, _, Const (@{const_name True}, _))
          $ body) =>
        (case throws_exception body of
            AlwaysFail thm => SOME thm
          | _ => NONE)
    | _ => NONE

fun always_progress_simproc empty_fail redex =
  case Thm.term_of redex of
      (Const (@{const_name "always_progress"}, _)
          $ body) =>
        ((SOME (empty_fail body)) handle Utils.InvalidInput _ => NONE)
    | _ => NONE

(* FIXME: make proper setup without term strings *)
fun simprocs ctxt callee_thms =
let
  fun wrapper proc =
    fn ctxt => fn x =>
      proc x
      |> Option.map (fn thm => Raw_Simplifier.mksimps ctxt thm |> hd)
  (* create fresh caches *)
  val always_progress = always_progress ()
  val throws_exception = throws_exception ctxt always_progress callee_thms
in
  map (Utils.mk_simproc' @{context}) [
    ("l1_condition_simproc",
        ["L1_catch (L1_seq (L1_condition ?c ?L ?R) ?X) ?E"],
        wrapper (l1_condition_simproc throws_exception)),
    ("nothrow_simproc", ["no_throw (%_. True) ?X"], wrapper (nothrow_simproc throws_exception)),
    ("noreturn_simproc", ["no_return (%_. True) ?X"], wrapper (noreturn_simproc throws_exception)),
    ("alwaysfail_simproc", ["always_fail (%_. True) ?X"], wrapper (alwaysfail_simproc throws_exception)),
    ("always_progress_simproc", ["always_progress ?X"], wrapper (always_progress_simproc always_progress))
  ]
end

local
  val forbidden_fields = [NameGeneration.global_rcd_name, NameGeneration.global_exn_var]
  fun no_suffix n s = not (is_some (try (unsuffix s) n))
  fun is_local n = 
    forall (no_suffix n) forbidden_fields andalso
    not (NameGeneration.is_return_or_tmp (MString.mk (Long_Name.base_name n)))
in
(* Simproc to merge assignments to same local variable *)


val l1_merge_assignments_simproc =
 Utils.mk_simproc' @{context} ("l1_merge_assignment_simproc", 
  ["L1_seq (L1_modify ?f) (L1_seq (L1_modify ?g) X)"], fn ctxt => fn cterm =>
    (* Optimize C-ideom to initialise a struct via consecutive assignments to its components.
     * We merge assignments to same local variable by l1_merge_assignments_simproc and then
     * record simprocs will take care to simplify a sequence of updates to structured values to a 
     * constructor. This eliminates the dependency of an the unitialized initial value.
     *)
  case Thm.term_of cterm of 
   (seq as Const (@{const_name "L1_seq"}, sT)) $ (mod1 as (Const (@{const_name "L1_modify"}, _) $ f)) $
    (Const (@{const_name "L1_seq"}, _) $ (mod2 as (Const (@{const_name "L1_modify"}, _) $ g)) $ _) =>
    let
       (* Heuristic to decide whether to merge the assignments (and not mess up L2 phase):
          - only assignments to same local variables
          - exclude return-variables
          - exclude array updates
         A precise analysis would only merge assignments if they sum up to a complete
         struct initialisation.
       *)
       fun is_array_update (Const (@{const_name \<open>Arrays.update\<close>}, _)) = true
         | is_array_update _ = false

       fun get_loc n value = if is_local n andalso not (Term.exists_subterm is_array_update value) then SOME n else NONE

       fun get_upd (Abs (_,_,upd)) = upd
         | get_upd upd = upd

       fun get_loc_var t = case HPInter.dest_local_var_update (get_upd t) of
               SOME (Const (n,_), _, value, _) => get_loc n value
             | NONE => NONE

      val l1 = get_loc_var f
      val l2 = get_loc_var g
    in
      if is_some l1 andalso l1 = l2 then
        let
          val record_ss = merge_ss (RecursiveRecordPackage.get_simpset (Proof_Context.theory_of ctxt), 
                  Record.get_simpset (Proof_Context.theory_of ctxt))
          val state_simprocs = @{code_simprocs "state_simp"}
          val ([stmt], ctxt') = Variable.add_fixes (map fst (Term.variant_frees (Thm.term_of cterm) [("stmt",())])) ctxt;
          val [thm] = Thm.cterm_of ctxt' (seq $ mod1 $ (seq $ mod2 $ Free (stmt, domain_type sT))) 
                |> Simplifier.rewrite (put_simpset record_ss ctxt'
                    addsimps @{thms L1_merge_assignments Fun.comp_def state_simp} 
                    addsimprocs ([Record.simproc, Record.upd_simproc] @ state_simprocs))
                |> single
                |> Variable.export ctxt' ctxt;
         in SOME thm end
      else
        NONE
    end
  | _ => NONE
)
end

(* Exception rewrite conversion / simplification. *)
fun except_rewrite_cache_ctxt ctxt thms =
      put_simpset HOL_basic_ss (Context_Position.set_visible false ctxt)
          addsimps thms
          addsimps (Utils.get_rules ctxt @{named_theorems L1except})
          addsimps (Utils.get_rules ctxt @{named_theorems L1opt})
          addsimprocs (simprocs ctxt thms@[l1_merge_assignments_simproc, Record.simproc, StateFun.lookup_simproc])

fun except_rewrite_cache_conv cache_ctxt =
    Simplifier.asm_full_rewrite cache_ctxt then_conv 
    Utils.eta_conv cache_ctxt

fun except_rewrite_conv ctxt thms =
    Simplifier.asm_full_rewrite (except_rewrite_cache_ctxt ctxt thms) then_conv 
    Utils.eta_conv ctxt




end
