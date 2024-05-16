(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Code to manage converting between L2_monad and other monad types.
 *
 * TypeStrengthen provides a higher level interface for converting entire programs.
 *)

structure Monad_Convert = struct

(* Utilities. *)
fun intersperse _ [] = []
  | intersperse _ [x] = [x]
  | intersperse a (x::xs) = x :: a :: intersperse a xs

fun theE NONE exc = raise exc
  | theE (SOME x) _ = x

fun oneE [] exc = raise exc
  | oneE (x::_) _ = x



(* From Find_Theorems *)
fun apply_dummies tm =
  let
    val (xs, _) = Term.strip_abs tm;
    val tm' = Term.betapplys (tm, map (Term.dummy_pattern o #2) xs);
  in #1 (Term.replace_dummy_patterns tm' 1) end;

fun parse_pattern ctxt nm =
  let
    val consts = Proof_Context.consts_of ctxt;
    val nm' =
      (case Syntax.parse_term ctxt nm of
        Const (c, _) => c
      | _ => Consts.intern consts nm);
  in
    (case try (Consts.the_abbreviation consts) nm' of
      SOME (_, rhs) => apply_dummies (Proof_Context.expand_abbrevs ctxt rhs)
    | NONE => Proof_Context.read_term_pattern ctxt nm)
  end;

(* Breadth-first term search *)
fun term_search_bf cont pred prune = let
  fun fresh_var vars v = if member (op =) vars v then fresh_var vars (v ^ "'") else v
  fun search ((vars, term), queue) =
    if pred term then cont (vars, term) (fn () => walk queue) else
    if prune term then walk queue else
    case term of
        t as Abs (v, typ, _) =>
            let val v' = fresh_var vars v in
                walk (Queue.enqueue
                          ((v'::vars), betapply (t, Free (v', typ))) queue)
            end
      | f $ x => walk (Queue.enqueue (vars, x) (Queue.enqueue (vars, f) queue))
      | _ => walk queue
  and walk queue = if Queue.is_empty queue then () else search (Queue.dequeue queue)
in
  (fn term => search (([], term), Queue.empty))
end

fun term_search_bf_first pred prune term = let
  val r = Unsynchronized.ref NONE
  val _ = term_search_bf (fn result => K (r := SOME result)) pred prune term
in !r end

(* From Pure/Tools/find_theorems.ML, because Florian made it private *)
fun matches_subterm thy (pat, obj) =
  let
    fun msub bounds obj = Pattern.matches thy (pat, obj) orelse
      (case obj of
        (abs as Abs (_, T, t)) => msub (bounds + 1) (snd (Term.dest_abs_fresh (Name.bound bounds) abs))
      | t $ u => msub bounds t orelse msub bounds u
      | _ => false)
  in msub 0 obj end;

fun grep_term ctxt pattern =
let
  val thy = Proof_Context.theory_of ctxt
in
  term_search_bf_first
      (fn term => Pattern.matches thy (pattern, term))
      (fn term => not (matches_subterm thy (pattern, term)))
end

(* Check whether the term is in L2_monad notation. *)
val term_is_L2 = Monad_Types.check_lifting_head
    [@{term "L2_unknown"}, @{term "L2_seq"}, @{term "L2_modify"},
     @{term "L2_gets"}, @{term "L2_condition"}, @{term "L2_catch"}, @{term "L2_while"},
     @{term "L2_throw"}, @{term "L2_spec"}, @{term "L2_assume"},
     @{term "L2_guard"}, @{term "L2_fail"},
     @{term "L2_call"}]

local
  val case_prod_eta_contract_thm =
      @{lemma "(\<lambda>x. (case_prod s) x) == (case_prod s)" by simp}
 in
  fun case_prod_eta_conv ctxt =
    Conv.bottom_conv (
        K (Conv.try_conv (Conv.rewrs_conv [case_prod_eta_contract_thm]))) ctxt
    then_conv
    Drule.beta_eta_conversion
end

fun unit_fun_rewr_conv ct = 
  case Thm.term_of ct of
    Abs (_, @{typ unit}, f) => 
     Conv.rewr_conv @{thm unit_bind'} ct
   | _ => Conv.no_conv ct

val unit_fun_conv = Conv.bottom_conv (K (Conv.try_conv unit_fun_rewr_conv))


local 

local
  fun strip t = snd (Synthesize_Rules.strip_abs_prod t)
in
fun l2_compound_index ((head as Const (@{const_name "L2_seq"}, _)) $ L $ R) = 
      head $ L $ l2_compound_index (strip R)
  | l2_compound_index ((head as Const (@{const_name "L2_while"}, _)) $ C $ B $ I $ ns) = 
      head $ strip C $ l2_compound_index (strip B) $ I $ ns
  | l2_compound_index ((head as Const (@{const_name "L2_condition"}, _)) $ C $ L $ R) = 
      head $ strip C $ l2_compound_index L $ l2_compound_index R
  | l2_compound_index ((head as Const (@{const_name "L2_try"}, _)) $ B) = 
      head $ l2_compound_index B 
  | l2_compound_index x = x
end

fun l2_index (@{const Trueprop} $ ((sim as Const (@{const_name \<open>refines\<close>}, _)) $ f $ s $ f' $ s' $ R)) =
      @{const Trueprop} $ (sim $ l2_compound_index f $ s $ f' $ s' $ R)
  | l2_index x = x
                                        
fun check_compound _ @{term_pat \<open>Trueprop (refines ?f _ _ _ _)\<close>} =
      (case strip_comb f |> fst of
         @{term_pat "L2_seq"} => true
       | @{term_pat "L2_while"} => true
       | @{term_pat "L2_condition"} => true
       | @{term_pat "L2_try"} => true
       | @{term_pat "L2_guarded"} => true
       | _ => false) 
   | check_compound _ _ = false
    
in
fun sim_nondet ctxt  
     (mt:Monad_Types.monad_type) 
     prev_def goal =
  let
    val mname = #name mt
    val {rules_name, lift_prev, ...} = #refines_nondet mt
    val fun_ptr_simps = 
              Named_Theorems.get ctxt @{named_theorems "global_const_selectors"} @
              Named_Theorems.get ctxt @{named_theorems "fun_ptr_simps"} 

    fun get_concr @{term_pat "refines ?f _ _ _ _"} = f
      | get_concr t = error ("prune_unused_bounds_sim_nondet_tac, unexpected term: " ^ @{make_string} t)

    val THIN_tac = Utils.THIN_tac (Utils.prune_unused_bounds_from_concr_tac get_concr)
    fun dyn_call_tac ctxt = EVERY' [
         K (Utils.verbose_print_tac 4 "sim_nondet_dyncall begin" ctxt), 
         AutoCorresUtil.dyn_call_split_simp_sidecondition_tac (K true) [] [] ctxt,
         K (Utils.verbose_print_tac 4 "sim_nondet_dyncall after split_simp_sidecondition_tac" ctxt)]

    val ctxt' = ctxt 
        |> Context.proof_map 
            (Synthesize_Rules.add_pattern_tac_rule rules_name dyn_call_tac @{binding DYN_CALL} 10 @{pattern \<open>DYN_CALL (PROP ?P)\<close>})
        |> Context.proof_map 
            (Synthesize_Rules.add_pattern_tac_rule rules_name THIN_tac @{binding THIN} 10 @{pattern \<open>THIN (PROP ?P)\<close>}) 

    val _ = Utils.verbose_fn 2 ctxt' (fn _ => Synthesize_Rules.print_rules (Context.Proof ctxt') rules_name NONE)

    val sim_rules = Synthesize_Rules.get_rules ctxt' rules_name |> the
    
    fun lift rules goal thm  = 
      case rules of [] => K CT.no_tac  
       | r::rules' => 
           (case try (fn thm => r OF [thm]) thm of 
              NONE => lift rules' goal thm 
            | SOME thm' =>
                 CT.resolve_tac [thm'] ORELSE_CTXT' (lift rules' goal thm))
 
    val cache = Synthesize_Rules.gen_cond_cache check_compound l2_index (lift lift_prev) sim_rules

    val thm = Goal.prove ctxt' [] [] goal (fn {context, ...} => 
       EqSubst.eqsubst_tac context [0] [prev_def] 1 THEN
       Context_Tactic.NO_CONTEXT_TACTIC context (
         CT.cache_deepen_tac (fn ctxt => Config.get ctxt Utils.verbose) cache
           (Synthesize_Rules.resolve_tacs sim_rules context) 1)
       )

    val _ = Utils.verbose_msg 2 ctxt (fn _ => ("sim_nondet_rewrite (" ^ mname ^ ") thm:\n " ^ 
                                         (Thm.string_of_thm ctxt thm)))
   
  in
    SOME thm
  end
  handle ERROR str => (Utils.verbose_msg 2 ctxt (fn _ => "sim_nondet proof failed:\n " ^ str); NONE) (* proof failed *)
end

(*
 * Apply polish to a theorem of the form:
 *
 *   <LHS> == <lift> $ <some term to polish>
 *
 * Return the new theorem.
 *)

fun polish_arg (arg: conv->conv) ctxt (mt : Monad_Types.monad_type) do_polish pretty_bounds_conv thm =
let
  (* Apply any polishing rules. *)
  val ctxt = Utils.set_hidden_ctxt ctxt
  val simps = if do_polish then Utils.get_rules ctxt @{named_theorems polish} else []
  val congs = if do_polish then Utils.get_rules ctxt @{named_theorems polish_cong} else []
  (* Simplify using polish rules. *)
  val simp_ctxt = put_simpset HOL_ss ctxt addsimps simps addsimprocs [@{simproc NO_MATCH}]
                  |> fold Simplifier.add_cong congs
                  
  val simp_conv = Simplifier.rewrite simp_ctxt


  (* eta-contract "case_prod clauses, so that they render as:
   * "%(a, b). P a b" instead of "case x of (a, b) => P a b". *)

  val ((_, [thm]), ctxt') = Variable.import true [thm] ctxt
 
  val [thm_p] = thm |>
    Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of thm) (arg (
        (unit_fun_conv ctxt) then_conv
        (pretty_bounds_conv ctxt') then_conv
        (unit_fun_conv ctxt) then_force_conv
        (pretty_bounds_conv ctxt') force_then_conv
        simp_conv then_conv
        (case_prod_eta_conv ctxt)
    )))  |> single |> Proof_Context.export ctxt' ctxt
in
  thm_p
end

val polish_refines = polish_arg (fn conv => Conv.arg_conv (Utils.nth_arg_conv 2 conv))
val polish_eq = polish_arg (fn conv => (Conv.arg_conv (Conv.arg_conv conv)))



(*
 * Wrap a tactic that doesn't handle invalid subgoal numbers to return
 * "Seq.empty" when appropriate.
 *)
fun handle_invalid_subgoals (tac : int -> tactic) n =
  fn thm =>
    if Logic.count_prems (term_of_thm thm) < n then
      no_tac thm
    else
      tac n thm

end
