(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

infix 1 THEN_CTXT THEN_CTXT' THEN_MAYBE_CTXT THEN_MAYBE_CTXT' THEN_ALL_NEW_CTXT 
        THEN_MAYBE_ALL_NEW_CTXT THEN_MAYBE_SOLVE_ABORT_ALL_NEW_CTXT;
infix 0 ORELSE_CTXT ORELSE_CTXT' SOLVED_ORELSE_CTXT' SOLVED_ABORT_ORELSE_CTXT' APPEND_CTXT APPEND_CTXT';
infix 0 THEN_ELSE_CTXT THEN_ELSE_CTXT'

signature BASIC_INFIX_CONTEXT_TACTIC =
sig

  val THEN_CTXT: context_tactic * context_tactic -> context_tactic
  val THEN_MAYBE_CTXT: context_tactic * context_tactic -> context_tactic
  val ORELSE_CTXT: context_tactic * context_tactic -> context_tactic
  val APPEND_CTXT: context_tactic * context_tactic -> context_tactic
  val THEN_ELSE_CTXT: context_tactic * (context_tactic * context_tactic) -> context_tactic

  val THEN_CTXT': (int -> context_tactic) * (int -> context_tactic) -> (int -> context_tactic)
  val THEN_MAYBE_CTXT': (int -> context_tactic) * (int -> context_tactic) -> (int -> context_tactic)
  val ORELSE_CTXT': (int -> context_tactic) * (int -> context_tactic) -> (int -> context_tactic)
  val SOLVED_ORELSE_CTXT': ((int -> context_tactic) * (Proof.context -> Proof.context -> Proof.context)) * (int -> context_tactic) -> (int -> context_tactic)
  val SOLVED_ABORT_ORELSE_CTXT': ((int -> context_tactic) * (Proof.context -> Proof.context -> Proof.context)) * (int -> context_tactic) -> (int -> context_tactic)
  val APPEND_CTXT': (int -> context_tactic) * (int -> context_tactic) -> (int -> context_tactic)
  val THEN_ELSE_CTXT': (int -> context_tactic) * ((int -> context_tactic) * (int -> context_tactic)) -> int ->  context_tactic
 
  val THEN_ALL_NEW_CTXT: (int -> context_tactic) * (int -> context_tactic) -> int -> context_tactic
  val THEN_MAYBE_ALL_NEW_CTXT: (int -> context_tactic) * (int -> context_tactic) -> int -> context_tactic
  val THEN_MAYBE_SOLVE_ABORT_ALL_NEW_CTXT: (int -> context_tactic) * (int -> context_tactic) -> int -> context_tactic
end

signature INFIX_CONTEXT_TACTIC =
sig
  include BASIC_INFIX_CONTEXT_TACTIC
  val all_tac : context_tactic
  val no_tac : context_tactic
  val print_tac: string -> context_tactic
  val gen_print_tac: (Proof.context -> int) -> (int * int) -> (Proof.context -> string) -> context_tactic
  val verbose_print_tac:(int * int) -> (Proof.context -> string) -> context_tactic
  val print_subgoal_tac: string -> int -> context_tactic
  val gen_print_subgoal_tac: (Proof.context -> int) -> (int * int) -> ((Proof.context * int) -> string) -> int -> context_tactic
  val verbose_print_subgoal_tac: (int * int) -> ((Proof.context * int) -> string) -> int -> context_tactic
end

signature MORE_CONTEXT_TACTIC = 
sig
  include CONTEXT_TACTIC
  include INFIX_CONTEXT_TACTIC
  val WITH_CONTEXT: (Proof.context -> context_tactic) -> context_tactic
  val CONTEXT_TACTIC': (Proof.context -> tactic) -> context_tactic
  val CSUBGOAL: ((cterm * int) -> context_tactic) -> int -> context_tactic
  val SINGLE: context_tactic -> context_state -> context_state option
  val FIRST: context_tactic list -> context_tactic
  val FIRST': (int -> context_tactic) list -> int -> context_tactic
  val SOLVED_FIRST': (Proof.context -> Proof.context -> Proof.context) -> (int -> context_tactic) list -> int -> context_tactic
  val SOLVED_ABORT_FIRST': (Proof.context -> Proof.context -> Proof.context) -> (int -> context_tactic) list -> int -> context_tactic
  val ONLY_SCHEMATIC_GOAL: bool -> (int -> context_tactic) -> int -> context_tactic
  val resolve_tac: thm list -> int -> context_tactic
  val only_schematic_resolve_tac: bool -> thm list -> int -> context_tactic
  val resolve_assm_tac: thm list -> int -> context_tactic
  val resolve_consumes_assm_tac: thm list -> int -> context_tactic
  val only_schematic_resolve_consumes_assm_tac: bool -> thm list -> int -> context_tactic
  val binding_resolve_tac: (binding * thm) list -> (binding * (int -> context_tactic)) list
  val assm_tac: int -> context_tactic
  val compose_tac: (bool * thm * int) -> int -> context_tactic

  type ctxt_cache = {
    lookup: Proof.context -> cterm -> int -> context_tactic, 
    insert: (Timing.timing * int * int) -> thm -> Proof.context -> Proof.context, 
    propagate: Proof.context -> Proof.context -> Proof.context
  }
  val no_cache: ctxt_cache
  val trace_cache: ctxt_cache

  val cache_deepen_tac: (Proof.context -> int) -> ctxt_cache ->
        (cterm -> (binding * (int -> context_tactic)) list) -> int -> context_tactic
  val concat_goal_funs:  (cterm -> 'a list) list -> cterm -> 'a list
end

structure Infix_Context_Tactic: INFIX_CONTEXT_TACTIC =
struct

val all_tac = CONTEXT_TACTIC all_tac
val no_tac = CONTEXT_TACTIC no_tac

val print_tac = fn msg => fn (ctxt, st) => 
  Context_Tactic.CONTEXT_TACTIC (print_tac ctxt msg) (ctxt, st) 

val print_subgoal_tac = fn msg => fn i => fn (ctxt, st) => 
  Context_Tactic.CONTEXT_TACTIC (Utils.print_subgoal_tac msg ctxt i) (ctxt, st) 

(* FIXME: optionally print goals in reverse order, as this is the convention in automated tactics.*)
fun gen_print_tac verbose (short, long) msg (ctxt, st) =
  let
    val level = verbose ctxt
  in 
    if level >= long andalso long >= 0
    then print_tac (msg ctxt) (ctxt, st) 
    else (if level >= short andalso short >= 0 then tracing (msg ctxt) else (); all_tac (ctxt, st))
  end

val verbose_print_tac = gen_print_tac (fn ctxt => Config.get ctxt Utils.verbose)

fun gen_print_subgoal_tac verbose (short, long) msg i (ctxt, st) =
  let
    val level = verbose ctxt
  in 
    if level >= long andalso long >= 0
    then print_subgoal_tac (msg (ctxt, i)) i (ctxt, st) 
    else (if level >= short andalso short >= 0 then tracing (msg (ctxt, i)) else (); all_tac (ctxt, st))
  end

val verbose_print_subgoal_tac = gen_print_subgoal_tac (fn ctxt => Config.get ctxt Utils.verbose)

(*** LCF-style tacticals ***)

(*the tactical THEN performs one tactic followed by another*)
fun (tac1 THEN_CTXT tac2) (ctxt, st) = Seq.maps_results tac2 (tac1 (ctxt, st));
(*The tactical ORELSE uses the first tactic that returns a nonempty sequence.
  Like in LCF, ORELSE commits to either tac1 or tac2 immediately.
  Does not backtrack to tac2 if tac1 was initially chosen. *)
fun (tac1 ORELSE_CTXT tac2) (ctxt, st) =
  (case Seq.pull (tac1 (ctxt, st)) of
    NONE => tac2 (ctxt, st)
  | some => Seq.make (fn () => some));

fun (tac1 THEN_CTXT' tac2) x = tac1 x THEN_CTXT tac2 x;
fun (tac1 ORELSE_CTXT' tac2) x = tac1 x ORELSE_CTXT tac2 x;
(*The tactical APPEND combines the results of two tactics.
  Like ORELSE, but allows backtracking on both tac1 and tac2.
  The tactic tac2 is not applied until needed.*)
fun (tac1 APPEND_CTXT tac2) (ctxt, st) =
  Seq.append (tac1 (ctxt, st)) (Seq.make(fn()=> Seq.pull (tac2 (ctxt,st))));

fun (tac1 APPEND_CTXT' tac2) x = tac1 x APPEND_CTXT tac2 x;


(*Conditional tactic.
        tac1 ORELSE_CTXT tac2 = tac1 THEN_ELSE_CTXT (all_tac, tac2)
        tac1 THEN_CTXT tac2   = tac1 THEN_ELSE_CTXT (tac2, no_tac)
*)
fun (tac THEN_ELSE_CTXT (tac1, tac2)) (ctxt, st) =
  (case Seq.pull (tac (ctxt, st)) of
    NONE => tac2 (ctxt, st)  (*failed; try tactic 2*)
  | some => Seq.maps_results tac1 (Seq.make (fn () => some)));  (*succeeded; use tactic 1*)

fun (tac THEN_ELSE_CTXT' (tac1, tac2)) x = tac x THEN_ELSE_CTXT (tac1 x, tac2 x);

(* Identity in case tac1 is empty result sequence *)
fun (tac1 THEN_MAYBE_CTXT tac2) = tac1 THEN_ELSE_CTXT (tac2, all_tac)
(* Identity in case tac1 is empty result sequence *)
fun (tac1 THEN_MAYBE_CTXT' tac2) = tac1 THEN_ELSE_CTXT' (tac2, K all_tac)

(* Deterministically executes tac1, if sub-goal is unsolved propagates context to tac2 *)
fun ((tac1, propagate) SOLVED_ORELSE_CTXT' tac2) i (ctxt, st)  =
  (case Seq.pull (Seq.filter_results (tac1 i (ctxt, st))) of
     NONE => tac2 i (ctxt, st)
   | SOME ((ctxt', st'), _) => if Thm.nprems_of st' < Thm.nprems_of st then all_tac (propagate ctxt' ctxt, st') else tac2 i (propagate ctxt' ctxt, st))

fun aborted i st =
  try (Utils.concl_of_subgoal_open o curry Logic.nth_prem i o Thm.prop_of) st = SOME @{term "PROP FALSE"}

fun unsolved i st =
  is_some (try (curry Logic.nth_prem i o Thm.prop_of) st) 

fun aborted_result i (Seq.Result (_, st)) = aborted i st
  | aborted_result _ _ = false

fun unsolved_result i (Seq.Result (ctxt, st)) = if unsolved i st then SOME (ctxt, st) else NONE
  | unsolved_result _ _ = NONE

fun ((tac1, propagate) SOLVED_ABORT_ORELSE_CTXT' tac2) i (ctxt, st)  =
  (case Seq.pull (Seq.filter_results (tac1 i (ctxt, st))) of
     NONE => tac2 i (ctxt, st)
   | SOME ((ctxt', st'), _) => 
         if Thm.nprems_of st' < Thm.nprems_of st then
              all_tac (ctxt', st') 
         else 
           if Thm.nprems_of st' = Thm.nprems_of st andalso aborted i st' then 
                verbose_print_subgoal_tac (4, 6) (fn _ => "SOLVED_ABORT_ORELSE_CTXT' unsolved subgoal " ^ string_of_int i) i 
                 (ctxt', st') \<comment> \<open>sic: subgoal i = @{term "PROP FALSE"}\<close>
           else
             tac2 i (propagate ctxt' ctxt, st))

fun INTERVAL_RESULT f (i: int) j cst =
  if i > j then all_tac cst
  else Seq.maps_results (INTERVAL_RESULT f i (j - 1)) (f j cst);


fun INTERVAL_SOLVE_ABORT_RESULT f (i: int) j cst =
  if i > j then all_tac cst
  else
    case Seq.pull (f j cst) of
      NONE => Seq.make (fn () => NONE)
    | SOME (rcst, rcst') =>
        if aborted_result j rcst then verbose_print_tac (4, ~1) (fn _ => "INTERVAL_SOLVE_ABORT_RESULT aborted subgoal " ^ string_of_int j) cst
        else (case unsolved_result j rcst of
               SOME cst => verbose_print_subgoal_tac (4, 6) (fn _ => "INTERVAL_SOLVE_ABORT_RESULT unsolved subgoal " ^ string_of_int j) j cst
              | NONE => Seq.maps_results (INTERVAL_SOLVE_ABORT_RESULT f i (j - 1)) 
                          (Seq.make (fn () => SOME (rcst, rcst'))))

(*Apply second tactic to all subgoals emerging from the first --
  following usual convention for subgoal-based tactics.*)
fun (tac1 THEN_ALL_NEW_CTXT tac2) i (ctxt, st) =
  (ctxt, st) |> (tac1 i THEN_CTXT (fn (ctxt', st') =>
    (ctxt', st') |> INTERVAL_RESULT tac2 i (i + Thm.nprems_of st' - Thm.nprems_of st)));

(* Identity in case tac1 is empty result sequence *)
fun (tac1 THEN_MAYBE_ALL_NEW_CTXT tac2) i (ctxt, st) =
  (ctxt, st) |> (tac1 i THEN_MAYBE_CTXT (fn (ctxt', st') =>
    (ctxt', st') |> INTERVAL_RESULT tac2 i (i + Thm.nprems_of st' - Thm.nprems_of st)));

(* Identity in case tac1 is empty result sequence, potentially aborting tac2 *)
fun (tac1 THEN_MAYBE_SOLVE_ABORT_ALL_NEW_CTXT tac2) i (ctxt, st) =
  (ctxt, st) |> (tac1 i THEN_MAYBE_CTXT (fn (ctxt', st') =>
    (ctxt', st') |> INTERVAL_SOLVE_ABORT_RESULT tac2 i (i + Thm.nprems_of st' - Thm.nprems_of st)));

end

structure CT: MORE_CONTEXT_TACTIC =
struct
open Context_Tactic
open Infix_Context_Tactic

fun WITH_CONTEXT ctxt_tac (ctxt, st) = ctxt_tac ctxt (ctxt, st)

fun CONTEXT_TACTIC' tac : context_tactic =
  fn (ctxt, st) => TACTIC_CONTEXT ctxt (tac ctxt st);
                           
fun CSUBGOAL goalfun i (ctxt, st) =
  (case SOME (Thm.cprem_of st i) handle THM _ => NONE of
    SOME goal => goalfun (goal, i) (ctxt, st)
  | NONE => Seq.empty);


fun ONLY_SCHEMATIC_GOAL false tac = tac
  | ONLY_SCHEMATIC_GOAL true tac =  
      CSUBGOAL (fn (g, i) =>
        if is_schematic (Thm.term_of g) then tac i  else no_tac ) 
  
val resolve_tac = fn thms => fn i => fn (ctxt, st) => 
  Context_Tactic.CONTEXT_TACTIC (resolve_tac ctxt thms i) (ctxt, st)

fun only_schematic_resolve_tac flag thms = ONLY_SCHEMATIC_GOAL flag (resolve_tac thms)

val resolve_assm_tac = fn thms => fn i => fn (ctxt, st) => 
  Context_Tactic.CONTEXT_TACTIC (Utils.resolve_assm_tac ctxt thms i) (ctxt, st)

val resolve_consumes_assm_tac = fn thms => fn i => fn (ctxt, st) => 
  Context_Tactic.CONTEXT_TACTIC (Utils.resolve_consumes_assm_tac ctxt thms i) (ctxt, st)

fun only_schematic_resolve_consumes_assm_tac flag thms = ONLY_SCHEMATIC_GOAL flag (resolve_consumes_assm_tac thms)

val binding_resolve_tac = map (apsnd (resolve_tac o single))

val assm_tac = fn i => fn (ctxt, st) => 
  Context_Tactic.CONTEXT_TACTIC (Method.assm_tac ctxt  i) (ctxt, st) 

val compose_tac = fn args => fn i => fn (ctxt, st) => 
  Context_Tactic.CONTEXT_TACTIC (compose_tac ctxt args i) (ctxt, st) 

(*Inverse (more or less) of PRIMITIVE*)
fun SINGLE tacf = Option.map fst o Seq.pull o Seq.filter_results o tacf

(* FIRST [tac1,...,tacn]   equals    tac1 ORELSE_CTXT ... ORELSE_CTXT tacn   *)
fun FIRST tacs = fold_rev (curry op ORELSE_CTXT) tacs no_tac;

(* FIRST' [tac1,...,tacn] i  equals    tac1 i ORELSE_CTXT ... ORELSE_CTXT tacn i   *)
fun FIRST' tacs = fold_rev (curry op ORELSE_CTXT') tacs (K no_tac);

(* SOLVED_FIRST' [tac1,...,tacn] i, for n \<ge> 2 equals (tac1 i, propagate) SOLVED_ORELSE_CTXT ... SOLVED_ORELSE_CTXT tacn i 
   Special cases: 
   - Identity if all tacs fail or tacs = [];  
   - tac if tacs = [tac]
   - tacn (potentially unsolved) if all all tacs failed to solve the goal
*)
fun SOLVED_FIRST' propagate tacs = 
  case tacs of [] => K all_tac
    | [tac] => tac
    | _ => foldr1 (fn (tac1, tac2) =>  (tac1, propagate) SOLVED_ORELSE_CTXT' tac2) tacs;

fun SOLVED_ABORT_FIRST' propagate tacs = 
  case tacs of [] => K all_tac
    | [tac] => tac
    | _ => foldr1 (fn (tac1, tac2) =>  (tac1, propagate) SOLVED_ABORT_ORELSE_CTXT' tac2) tacs;



fun subgoal_prove ctxt goal ctxt_tac =
  let
    val st = Goal.init goal
  in
    case SINGLE ctxt_tac (ctxt, st) of 
      NONE => (warning ("subgoal_prove: empty result sequence (context not propagated).\n To propagate result leave an unfinished goal instead: " ^ Syntax.string_of_term ctxt (Thm.term_of goal)); 
              (ctxt,  Goal.conclude st, 1))
    | SOME (ctxt', st') => let val n = Thm.nprems_of st'; val st' = Goal.conclude st' in (ctxt', st', n) end
  end

type ctxt_cache = {
  lookup: Proof.context -> cterm -> int -> context_tactic,
  insert: (Timing.timing * int * int) -> thm -> Proof.context -> Proof.context, 
  propagate: Proof.context -> Proof.context -> Proof.context
}

val no_cache:ctxt_cache = {lookup = K (K (K no_tac)), insert = K (K I), propagate = fn current => fn old => current}
val trace_cache:ctxt_cache = {
  lookup = fn ctxt => fn goal => (tracing ("lookup: " ^ Syntax.string_of_term ctxt (Thm.term_of goal)); K no_tac),
  insert = fn timing => fn thm => fn ctxt => 
    let
      val thm' = thm |> Thm.forall_elim_vars ((Thm.maxidx_of thm) + 1) |> zero_var_indexes
      val _ = tracing ("insert: " ^ Thm.string_of_thm ctxt thm')
    in
      ctxt
    end,
  propagate = fn current => fn old => current
}

local
fun matcher context ps os =
  let
    val thy = Context.theory_of context
  in
    if length ps <> length os then NONE
    else try (fold (Pattern.match thy) (ps ~~ os)) (Vartab.empty, Vartab.empty) |> Option.map (fn (tyenv, tenv) => 
           Envir.Envir {maxidx = ~1, tenv = tenv, tyenv = tyenv})
  end
in
\<comment> \<open>See also @{ML Proof_Display.pretty_goal_inst}\<close>
fun pretty_insts ctxt open_goals solved_concls =
  if null open_goals then [] else
  let
    val title = "goal instantiation:";
    val goals' = (map Thm.term_of open_goals)
    fun prt_inst env =
      if Envir.is_empty env then []
      else
        let
          val Envir.Envir {tyenv, tenv, ...} = env;

          val prt_type = Syntax.pretty_typ ctxt;
          val prt_term = Syntax.pretty_term ctxt;

          fun instT v =
            let
              val T = TVar v;
              val T' = Envir.subst_type tyenv T;
            in if T = T' then NONE else SOME (prt_type T, prt_type T') end;

          fun subst_term_closure t = 
            let val t' = Envir.subst_term (tyenv, tenv) (Envir.subst_term_types tyenv t)
            in if t aconv t' then t else subst_term_closure t' end

          fun inst v =
            let
              val t = Var v;
              val t' = subst_term_closure t

            in if t aconv t' then NONE else SOME (prt_term t, prt_term t') end;

          fun inst_pair (x, y) = Pretty.item [x, Pretty.str " \<leadsto>", Pretty.brk 1, y];

          val prts =
            (Term.add_tvars (hd goals') [] |> sort Term_Ord.tvar_ord |> map_filter instT) @
            (Term.add_vars (hd goals') [] |> sort Term_Ord.var_ord |> map_filter inst);
        in if null prts then [] else [Pretty.big_list title (map inst_pair prts)] end;

     fun no_new_vars (goal, solved) = 
       subset (op =) (Term.add_tvars solved [], (Term.add_tvars goal [])) andalso
       subset (op =) (Term.add_vars solved [], (Term.add_vars goal []))

     (* avoid stutter steps that matching probably has trouble with *)
     val (goals1, solved_concls1) = split_list (filter_out (no_new_vars) (goals' ~~ solved_concls)) 
     fun goal_matcher () =
          matcher (Context.Proof ctxt) goals1 solved_concls1

    fun failure msg = (warning (title ^ " " ^ msg);
          []);
  in 
    (case goal_matcher () of
      SOME env => prt_inst env
    | NONE => failure "match failed")
  end
end

\<comment> \<open> Recursively deepening into goal by applying get_step_tacs on each depth level
   - backtracking by depth first exploration of alternatives returned by get_step_tacs, level by level
   - caching of subgoals: positive and negative attempts
     - negative attempts are modelled as instances of @{thm ex_falso_quodlibet}
     - on negative cache hit search is aborted, no retry to prove subgoal! So be sure
       to only add those subgoals to the negative cache where you do not attempt to try
       an alternative proof.
     - @{prop "PROP FALSE"} is considered an internal artefact, resulting from a negative cache hit.
       They are not supposed to pop up at the top-level.
   - unsolved subgoals might remain

   NB on implementation: To propagate the cache even through 'failed' tactics, 
   internal tactic failure is not represented as empty result sequence, but by leaving the last state
   unchanged, aka: 'all_tac' instead of 'no_tac'. 
   Hence the cache on that last state can still be accessed and propagated. Moreover,
   in case there is no other way to solve the subgoal it remains as leftover subgoal and can be
   inspected for debugging. This non-standard use of 'tactics' does not hold for the
   tactics provided by get_step_tacs! As usual they should still fail with an empty result sequence. 
   Otherwise it is quite likely that we enter a loop.
\<close>
fun gen_cache_deepen_tac (depth, alt, total, path, goals, concls) verbose (cache: ctxt_cache) get_step_tacs i = 
  i |> CSUBGOAL (fn (goal, i) => fn (ctxt, st) => 
  let
    fun compose_subgoal n thms = FIRST' (map (fn thm => compose_tac (false, thm, n)) thms)  

    val nprems = Thm.nprems_of st
    val concl = Logic.unprotect (Thm.concl_of st)
    fun trace_inst more_goals more_concls =
      if null goals then () else
        Utils.verbose_msg 3 ctxt (fn _ => Pretty.string_of (Pretty.paragraph 
            (pretty_insts ctxt (goals @ more_goals) (drop 1 concls @ more_concls))))
    fun msg_common alt total = fn _ => "cache_deepen_tac (depth " ^ string_of_int depth ^ 
         ", subgoals " ^ string_of_int nprems ^
         ", tactic " ^ string_of_int alt ^ " of " ^ string_of_int total ^
         ", path " ^ @{make_string} path ^ 
          ")"
    fun subgoal_msg alt total str i = fn _ => msg_common alt total () ^ "\n " ^ str ^ " " ^ string_of_int i

    fun trace_inst_tac more_goals more_concls = (fn st => (trace_inst more_goals more_concls; all_tac st))

    fun trace_inst_after_tac goal st_open st_solved st =
      let
         val concl_solved = Thm.concl_of st_solved
         val concl_orig = Logic.unprotect (Thm.concl_of st_open)
      in trace_inst_tac [goal] [concl_orig, concl_solved] st end
   
    fun cached_goal goal i (ctxt, st) =
      let
        val cache_tac = #lookup cache ctxt goal
      in                   
        (ctxt, st) |> (
          cache_tac i THEN_ELSE_CTXT 
            (gen_print_tac verbose (1, ~1) (subgoal_msg alt total "cache hit on subgoal:" i),
             gen_print_tac verbose (3, ~1) (subgoal_msg alt total "cache miss on subgoal:" i)))
      end

    fun new_goal goal total (alt, (b, tac)) i (ctxt, st) =
      let
        val alt = alt + 1; (* count from 1 instead of 0 *)
        fun trace_tac b tac = tac THEN_ELSE_CTXT'
          (fn i => gen_print_tac verbose (1, ~1) (subgoal_msg alt total ("tactic " ^ More_Binding.here b ^ " applied to subgoal:") i),
           fn i => gen_print_tac verbose (3, ~1) (subgoal_msg alt total ("tactic " ^ More_Binding.here b ^ " failed on subgoal:") i) THEN_CTXT no_tac)

        val (timing, (ctxt', st', nsubgoals)) = Timing.timing (subgoal_prove ctxt goal) (1 |> (
          trace_tac b tac THEN_MAYBE_SOLVE_ABORT_ALL_NEW_CTXT (gen_cache_deepen_tac (depth + 1, alt, total, path @ [alt], goals @ [goal], concls @ [concl]) verbose cache get_step_tacs )))

        val subgoal_was_solved = nsubgoals = 0       
        fun compose_print_subgoal l str =
          compose_subgoal nsubgoals [st'] i THEN_CTXT 
          gen_print_tac verbose (l, ~1) (subgoal_msg alt total str i) THEN_CTXT
          (if subgoal_was_solved then trace_inst_after_tac goal st st' else all_tac)
      in
        if subgoal_was_solved
        then (#insert cache (timing, total, alt) st' ctxt', st) |> compose_print_subgoal 1 "solved subgoal:"
        else (#insert cache (timing, total, alt) (Thm.instantiate' [] [SOME goal] @{thm ex_falso_quodlibet}) ctxt', st) 
             |> compose_print_subgoal 3 "failed on subgoal:" 
      end
                         
    val fresh_proof = CSUBGOAL (fn (goal, i) =>
       let
         val step_tacs = get_step_tacs goal
         val n = length step_tacs
         val long = if n = 0 then 2 else ~1
       in               
         gen_print_subgoal_tac verbose (2, long) (subgoal_msg alt total (string_of_int n ^  " tactic(s) for subgoal:") i) i THEN_CTXT
         SOLVED_FIRST' (#propagate cache) (map_index (new_goal goal n) step_tacs) i
       end)
  in
    (i, (ctxt, st)) |> uncurry (
      gen_print_subgoal_tac verbose (4, 4) (msg_common alt total) THEN_CTXT' (K (trace_inst_tac [] [concl])) THEN_CTXT' (
        \<comment> \<open>When cache yields @{term "PROP FALSE"} this is the overall result and recursion-level above cleans up.\<close>
      (cached_goal goal, #propagate cache) 
        SOLVED_ABORT_ORELSE_CTXT' 
      fresh_proof))
     
  end)

fun cache_deepen_tac verbose cache get_step_tacs i  =  
  i |> CSUBGOAL (fn (goal, i) =>  gen_cache_deepen_tac (0, ~1, 0, [], [], []) verbose cache get_step_tacs i)

fun concat_goal_funs funs goal = 
  [] |> fold_rev (curry (op @)) (map (rev_app goal) funs)

end



structure Basic_Infix_Context_Tactic: BASIC_INFIX_CONTEXT_TACTIC = Infix_Context_Tactic;
open Basic_Infix_Context_Tactic;