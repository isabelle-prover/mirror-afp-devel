(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Simplifier statistics and easier tracing *)

theory Simp_Trace
  imports AutoCorres_Utils
begin

text \<open>

ATTENTION: to activate these methods use the following line:

  \<open>setup \<open>Raw_Simplifier.set_trace_ops Simp_Trace.trace_ops\<close>\<close>

Provide a tactic wrapper to activate simplifier tracing and produce a statistic how many
conditional rules were tried for how long. Also provides a shorthand for simp trace activation by
adding \<open>T\<close> to the method name: \<open>simpT\<close> \<open>simp_allT\<close> \<open>autoT\<close>

\<close>

ML \<open>

structure Simp_Trace =
struct

type cumulative_statistics = 
  {
    cumulative_time : Time.time,
    calls : int
  }

type call_statistics = 
  { successes : cumulative_statistics, failures : cumulative_statistics }

type trace_statistics =
  {
    conditional_rules : call_statistics Thm_Name.Table.table,
    simprocs : call_statistics Symtab.table,
    rules : int Thm_Name.Table.table,
    steps : int,
    max_steps : int,
    depth : int,
    max_depth : int,
    do_trace : bool,
    in_simproc : bool
  }

structure Data = Proof_Data
( 
  type T = trace_statistics Synchronized.var option
  fun init _ = NONE
)

val trace_data : Proof.context -> trace_statistics Synchronized.var option = Data.get

fun initial n do_trace : trace_statistics =
  {
    conditional_rules = Thm_Name.Table.empty,
    simprocs = Symtab.empty,
    rules = Thm_Name.Table.empty,
    steps = 0,
    max_steps = n,
    depth = 0,
    max_depth = 0,
    do_trace = do_trace,
    in_simproc = false
  }

fun activate n do_trace = Data.put (SOME (Synchronized.var "trace_data" (initial n do_trace)))

fun call_statistics_ord (x, y:('a * call_statistics)) =
  (x, y) |> apply2 (snd #> #failures #> #cumulative_time) |> Time.compare


fun print_cumulative_statistics txt { cumulative_time = t, calls = n} =
  if n = 0 then "no " ^ txt else txt ^ ": " ^ 
  Time.toString t ^ " / " ^ string_of_int n ^ " = " ^
    Real.fmt (StringCvt.FIX (SOME 3)) (Time.toReal t / Real.fromInt n)

fun print ({conditional_rules, rules, simprocs, steps, max_depth, ...} : trace_statistics) =
  let
    val _ = writeln ("=== SIMP STATISTICS (" ^
      string_of_int steps ^ " steps, " ^ string_of_int max_depth ^ " max depth) ===")
    val _ = writeln "Conditional Rules (sorted in failure time):"
    val _ = conditional_rules |> Thm_Name.Table.dest
      |> sort (call_statistics_ord #> rev_order)
      |> app (fn (name, cs) =>
        writeln ("  " ^ Thm_Name.print name ^ ": " ^ print_cumulative_statistics "failures" (#failures cs) ^
          " (" ^ print_cumulative_statistics "successes" (#successes cs) ^ ")"))
    val _ = writeln "Rules:"
    val _ = rules |> Thm_Name.Table.dest
      |> sort (make_ord (fn ((_, c1), (_, c2)) => c2 < c1))
      |> app (fn (name, c) => writeln ("  " ^ Thm_Name.print name ^ ": " ^ string_of_int c))
    val _ = writeln "Simprocs (sorted in failure time):"
    val _ = simprocs |> Symtab.dest
      |> sort (call_statistics_ord #> rev_order)
      |> app (fn (name, cs) =>
        writeln ("  " ^ name ^ ": " ^ print_cumulative_statistics "failures" (#failures cs) ^
          " (" ^ print_cumulative_statistics "successes" (#successes cs) ^ ")"))
    val _ = writeln ("======")
  in
    ()
  end

fun map_success f ({ successes, failures } : call_statistics) : call_statistics = 
  { successes = f successes, failures = failures }

fun map_failure f ({ successes, failures } : call_statistics) : call_statistics = 
  { successes = successes, failures = f failures }

fun incr_cumulative t ({ cumulative_time, calls } : cumulative_statistics) = 
  { cumulative_time = Time.+ (t, cumulative_time), calls = calls + 1 }

fun incr_call success t = 
  (if success then map_success else map_failure) (incr_cumulative t)

val zero_cumulative = { cumulative_time = Time.zeroTime, calls = 0 }

val zero_calls = { successes = zero_cumulative, failures = zero_cumulative }

fun map_depth f
  ({ conditional_rules, simprocs, rules, steps, depth, max_steps, max_depth, do_trace, in_simproc} :
    trace_statistics) :
  trace_statistics =
let
  val d = f depth
in
  { conditional_rules = conditional_rules,
    simprocs = simprocs,
    rules = rules,
    steps = steps,
    depth = d,
    max_depth = if max_depth < d then d else max_depth,
    max_steps = max_steps,
    do_trace = do_trace,
    in_simproc = in_simproc }
end

fun map_in_simproc f
  ({ conditional_rules, simprocs, rules, steps, depth, max_steps, max_depth, do_trace, in_simproc} :
    trace_statistics) :
  trace_statistics =
{ 
  conditional_rules = conditional_rules,
  simprocs = simprocs,
  rules = rules, 
  steps = steps, 
  depth = depth, 
  max_steps = max_steps, 
  max_depth = max_depth, 
  do_trace = do_trace, 
  in_simproc = f in_simproc
}

fun trace_apply var {unconditional, rrule, ...} ctxt cont =
  let
    val d = Synchronized.value var
    val _ = #max_steps d <= #steps d andalso error ("simp trace: max steps reaches")
    fun store success time = Synchronized.change var (fn
      ({ conditional_rules, simprocs, rules, steps, depth, max_steps, max_depth, do_trace,
         in_simproc } : trace_statistics) =>
      {
        conditional_rules = (if unconditional then conditional_rules else
          conditional_rules |>
          Thm_Name.Table.map_default (#name rrule, zero_calls) (incr_call success (#cpu time))),
        simprocs = simprocs,
        rules = rules |> Thm_Name.Table.map_default (#name rrule, 0) (fn c => c + 1),
        steps = steps + 1,
        max_steps = max_steps,
        depth = depth,
        max_depth = max_depth,
        do_trace = do_trace,
        in_simproc = in_simproc
      }
    )
  in
    Timing.timing (Exn.capture cont) ctxt
    |> (fn (t, x) => (store (Exn.is_res x) t; Exn.release x))
  end

fun trace_simproc var name ctxt cont =
  let
    val d = Synchronized.value var
    val _ = #max_steps d <= #steps d andalso error ("simp trace: max steps reaches")
    fun store success time = Synchronized.change var (fn
      ({ conditional_rules, simprocs, rules, steps, depth, max_steps, max_depth, do_trace, in_simproc }  : trace_statistics) =>
      {
        conditional_rules = conditional_rules,
        simprocs = simprocs |>
          Symtab.map_default (name, zero_calls) (incr_call success (#cpu time)),
        rules = rules,
        steps = steps + 1,
        max_steps = max_steps,
        depth = depth,
        max_depth = max_depth,
        do_trace = do_trace,
        in_simproc = false
      }
    )
    fun is_success (Exn.Res (SOME _)) = true
      | is_success _ = false
    fun set_in_simproc f x =
      (Synchronized.change var (map_in_simproc (K f)); x)
  in
    Timing.timing (Exn.capture
      (set_in_simproc true #> cont)) ctxt
    |> (fn (t, x) => (store (is_success x) t; Exn.release x))
  end

fun increase_depth var ctxt =
  (Synchronized.change var (map_depth (fn d => d + 1)); ctxt)

fun check_trace_data ctxt =
  case trace_data ctxt of SOME var => 
    let
      val d = Synchronized.value var
    in
      if #in_simproc d then NONE else SOME var
    end
  | NONE => NONE

val trace_ops : Raw_Simplifier.trace_ops = {
  trace_invoke = fn _ => fn ctxt =>
    (case check_trace_data ctxt of SOME var => increase_depth var ctxt
      | NONE => ctxt),
  trace_rrule = fn rule => fn ctxt => fn cont =>
    case check_trace_data ctxt of
      SOME var => trace_apply var rule ctxt cont
    | NONE => cont ctxt,
  trace_simproc = fn {name, ...} => fn ctxt => fn cont =>
    case check_trace_data ctxt of
      SOME var => trace_simproc var name ctxt cont
    | NONE => cont ctxt
}

fun wrapper n do_trace tac ctxt st =
  let
    val ctxt' = ctxt
      |> activate n do_trace
      |> Config.put Raw_Simplifier.simp_trace do_trace
      |> Config.put Raw_Simplifier.simp_trace_depth_limit 4
    val res = Exn.capture (fn () => (tac ctxt' st |> Seq.pull)) ()
    val _ = print (Synchronized.value (the (trace_data ctxt')))
  in
    case Exn.release res of
      SOME (x, _) => Seq.cons x (Seq.make (fn () =>
        error ("stat simp tracer does not allow back" ^ Position.here \<^here>)))
    | NONE => Seq.empty
  end

fun method_wrapper (n : int option) (do_trace : bool) (m : Proof.context -> Method.method) ctxt : 
  Method.method =
  fn thms => Method.RUNTIME
    (wrapper (the_default 1000 n) do_trace 
      (fn ctxt => fn (_, thm) => m ctxt thms (ctxt, thm)) ctxt)

val no_asmN = "no_asm";
val no_asm_useN = "no_asm_use";
val no_asm_simpN = "no_asm_simp";
val asm_lrN = "asm_lr";

val simp_options =
 (Args.parens (Scan.option Parse.nat -- Args.$$$ no_asmN) >> apsnd (K simp_tac) ||
  Args.parens (Scan.option Parse.nat -- Args.$$$ no_asm_simpN) >> apsnd (K asm_simp_tac) ||
  Args.parens (Scan.option Parse.nat -- Args.$$$ no_asm_useN) >> apsnd (K full_simp_tac) ||
  Args.parens (Scan.option Parse.nat -- Args.$$$ asm_lrN) >> apsnd (K asm_lr_simp_tac) ||
  Args.parens Parse.nat >> (fn n => (SOME n, asm_full_simp_tac)) ||
  Scan.succeed (NONE, asm_full_simp_tac));

val no_traceN = "no_trace";

val wrapper : (Proof.context -> Method.method) context_parser =
  (Scan.lift (
    Args.parens Parse.nat >> (fn n => (SOME n, true)) || 
    Args.parens (Parse.nat -- Args.$$$ no_traceN) >> (fn (n, _) => (SOME n, false)) ||
    Args.parens (Args.$$$ no_traceN) >> (fn _ => (NONE, false)) ||
    Scan.succeed (NONE, true)) -- 
  Method.text_closure)
  >> (fn ((n, do_trace), text) =>
    method_wrapper n do_trace (fn ctxt => Method.evaluate_runtime text ctxt))

fun simpT_method meth =
  Scan.lift simp_options --|
    Method.sections Simplifier.simp_modifiers' >>
    (fn (n, tac) => method_wrapper n true (fn ctxt => METHOD (fn facts => meth ctxt tac facts)))

val simp_wrapper =
  simpT_method (fn ctxt => fn tac => fn facts =>
    HEADGOAL (Method.insert_tac ctxt facts THEN'
      (CHANGED_PROP oo tac) ctxt))

val simp_all_wrapper =
  simpT_method (fn ctxt => fn tac => fn facts =>
    ALLGOALS (Method.insert_tac ctxt facts) THEN
      (CHANGED_PROP o PARALLEL_ALLGOALS o tac) ctxt)

val auto_wrapper =
  (Scan.lift (Scan.option (Args.parens Parse.nat)) -- 
    Scan.lift (Scan.option (Parse.nat -- Parse.nat))) --|
    Method.sections clasimp_modifiers >>
  (fn (i, NONE) => 
      method_wrapper i true (SIMPLE_METHOD o CHANGED_PROP o auto_tac)
    | (i, SOME (m, n)) => 
      method_wrapper i true (fn ctxt => SIMPLE_METHOD (CHANGED_PROP (mk_auto_tac ctxt m n))));

end

\<close>

setup \<open>Method.setup \<^binding>\<open>stat\<close> Simp_Trace.wrapper
  ("Simplifier statisitics: wraps a method call and computes statistics from simplifier calls." ^
   " Needs active Simp_Trace.trace_ops")\<close>

setup \<open>Method.setup \<^binding>\<open>simpT\<close> Simp_Trace.simp_wrapper
  ("simplification with tracing" ^ 
   " Needs active Simp_Trace.trace_ops")\<close>

setup \<open>Method.setup \<^binding>\<open>simp_allT\<close> Simp_Trace.simp_all_wrapper
  ("simplification on all goals with tracing" ^
   " Needs active Simp_Trace.trace_ops")\<close>

setup \<open>Method.setup \<^binding>\<open>autoT\<close> Simp_Trace.auto_wrapper
  ("auto with tracing " ^
   " Needs active Simp_Trace.trace_ops")\<close>

end