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

type trace_statistics =
  {
    conditional_rules : (Time.time * int) Thm_Name.Table.table,
    rules : int Thm_Name.Table.table,
    steps : int,
    max_steps : int,
    depth : int,
    max_depth : int
  }

structure Data = Proof_Data
( type T = trace_statistics Synchronized.var option
  fun init _ = NONE
)

val trace_data : Proof.context -> trace_statistics Synchronized.var option = Data.get

fun initial n : trace_statistics =
  {
    conditional_rules = Thm_Name.Table.empty,
    rules = Thm_Name.Table.empty,
    steps = 0,
    max_steps = n,
    depth = 0,
    max_depth = 0
  }

fun activate n = Data.put (SOME (Synchronized.var "trace_data" (initial n)))

fun print ({conditional_rules, rules, steps, max_depth, ...} : trace_statistics) =
  let
    val _ = writeln ("=== SIMP STATISTICS (" ^
      string_of_int steps ^ " steps, " ^ string_of_int max_depth ^ " max depth) ===")
    val _ = writeln "Conditional Rules:"
    val _ = conditional_rules |> Thm_Name.Table.dest
      |> sort (make_ord (fn ((_, (t1, _)), (_, (t2, _))) => Time.< (t2, t1)))
      |> app (fn (name, (t, c)) =>
        writeln ("  " ^ Thm_Name.print name ^ ": " ^ Time.toString t ^ " / " ^ string_of_int c ^ " = " ^
          Real.toString (Time.toReal t / Real.fromInt c)))
    val _ = writeln "Rules:"
    val _ = rules |> Thm_Name.Table.dest
      |> sort (make_ord (fn ((_, c1), (_, c2)) => c2 < c1))
      |> app (fn (name, c) => writeln ("  " ^ Thm_Name.print name ^ ": " ^ string_of_int c))
    val _ = writeln ("======")
  in
    ()
  end

fun trace_apply var {unconditional, rrule, thm, ...} ctxt cont =
  let
    val d = Synchronized.value var
    val _ = #max_steps d <= #steps d andalso error ("simp tracer: max steps reaches")
    fun store time = Synchronized.change var (fn
      { conditional_rules, rules, steps, depth, max_steps, max_depth } =>
      {
        conditional_rules = (if unconditional then conditional_rules else
          conditional_rules |>
          Thm_Name.Table.map_default (#name rrule, (Time.zeroTime, 0))
            (fn (t, c) => (Time.+ (t, #cpu time), c + 1))),
        rules = rules |> Thm_Name.Table.map_default (#name rrule, 0) (fn c => c + 1),
        steps = steps + 1,
        max_steps = max_steps,
        depth = depth,
        max_depth = max_depth
      }
    )
  in
    Timing.timing (Exn.capture cont) ctxt
    |> (fn (t, x) => (store t; Exn.release x))
  end

fun map_depth f
  ({ conditional_rules, rules, steps, depth, max_steps, max_depth} : trace_statistics) :
  trace_statistics =
let
  val d = f depth
in
  { conditional_rules = conditional_rules,
    rules = rules,
    steps = steps,
    depth = d,
    max_depth = if max_depth < d then d else max_depth,
    max_steps = max_steps }
end

fun increase_depth var ctxt =
  (Synchronized.change var (map_depth (fn d => d + 1)); ctxt)

val trace_ops : Raw_Simplifier.trace_ops = {
  trace_invoke = fn _ => fn ctxt =>
    (case trace_data ctxt of SOME var => increase_depth var ctxt
      | NONE => ctxt),
  trace_rrule = fn rule => fn ctxt => fn cont =>
    case trace_data ctxt of
      SOME var => trace_apply var rule ctxt cont
    | NONE => cont ctxt,
  trace_simproc = K (K (K NONE))
}

fun wrapper n tac ctxt st =
  let
    val ctxt' = ctxt
      |> activate n
      |> Config.put Raw_Simplifier.simp_trace true
      |> Config.put Raw_Simplifier.simp_trace_depth_limit 4
    val res = Exn.capture (fn () => (tac ctxt' st |> Seq.pull)) ()
    val _ = print (Synchronized.value (the (trace_data ctxt')))
  in
    case Exn.release res of
      SOME (x, _) => Seq.cons x (Seq.make (fn () =>
        error ("stat simp tracer does not allow back" ^ Position.here \<^here>)))
    | NONE => Seq.empty
  end

fun wrapper' n tac ctxt = wrapper n (fn ctxt => tac ctxt 1) ctxt

fun wrapper_method method ctxt' (_, thm) =
  method (ctxt', thm)

fun method_wrapper (n : int option) (m : Proof.context -> Method.method) ctxt : Method.method =
  fn thms => Method.RUNTIME
    (wrapper (the_default 1000 n) (fn ctxt => wrapper_method (m ctxt thms) ctxt) ctxt)

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

val wrapper : (Proof.context -> Method.method) context_parser =
  (Scan.lift (Scan.option (Args.parens Parse.nat)) -- Method.text_closure)
  >> (fn (n, text) => method_wrapper n (fn ctxt => Method.evaluate_runtime text ctxt))

fun simpT_method meth =
  Scan.lift simp_options --|
    Method.sections Simplifier.simp_modifiers' >>
    (fn (n, tac) => method_wrapper n (fn ctxt => METHOD (fn facts => meth ctxt tac facts)))

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
      method_wrapper i (SIMPLE_METHOD o CHANGED_PROP o auto_tac)
    | (i, SOME (m, n)) => 
      method_wrapper i (fn ctxt => SIMPLE_METHOD (CHANGED_PROP (mk_auto_tac ctxt m n))));

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