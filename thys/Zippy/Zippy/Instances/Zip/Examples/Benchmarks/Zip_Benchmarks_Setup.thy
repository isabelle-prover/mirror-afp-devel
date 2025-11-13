\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Benchmarks for Zip\<close>
theory Zip_Benchmarks_Setup
  imports
    Zippy.Zip_HOL
begin

paragraph \<open>Summary\<close>
text \<open>Setup for Zippy benchmarks.\<close>

text \<open>This file provides wrappings and overrides to benchmark proof-exploration tactics.
It uses Isabelle's export facilities to store benchmark results for each wrapped tactic call.
For identification purposes, the export functionality requires unique positional information for
each tactic invocation. As such, repeating method combinators (";", "+", etc.) are not supported.\<close>

ML\<open>
structure Zip_Benchmark =
struct

val id = "zip_benchmark"

structure Export =
struct
val encode_entry =
  let open XML.Encode
    val time = Time.print
    fun timing_properties {elapsed, cpu, gc} = [
      ("elapsed", time elapsed),
      ("cpu", time cpu),
      ("gc", time gc)]
    val timing = timing_properties #> properties
    val res = variant [fn Either.Left t => ([], time t |> string),
      fn Either.Right opt_res => ([], bool (is_some opt_res))]
  in triple (Binding.name_of #> string) (Position.properties_of #> properties) (pair timing res) end

val decode_entry =
  let open XML.Decode
    val time = Time.parse
    fun timing_properties [("elapsed", te), (_, tc), (_, tg)] =
      {elapsed = time te, cpu = time tc, gc = time tg}
    val timing = properties #> timing_properties
    val res = variant [fn (_, t) => Either.Left (string t |> time),
      fn (_, b) => Either.Right (bool b)]
  in triple (string #> Binding.name) (properties #> Position.of_properties) (pair timing res) end

val benchmark_dir = Path.basic id

fun export ctxt pos =
  let val path = Position.offset_of pos |> the |> string_of_int |> Path.basic
    |> Path.append benchmark_dir |> Path.binding0
  in encode_entry #> Export.export (Proof_Context.theory_of ctxt) path end

local fun append_dir_file_paths dir = File.read_dir dir |> map (Path.basic #> Path.append dir)
in
val mk_xml = AList.make (File.read #> YXML.parse_body #> decode_entry)
val mk_calls = AList.make (fn dir => Path.append dir benchmark_dir |> append_dir_file_paths |> mk_xml)
val mk_thys = AList.make (append_dir_file_paths #> mk_calls)
val mk_runs = AList.make (append_dir_file_paths #> mk_thys)
fun mk_export export_dir = (export_dir, append_dir_file_paths export_dir |> mk_runs)
end
end

fun parse method = let val parse_fuel = Parse_Util.option Parse.nat
  in
    Parse_Util.position' (Scan.lift (Scan.option (Parse.nat -- Parse.nat)) (*for auto*)
    -- Scan.lift parse_fuel (*for zippy*)
    --| Zip.Context_Parsers.parse) (*for all*)
    >> (fn (args, pos) => method args pos)
  end
fun setup_method method descr binding = Method.local_setup binding (parse method) descr

fun all_existing_tac opt_fuel ctxt = let val HEADGOAL_SOLVED = HEADGOAL o SOLVED'
  in if is_none opt_fuel
    then PARALLEL_GOALS (DEPTH_FIRST Thm.no_prems (PARALLEL_CHOICE [
      SOLVE (auto_tac ctxt),
      HEADGOAL_SOLVED (SELECT_GOAL (auto_tac ctxt)),
      HEADGOAL_SOLVED (force_tac ctxt),
      HEADGOAL_SOLVED (fast_force_tac ctxt),
      HEADGOAL_SOLVED (slow_simp_tac ctxt),
      HEADGOAL_SOLVED (best_simp_tac ctxt),
      HEADGOAL_SOLVED (fast_tac ctxt),
      HEADGOAL_SOLVED (slow_tac ctxt),
      HEADGOAL_SOLVED (best_tac ctxt),
      HEADGOAL_SOLVED (asm_full_simp_tac ctxt)]))
    (*keep non-terminal calls are since they cannot be solved directly*)
    else Zip.Run.tac opt_fuel ctxt
  end

val setups as [setup_zip, setup_auto, setup_force,
  setup_fastforce, setup_slowsimp, setup_bestsimp,
  setup_fast, setup_slow, setup_best,
  setup_all_existing] = [
    (@{binding zip}, (Zip.Run.tac o snd, "White-box prover based on Zippy")),
    (@{binding auto}, (
      fn (NONE, _) => CHANGED_PROP o auto_tac
        | (SOME (m, n), _) => fn ctxt => CHANGED_PROP (mk_auto_tac ctxt m n),
      "auto")),
    (@{binding force}, (K (REPEAT_FIRST o force_tac), "force")),
    (@{binding fastforce}, (K (REPEAT_FIRST o fast_force_tac), "combined fast and simp")),
    (@{binding slowsimp}, (K (REPEAT_FIRST o slow_simp_tac), "combined slow and simp")),
    (@{binding bestsimp}, (K (REPEAT_FIRST o best_simp_tac), "combined best and simp")),
    (@{binding fast}, (K (REPEAT_FIRST o fast_tac), "fast")),
    (@{binding slow}, (K (REPEAT_FIRST o slow_tac), "slow")),
    (@{binding best}, (K (REPEAT_FIRST o best_tac), "best")),
    (@{binding all_existing}, (all_existing_tac o snd, "try all existing tactics in parallel"))
  ]

val timeout = Attrib.setup_config_real (Binding.make (id ^ "_timeout", \<^here>)) (K 30.0)

fun wrap_tac orig_tac binding tac args pos ctxt state =
  if Term_Util.has_dummy_pattern (Thm.concl_of state) then no_tac state
  else
    let
      val timeout = seconds (Config.get ctxt timeout)
      fun run _ =
        Timeout.apply timeout (tac args ctxt |> SOLVE #> Seq.pull) state |> Either.Right
        handle Timeout.TIMEOUT time => Either.Left time
      val (timing, res) = Timing.timing run () |> apfst @{print}
      val _ = Export.export ctxt pos (binding, pos, (timing, res))
    in case res of
      Either.Right (x as SOME _) => Seq.make (K x)
    | _ => (warning "Wrapped tactic failed. Using original tactic instead.";
        orig_tac args ctxt state)
    end

val setup_origs = fold (fn (binding, (tac, descr)) => setup_method (SIMPLE_METHOD ooo K o tac) descr
  (Binding.suffix_name "_orig" binding)) setups

fun setup_wrapped (binding, (tac, descr)) (orig_binding, orig_tac) = setup_method
  (SIMPLE_METHOD ooo wrap_tac orig_tac binding tac) descr orig_binding
fun setup_override x = fold (apsnd fst #> setup_wrapped x) setups
val setup_overrides = fold (fn x => setup_wrapped x (apsnd fst x)) setups
end
\<close>

text \<open>Setup alternative names for original methods and override.\<close>

local_setup \<open>Zip_Benchmark.setup_origs\<close>

(*Select the method to use as an override here...*)
local_setup \<open>Zip_Benchmark.setup_override Zip_Benchmark.setup_zip\<close>
(*...or uncomment below line to use standard tactics for benchmarks instead*)
(* local_setup \<open>Zip_Benchmark.setup_overrides\<close> *)

end
