(*  Title:      Zippy/zippy_run_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_RUN_MIXIN =
sig
  include ZIPPY_LOGGER_MIXIN_BASE
  include ZIPPY_RUN_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  sharing type M.t = Seq_From_Monad.M.t

  type ('ss, @{AllT_args encl: "" ""}) finished_data = {
    thm_states : GClusters.GCS.state Seq.seq,
    steps : int,
    zipper : @{AllT_args} GClusters.L.container,
    step_state : 'ss,
    monad_state : @{AllT_args} Seq_From_Monad.state}

  type @{AllT_args} container1

  val repeat_step : ('ss -> (@{ParaT_args} @{AllT_args} container1,
      (((@{AllT_args} GClusters.L.container * Results.results)) option * 'ss) option) morph) ->
    (int -> 'ss -> (@{ParaT_args} @{AllT_args} container1,
      (('ss, @{AllT_args encl: "" ""}) finished_data, 'u) Zippy_Run_Result.result Seq.seq) morph) ->
    (int -> 'ss -> (@{ParaT_args} @{AllT_args} container1,
      (('ss, @{AllT_args encl: "" ""}) finished_data, 'u) Zippy_Run_Result.result Seq.seq) morph) ->
    int option -> 'ss -> @{AllT_args} Seq_From_Monad.state -> @{AllT_args} container1 ->
    (('ss, @{AllT_args encl: "" ""}) finished_data, 'u) Zippy_Run_Result.result Seq.seq

  val filter_unfinished_statesq : GClusters.GCS.state Seq.seq -> GClusters.GCS.state Seq.seq
  val mk_unreturned_statesq :
    (@{ParaT_args} @{AllT_args} GClusters.L.container, GClusters.GCS.state Seq.seq) morph ->
    (@{ParaT_args} @{AllT_args} GClusters.L.container, GClusters.GCS.state Seq.seq) morph
end

functor Zippy_Run_Mixin(
    structure Z : ZIPPY_BASE_BASE
    structure Run : ZIPPY_RUN_MIXIN_BASE
    sharing type Run.GClusters.L.container = Z.Z1.zipper
    sharing type Run.Seq_From_Monad.M.t = Z.M.t
    val with_state : (@{AllT_args} Run.Seq_From_Monad.state -> (@{ParaT_args} 'a, 'b) Z.morph) ->
      (@{ParaT_args} 'a, 'b) Z.morph
    structure Exn : ZIPPY_EXCEPTION_MIXIN
    sharing type Exn.M.t = Z.M.t
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
  ) : ZIPPY_RUN_MIXIN =
struct

open Run Z Log
structure Show = SpecCheck_Show
structure RR = Zippy_Run_Result
structure MU = Zippy_Monad_Util(M); open MU
structure GClusters = Zippy_Goal_Clusters_Mixin(GClusters)
structure GClusters_Results = Zippy_Goal_Results_Mixin(GClusters_Results)

type ('ss, @{AllT_args encl: "" ""}) finished_data = {
  thm_states : GClusters.GCS.state Seq.seq,
  steps : int,
  zipper : @{AllT_args} GClusters.L.container,
  step_state : 'ss,
  monad_state : @{AllT_args} Seq_From_Monad.state}

type @{AllT_args} container1 = @{AllT_args} Z1.ZM.container
fun pretty_fuel NONE = Pretty.str "Unlimited"
  | pretty_fuel (SOME n) = Show.int n

local open SC Mo A
  fun finished_data steps step_state zipper monad_state thm_states = {steps = steps,
    step_state = step_state, monad_state = monad_state, zipper = zipper, thm_states = thm_states}
in
fun repeat_step step finish_empty_fuel finish_no_steps =
  let fun run steps opt_fuel ss ms c = Seq.make (fn _ => Ctxt.get_ctxt () >>= (fn ctxt => c |>
    (if the_default 1 opt_fuel <= 0
    then (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
          Pretty.str "Ran out of fuel after ", Show.int steps, Pretty.str " step(s)."
        ] |> Pretty.string_of);
      finish_empty_fuel steps ss)
    else Exn.AE.catch'
      (fn c => (@{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
            Pretty.str "Running one step.",
            Pretty.block [Pretty.str "Step count: ", Show.int steps, Pretty.str "."],
            Pretty.block [Pretty.str "Remaining fuel: ", pretty_fuel opt_fuel]
          ] |> Pretty.block |> Pretty.string_of);
        step ss c)
      >>= (fn x => x |>
        let val steps = steps + 1
        in AC.opt
          (Ctxt.with_ctxt (fn ctxt => fn _ => (@{log Logger.DEBUG} ctxt (fn _ => "No more steps left.");
            finish_no_steps steps ss c)))
          (with_state (fn ms => fn (opt_res, ss) =>
            let val nextsq = run steps (Option.map General_Util.pred opt_fuel) ss ms
            in case opt_res of
              NONE => Ctxt.get_ctxt () >>= (fn ctxt =>
                (@{log Logger.DEBUG} ctxt (fn _ => "No zipper changes. Continuing with next step.");
                arr nextsq c))
            | SOME (z, results) => Z1.ZM.Unzip.morph z >>= Ctxt.with_ctxt (fn ctxt => arr (nextsq #>
                (if Results.has_results results
                then (@{log Logger.DEBUG} ctxt (fn _ => "Returning new results.");
                  Seq.cons (RR.Finished (finished_data steps ss z ms (Results.get_states results))))
                else (@{log Logger.DEBUG} ctxt (fn _ => "No new results. Continuing with next step.");
                  I))))
            end))
        end))
      (fn _ => (@{log Logger.WARN} ctxt (fn _ => "Error while running step. Stopping run.");
        pure Seq.empty))))
    |> Seq_From_Monad.seq_from_monad ms |> Seq.pull)
  in run 0 end

fun filter_unfinished_statesq sq = Seq.filter (Zippy_Thm_State.is_finished #> not) sq
fun mk_unreturned_statesq mk_statesq z =
  if not (GClusters.has_meta_vars z) andalso GClusters_Results.has_results z
  then pure Seq.empty
  else mk_statesq z >>= arr filter_unfinished_statesq
end
end
