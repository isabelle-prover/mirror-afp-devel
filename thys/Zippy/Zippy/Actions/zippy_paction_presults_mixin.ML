(*  Title:      Zippy/zippy_paction_presults_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PACTION_PRESULTS_MIXIN =
sig
  include ZIPPY_LOGGER_MIXIN_BASE
  include ZIPPY_PACTION_PRESULTS_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  sharing type M.t = PAction.M.t

  type @{AllT_args} zipper = @{AllT_args} PAction.zipper

  val gen_paction_from_presults :
    (*action when results are empty*)
    @{AllT_args} PAction.action ->
    (*action with pulled result and the remaining presults*)
    (PResults.result * @{AllT_args} PResults.presults -> @{AllT_args} PAction.action) ->
    @{AllT_args} PResults.presults -> @{AllT_args} PAction.paction

  (*recursively sets new action using remaining presults*)
  val paction_from_presults :
    (*takes number of previously returned results as argument*)
    (int -> @{AllT_args} PAction.action) ->
    (*additional updates with remaining presults*)
    (@{AllT_args} PResults.presults -> prio -> (@{ParaT_args} @{AllT_args} zipper) emorph) ->
    (PResults.result -> @{AllT_args} PAction.action) ->
    @{AllT_args} PResults.presults -> @{AllT_args} PAction.paction
end

functor Zippy_PAction_PResults_Mixin(
    structure PAction_PResults : ZIPPY_PACTION_PRESULTS_MIXIN_BASE
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = PAction_PResults.PAction.M.t
    structure Show_PAction_Zipper : ZIPPY_SHOW_MIXIN_BASE
    sharing type Show_PAction_Zipper.t = PAction_PResults.PAction.zipper
    structure Log_PAction : ZIPPY_LOGGER_MIXIN_BASE
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
  ) : ZIPPY_PACTION_PRESULTS_MIXIN =
struct

open PAction_PResults Log
structure MU = Zippy_Monad_Util(PAction.M); open MU MU.MB
structure Exn = Zippy_Exception_Mixin(PResults.Co)
structure PAction = Zippy_PAction_Mixin(structure PAction = PAction; structure Exn = Exn
  structure Ctxt = Ctxt; structure Log = Log_PAction; structure Show = Show_PAction_Zipper)
structure PResults = Zippy_PResults_Mixin(PResults)

type @{AllT_args} zipper = @{AllT_args} PAction.zipper
type prio = PAction.prio

local open SC Mo A PResults.Co Exn
in
fun gen_paction_from_presults empty_action result_tail_presults_action presults =
  let fun update_action rp_aco prio = AE.catch'
    (fn z => Co.resume rp_aco z
      >>= (apsnd PResults.presults #> (fn rpress => result_tail_presults_action rpress prio z)))
    (Ctxt.with_ctxt (fn ctxt => (@{log Logger.DEBUG} ctxt (fn _ => "PResults empty.");
      empty_action prio)))
  in PResults.run_presults presults >>> second (arr update_action) |> PAction.paction end

fun paction_from_presults empty_action update_tail_presults result_action =
  let
    fun update_tail_presults_set_rec counter presults prio =
      PAction.set_paction (run (counter + 1) presults) #> update_tail_presults presults prio
    and result_tail_presults_action counter (result, presults) prio =
      update_tail_presults_set_rec counter presults prio >>> result_action result prio
    and run counter = gen_paction_from_presults (empty_action counter)
      (result_tail_presults_action counter)
  in run 0 end
end

end

