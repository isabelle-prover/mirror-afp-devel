(*  Title:      Zippy/zippy_paction_presults_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PACTION_PRESULTS_MIXIN_BASE =
sig
  type prio
  structure PAction : ZIPPY_PACTION_MIXIN_BASE
  sharing type PAction.prio = prio

  structure PResults : ZIPPY_PRESULTS_MIXIN_BASE
  sharing type PResults.M.t = PAction.M.t
  sharing type PResults.zipper = PAction.zipper
  sharing type PResults.prio = prio
end

functor Zippy_PAction_PResults_Mixin_Base(A :
  sig
    structure PAction : ZIPPY_PACTION_MIXIN_BASE
    structure PResults : ZIPPY_PRESULTS_MIXIN_BASE
    sharing type PResults.M.t = PAction.M.t
    sharing type PResults.zipper = PAction.zipper
    sharing type PResults.prio = PAction.prio
  end
  ) : ZIPPY_PACTION_PRESULTS_MIXIN_BASE
  =
struct
open A
type prio = PAction.prio
end