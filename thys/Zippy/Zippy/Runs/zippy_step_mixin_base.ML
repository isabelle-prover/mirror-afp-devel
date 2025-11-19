(*  Title:      Zippy/zippy_step_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_STEP_MIXIN_BASE =
sig
  include ZIPPY_GOALS_RESULTS_TOP_META_VARS_MIXIN_BASE
  structure PAction_Queue : ZIPPY_PACTION_QUEUE_MIXIN_BASE
end

functor Zippy_Step_Mixin_Base(A :
  sig
    include ZIPPY_GOALS_RESULTS_TOP_META_VARS_MIXIN_BASE
    structure PAction_Queue : ZIPPY_PACTION_QUEUE_MIXIN_BASE
  end) : ZIPPY_STEP_MIXIN_BASE
  = A