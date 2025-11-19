(*  Title:      Zippy/zippy_run_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_RUN_MIXIN_BASE =
sig
  include ZIPPY_GOALS_RESULTS_MIXIN_BASE
  structure Seq_From_Monad : ZIPPY_SEQ_FROM_MONAD_MIXIN_BASE
end

functor Zippy_Run_Mixin_Base(A :
  sig
    include ZIPPY_GOALS_RESULTS_MIXIN_BASE
    structure Seq_From_Monad : ZIPPY_SEQ_FROM_MONAD_MIXIN_BASE
  end) : ZIPPY_RUN_MIXIN_BASE
  = A
