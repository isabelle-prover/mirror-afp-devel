(*  Title:      Zippy/zippy_tactic_action_app_metadata_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_TACTIC_ACTION_APP_METADATA_MIXIN_BASE =
sig
  structure Meta : ZIPPY_ACTION_APP_METADATA_MIXIN_BASE
  structure Tac : ZIPPY_ZTACTIC
end

functor Zippy_Tactic_Action_App_Metadata_Mixin_Base(A :
  sig
    structure Meta : ZIPPY_ACTION_APP_METADATA_MIXIN_BASE
    structure Tac : ZIPPY_ZTACTIC
  end) : ZIPPY_TACTIC_ACTION_APP_METADATA_MIXIN_BASE
  = A
