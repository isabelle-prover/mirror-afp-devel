(*  Title:      Zippy/zippy_goals_pos_copy_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_POS_COPY_MIXIN_BASE =
sig
  include ZIPPY_GOALS_POS_MIXIN_BASE

  structure Copy : ZIPPY_COPY_MIXIN_BASE
  where type copy_update_data = GPU.focus_update
end

functor Zippy_Goals_Pos_Copy_Mixin_Base(A :
  sig
    include ZIPPY_GOALS_POS_MIXIN_BASE
    structure Copy : ZIPPY_COPY_MIXIN_BASE
    where type copy_update_data = GPU.focus_update
  end) : ZIPPY_GOALS_POS_COPY_MIXIN_BASE
  = A
