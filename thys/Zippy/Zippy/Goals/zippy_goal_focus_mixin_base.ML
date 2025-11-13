(*  Title:      Zippy/zippy_goal_focus_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_FOCUS_MIXIN_BASE =
sig
  structure F : ZIPPY_GOAL_FOCUS
  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = F.focus
end

functor Zippy_Goal_Focus_Mixin_Base(A :
  sig
    structure F : ZIPPY_GOAL_FOCUS
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} data = F.focus
  end) : ZIPPY_GOAL_FOCUS_MIXIN_BASE
  = A