(*  Title:      Zippy/zippy_goal_results_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_RESULTS_MIXIN_BASE =
sig
  structure R : ZIPPY_GOAL_RESULTS
  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = R.results
end

functor Zippy_Goal_Results_Mixin_Base(A :
  sig
    structure R : ZIPPY_GOAL_RESULTS
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} data = R.results
  end) : ZIPPY_GOAL_RESULTS_MIXIN_BASE
  = A