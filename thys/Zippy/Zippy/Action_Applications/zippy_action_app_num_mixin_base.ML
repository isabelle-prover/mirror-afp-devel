(*  Title:      Zippy/zippy_action_app_num_mixin_base.ML
    Author:     Kevin Kappelmann

Action application numbers.
*)
signature ZIPPY_ACTION_APP_NUM_MIXIN_BASE =
sig
  structure AANum : ZIPPY_ACTION_APP_NUM

  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = AANum.action_app_num
end

functor Zippy_Action_App_Num_Mixin_Base(A :
  sig
    structure AANum : ZIPPY_ACTION_APP_NUM
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} data = AANum.action_app_num
  end
  ) : ZIPPY_ACTION_APP_NUM_MIXIN_BASE
  = A