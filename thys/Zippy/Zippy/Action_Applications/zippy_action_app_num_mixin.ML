(*  Title:      Zippy/zippy_action_app_num_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_APP_NUM_MIXIN =
sig
  include ZIPPY_ACTION_APP_NUM_MIXIN_BASE
  val inc_action_app_num : @{AllT_args} L.container -> @{AllT_args} L.container
end

functor Zippy_Action_App_Num_Mixin(
    AANum : ZIPPY_ACTION_APP_NUM_MIXIN_BASE
  ) : ZIPPY_ACTION_APP_NUM_MIXIN =
struct

open AANum
fun inc_action_app_num x = L.modifier (AANum.inc, x)

end
