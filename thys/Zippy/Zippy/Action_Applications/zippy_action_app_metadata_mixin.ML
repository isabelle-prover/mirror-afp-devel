(*  Title:      Zippy/zippy_action_app_metadata_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_APP_METADATA_MIXIN =
sig
  include ZIPPY_ACTION_APP_METADATA_MIXIN_BASE

  structure Progress : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} container = @{AllT_args} L.container
  where type @{AllT_args} data = Meta.progress
end

functor Zippy_Action_App_Metadata_Mixin(
    Meta : ZIPPY_ACTION_APP_METADATA_MIXIN_BASE
  ) : ZIPPY_ACTION_APP_METADATA_MIXIN =
struct

open Meta

structure Progress = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = L; structure L2 = Meta.Progress)

end
