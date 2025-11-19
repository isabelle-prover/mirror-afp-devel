(*  Title:      Zippy/zippy_action_metadata_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_METADATA_MIXIN_BASE =
sig
  structure Meta : ZIPPY_ACTION_METADATA
  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = Meta.metadata
end

functor Zippy_Action_Metadata_Mixin_Base(A :
  sig
    structure Meta : ZIPPY_ACTION_METADATA
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} data = Meta.metadata
  end) : ZIPPY_ACTION_METADATA_MIXIN_BASE
  = A
