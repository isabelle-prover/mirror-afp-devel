(*  Title:      Zippy/zippy_top_meta_vars_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_TOP_META_VARS_MIXIN_BASE =
sig
  structure TMV : ZIPPY_TOP_META_VARS
  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = TMV.top_meta_vars
end

functor Zippy_Top_Meta_Vars_Mixin_Base(A :
  sig
    structure TMV : ZIPPY_TOP_META_VARS
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} data = TMV.top_meta_vars
  end) : ZIPPY_TOP_META_VARS_MIXIN_BASE
  = A