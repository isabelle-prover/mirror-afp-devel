(*  Title:      Zippy/zippy_top_meta_vars_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_TOP_META_VARS_MIXIN =
sig
  include ZIPPY_TOP_META_VARS_MIXIN_BASE
  val is_empty : @{AllT_args} L.container -> bool
end

functor Zippy_Top_Meta_Vars_Mixin(
    Top_Meta_Vars : ZIPPY_TOP_META_VARS_MIXIN_BASE
  ) : ZIPPY_TOP_META_VARS_MIXIN =
struct
open Top_Meta_Vars
fun is_empty x = L.getter x |> TMV.is_empty
end
