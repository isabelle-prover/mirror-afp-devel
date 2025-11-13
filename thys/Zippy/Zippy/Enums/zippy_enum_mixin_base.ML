(*  Title:      Zippy/zippy_enum_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ENUM_MIXIN_BASE =
sig
  include ZIPPY_BASE_BASE
  structure Co : ZIPPY_COROUTINE_MIXIN_BASE
  sharing type Co.M.t = M.t
end

functor Zippy_Enum_Mixin_Base(A :
  sig
    structure Z : ZIPPY_BASE_BASE
    structure Co : ZIPPY_COROUTINE_MIXIN_BASE
    sharing type Co.M.t = Z.M.t
  end) : ZIPPY_ENUM_MIXIN_BASE
  =
struct
open A A.Z
end