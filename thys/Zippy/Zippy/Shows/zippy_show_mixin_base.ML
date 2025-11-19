(*  Title:      Zippy/zippy_show_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_SHOW_MIXIN_BASE =
sig
  type @{AllT_args} t
  val pretty : Proof.context -> @{AllT_args} t SpecCheck_Show.show
end

functor Zippy_Show_Mixin_Base(A :
  sig
    type @{AllT_args} t
    val pretty : Proof.context -> @{AllT_args} t SpecCheck_Show.show
  end
  ) : ZIPPY_SHOW_MIXIN_BASE
  = A