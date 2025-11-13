(*  Title:      Zippy/zippy_prio_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PRIO_MIXIN_BASE =
sig
  type prio
  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = prio
end

functor Zippy_Prio_Mixin_Base(A :
  sig
    type prio
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} data = prio
  end
  ) : ZIPPY_PRIO_MIXIN_BASE
  = A