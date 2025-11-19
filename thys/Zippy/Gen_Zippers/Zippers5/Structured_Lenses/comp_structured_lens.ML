(*  Title:      Zippy/comp_structured_lens.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "COMP_STRUCTURED_LENS"\<close> =
sig
  structure L1 : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  structure L2 : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  sharing type L2.container = L1.data
  sharing type L1.lens = L2.lens
  sharing type L1.K.M.t = L2.K.M.t

  include \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  sharing type container = L1.container
  sharing type data = L2.data
  sharing type lens = L1.lens
  sharing type K.M.t = L1.K.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
    structure L1 : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
    structure L2 : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  sharing type L2.container = L1.data
    sharing type L1.lens = L2.lens
    sharing type L1.K.M.t = L2.K.M.t
  ) : \<^eval>\<open>sfx_T_nargs "COMP_STRUCTURED_LENS"\<close>
  =
struct

structure L1 = L1
structure L2 = L2

open L1

type @{AllT_args} data = @{AllT_args} L2.data

fun getter x = C.comp L2.getter L1.getter x
fun modifier x = comp_modify L2.modifier L1.modifier x
fun lens _ = mk_lens getter modifier
end
