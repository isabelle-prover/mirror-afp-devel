(*  Title:      Zippy/pair_structured_lens.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "PAIR_STRUCTURED_LENS"\<close> =
sig
  structure L1 : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  structure L2 : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  sharing type L1.lens = L2.lens
  sharing type L1.K.M.t = L2.K.M.t

  include \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} container = @{AllT_args} L1.container * @{AllT_args} L2.container
  where type @{AllT_args} data = @{AllT_args} L1.data * @{AllT_args} L2.data
  sharing type lens = L1.lens
  sharing type K.M.t = L1.K.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Pair_Structured_Lens"\<close>(
    structure L1 : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
    structure L2 : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
    sharing type L1.lens = L2.lens
    sharing type L1.K.M.t = L2.K.M.t
  ) : \<^eval>\<open>sfx_T_nargs "PAIR_STRUCTURED_LENS"\<close>
  =
struct

structure L1 = L1
structure L2 = L2

open L1

type @{AllT_args} container = @{AllT_args} L1.container * @{AllT_args} L2.container
type @{AllT_args} data = @{AllT_args} L1.data * @{AllT_args} L2.data

local structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Arrow_Apply"\<close>(K.M)
in
structure LP = \<^eval>\<open>sfx_ParaT_nargs "Pair_Lens"\<close>(open A; structure L = L1)
end

fun getter x = LP.get_pair L1.getter L2.getter x
fun modifier x = LP.modify_pair getter L1.modifier L2.modifier x
fun lens _ = mk_lens getter modifier
end

