(*  Title:      Zippy/pair_zipper_data.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER_DATA"\<close> =
sig
  structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
  structure Z2 : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>

  include \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
  where type @{AllT_args} content = @{AllT_args} Z1.content * @{AllT_args} Z2.content
  where type @{AllT_args} zcontext = @{AllT_args} Z1.zcontext * @{AllT_args} Z2.zcontext
  where type @{AllT_args} zipper = @{AllT_args} Z1.zipper * @{AllT_args} Z2.zipper
end

functor \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Data"\<close>(
    structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    structure Z2 : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
  ) : \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER_DATA"\<close> =
struct

structure Z1 = Z1
structure Z2 = Z2

type @{AllT_args} content = @{AllT_args} Z1.content * @{AllT_args} Z2.content
type @{AllT_args} zcontext = @{AllT_args} Z1.zcontext * @{AllT_args} Z2.zcontext
type @{AllT_args} zipper = @{AllT_args} Z1.zipper * @{AllT_args} Z2.zipper

structure Co = \<^eval>\<open>sfx_T_nargs "Pair_Structured_Lens"\<close>(
  structure L1 = Z1.Co; structure L2 = Z2.Co)
structure ZCtxt = \<^eval>\<open>sfx_T_nargs "Pair_Structured_Lens"\<close>(
  structure L1 = Z1.ZCtxt; structure L2 = Z2.ZCtxt)

local
  structure A = \<^eval>\<open>sfx_ParaT_nargs "SArrow_Arrow_Apply" ^ ".A"\<close>
  open A
in
fun zipper ((c1, c2), (zctxt1, zctxt2)) = (Z1.zipper *** Z2.zipper) ((c1, zctxt1), (c2, zctxt2))
end

end
