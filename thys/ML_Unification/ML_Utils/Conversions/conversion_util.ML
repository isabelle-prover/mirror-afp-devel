(*  Title:      ML_Utils/conversion_util.ML
    Author:     Kevin Kappelmann

Conversion utilities.
*)
signature CONVERSION_UTIL =
sig
  val move_prem_to_front_conv : int -> conv
  val move_prems_to_front_conv : int list -> conv
  val thm_conv : conv -> thm -> thm
  val binop_conv : conv -> conv -> conv
  val lhs_conv : conv -> conv
  val rhs_conv : conv -> conv
  val repeat_forall_conv : (cterm list -> Proof.context -> conv) -> Proof.context -> conv
  val imp_conv : conv -> conv -> conv
  val symmetric_conv : conv
end

structure Conversion_Util : CONVERSION_UTIL =
struct

fun move_prem_to_front_conv 1 = Conv.all_conv
  | move_prem_to_front_conv i = Conv.implies_concl_conv (move_prem_to_front_conv (i - 1))
    then_conv Conv.rewr_conv Drule.swap_prems_eq

val move_prems_to_front_conv = sort (rev_order o int_ord)
  #> map_index (op +)
  #> map move_prem_to_front_conv
  #> Conv.every_conv

val thm_conv = Conv.fconv_rule

fun binop_conv conv_lhs conv_rhs =
  Conv.combination_conv (Conv.arg_conv conv_lhs) conv_rhs

val lhs_conv = Conv.arg1_conv
val rhs_conv = Conv.arg_conv

fun repeat_forall_conv cv =
  let
    fun conv fs ctxt =
      Conv.forall_conv (fn (f, ctxt) => conv (f :: fs) ctxt) ctxt
      else_conv (cv fs ctxt)
  in conv [] end

fun imp_conv cvprem cvconcl ct = (case try Thm.dest_implies ct of
    NONE => cvconcl ct
  | SOME (A, C) => Drule.imp_cong_rule (cvprem A) (imp_conv cvprem cvconcl C))

fun symmetric_conv ceq = let val (cl, cr) = Thm.dest_equals ceq
  in Thm.instantiate' [SOME (Thm.ctyp_of_cterm cl)] [SOME cl, SOME cr] @{thm meta_eq_symmetric} end

end
