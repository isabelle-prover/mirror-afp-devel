(*  Title:      Zippy/zippy_ml_tactic_util.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ML_TACTIC_UTIL =
sig
  val find_subterms : (Term_Zipper.T -> Term_Zipper.T Seq.seq) -> (Term_Zipper.T -> bool) list ->
    term -> Term_Zipper.T list list
  (*return combinations of terms found for each predicate*)
  val find_subterms_comb : (Term_Zipper.T -> Term_Zipper.T Seq.seq) ->
    (Term_Zipper.T -> bool) list -> term -> Term_Zipper.T list list
end

structure Zippy_ML_Tactic_Util : ZIPPY_ML_TACTIC_UTIL =
struct

fun find_subterms search ps = Term_Zipper.mktop #> search #> Seq.list_of
  #> (fn ts => fold_rev (fn t => map2 (fn p => fn acc =>
    if not (member (eq_fst (op =)) acc t) andalso p t then t :: acc else acc) ps)
    ts (replicate (length ps) []))

local
  structure ListT = \<^eval>\<open>sfx_ParaT_nargs "List_Traversable_Trans"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Identity_Traversable"\<close>(\<^eval>\<open>sfx_ParaT_nargs "List_Monad_Trans"\<close>(
      \<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close>)))
in
fun find_subterms_comb search ps = find_subterms search ps #> ListT.traverse I
end

end
