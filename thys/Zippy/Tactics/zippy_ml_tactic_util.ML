(*  Title:      Zippy/zippy_ml_tactic_util.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ML_TACTIC_UTIL =
sig
  val find_subterms_rev : (term -> bool) list -> term -> term list list
  val find_subterms : (term -> bool) list -> term -> term list list
  (*return combinations of terms found for each predicate*)
  val find_subterms_comb : (term -> bool) list -> term -> term list list
end

structure Zippy_ML_Tactic_Util : ZIPPY_ML_TACTIC_UTIL =
struct

fun find_subterms_rev ps t =
  let fun find t =
    map2 (fn p => fn acc => if not (member (op =) acc t) andalso p t then t :: acc else acc) ps
    #> (case t of t $ u => find t #> find u | Abs (_, _, t) => find t | _ => I)
  in find t (replicate (length ps) []) end

fun find_subterms ps = find_subterms_rev ps #> map rev

local
  structure ListT = \<^eval>\<open>sfx_ParaT_nargs "List_Traversable_Trans"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Identity_Traversable"\<close>(\<^eval>\<open>sfx_ParaT_nargs "List_Monad_Trans"\<close>(
      \<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close>)))
in
fun find_subterms_comb ps = find_subterms ps #> ListT.traverse I
end

end
