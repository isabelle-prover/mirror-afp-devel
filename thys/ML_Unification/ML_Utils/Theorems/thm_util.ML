(*  Title:      ML_Utils/thm_util.ML
    Author:     Kevin Kappelmann

Theorem utilities.
*)
signature THM_UTIL =
sig
  (*"match_implies_elim prem thm" matches the first premise of thm against prem and then removes
    the premise; without lifting*)
  val match_implies_elim : thm -> thm -> thm
  val protect : thm -> thm
end

structure Thm_Util : THM_UTIL =
struct

fun match_implies_elim prem thm =
  Thm.instantiate (Thm.first_order_match (Thm.cprem_of thm 1, Thm.cprop_of prem)) thm
  |> (fn thm => Thm.implies_elim thm prem)

fun protect thm = Drule.protectI
  |> Thm.instantiate (TVars.empty, Vars.make [((("A", 0), propT), Thm.cprop_of thm)])
  |> Thm.elim_implies thm

end