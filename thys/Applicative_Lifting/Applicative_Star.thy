(* Author: Andreas Lochbihler, ETH Zurich *)

subsection \<open>Ultrafilter\<close>

theory Applicative_Star imports
  "Applicative"
  "~~/src/HOL/NSA/StarDef"
begin

applicative star (C, K, W)
for
  pure: star_of
  ap: Ifun
proof -
  show "star_of f \<star> star_of x = star_of (f x)" for f x by(fact Ifun_star_of)
  show "\<And>f. f \<star> star_of x = star_of (\<lambda>f. f x) \<star> f" for x by transfer(rule refl)
qed(transfer; rule refl)+

end