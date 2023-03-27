(*
   Mike Stannett
   Feb 2023
*)

section \<open> AXIOM: AxDiff \<close>

text \<open> This theory declares the axiom AxDiff. \<close>

theory AxDiff
  imports Affine WorldView
begin

text \<open>AxDiff:
  Worldview transformations are differentiable wherever they are defined - 
  they can be approximated locally by affine transformations.\<close>

(*
  ADDED JUDIT'S ASSUMPTION to affApprox definition: A is invertible
*)
class axDiff = Affine + WorldView
begin
  abbreviation axDiff :: "Body \<Rightarrow> Body \<Rightarrow> 'a Point \<Rightarrow> bool" 
    where "axDiff m k p \<equiv> (definedAt (wvtFunc m k) p) 
                              \<longrightarrow> (\<exists> A . (affineApprox A (wvtFunc m k) p ))"
end (* of class axDiff *)


class AxDiff = axDiff +
  assumes AxDiff: "\<forall> m k p  . axDiff m k p"
begin
end (* of class AxDiff *)

end (* of theory AxDiff *)

