(* Author: Joshua Schneider, ETH Zurich *)

section \<open>Common applicative functors\<close>

subsection \<open>Environment functor\<close>

theory Applicative_Environment imports 
  Applicative
  "~~/src/Tools/Adhoc_Overloading"
begin

definition "const x = (\<lambda>_. x)"
definition "apf x y = (\<lambda>z. x z (y z))"

adhoc_overloading Applicative.pure const
adhoc_overloading Applicative.ap apf

applicative env (C, K, W)
for
  pure: const
  ap: apf
by(simp_all add: const_def apf_def)

end