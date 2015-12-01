(*  Title:       Implementing field extensions of the form Q[sqrt(b)]
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

(*
Copyright 2009-2014 René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)
section {* Auxiliary lemmas which might be moved into the Isabelle distribution. *}

theory Real_Impl_Auxiliary
imports 
  "~~/src/HOL/Number_Theory/UniqueFactorization"
begin

lemma multiplicity_prime: assumes p: "prime (i :: nat)" and ji: "j \<noteq> i"
  shows "multiplicity j i = 0"
proof (rule ccontr)
  assume "\<not> ?thesis"
  hence "multiplicity j i > 0" by auto
  hence j: "j \<in> prime_factors i"
    by (metis less_not_refl multiplicity_not_factor_nat)
  hence d: "j dvd i" 
    by (metis p prime_factors_altdef2_nat prime_gt_0_nat)
  then obtain k where i: "i = j * k" ..
  from j have "j \<ge> 2" 
    by (metis prime_factors_prime_nat prime_ge_2_nat)
  hence j1: "j \<noteq> 1" by auto
  from i have "j dvd i" by auto
  with j1 ji p[unfolded prime_def] show False by auto
qed

end
