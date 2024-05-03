(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Mutual_Fixed_Points
  imports AutoCorres2_Main.AutoCorres_Main
begin

text \<open>
To define functions from (mutually) recursive C function we use @{command fixed_point}.
This is a generalisation of @{command partial_function} supporting mutual recursion and is also
based on chain complete partial orders (CCPO), cf:
\<^item> \<^url>\<open>https://www21.in.tum.de/~krauss/publication/2016-overview-paper/\<close>
\<^item> \<^url>\<open>https://www21.in.tum.de/~krauss/publication/2010-monadic-functions/\<close>

In contrast to @{command function} we do not have to provide any termination argument in order to get
get the equations and an induction principle. However, the induction principle only allows
to prove admissible properties (@{const ccpo.admissible}). Lukily, the simulation properties
that we use in autocorres are admissible.

Moreover, to perform the fixed point construction from the defining equations monotonicity of 
the functionals has to be proven @{const monotone}. The lemmas for those proofs are
collected in @{thm partial_function_mono}.
\<close>

thm partial_function_mono


fun even'::"nat \<Rightarrow> bool" and odd':: "nat \<Rightarrow> bool"
  where
  "even' 0 = True"
| "odd' 0 = False"
| "even' (Suc n) = odd' n"
| "odd' (Suc n) = even' n"
thm even'_odd'.induct
thm even'.simps


lemma even'_odd'_mod2:
 "even' n = (n mod 2 = 0)"
 "odd' n = (n mod 2 = 1)"
   apply (induct n and n rule: even'_odd'.induct)
     apply simp_all
   apply arith
  apply arith
  done

fixed_point (option) eveno oddo:: "nat \<Rightarrow> bool option"
  where
  "eveno n = (if n = 0 then Some True else oddo (n - 1))"
| "oddo n = (if n = 0 then Some False else eveno (n - 1))"
  by simp_all
print_theorems
thm eveno_oddo.induct
thm eveno.simps
thm oddo.simps

text \<open>One can also use patterns in the defining equations. 
The usage and effect differs from @{command function}.
\<^item> Patterns do not have to be complete but they have to be unambiguous (no overlapping patterns). 
  This is captured in the proof obligations @{const subsingleton_set}.
\<^item> There is no automatic disambiguation going on, like taking the order of appearance into account.
\<close>
fixed_point (option) eveno' oddo':: "nat \<Rightarrow> bool option"
  where
  "eveno' 0 = Some True"
| "eveno' (Suc n) = oddo' n"
| "oddo' 0 = Some False"
| "oddo' (Suc n) = eveno' n"
  thm subsingleton_set_def
  by (auto simp add: subsingleton_set_def)
thm eveno'_oddo'.induct
thm eveno'.simps
thm oddo'.simps

text \<open>One can also push the arguments to the right hand side.\<close>
fixed_point (option) eveno'' oddo'':: "nat \<Rightarrow> bool option"
  where
  "eveno'' = (\<lambda>n. if n = 0 then Some True else oddo'' (n - 1))"
| "oddo'' = (\<lambda>n. if n = 0 then Some False else eveno'' (n - 1))"
  by simp_all
thm eveno''_oddo''.induct
thm eveno''.simps
thm oddo''.simps

text \<open>Partial correctness properties are admissible. So the induction principle can be used.
However, this is more an academic (artificial) choice here,
as it is more straightforward to use plain natural number induction on the parameter.\<close>

lemma eveno_oodo_mod2:
"\<forall>x. (eveno n = Some x) \<longrightarrow> (x = (n mod 2 = 0))"
"\<forall>x. (oddo n = Some x) \<longrightarrow> (x = (n mod 2 = 1))"
   apply (induct n and n rule: eveno_oddo.induct)
  apply simp_all
  apply (smt (verit, best) ccpo.admissibleI flat_lub_in_chain option.simps(3))
    apply (smt (verit, best) ccpo.admissibleI flat_lub_in_chain option.simps(3))
   apply (metis cong_exp_iff_simps(6) diff_Suc_Suc even'.cases minus_nat.diff_0 
      mod_Suc_eq mod_self nat_minus_mod not_mod2_eq_Suc_0_eq_0 numeral_1_eq_Suc_0)
  by (metis One_nat_def Suc_pred bits_one_mod_two_eq_one bot_nat_0.not_eq_extremum 
      mod_Suc_eq nat_minus_mod)

lemma 
"\<forall>x. (eveno n = Some x) \<longrightarrow> (x = (n mod 2 = 0))"
"\<forall>x. (oddo n = Some x) \<longrightarrow> (x = (n mod 2 = 1))"
   apply (induct n)
     apply (subst eveno.simps, simp)
    apply (subst oddo.simps, simp)
   apply (subst eveno.simps, simp)
   apply (clarsimp, arith)
  apply (subst oddo.simps, simp)
  apply (clarsimp, arith)
  done



text \<open>Termination might be shown. Analogous to @{command function}, proving termination might 
be a non-trivial effort requiring involved semantic arguments. In this case we can
use plain natural number induction on the parameter.\<close>

lemma eveno_oodo_defined:
"(eveno n = None) = False"
"(oddo n = None) = False"
   apply (induct n )
     apply (simp_all add: eveno.simps oddo.simps)
  done

text \<open>For this example, natural number induction on the parameter is also sufficient to 
directly proof total correctness.\<close>
lemma 
  "eveno' n = Some (n mod 2 = 0)"
  "oddo' n = Some (n mod 2 = 1)"
  apply (induct n)
     apply (simp_all add: eveno'.simps oddo'.simps)
   apply arith
  apply arith
  done

fixed_point (spec_monad_gfp) fac:: "int \<Rightarrow> (int, unit) res_monad"
  where
  "fac n = (if n = 0 then return 0 else fac (n - 1)  >>= (\<lambda>m. return (n * m)))"
  apply simp_all
  done
thm fac.induct
thm fac.simps


fixed_point (spec_monad_gfp) odd even:: "nat \<Rightarrow> (bool, unit) res_monad"
  where
  "even n = (if n = 0 then return True else odd (n - 1))"
| "odd n = (if n = 0 then return False else even (n - 1))"
  apply simp_all
  done
thm odd_even.induct
thm odd.simps
thm even.simps

fixed_point (spec_monad_gfp)
  F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20
    :: "unit \<Rightarrow> (unit, unit) res_monad"
  where
  "F0 p  = F1 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F1 p  = F2 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F2 p  = F3 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F3 p  = F4 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F4 p  = F5 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F5 p  = F6 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F6 p  = F7 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F7 p  = F8 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F8 p  = F9 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F9 p  = F10 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F10 p = F1 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F11 p = F2 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F12 p = F3 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F13 p = F4 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F14 p = F5 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F15 p = F6 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F16 p = F7 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F17 p = F8 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F18 p = F9 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F19 p = F10 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
| "F20 p = F10 p >>= F2 >>= F3 >>= F4 >>= F5 >>= F6"
  apply simp_all
  done
thm F0_F1_F2_F3_F4_F5_F6_F7_F8_F9_F10_F11_F12_F13_F14_F15_F16_F17_F18_F19_F20.induct
locale numbers =
  fixes NN::nat
begin
fixed_point (option) X Y Z:: "nat \<Rightarrow> nat option"
  where
  "X 0 = X 0"
| "X 1 = Y 0"
| "X 2 = Z 0"
| "X 3 = Some NN"
| "X 4 = None"
| "X 5 = None"
| "X 6 = None"
| "X 7 = None"
| "X 8 = None"
| "X 9 = None"
| "X 10 = None"
| "X 11 = None"
| "X 12 = None"
| "X 13 = None"
| "X 14 = None"
| "Y n = Z n"
| "Z n = Z n"
proof -
  fix X Y Z and n :: nat
  have "n = 0 \<or> n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4 \<or> n = 5 \<or> n = 6 \<or> n = 7 \<or> n = 8 \<or> n = 9 \<or> n = 10 \<or>
    n = 11 \<or> n = 12 \<or> n = 13 \<or> n = 14 \<or> 14 < n"
    by arith
  then show "?unique_X X Y Z n" 
    by auto
qed simp_all
thm X_Y_Z.induct
thm X.simps
end

fixed_point (spec_monad_gfp)
  H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20
  G0 G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 G17 G18 G19 G20
    :: "unit \<Rightarrow> (unit, unit) res_monad"
  where
  "H0 p  = H1 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H1 p  = H2 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H2 p  = H3 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H3 p  = H4 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H4 p  = H5 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H5 p  = H6 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H6 p  = H7 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H7 p  = H8 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H8 p  = H9 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H9 p  = H10 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H10 p = H1 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H11 p = H2 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H12 p = H3 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H13 p = H4 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H14 p = H5 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H15 p = H6 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H16 p = H7 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H17 p = H8 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H18 p = H9 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H19 p = H10 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "H20 p = H10 p >>= H2 >>= H3 >>= H4 >>= H5 >>= H6"
| "G0 p  = G1 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G1 p  = G2 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G2 p  = G3 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G3 p  = G4 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G4 p  = G5 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G5 p  = G6 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G6 p  = G7 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G7 p  = G8 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G8 p  = G9 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G9 p  = G10 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G10 p = G1 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G11 p = G2 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G12 p = G3 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G13 p = G4 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G14 p = G5 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G15 p = G6 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G16 p = G7 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G17 p = G8 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G18 p = G9 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G19 p = G10 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
| "G20 p = G10 p >>= G2 >>= G3 >>= G4 >>= G5 >>= G6"
  apply simp_all
  done


end