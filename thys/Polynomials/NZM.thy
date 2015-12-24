(*  Title:       Executable multivariate polynomials
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 Rene Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and Rene Thiemann
    License:     LGPL
*)

(*
Copyright 2009 Christian Sternagel, René Thiemann, Sarah Winkler, Harald Zankl

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

section {* Monotonicity criteria of Neurauter, Zankl, and Middeldorp *}

theory NZM
imports "../Abstract-Rewriting/SN_Order_Carrier" Polynomials
begin

text {* 
We show that our check on monotonicity is strong enough to capture the 
exact criterion for polynomials of degree 2 that is presented in \cite{NZM10}:
\begin{itemize}
\item $ax^2 + bx + c$ is monotone if $b + a > 0$ and $a \geq 0$
\item $ax^2 + bx + c$ is weakly monotone if $b + a \geq 0$ and $a \geq 0$
\end{itemize}
*}

lemma assumes b: "b + a > 0" and a: "(a :: int) \<ge> 0"
  shows "check_poly_strict_mono_discrete (op >) (poly_of (PSum [PNum c, PMult [PNum b, PVar x], PMult [PNum a, PVar x, PVar x]])) x"
proof (cases "a = 0")
  case True
  with b have b: "b > 0 \<and> b \<noteq> 0" by auto
  show ?thesis using b True 
    by (simp add: b True extract_def poly_add.simps eq_monom.simps poly_mult.simps monom_mult_poly.simps monom_mult.simps poly_subst.simps monom_subst.simps poly_power.simps one_poly_def zero_poly_def check_poly_gt_def check_poly_ge.simps check_poly_strict_mono_discrete_def poly_split_def, auto)
next
  case False
  show ?thesis using False a b
    by (simp add: b False extract_def poly_add.simps eq_monom.simps poly_mult.simps monom_mult_poly.simps monom_mult.simps poly_subst.simps monom_subst.simps poly_power.simps one_poly_def zero_poly_def check_poly_gt_def check_poly_ge.simps check_poly_strict_mono_discrete_def poly_split_def, auto)
qed

lemma assumes b: "b + a \<ge> 0" and a: "(a :: int) \<ge> 0" 
  shows "check_poly_weak_mono_discrete (poly_of (PSum [PNum c, PMult [PNum b, PVar x], PMult [PNum a, PVar x, PVar x]])) x"
proof (cases "a = 0")
  case True
  with b have b: "0 \<le> b" by auto
  show ?thesis using b True
    by (simp add: b True extract_def poly_add.simps eq_monom.simps poly_mult.simps monom_mult_poly.simps monom_mult.simps poly_subst.simps monom_subst.simps poly_power.simps one_poly_def zero_poly_def check_poly_ge.simps check_poly_weak_mono_discrete_def, auto)
next
  case False
  show ?thesis using False a b
    by (simp add: b False extract_def poly_add.simps eq_monom.simps poly_mult.simps monom_mult_poly.simps monom_mult.simps poly_subst.simps monom_subst.simps poly_power.simps one_poly_def zero_poly_def check_poly_ge.simps check_poly_weak_mono_discrete_def, auto)
qed


end
