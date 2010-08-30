(*  Title:       Executable multivariate polynomials
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:	 LGPL
*)

(*
Copyright 2010 Christian Sternagel, René Thiemann

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


header {* Util *}

theory Util
imports Main 
begin

text {* This theory contains small auxiliary lemmas which are
        not only useful for the formalization of matrices
     *}



text {* Extract: a function to extract some element out of a list that satisfies
some predicate. Moreover, the remaining elements before and after the 
specific elements are also returned *}

fun "extract" :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a \<times> 'a list)option"
where "extract p [] = None"
  |   "extract p (x # xs) = (if p x then Some ([], x, xs) else 
                                case extract p xs of
                                   None \<Rightarrow> None
                                 | Some (ys,y,zs) \<Rightarrow> Some (x # ys, y, zs))"


lemma extract_None: "extract p xs = None \<Longrightarrow> \<forall> x \<in> set xs. \<not> p x"
proof (induct xs, simp)
  case (Cons x xs)
  show ?case 
  proof (cases "p x")
    case True
    hence False using Cons(2) by simp
    thus ?thesis ..
  next
    case False
    with Cons show ?thesis by (cases "extract p xs", auto)
  qed
qed

lemma extract_Some: assumes "extract p xs = Some (ys, y, zs)" 
  shows "xs = ys @ y # zs \<and> p y"
using assms
proof (induct xs arbitrary: ys, simp)
  case (Cons x xs)
  show ?case 
  proof (cases "p x")
    case True
    thus ?thesis using Cons(2) by auto
  next
    case False
    show ?thesis 
    proof (cases "extract p xs")
      case None
      with Cons(2) False show ?thesis by simp
    next
      case (Some res)
      with False Cons(2) obtain us where rec: "extract p xs = Some (us, y, zs)" and ys: "ys = x # us" by (cases res, auto)
      from Cons(1)[OF rec] ys show ?thesis by simp        
    qed
  qed
qed

text {* 
distinct\_eq: a more generic version of distinct which uses an equality function as parameter 
*}

primrec distinct_eq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where "distinct_eq _ [] \<longleftrightarrow> True"
  |   "distinct_eq eq (x # xs) \<longleftrightarrow> (\<forall>y \<in> set xs. \<not> eq y x) \<and> distinct_eq eq xs"

lemma distinct_eq_append:
  "distinct_eq eq (xs @ ys) \<longleftrightarrow> distinct_eq eq xs \<and> distinct_eq eq ys
    \<and> (\<forall>x \<in> set xs. \<forall>y \<in> set ys. \<not> eq y x)"
  by (induct xs) auto

end
