(*  Title:       Executable Matrix-Operations with Arbitrary Dimension
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
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


text {* some obvious lemma about replicate*}
lemma replicate_prop: assumes "p x"
  shows "\<forall> y \<in> set (replicate n x). p y"
using assms by (induct n, auto)

text {* the infinite pigeon hole principle: if you put infinite things into n buckets,
  then there is one bucket i < n which contains infinitely many things *}

lemma inf_pigeon_hole_principle : assumes "\<forall> k :: nat. \<exists> i < n :: nat. f k i"
  shows "\<exists> i < n. \<forall> k. \<exists> k' \<ge> k. f k' i"
using assms 
proof (induct n arbitrary: f, simp)
  case (Suc n)
  show ?case
  proof (cases "\<forall> k. \<exists> k' \<ge> k. f k' n")
    case True
    thus ?thesis by auto
  next
    case False
    then obtain k where k: "\<forall> k' \<ge> k. \<not> f k' n" by auto
    let ?f = "\<lambda> k' i. f (k + k') i"
    have n: "\<forall> k'. \<exists> i < n. ?f k' i"
    proof
      fix k'
      have k': "k + k' \<ge> k" by simp
      from mp[OF spec[OF k] k'] have notN: "\<not> ?f k' n" by auto
      from spec[OF Suc(2), of "k + k'"] obtain i where i: "i < Suc n" and f:  "?f k' i"
        by auto
      with notN have "i \<noteq> n" by auto 
      with i have "i < n" by auto
      with f show "\<exists> i < n. ?f k' i" by auto
    qed
    from Suc(1)[OF n] obtain i where i: "i < n" and f: "\<forall> l. \<exists> k' \<ge> l. ?f k' i" by auto
    hence i: "i < Suc n" by auto
    show ?thesis
    proof (rule exI[of _ i], simp add: i, intro allI)
      fix l
      from spec[OF f, of l] obtain k' where k': "(k' :: nat) \<ge> l" and f: "f (k + k') i" by auto
      from k' have "k + k' \<ge> l" by simp
      with f show "\<exists> k' \<ge> l. f k' i" by auto
    qed
  qed
qed


end
