(*  Title:       Executable Transitive Closures of Finite Relations
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)

(*
Copyright 2011 Christian Sternagel, René Thiemann

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

header {* A generic work-list algorithm *}

theory Transitive_Closure_Impl
imports Main
begin

text {*
\label{closure generic}
  Let $R$ be some finite relation.

  We start to present a standard work-list algorithm to compute all elements
  that are reachable from some initial set by at most $n$ $R$-steps.  Then, we
  obtain algorithms for the (reflexive) transitive closure from a given starting
  set by exploiting the fact that for finite relations we have to iterate at
  most $|R|$ times. The presented algorithms are generic in the sense that the
  underlying data structure can freely be chosen, you just have to provide
  certain operations like union, membership, etc.
*}

subsection {* Bounded reachability *} 

text {*
  We provide an algorithm @{text relpow_impl} that computes all states that are
  reachable from an initial set of states @{term new} by at most $n$ steps.  The
  algorithm also stores a set of states that have already been visited @{term
  have}, and thus, do not have to be expanded a second time.  The algorithm is
  parametric in the underlying data structure, it just requires operations for
  union and membership as well as a function to compute the successors of a
  list.
*}
fun
  relpow_impl ::
    "('a list \<Rightarrow> 'a list) \<Rightarrow> ('a list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)
      \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> 'b"
where
  "relpow_impl succ un memb new have 0 = un new have"
| "relpow_impl succ un memb new have (Suc m) = (if new = [] then have else (
  let maybe = succ new;
    have' = un new have;
    new' = filter (\<lambda> n. \<not> (memb n have')) maybe
      in relpow_impl succ un memb new' have' m))"

text {*
  Before we can prove what @{const relpow_impl} computes, we need the following
  auxiliary lemma that makes all elements in a sequence $a \mathrel{R} \ldots \mathrel{R} b$ 
  of length $n$ accessible.
*}

lemma relpow_fun_conv:
  "((a,b) \<in> R ^^ n) = (\<exists>f. f 0 = a \<and> f n = b \<and> (\<forall>i < n. (f i, f (Suc i)) \<in> R))"
proof (induct n arbitrary: b)
  case 0
  show ?case by auto
next
  case (Suc n)
  show ?case 
  proof (simp add: relpow.simps relcomp_unfold Suc) 
    show "(\<exists> y. (\<exists> f. f 0 = a \<and> f n = y \<and> (\<forall> i < n. (f i, f (Suc i)) \<in> R)) \<and> (y,b) \<in> R) = (\<exists> f. f 0 = a \<and> f (Suc n) = b \<and> (\<forall>i < Suc n. (f i, f (Suc i)) \<in> R))" (is "?l = ?r")
    proof
      assume ?l
      then obtain c f where a: "f 0 = a" and c: "f n = c" and R: "\<And> i. i < n \<Longrightarrow> (f i, f (Suc i)) \<in> R" and cb: "(c,b) \<in> R" by auto
      let ?g = "\<lambda> m. if m = Suc n then b else f m"
      show ?r
        by (rule exI[of _ ?g], simp add: a c cb R)
    next
      assume ?r
      then obtain f where a: "f 0 = a" and b: "b = f (Suc n)" and R: "\<And> i. i < Suc n \<Longrightarrow> (f i, f (Suc i)) \<in> R" by auto
      show ?l
        by (rule exI[of _ "f n"], rule conjI, rule exI[of _ f], insert a b R, auto)
    qed
  qed
qed

text {* Moreover we need to know that the provided union, membership, \ldots{}
operations behave correctly *}

locale set_access =
  fixes un :: "'a list \<Rightarrow> 'b \<Rightarrow> 'b"
    and set_of :: "'b \<Rightarrow> 'a set"
    and memb :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
    and empty :: 'b
  assumes un: "set_of (un as bs) = set as \<union> set_of bs"
    and memb: "memb a bs = (a \<in> set_of bs)"
    and empty: "set_of empty = {}"

locale set_access_succ = set_access un 
  for un :: "'a list \<Rightarrow> 'b \<Rightarrow> 'b" +
  fixes succ :: "'a list \<Rightarrow> 'a list"
   and  rel :: "('a \<times> 'a) set"
  assumes succ: "set (succ as) = {b. \<exists> a \<in> set as. (a,b) \<in> rel}"
begin

abbreviation relpow_i where "relpow_i \<equiv> relpow_impl succ un memb"

text {* What follows is the main technical result of the @{const relpow_impl}
algorithm: what it computes for arbitrary values of @{term new} and @{term
have}. *}

lemma relpow_impl_main: 
  "set_of (relpow_i new have n) = 
  {b | a b m. a \<in> set new \<and> m \<le> n \<and> (a,b) \<in> (rel  \<inter> {(a,b). b \<notin> set_of have})^^m} \<union> set_of have " 
  (is "?l new have n = ?r new have n")
proof (induct n arbitrary: "have" new)
  case 0
  thus ?case by (auto simp: un)
next
  case (Suc n hhave nnew)
  show ?case
  proof (cases "nnew = []")
    case True
    show ?thesis unfolding True by auto
  next
    case False
    let ?have = "set_of hhave"
    let ?new = "set nnew"
    obtain "have" new where hav: "have = ?have" and new: "new = ?new" by auto
    let ?reln = "\<lambda> m. (rel \<inter> {(a, b). b \<notin> new \<and> b \<notin> have}) ^^  m"
    let ?rel = "\<lambda> m. (rel \<inter> {(a, b). b \<notin> have}) ^^  m"
    have idl: "?l nnew hhave (Suc n) = 
      {uu. \<exists>a. (\<exists>aa\<in> new. (aa,a) \<in> rel) \<and>
         a \<notin> new \<and> a \<notin> have \<and> (\<exists>m \<le> n. (a, uu)
                \<in> ?reln m)} \<union>
    (new \<union> have)" (is "_ = ?l1 \<union> (?l2 \<union> ?l3)")
      by (simp add: hav new False Let_def Suc, simp add: memb un succ)
    let ?l = "?l1 \<union> (?l2 \<union> ?l3)"
    have idr: "?r nnew hhave (Suc n) = {b. \<exists> a m. a \<in> new \<and> m \<le> Suc n \<and> (a,b) \<in> ?rel m} \<union> have" (is "_ = (?r1 \<union> ?r2)") by (simp add: hav new)
    let ?r = "?r1 \<union> ?r2"
    {
      fix b
      assume b: "b \<in> ?l"      
      have "b \<in> ?r" 
      proof (cases "b \<in> new \<or> b \<in> have")
        case True thus ?thesis 
        proof
          assume "b \<in> have" thus ?thesis by auto
        next
          assume b: "b \<in> new"
          have "b \<in> ?r1"
            by (intro CollectI, rule exI, rule exI[of _ 0], intro conjI, rule b, auto)
          thus ?thesis by auto
        qed
      next
        case False
        with b have "b \<in> ?l1" by auto
        then obtain a2 a1 m where a2n: "a2 \<notin> new" and a2h: "a2 \<notin> have" and a1: "a1 \<in> new" and a1a2: "(a1,a2) \<in> rel"
          and m: "m \<le> n" and a2b: "(a2,b) \<in> ?reln m" by auto
        have "b \<in> ?r1"
          by (rule CollectI, rule exI, rule exI[of _ "Suc m"], intro conjI, rule a1, simp add: m, rule relpow_Suc_I2, rule, rule a1a2, simp add: a2h, insert a2b, induct m arbitrary: a2 b, auto)
        thus ?thesis by auto
      qed
    }     
    moreover
    { 
      fix b
      assume b: "b \<in> ?r"
      hence "b \<in> ?l" 
      proof (cases "b \<in> have")
        case True thus ?thesis by auto
      next
        case False
        with b have "b \<in> ?r1" by auto
        then obtain a m where a: "a \<in> new" and m: "m \<le> Suc n" and ab: "(a,b) \<in> ?rel m" by auto
        have seq: "\<exists> a \<in> new. (a,b) \<in> ?rel m"
          using a  ab by auto
        obtain l where l: "l = (LEAST m. (\<exists> a \<in> new. (a,b) \<in> ?rel m))" by auto
        have least: "(\<exists> a \<in> new. (a,b) \<in> ?rel l)"
          by (unfold l, rule LeastI, rule seq)
        have lm: "l \<le> m" unfolding l
          by (rule Least_le, rule seq)
        with m have ln: "l \<le> Suc n" by auto
        from least obtain a where a: "a \<in> new"
          and ab: "(a,b) \<in> ?rel l" by auto
        from ab[unfolded relpow_fun_conv]
        obtain f where fa: "f 0 = a" and fb: "b = f l"
          and steps: "\<And> i. i < l \<Longrightarrow> (f i, f (Suc i)) \<in> ?rel 1" by auto
        {
          fix i
          assume i: "i < l"
          have main: "f (Suc i) \<notin> new" 
          proof
            assume new: "f (Suc i) \<in> new"
            let ?f = "\<lambda> j. f (Suc i + j)"
            have seq: "(f (Suc i), b) \<in> ?rel (l - Suc i)"
              unfolding relpow_fun_conv
            proof (rule exI[of _ ?f], intro conjI allI impI)
              from i show "f (Suc i + (l - Suc i)) = b"
                unfolding fb by auto
            next
              fix j
              assume "j < l - Suc i"
              hence small: "Suc i + j < l" by auto
              show "(?f j, ?f (Suc j)) \<in> rel \<inter> {(a,b). b \<notin> have}" using steps[OF small] by auto
            qed simp
            from i have small: "l - Suc i < l" by auto
            from seq new have "\<exists> a \<in> new. (a,b) \<in> ?rel (l - Suc i)"  by auto
            with not_less_Least[OF small[unfolded l]]
            show False unfolding l by auto
          qed
          hence "(f i, f (Suc i)) \<in> ?reln 1"
            using steps[OF i] by auto
        } note steps = this
        have ab: "(a,b) \<in> ?reln l" unfolding relpow_fun_conv
          by (intro exI conjI, insert fa fb steps, auto)
        have "b \<in> ?l1 \<union> ?l2" 
        proof (cases l)
          case 0
          with ab a show ?thesis by auto
        next
          case (Suc ll)
          from relpow_Suc_D2[OF ab[unfolded Suc]] a ln Suc 
          show ?thesis by auto
        qed
        thus ?thesis by auto
      qed
    }
    ultimately show ?thesis
      unfolding idl idr by blast
  qed
qed

text {* From the previous lemma we can directly derive that @{const relpow_impl}
  works correctly if @{term have} is initially set to @{text empty}
*}
lemma relpow_impl: "set_of (relpow_i new empty n) = 
  {b | a b m. a \<in> set new \<and> m \<le> n \<and> (a,b) \<in> rel^^m}" 
proof -
  have id: "rel \<inter> {(a,b). True} = rel" by auto
  show ?thesis
  unfolding relpow_impl_main empty by (simp add: id)
qed
end

subsection {* Reflexive transitive closure and transitive closure *}

text {* Using @{const relpow_impl} it is now easy to obtain algorithms for the
reflexive transitive closure and the transitive closure by restricting the
number of steps to $|R|$. Note that @{const relpow_impl} will abort the
computation as soon as no new states are detected.  Hence, there is no penalty
in using this large bound.  *}

definition rtrancl_impl :: "(('a \<times> 'a)list \<Rightarrow> 'a list \<Rightarrow> 'a list) \<Rightarrow> ('a list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> ('a \<times> 'a)list \<Rightarrow> 'a list \<Rightarrow> 'b"
  where "rtrancl_impl gen_succ un memb emp rel \<equiv> 
              let succ = gen_succ rel;
                  n = length rel
               in (\<lambda> as. relpow_impl succ un memb as emp n)"

definition trancl_impl :: "(('a \<times> 'a)list \<Rightarrow> 'a list \<Rightarrow> 'a list) \<Rightarrow> ('a list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> ('a \<times> 'a)list \<Rightarrow> 'a list \<Rightarrow> 'b"
  where "trancl_impl gen_succ un memb emp rel \<equiv> 
              let succ = gen_succ rel;
                  n = length rel
               in (\<lambda> as. relpow_impl succ un memb (succ as) emp n)"

text {* The soundness of both @{const rtrancl_impl} and @{const trancl_impl}
follows from the soundness of @{const relpow_impl} and the fact that for finite
relations, we can limit the number of steps to explore all elements in the
reflexive transitive closure. *}

lemma rtrancl_finite_relpow: "((a,b) \<in> (set rel)^*) = (\<exists> n \<le> length rel. (a,b) \<in> set rel ^^ n)" (is "?l = ?r")
proof
  assume ?r
  thus ?l
    unfolding rtrancl_power by auto
next
  assume ?l
  from this[unfolded rtrancl_power]
  obtain n where ab: "(a,b) \<in> set rel ^^ n" ..
  obtain l where l: "l = (LEAST n. (a,b) \<in> set rel ^^ n)" by auto
  have ab: "(a,b) \<in> set rel ^^ l" unfolding l
    by (intro LeastI, rule ab)
  from this[unfolded relpow_fun_conv]
  obtain f where a: "f 0 = a" and b: "f l = b" and steps: "\<And> i. i < l \<Longrightarrow> (f i, f (Suc i)) \<in> set rel" by auto
  let ?hits = "map (\<lambda> i. f (Suc i)) [0 ..< l]"
  from steps have subset: "set ?hits \<subseteq> snd ` set rel" by force
  have "l \<le> length rel"
  proof (cases "distinct ?hits")
    case True
    have "l = length ?hits" by simp
    also have "... = card (set ?hits)" unfolding distinct_card[OF True] ..
    also have "... \<le> card (snd ` set rel)" by (rule card_mono[OF _ subset], auto)
    also have "... = card (set (map snd rel))" by auto
    also have "... \<le> length (map snd rel)" by (rule card_length)
    finally  show ?thesis by simp
  next
    case False
    from this[unfolded distinct_conv_nth]
    obtain i j where i: "i < l" and j: "j < l" and ij: "i \<noteq> j" and fij: "f (Suc i) = f (Suc j)" by auto
    let ?i = "min i j"
    let ?j = "max i j"
    have i: "?i < l" and j: "?j < l" and fij: "f (Suc ?i) = f (Suc ?j)" 
      and ij: "?i < ?j"
      using i j ij fij unfolding min_def max_def by (cases "i \<le> j", auto)
    from i j fij ij obtain i j where i: "i < l" and j: "j < l" and ij: "i < j" and fij: "f (Suc i) = f (Suc j)" by blast
    let ?g = "\<lambda> n. if n \<le> i then f n else f (n + (j - i))"
    let ?l = "l - (j - i)"
    have abl: "(a,b) \<in> set rel ^^ ?l"
      unfolding relpow_fun_conv
    proof (rule exI[of _ ?g], intro conjI impI allI)
      show "?g ?l = b" unfolding b[symmetric] using j ij by auto
    next
      fix k
      assume k: "k < ?l"
      show "(?g k, ?g (Suc k)) \<in> set rel" 
      proof (cases "k < i")
        case True
        with i have "k < l" by auto
        from steps[OF this] show ?thesis using True by simp
      next
        case False
        hence ik: "i \<le> k" by auto
        show ?thesis
        proof (cases "k = i")
          case True
          thus ?thesis using ij fij steps[OF i] by simp
        next
          case False
          with ik have ik: "i < k" by auto
          hence small: "k + (j - i) < l" using k by auto
          show ?thesis using steps[OF small] ik by auto
        qed
      qed
    qed (simp add: a)
    from ij i have ll: "?l < l" by auto
    have "l \<le> ?l" unfolding l
      by (rule Least_le, rule abl[unfolded l])
    with ll have False by simp
    thus ?thesis by simp
  qed
  with ab show ?r by auto
qed



locale set_access_gen = set_access un
  for un :: "'a list \<Rightarrow> 'b \<Rightarrow> 'b" +
  fixes gen_succ :: "(('a \<times> 'a)list \<Rightarrow> 'a list \<Rightarrow> 'a list)"
  assumes gen_succ: "set(gen_succ rel as) = {b. \<exists> a \<in> set as. (a,b) \<in> set rel}"
begin

abbreviation rtrancl_i where "rtrancl_i \<equiv> rtrancl_impl gen_succ un memb empty"
abbreviation trancl_i where "trancl_i \<equiv> trancl_impl gen_succ un memb empty"

lemma rtrancl_impl: "set_of (rtrancl_i rel as) = {b. (\<exists> a \<in> set as. (a,b) \<in> (set rel)^*)}"
proof -
  interpret set_access_succ set_of memb empty un "gen_succ rel" "set rel"
    by (unfold_locales, insert gen_succ, auto)
  show ?thesis unfolding rtrancl_impl_def Let_def relpow_impl
    by (auto simp: rtrancl_finite_relpow)
qed

lemma trancl_impl: "set_of (trancl_i rel as) = {b. (\<exists> a \<in> set as. (a,b) \<in> (set rel)^+)}"
proof -
  interpret set_access_succ set_of memb empty un "gen_succ rel" "set rel"
    by (unfold_locales, insert gen_succ, auto)
  show ?thesis unfolding trancl_impl_def Let_def relpow_impl trancl_unfold_left relcomp_unfold rtrancl_finite_relpow succ by auto
qed
end

end
