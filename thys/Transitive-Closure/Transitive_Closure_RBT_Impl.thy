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

header {* Closure computation via red black trees *}

theory Transitive_Closure_RBT_Impl
imports Transitive_Closure_Impl RBT_Map_Set_Extension
begin

text {*
\label{closure rbt}
We provide two algorithms to compute the reflexive transitive closure which
internally work on red black trees. Therefore, the carrier has to be linear
ordered.  The first one (@{term rtrancl_rbt_impl}) computes the closure on
demand for a given set of initial states.  The second one (@{term
memo_rbt_rtrancl}) precomputes the closure for each individual state, stores
these results, and then only does a look-up.

For the transitive closure there are the corresponding algorithms @{term
trancl_rbt_impl} and @{term memo_rbt_trancl}
*}

subsection {* Computing closures from sets on-the-fly *} 

text {*
The algorithms are based on the generic algorithms @{const rtrancl_impl} and
@{const trancl_impl} using red black trees. To compute the successors
efficiently, all successors of a state are collected and stored in a red black
tree map by using @{const elem_list_to_rm}.  Then, to lift the successor
relation for single states to lists of states, all results are united using
@{const rs_Union}. The rest is standard. 
*} 

interpretation set_access "\<lambda> as bs. rs_union bs (list_to_rs as)" rs_\<alpha> rs_memb rs_empty
  by (unfold_locales, auto simp: rs_correct)

abbreviation rm_succ :: "('a :: linorder \<times> 'a)list \<Rightarrow> 'a list \<Rightarrow> 'a list" where "rm_succ \<equiv> (\<lambda> rel. let rm = elem_list_to_rm fst rel in
  (\<lambda> as. rs_to_list (rs_Union (map (\<lambda> a. list_to_rs (map snd (rm_set_lookup rm a))) as))))"

definition rtrancl_rbt_impl :: "('a :: linorder \<times> 'a)list \<Rightarrow> 'a list \<Rightarrow> 'a rs"
  where "rtrancl_rbt_impl \<equiv> rtrancl_impl rm_succ
  (\<lambda> as bs. rs_union bs (list_to_rs as)) rs_memb rs_empty" 

definition trancl_rbt_impl :: "('a :: linorder \<times> 'a)list \<Rightarrow> 'a list \<Rightarrow> 'a rs"
  where "trancl_rbt_impl \<equiv> trancl_impl rm_succ
  (\<lambda> as bs. rs_union bs (list_to_rs as)) rs_memb rs_empty" 

lemma rtrancl_rbt_impl: "rs_\<alpha> (rtrancl_rbt_impl rel as) = {b. \<exists> a \<in> set as. (a,b) \<in> (set rel)^*}"
  unfolding rtrancl_rbt_impl_def
  by (rule set_access_gen.rtrancl_impl, unfold_locales, unfold Let_def, simp add: rs_correct elem_list_to_rm.rm_set_lookup, force)

lemma trancl_rbt_impl: "rs_\<alpha> (trancl_rbt_impl rel as) = {b. \<exists> a \<in> set as. (a,b) \<in> (set rel)^+}"
  unfolding trancl_rbt_impl_def
  by (rule set_access_gen.trancl_impl, unfold_locales, unfold Let_def, simp add: rs_correct elem_list_to_rm.rm_set_lookup, force)

subsection {* Precomputing closures for single states *}

text {* Storing all relevant entries is done by mapping all left-hand sides of the relation
  to their closure. Since we assume a linear order on the carrier,
  for the lookup we can use maps that are implemented as red black trees.
*}

definition memo_rbt_rtrancl :: "('a :: linorder \<times> 'a)list \<Rightarrow> ('a \<Rightarrow> 'a rs)" 
where "memo_rbt_rtrancl rel \<equiv> let tr = rtrancl_rbt_impl rel;
                               rm = list_to_rm (map (\<lambda> a. (a,tr [a])) ((rs_to_list o list_to_rs o map fst) rel))
                             in (\<lambda> a. case rm_lookup a rm of None \<Rightarrow> list_to_rs [a] | Some as \<Rightarrow> as)"

lemma memo_rbt_rtrancl:
  "rs_\<alpha> (memo_rbt_rtrancl rel a) = {b. (a,b) \<in> (set rel)^*}" (is "?l = ?r")
proof -
  let ?rm = "list_to_rm (map (\<lambda> a. (a, rtrancl_rbt_impl rel [a])) ((rs_to_list o list_to_rs o map fst) rel))"
  show ?thesis
  proof (cases "rm_lookup a ?rm")
    case None
    have one: "?l = {a}"
      unfolding memo_rbt_rtrancl_def Let_def None
      by (simp add: rs_correct)
    from None[unfolded rm.lookup_correct[OF TrueI], simplified rm_correct map_of_eq_None_iff]
    have a: "a \<notin> fst ` set rel" by (simp add: rs_correct, force)
    {
      fix b
      assume "b \<in> ?r"
      from this[unfolded rtrancl_power rel_pow_fun_conv] obtain n f where 
        ab: "f 0 = a \<and> f n = b" and steps: "\<And> i. i < n \<Longrightarrow> (f i, f (Suc i)) \<in> set rel" by auto
      from ab steps[of 0] a have "b = a" 
        by (cases n, force+)
    }
    hence "?r = {a}" by auto
    thus ?thesis unfolding one by simp
  next
    case (Some as) 
    have as: "rs_\<alpha> as = {b. (a,b) \<in> (set rel)^*}"
      using map_of_SomeD[OF Some[unfolded rm.lookup_correct[OF TrueI], simplified rm_correct]]
        rtrancl_rbt_impl[of rel "[a]"] by force
    thus ?thesis unfolding memo_rbt_rtrancl_def Let_def Some by simp
  qed
qed


definition memo_rbt_trancl :: "('a :: linorder \<times> 'a)list \<Rightarrow> ('a \<Rightarrow> 'a rs)" 
where "memo_rbt_trancl rel \<equiv> let tr = trancl_rbt_impl rel;
                               rm = list_to_rm (map (\<lambda> a. (a,tr [a])) ((rs_to_list o list_to_rs o map fst) rel))
                             in (\<lambda> a. case rm_lookup a rm of None \<Rightarrow> rs_empty | Some as \<Rightarrow> as)"

lemma memo_rbt_trancl:
  "rs_\<alpha> (memo_rbt_trancl rel a) = {b. (a,b) \<in> (set rel)^+}" (is "?l = ?r")
proof -
  let ?rm = "list_to_rm (map (\<lambda> a. (a, trancl_rbt_impl rel [a])) ((rs_to_list o list_to_rs o map fst) rel))"
  show ?thesis
  proof (cases "rm_lookup a ?rm")
    case None
    have one: "?l = {}"
      unfolding memo_rbt_trancl_def Let_def None
      by (simp add: rs_correct)
    from None[unfolded rm.lookup_correct[OF TrueI], simplified rm_correct map_of_eq_None_iff]
    have a: "a \<notin> fst ` set rel" by (simp add: rs_correct, force)
    {
      fix b
      assume "b \<in> ?r"
      from this[unfolded trancl_unfold_left] a have False by force
    }
    hence "?r = {}" by auto
    thus ?thesis unfolding one by simp
  next
    case (Some as) 
    have as: "rs_\<alpha> as = {b. (a,b) \<in> (set rel)^+}"
      using map_of_SomeD[OF Some[unfolded rm.lookup_correct[OF TrueI], simplified rm_correct]]
        trancl_rbt_impl[of rel "[a]"] by force
    thus ?thesis unfolding memo_rbt_trancl_def Let_def Some by simp
  qed
qed


end
