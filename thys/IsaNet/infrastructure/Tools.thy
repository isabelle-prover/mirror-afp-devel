(*******************************************************************************
 
  Project: IsaNet

  Author:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022 Tobias Klenze
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)

*******************************************************************************)

section\<open>Tools\<close>
theory Tools imports Main "HOL-Library.Sublist"
begin

(******************************************************************************)
subsection \<open> Prefixes, suffixes, and fragments \<close>
(******************************************************************************)


thm Cons_eq_appendI (*similar to*)
lemma prefix_cons: "\<lbrakk>prefix xs ys; zs = x # ys; prefix xs' (x # xs)\<rbrakk> \<Longrightarrow> prefix xs' zs" 
  by (auto simp add: prefix_def Cons_eq_appendI)

lemma suffix_nonempty_extendable:
  "\<lbrakk>suffix xs l; xs \<noteq> l\<rbrakk> \<Longrightarrow> \<exists> x . suffix (x#xs) l"
apply (auto simp add: suffix_def)
  by (metis append_butlast_last_id)

lemma set_suffix:
  "\<lbrakk>x \<in> set l'; suffix l' l\<rbrakk> \<Longrightarrow> x \<in> set l"
by (auto simp add: suffix_def)

lemma set_prefix:
  "\<lbrakk>x \<in> set l'; prefix l' l\<rbrakk> \<Longrightarrow> x \<in> set l"
by (auto simp add: prefix_def)

lemma set_suffix_elem: "suffix (x#xs) p \<Longrightarrow> x \<in> set p"
  by (meson list.set_intros(1) set_suffix)

lemma set_prefix_elem: "prefix (x#xs) p \<Longrightarrow> x \<in> set p"
  by (meson list.set_intros(1) set_prefix)

lemma Cons_suffix_set: "x \<in> set y \<Longrightarrow> \<exists> xs . suffix (x#xs) y"
  using suffix_def  by (metis split_list)

(******************************************************************************)
subsection \<open> Fragments \<close>
(******************************************************************************)

definition fragment :: "'a list \<Rightarrow> 'a list set \<Rightarrow> bool"
  where "fragment xs St \<longleftrightarrow> (\<exists>zs1 zs2. zs1 @ xs @ zs2 \<in> St)"

lemma fragmentI: "\<lbrakk> zs1 @ xs @ zs2 \<in> St \<rbrakk> \<Longrightarrow> fragment xs St"
by (auto simp add: fragment_def)

lemma fragmentE [elim]: "\<lbrakk>fragment xs St; \<And>zs1 zs2. \<lbrakk> zs1 @ xs @ zs2 \<in> St \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by (auto simp add: fragment_def)

lemma fragment_Nil [simp]: "fragment [] St \<longleftrightarrow> St \<noteq> {}"  
by (force simp add: fragment_def dest: spec [where x="[]"])

lemma fragment_subset: "\<lbrakk>St \<subseteq> St'; fragment l St\<rbrakk> \<Longrightarrow> fragment l St'"
by(auto simp add: fragment_def)

lemma fragment_prefix: "\<lbrakk>prefix l' l; fragment l St\<rbrakk> \<Longrightarrow> fragment l' St"
by(auto simp add: fragment_def prefix_def) blast

lemma fragment_suffix: "\<lbrakk>suffix l' l; fragment l St\<rbrakk> \<Longrightarrow> fragment l' St"
by(auto simp add: fragment_def suffix_def)
  (metis append.assoc)

lemma fragment_self [simp, intro]: "\<lbrakk>l \<in> St\<rbrakk> \<Longrightarrow> fragment l St"
by(auto simp add: fragment_def intro!: exI [where x="[]"])

lemma fragment_prefix_self [simp, intro]:
  "\<lbrakk>l \<in> St; prefix l' l\<rbrakk> \<Longrightarrow> fragment l' St"
using fragment_prefix fragment_self by blast

lemma fragment_suffix_self [simp, intro]:
  "\<lbrakk>l \<in> St; suffix l' l\<rbrakk> \<Longrightarrow> fragment l' St"
using fragment_suffix fragment_self by metis

lemma fragment_is_prefix_suffix:
  "fragment l St \<Longrightarrow> \<exists>pre suff . prefix l pre \<and> suffix pre suff \<and> suff \<in> St"
  by (meson fragment_def prefixI suffixI)


(******************************************************************************)
subsection \<open> Pair Fragments \<close>
(******************************************************************************)

definition pfragment :: "'a \<Rightarrow> ('b list) \<Rightarrow> ('a \<times> ('b list)) set \<Rightarrow> bool"
  where "pfragment a xs St \<longleftrightarrow> (\<exists>zs1 zs2. (a, zs1 @ xs @ zs2) \<in> St)"

lemma pfragmentI: "\<lbrakk> (ainf, zs1 @ xs @ zs2) \<in> St \<rbrakk> \<Longrightarrow> pfragment ainf xs St"
by (auto simp add: pfragment_def)

lemma pfragmentE [elim]: "\<lbrakk>pfragment ainf xs St; \<And>zs1 zs2. \<lbrakk> (ainf, zs1 @ xs @ zs2) \<in> St \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by (auto simp add: pfragment_def)

lemma pfragment_prefix:
  "pfragment ainf (xs @ ys) St \<Longrightarrow> pfragment ainf xs St"
  by(auto simp add: pfragment_def)

lemma pfragment_prefix':
  "\<lbrakk>pfragment ainf ys St; prefix xs ys\<rbrakk> \<Longrightarrow> pfragment ainf xs St"
  by(auto 3 4 simp add: pfragment_def prefix_def)

lemma pfragment_suffix: "\<lbrakk>suffix l' l; pfragment ainf l St\<rbrakk> \<Longrightarrow> pfragment ainf l' St"
  by(auto simp add: pfragment_def suffix_def)
  (metis append.assoc)

lemma pfragment_self [simp, intro]: "\<lbrakk>(ainf, l) \<in> St\<rbrakk> \<Longrightarrow> pfragment ainf l St"
by(auto simp add: pfragment_def intro!: exI [where x="[]"])

lemma pfragment_suffix_self [simp, intro]:
  "\<lbrakk>(ainf, l) \<in> St; suffix l' l\<rbrakk> \<Longrightarrow> pfragment ainf l' St"
using pfragment_suffix pfragment_self by metis


lemma pfragment_self_eq:
"\<lbrakk>pfragment ainf l S; \<And>zs1 zs2 . (ainf, zs1@l@zs2) \<in> S \<Longrightarrow> (ainf, zs1@l'@zs2) \<in> S\<rbrakk> \<Longrightarrow> pfragment ainf l' S"
  by(auto simp add: pfragment_def)

lemma pfragment_self_eq_nil:
"\<lbrakk>pfragment ainf l S; \<And>zs1 zs2 . (ainf, zs1@l@zs2) \<in> S \<Longrightarrow> (ainf, l'@zs2) \<in> S\<rbrakk> \<Longrightarrow> pfragment ainf l' S"
  apply(auto simp add: pfragment_def)
  apply(rule exI[of _ "[]"])
  by auto

lemma pfragment_cons: "pfragment ainfo (x # fut) S \<Longrightarrow> pfragment ainfo fut S"
  apply(auto 3 4 simp add: pfragment_def)
  subgoal for zs1 zs2
  apply(rule exI[of _ "zs1@[x]"])
    by auto
  done

(******************************************************************************)
subsection \<open> Head and Tails \<close>
(******************************************************************************)

fun head where "head [] = None" | "head (x#xs) = Some x"
fun ifhead where "ifhead [] n = n" | "ifhead (x#xs) _ = Some x"
fun tail where "tail [] = None" | "tail xs = Some (last xs)"

lemma head_cons: "xs \<noteq> [] \<Longrightarrow> head xs = Some (hd xs)" by(cases xs, auto)
lemma tail_cons: "xs \<noteq> [] \<Longrightarrow> tail xs = Some (last xs)" by(cases xs, auto)
lemma tail_snoc: "tail (xs @ [x]) = Some x" by(cases xs, auto)
lemma "\<forall>y ys . l \<noteq> ys @ [y] \<Longrightarrow> l = []" 
  using rev_exhaust by blast


lemma tl_append2: "tl (pref @ [a, b]) = tl (pref @ [a])@[b]"
  by(induction pref, auto)


end
