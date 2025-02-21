(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : The notion of processes
 *
 * Copyright (c) 2009 Université Paris-Sud, France
 * Copyright (c) 2025 Université Paris-Saclay, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************\<close>
(*>*)

chapter\<open>The Notion of Processes\<close>

text\<open>As mentioned earlier, we base the theory of CSP on HOLCF, a Isabelle/HOL library
providing a theory of continuous functions, fixpoint induction and recursion.\<close>

(*<*)
theory Process
  imports HOLCF "HOL-Library.Prefix_Order" "HOL-Eisbach.Eisbach"
begin
  (*>*)

text\<open>HOLCF sets the default type class to @{class cpo}, while our 
Process theory establishes links between standard types and @{class pcpo} 
types. Consequently, we reset the default type class to the default in HOL.\<close>

default_sort type

section\<open>Pre-Requisite: Basic Traces and tick-Freeness\<close>

text\<open>The denotational semantics of CSP assumes a distinguishable
special event, called \verb+tick+ and written $\checkmark$, that is required
to occur only in the end of traces in order to signalize successful termination of
a process. (In the original text of Hoare, this treatment was more
liberal and lead to foundational problems: the process invariant
could not be established for the sequential composition operator
of CSP; see \<^cite>\<open>"tej.ea:corrected:1997"\<close> for details.)\<close>

text \<open>From the Isabelle-2025 version on, the classical constant tick (\<open>\<checkmark>\<close>) of the CSP theory
      has been replaced by a parameterized version carrying a kind of return value.\<close>

datatype ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k =
    is_ev   : ev   (of_ev   : 'a)
  | is_tick : tick (of_tick : 'r) (\<open>\<checkmark>'(_')\<close>)


text \<open>This type \<^typ>\<open>('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> is of course isomorphic to the sum type \<^typ>\<open>'a + 'r\<close>.\<close>
text \<open>``ptick'' stands for parameterized tick, and we introduce the type synonym for
      the classical process event type.\<close>

type_synonym 'a event = \<open>('a, unit) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>

abbreviation tick_unit :: \<open>'a event\<close> (\<open>\<checkmark>\<close>) where \<open>\<checkmark> \<equiv> \<checkmark>(())\<close>

definition sum_of_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'a + 'r\<close>
  where \<open>sum_of_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k e \<equiv> case e of ev a \<Rightarrow> Inl a | \<checkmark>(r) \<Rightarrow> Inr r\<close>

definition event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_sum :: \<open>'a + 'r \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_sum s \<equiv> case s of Inl a \<Rightarrow> ev a | Inr r \<Rightarrow> \<checkmark>(r)\<close>

lemma type_definition_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>type_definition sum_of_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_sum UNIV\<close>
proof unfold_locales
  show \<open>sum_of_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k s \<in> UNIV\<close> for s :: \<open>('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> by simp
next
  show \<open>event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_sum (sum_of_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k e) = e\<close> for e :: \<open>('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (cases e) (simp_all add: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_sum_def sum_of_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
next
  show \<open>sum_of_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_sum s) = s\<close> for s :: \<open>'a + 'r\<close>
    by (cases s) (simp_all add: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_sum_def sum_of_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
qed

setup_lifting type_definition_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k

lemma range_tick_Un_range_ev_is_UNIV [simp] : \<open>range tick \<union> range ev = UNIV\<close>
  by (metis UNIV_eq_I UnCI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust rangeI)

text \<open>The generalization is done in a very straightforward way:
      the old version is recovered by considering \<^typ>\<open>('a, unit) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>.\<close>

(* 
typedef ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k = \<open>UNIV :: ('a + 'r) set\<close>
  morphisms event_of_sum sum_of_event by simp

setup_lifting type_definition_event

lift_definition ev :: \<open>'a \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> is \<open>\<lambda>a. Inl a\<close> .
lift_definition tick :: \<open>'r \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>\<checkmark>'(_')\<close>) is \<open>\<lambda>r. Inr r\<close> .

free_constructors event for is_ev : ev of_ev | is_tick : tick of_tick
proof transfer
  show \<open>(\<And>x1. y = Inl x1 \<Longrightarrow> P) \<Longrightarrow> (\<And>x2. y = Inr x2 \<Longrightarrow> P) \<Longrightarrow> P\<close> for y :: \<open>'a + 'b\<close> and P
    by (metis isl_def sum.collapse(2))
next
  show \<open>ev x = ev y \<longleftrightarrow> x = y\<close> for x y :: 'a by (metis ev.rep_eq sum.inject(1))
next
  show \<open>\<checkmark>(x) = \<checkmark>(y) \<longleftrightarrow> x = y\<close> for x y :: 'r by (metis sum.inject(2) tick.rep_eq)
next
  show \<open>ev x \<noteq> \<checkmark>(y)\<close> for x :: 'a and y :: 'r
    by (metis Inl_Inr_False ev.rep_eq tick.rep_eq)
qed

this looks more natural, but does not work fine with the typedef of process
 *)

lemma not_is_ev   [simp] : \<open>\<not> is_ev   e \<longleftrightarrow> is_tick e\<close>
  and not_is_tick [simp] : \<open>\<not> is_tick e \<longleftrightarrow> is_ev   e\<close>
  by (use event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust_disc in blast)+


type_synonym ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k = \<open>('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list\<close>

text \<open>We recover the classical version with \<^typ>\<open>unit\<close>.\<close>

type_synonym 'a trace = \<open>('a, unit) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>


text\<open>We chose as standard ordering on traces the prefix ordering.\<close>


text\<open>Some facts on the prefix ordering.\<close>

lemma nil_le     [simp]: \<open>[] \<le> s\<close>
  and nil_le2    [simp]: \<open>s \<le> [] \<longleftrightarrow> s = []\<close>
  and nil_less   [simp]: \<open>\<not> t < []\<close>
  and nil_less2  [simp]: \<open>[] < t @ [a]\<close>
  and less_self  [simp]: \<open>t < t @ [a]\<close>
  and le_cons    [simp]: \<open>a # s \<le> a # t \<longleftrightarrow> s \<le> t\<close>
  and le_append  [simp]: \<open>b @ s \<le> b @ t \<longleftrightarrow> s \<le> t\<close>
  and less_cons  [simp]: \<open>a # s < a # t \<longleftrightarrow> s < t\<close>
  and less_append[simp]: \<open>b @ s < b @ t \<longleftrightarrow> s < t\<close>

and   le_length_mono: \<open>s \<le> t \<Longrightarrow> length s \<le> length t\<close>
and less_length_mono: \<open>s < t \<Longrightarrow> length s < length t\<close>
and   le_tail: \<open>s \<noteq> [] \<Longrightarrow> s \<le> t \<Longrightarrow> tl s \<le> tl t\<close>
and less_tail: \<open>s \<noteq> [] \<Longrightarrow> s < t \<Longrightarrow> tl s < tl t\<close>
              apply (simp_all add: less_eq_list_def less_list_def prefix_length_le)
    apply (metis prefix_length_less prefix_order.dual_order.not_eq_order_implies_strict)
   apply (metis prefix_def tl_append2)
  by (metis prefix_def prefix_order.eq_iff self_append_conv tl_append2)


lemma le_same_imp_eq_or_less: \<open>(s :: 'a list) \<le> u \<Longrightarrow> t \<le> u \<Longrightarrow> t = s \<or> s < t \<or> t < s\<close>
  by (metis less_eq_list_def linorder_le_cases nless_le prefix_length_prefix)


lemma append_eq_first_pref_spec: \<open>s @ t = r @ [x] \<Longrightarrow> t \<noteq> [] \<Longrightarrow> s \<le> r\<close>
  by (metis butlast_append butlast_snoc less_eq_list_def prefix_def)


lemma prefixes_fin: \<open>finite {t. t \<le> s} \<and> card {t. t \<le> s} = Suc (length s)\<close>
proof (induct s)
  show \<open>finite {t. t \<le> []} \<and> card {t. t \<le> []} = Suc (length [])\<close> by simp
next
  case (Cons x s)
  have * : \<open>{t. t \<le> x # s} = {[]} \<union> (\<lambda>t. x # t) ` {t. t \<le> s}\<close>
    by (simp add: image_def less_eq_list_def set_eq_iff)
      (meson Sublist.prefix_Cons)
  show \<open>finite {t. t \<le> x # s} \<and> card {t. t \<le> x # s} = Suc (length (x # s))\<close>
  proof (intro conjI)
    show \<open>finite {t. t \<le> x # s}\<close> by (simp add: "*" Cons.hyps)
  next
    have \<open>finite ((\<lambda>t. x # t) ` {t. t \<le> s})\<close> by (simp add: Cons.hyps)
    show \<open>card {t. t \<le> x # s} = Suc (length (x # s))\<close>
      by (subst card_Un_disjoint[of \<open>{[]}\<close> \<open>(\<lambda>t. x # t) ` {t. t \<le> s}\<close>, folded "*"])
        (auto simp add: card_image Cons.hyps)   
  qed
qed


lemma sublists_fin: \<open>finite {t. \<exists>t1 t2. s = t1 @ t @ t2}\<close>
proof (induct s)
  show \<open>finite {t. \<exists>t1 t2. [] = t1 @ t @ t2}\<close> by simp
next
  case (Cons x s)
  have \<open>{t. t \<le> x # s} = {t. \<exists>t2. x # s = t @ t2}\<close>
    by (simp add: less_eq_list_def prefix_def)
  with prefixes_fin[of \<open>x # s\<close>] have \<open>finite {t. \<exists>t2. x # s = t @ t2}\<close> by simp
  have \<open>{t. \<exists>t1 t2. x # s = t1 @ t @ t2} \<subseteq>
        {t. \<exists>t1 t2. s = t1 @ t @ t2} \<union> {t. \<exists>t2. x # s = t @ t2}\<close>
    by (simp add: subset_iff) (meson Cons_eq_append_conv)
  show \<open>finite {t. \<exists>t1 t2. x # s = t1 @ t @ t2}\<close>
    by (rule finite_subset[OF \<open>?this\<close>], rule finite_UnI)
      (simp_all add: Cons.hyps \<open>finite {t. \<exists>t2. x # s = t @ t2}\<close>)
qed


lemma suffixes_fin: \<open>finite {t. \<exists>t1. s = t1 @ t}\<close>
  by (rule finite_subset[of _ \<open>{t. \<exists>t1 t2. s = t1 @ t @ t2}\<close>];
      simp add: subset_iff sublists_fin) blast 


text\<open>For the process invariant, it is a key element to
reduce the notion of traces to traces that may only contain
one tick event at the very end. This is captured by the definition
of the predicate \verb+front_tickFree+ and its stronger version
\verb+tickFree+. Here is the theory of this concept.\<close>

definition tickFree :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close> (\<open>tF\<close>)
  where \<open>tF s \<equiv> range tick \<inter> set s = {}\<close>

definition front_tickFree :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close> (\<open>ftF\<close>)
  where \<open>ftF s \<equiv> s = [] \<or> tickFree (tl (rev s))\<close>

lemma tickFree_Nil        [simp] : \<open>tF []\<close>
  and tickFree_Cons_iff   [simp] : \<open>tF (a # t) \<longleftrightarrow> is_ev a \<and> tF t\<close>
  and tickFree_append_iff [simp] : \<open>tF (s @ t) \<longleftrightarrow> tF s    \<and> tF t\<close>
  and tickFree_rev_iff    [simp] : \<open>tF (rev t) \<longleftrightarrow> tF t\<close>
  and non_tickFree_tick   [simp] : \<open>\<not> tF [\<checkmark>(r)]\<close>
  by (cases a; auto simp add: tickFree_def)+

lemma tickFree_iff_is_map_ev : \<open>tF t \<longleftrightarrow> (\<exists>u. t = map ev u)\<close>
  by (induct t) (simp_all add: Cons_eq_map_conv is_ev_def)

lemma front_tickFree_Nil   [simp] : \<open>ftF []\<close>
  and front_tickFree_single[simp] : \<open>ftF [a]\<close>
  by (simp_all add: front_tickFree_def)


lemma tickFree_tl : \<open>tF s \<Longrightarrow> tF (tl s)\<close>
  by (cases s) simp_all

lemma non_tickFree_imp_not_Nil: \<open>\<not> tF s \<Longrightarrow> s \<noteq> []\<close>
  using tickFree_Nil by blast

lemma tickFree_butlast: \<open>tF s \<longleftrightarrow> tF (butlast s) \<and> (s \<noteq> [] \<longrightarrow> is_ev (last s))\<close>
  by (induct s) simp_all

lemma front_tickFree_iff_tickFree_butlast: \<open>ftF s \<longleftrightarrow> tF (butlast s)\<close>
  by (induct s) (auto simp add: front_tickFree_def)

lemma front_tickFree_Cons_iff: \<open>ftF (a # s) \<longleftrightarrow> s = [] \<or> is_ev a \<and> ftF s\<close>
  by (simp add: front_tickFree_iff_tickFree_butlast)

lemma front_tickFree_append_iff:
  \<open>ftF (s @ t) \<longleftrightarrow> (if t = [] then ftF s else tF s \<and> ftF t)\<close>
  by (simp add: butlast_append front_tickFree_iff_tickFree_butlast)

lemma tickFree_imp_front_tickFree [simp] : \<open>tF s \<Longrightarrow> ftF s\<close>
  by (simp add: front_tickFree_def tickFree_tl)

lemma front_tickFree_charn: \<open>ftF s \<longleftrightarrow> s = [] \<or> (\<exists>a t. s = t @ [a] \<and> tF t)\<close>
  by (cases s rule: rev_cases) (simp_all add: front_tickFree_def)


lemma nonTickFree_n_frontTickFree: \<open>\<not> tF s \<Longrightarrow> ftF s \<Longrightarrow> \<exists>t r. s = t @ [\<checkmark>(r)]\<close>
  by (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust front_tickFree_append_iff list.distinct(1)
      rev_exhaust tickFree_Cons_iff tickFree_Nil tickFree_append_iff)

lemma front_tickFree_dw_closed : \<open>ftF (s @ t) \<Longrightarrow> ftF s\<close>
  by (metis front_tickFree_append_iff tickFree_imp_front_tickFree)

lemma front_tickFree_append: \<open>tF s \<Longrightarrow> ftF t \<Longrightarrow> ftF (s @ t)\<close>
  by (simp add: front_tickFree_append_iff)

lemma tickFree_imp_front_tickFree_snoc: \<open>tF s \<Longrightarrow> ftF (s @ [a])\<close>
  by (simp add: front_tickFree_append)

lemma front_tickFree_nonempty_append_imp: \<open>ftF (t @ r) \<Longrightarrow> r \<noteq> [] \<Longrightarrow> tF t \<and> ftF r\<close>
  by (simp add: front_tickFree_append_iff)

lemma tickFree_map_ev [simp] : \<open>tF (map ev t)\<close>
  by (induct t) simp_all

lemma tickFree_map_tick_iff [simp] : \<open>tF (map tick t) \<longleftrightarrow> t = []\<close>
  by (induct t) simp_all

lemma front_tickFree_map_tick_iff [simp] : \<open>ftF (map tick t) \<longleftrightarrow> t = [] \<or> (\<exists>r. t = [r])\<close>
  by (simp add: front_tickFree_iff_tickFree_butlast map_butlast[symmetric])
    (metis append_Nil append_butlast_last_id butlast.simps(1, 2))

\<comment> \<open>\<^term>\<open>map ev (map f t)\<close> if automatically simplified into \<^term>\<open>map (ev \<circ> f) t\<close> by the
    simplified, so we need to add the following versions.\<close>

lemma tickFree_map_ev_comp [simp] : \<open>tF (map (ev \<circ> f) t)\<close>
  by (metis list.map_comp tickFree_map_ev)

lemma tickFree_map_tick_comp_iff [simp] : \<open>tF (map (tick \<circ> f) t) \<longleftrightarrow> t = []\<close>
  by (fold map_map, unfold tickFree_map_tick_iff) simp

lemma front_tickFree_map_tick_comp_iff [simp] : \<open>ftF (map (tick \<circ> f) t) \<longleftrightarrow> t = [] \<or> (\<exists>r. t = [r])\<close>
  by (fold map_map, unfold front_tickFree_map_tick_iff)
    (simp add: map_eq_Cons_conv)



section\<open> Basic Types, Traces, Failures and Divergences \<close>

type_synonym ('a, 'r) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k = \<open>('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
type_synonym 'a refusal = \<open>('a, unit) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
type_synonym ('a, 'r) failure\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k = \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<times> ('a, 'r) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
type_synonym 'a failure = \<open>('a, unit) failure\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
type_synonym ('a, 'r) divergence\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k = \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
type_synonym 'a divergence = \<open>('a, unit) divergence\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
type_synonym ('a, 'r) process\<^sub>0 = \<open>('a, 'r) failure\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set \<times> ('a, 'r) divergence\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>

definition FAILURES :: \<open>('a, 'r) process\<^sub>0 \<Rightarrow> ('a, 'r) failure\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
  where \<open>FAILURES P \<equiv> fst P\<close>

definition TRACES :: \<open>('a, 'r) process\<^sub>0 \<Rightarrow> ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
  where \<open>TRACES P \<equiv> {tr. \<exists>ref. (tr, ref) \<in> FAILURES P}\<close>

definition DIVERGENCES :: \<open>('a, 'r) process\<^sub>0 \<Rightarrow> ('a, 'r) divergence\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
  where \<open>DIVERGENCES P \<equiv> snd P\<close>

definition REFUSALS :: \<open>('a, 'r) process\<^sub>0 \<Rightarrow> ('a, 'r) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
  where \<open>REFUSALS P \<equiv> {ref. ([], ref) \<in> FAILURES P}\<close>

section\<open> The Process Type Invariant \<close>

definition is_process :: \<open>('a, 'r) process\<^sub>0 \<Rightarrow> bool\<close> where
  \<open>is_process P \<equiv>
   ([], {}) \<in> FAILURES P \<and>
   (\<forall>s X. (s, X) \<in> FAILURES P \<longrightarrow> ftF s) \<and>
   (\<forall>s t. (s @ t, {}) \<in> FAILURES P \<longrightarrow> (s, {}) \<in> FAILURES P) \<and>
   (\<forall>s X Y. (s, Y) \<in> FAILURES P \<and> X \<subseteq> Y \<longrightarrow> (s, X) \<in> FAILURES P) \<and>
   (\<forall>s X Y. (s, X) \<in> FAILURES P \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> FAILURES P)
            \<longrightarrow> (s, X \<union> Y) \<in> FAILURES P) \<and>
   (\<forall>s r X. (s @ [\<checkmark>(r)], {}) \<in> FAILURES P \<longrightarrow> (s, X - {\<checkmark>(r)}) \<in> FAILURES P) \<and>
   (\<forall>s t. s \<in> DIVERGENCES P \<and> tF s \<and> ftF t \<longrightarrow> s @ t \<in> DIVERGENCES P) \<and>
   (\<forall>s X. s \<in> DIVERGENCES P \<longrightarrow> (s, X) \<in> FAILURES P) \<and>
   (\<forall>s r. s @ [\<checkmark>(r)] \<in> DIVERGENCES P \<longrightarrow> s \<in> DIVERGENCES P)\<close>


lemma is_process_spec:
  \<open>is_process P \<longleftrightarrow>
  ([], {}) \<in> FAILURES P \<and>
  (\<forall>s X. (s, X) \<in> FAILURES P \<longrightarrow> ftF s) \<and>
  (\<forall>s t. (s @ t, {}) \<notin> FAILURES P \<or> (s, {}) \<in> FAILURES P) \<and>
  (\<forall>s X Y. (s, Y) \<notin> FAILURES P \<or> \<not> X \<subseteq> Y \<or> (s, X) \<in> FAILURES P) \<and>
  (\<forall>s X Y. (s, X) \<in> FAILURES P \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> FAILURES P)
           \<longrightarrow> (s, X \<union> Y) \<in> FAILURES P) \<and>
  (\<forall>s r X. (s @ [\<checkmark>(r)], {}) \<in> FAILURES P \<longrightarrow> (s, X - {\<checkmark>(r)}) \<in> FAILURES P) \<and>
  (\<forall>s t. s \<notin> DIVERGENCES P \<or> \<not> tF s \<or> \<not> ftF t \<or> s @ t \<in> DIVERGENCES P) \<and>
  (\<forall>s X. s \<notin> DIVERGENCES P \<or> (s, X) \<in> FAILURES P) \<and>
  (\<forall>s r. s @ [\<checkmark>(r)] \<notin> DIVERGENCES P \<or> s \<in> DIVERGENCES P)\<close>
  by (simp only: is_process_def HOL.nnf_simps(1)
      HOL.nnf_simps(3) [symmetric] HOL.imp_conjL[symmetric])

lemma Process_eqI :
  \<open>FAILURES P = FAILURES Q \<Longrightarrow> DIVERGENCES P = DIVERGENCES Q \<Longrightarrow> P = Q\<close>
  by (metis DIVERGENCES_def FAILURES_def prod_eq_iff)

lemma process_eq_spec:
  \<open>P = Q \<longleftrightarrow> FAILURES P = FAILURES Q \<and> DIVERGENCES P = DIVERGENCES Q\<close>
  by (meson Process_eqI)


lemma process_surj_pair: \<open>(FAILURES P, DIVERGENCES P) = P\<close>
  by(auto simp: FAILURES_def DIVERGENCES_def)

lemma Fa_eq_imp_Tr_eq: \<open>FAILURES P = FAILURES Q \<Longrightarrow> TRACES P = TRACES Q\<close>
  by (auto simp: FAILURES_def DIVERGENCES_def TRACES_def) 



lemma is_process1 : \<open>([], {}) \<in> FAILURES P\<close>
  and is_process2 : \<open>(s, X) \<in> FAILURES P \<Longrightarrow> ftF s\<close>
  and is_process3 : \<open>(s @ t, {}) \<in> FAILURES P \<Longrightarrow> (s, {}) \<in> FAILURES P\<close>
  and is_process4 : \<open>\<lbrakk>is_process P; (s, Y) \<in> FAILURES P; X \<subseteq> Y\<rbrakk> \<Longrightarrow> (s, X) \<in> FAILURES P\<close>
  and is_process5 : \<open>\<lbrakk>is_process P; (s, X) \<in> FAILURES P; \<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> FAILURES P\<rbrakk>
                     \<Longrightarrow> (s, X \<union> Y) \<in> FAILURES P\<close>
  and is_process6 : \<open>(s @ [\<checkmark>(r)], {}) \<in> FAILURES P \<Longrightarrow> (s, X - {\<checkmark>(r)}) \<in> FAILURES P\<close>
  and is_process7 : \<open>\<lbrakk>s \<in> DIVERGENCES P; tF s; ftF t\<rbrakk> \<Longrightarrow> s @ t \<in> DIVERGENCES P\<close>
  and is_process8 : \<open>s \<in> DIVERGENCES P \<Longrightarrow> (s, X) \<in> FAILURES P\<close>
  and is_process9 : \<open>s @ [\<checkmark>(r)] \<in> DIVERGENCES P \<Longrightarrow> s \<in> DIVERGENCES P\<close>
  if \<open>is_process P\<close>
  using \<open>is_process P\<close> unfolding is_process_def by metis+


(* 
lemma is_process3_S_pref: \<open>\<lbrakk>is_process P; (t, {}) \<in> FAILURES P; s \<le> t\<rbrakk> \<Longrightarrow> (s, {}) \<in> FAILURES P\<close>
  by (metis prefixE is_process3)

lemma is_process4: \<open>is_process P \<Longrightarrow> \<forall>s X Y. (s, Y) \<notin> FAILURES P \<or> \<not> X \<subseteq> Y \<or> (s, X) \<in> FAILURES P\<close>
  by (simp only: is_process_spec) simp

lemma is_process4_S: \<open>\<lbrakk>is_process P; (s, Y) \<in> FAILURES P; X \<subseteq> Y\<rbrakk> \<Longrightarrow> (s, X) \<in> FAILURES P\<close>
  by (drule is_process4, auto)

lemma is_process4_S1: \<open>\<lbrakk>is_process P; x \<in> FAILURES P; X \<subseteq> snd x\<rbrakk> \<Longrightarrow> (fst x, X) \<in> FAILURES P\<close>
  by (drule is_process4_S, auto)

lemma is_process5:
  \<open>is_process P \<Longrightarrow> \<forall>s X Y. (s, X) \<in> FAILURES P \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> FAILURES P)
                            \<longrightarrow> (s, X \<union> Y) \<in> FAILURES P\<close>
  by (drule is_process_spec[THEN iffD1],metis)

lemma is_process5_S:
  \<open>\<lbrakk>is_process P; (sa, X) \<in> FAILURES P; \<forall>c. c \<in> Y \<longrightarrow> (sa @ [c], {}) \<notin> FAILURES P\<rbrakk>
   \<Longrightarrow> (sa, X \<union> Y) \<in> FAILURES P\<close>
  by (drule is_process5, metis)

lemma is_process5_S1:
  \<open>\<lbrakk>is_process P; (sa, X) \<in> FAILURES P; (sa, X \<union> Y) \<notin> FAILURES P\<rbrakk>
   \<Longrightarrow> \<exists>c. c \<in> Y \<and> (sa @ [c], {}) \<in> FAILURES P\<close>
  by (erule contrapos_np, drule is_process5_S, simp_all)

lemma is_process6: \<open>is_process P \<Longrightarrow> \<forall>s X. (s @ [\<checkmark>(r)], {}) \<in> FAILURES P \<longrightarrow> (s, X - {\<checkmark>(r)}) \<in> FAILURES P\<close>
  by (drule is_process_spec[THEN iffD1], metis)

lemma is_process6_S: \<open>is_process P \<Longrightarrow> (s @ [\<checkmark>(r)], {}) \<in> FAILURES P \<Longrightarrow> (s, X - {\<checkmark>(r)}) \<in> FAILURES P\<close>
  by (simp add: is_process6)

lemma is_process7:
  \<open>is_process P \<Longrightarrow> \<forall> s t. s \<notin> DIVERGENCES P \<or> \<not> tickFree s \<or> \<not> front_tickFree t \<or> s @ t \<in> DIVERGENCES P\<close>
  by (drule is_process_spec[THEN iffD1], metis)

lemma is_process7_S:
  \<open>is_process P \<Longrightarrow> s \<in> DIVERGENCES P \<Longrightarrow> tickFree s \<Longrightarrow>
   front_tickFree t \<Longrightarrow> s @ t \<in> DIVERGENCES P\<close>
  by (drule is_process7, metis)

lemma is_process8: \<open>is_process P \<Longrightarrow> \<forall>s X. s \<notin> DIVERGENCES P \<or> (s, X) \<in> FAILURES P\<close>
  by (drule is_process_spec[THEN iffD1], metis)

lemma is_process8_S: \<open>is_process P \<Longrightarrow> s \<in> DIVERGENCES P \<Longrightarrow> (s, X) \<in> FAILURES P\<close>
  by (drule is_process8, metis)

lemma is_process9: \<open>is_process P \<Longrightarrow> \<forall>s. s @ [tick] \<notin> DIVERGENCES P \<or> s \<in> DIVERGENCES P\<close>
  by (drule is_process_spec[THEN iffD1], metis)

lemma is_process9_S: \<open>is_process P \<Longrightarrow> s @ [tick] \<in> DIVERGENCES P \<Longrightarrow> s \<in> DIVERGENCES P\<close>
  by (drule is_process9, metis)

lemma Failures_implies_Traces: \<open> \<lbrakk>is_process P; (s, X) \<in> FAILURES P\<rbrakk> \<Longrightarrow> s \<in> TRACES P\<close>
  by( simp add: TRACES_def, metis)

lemma is_process5_sing: 
  \<open>is_process P \<Longrightarrow> (s, {x}) \<notin> FAILURES P \<Longrightarrow> (s, {}) \<in> FAILURES P \<Longrightarrow> (s @ [x], {}) \<in> FAILURES P\<close>
  by (drule_tac X = \<open>{}\<close> in is_process5_S1, auto)

lemma is_process5_singT: 
  \<open>is_process P \<Longrightarrow> (s, {x}) \<notin> FAILURES P \<Longrightarrow> (s, {}) \<in> FAILURES P \<Longrightarrow> s @ [x] \<in> TRACES P\<close>
  by (drule is_process5_sing) (auto simp add: TRACES_def)
 *)

lemma trace_with_Tick_imp_tickFree_front :
  \<open>is_process P \<Longrightarrow> t @ [\<checkmark>(r)] \<in> TRACES P \<Longrightarrow> tF t\<close>
  by (simp add: TRACES_def) (meson front_tickFree_append_iff is_process2 neq_Nil_conv)


section \<open> The Abstraction to the process-Type \<close>

typedef ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k = \<open>{p :: ('a, 'r) process\<^sub>0 . is_process p}\<close>
  morphisms process\<^sub>0_of_process process_of_process\<^sub>0
proof - 
  have \<open>({(s, X). s = []}, {}) \<in> {p. is_process p}\<close>
    by (simp add: DIVERGENCES_def FAILURES_def is_process_def)
  thus ?thesis by auto
qed

text \<open>Again, the old version without parameterized termination can be recovered
      by considering \<^typ>\<open>('a, unit) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>.\<close>

type_synonym 'a process = \<open>('a, unit) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>

setup_lifting type_definition_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k

text \<open>This is where we differ from previous versions: we lift definitions 
      using Isabelle's machinery instead of doing it by hand.\<close>

lift_definition Failures :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) failure\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close> (\<open>\<F>\<close>) is FAILURES .

lift_definition Traces :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close> (\<open>\<T>\<close>) is TRACES .

lift_definition Divergences :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) divergence\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close> (\<open>\<D>\<close>) is DIVERGENCES .

lift_definition Refusals :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close> (\<open>\<R>\<close>) is REFUSALS .

lemma Refusals_def_bis : \<open>\<R> P = {X. ([], X) \<in> \<F> P}\<close>
  by (simp add: Failures.rep_eq REFUSALS_def Refusals.rep_eq)

lemma Refusals_iff : \<open>X \<in> \<R> P \<longleftrightarrow> ([], X) \<in> \<F> P\<close>
  by (simp add: Failures_def Refusals_def_bis)

lemma T_def_spec: \<open>\<T> P = {tr. \<exists>f. f \<in> \<F> P \<and> tr = fst f}\<close>
  by (simp add: Traces_def TRACES_def Failures_def)

lemma T_F_spec : \<open>(t, {}) \<in> \<F> P \<longleftrightarrow> t \<in> \<T> P\<close>
  by transfer (auto simp add: TRACES_def intro: is_process4)


lemma Process_spec: \<open>process_of_process\<^sub>0 (\<F> P, \<D> P) = P\<close>
  by (simp add: Divergences.rep_eq Failures.rep_eq
      process\<^sub>0_of_process_inverse process_surj_pair)


lemma Process_eq_spec: \<open>P = Q \<longleftrightarrow> \<F> P = \<F> Q \<and> \<D> P = \<D> Q\<close>
  by (metis Process_spec)


lemma Process_eq_spec_optimized: \<open>P = Q \<longleftrightarrow> \<D> P = \<D> Q \<and> (\<D> P = \<D> Q \<longrightarrow> \<F> P = \<F> Q)\<close>
  using Process_eq_spec by auto

lemma is_processT:
  \<open>([], {}) \<in> \<F> P \<and>
   (\<forall>s X. (s, X) \<in> \<F> P \<longrightarrow> ftF s) \<and>
   (\<forall>s t. (s @ t, {}) \<in> \<F> P \<longrightarrow> (s, {}) \<in> \<F> P) \<and>
   (\<forall>s X Y. (s, Y) \<in> \<F> P \<and> X \<subseteq> Y \<longrightarrow> (s, X) \<in> \<F> P) \<and>
   (\<forall>s X Y. (s, X) \<in> \<F> P \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> \<F> P) \<longrightarrow> (s, X \<union> Y) \<in> \<F> P) \<and>
   (\<forall>s r X. (s @ [\<checkmark>(r)], {}) \<in> \<F> P \<longrightarrow> (s, X - {\<checkmark>(r)}) \<in> \<F> P) \<and>
   (\<forall>s t. s \<in> \<D> P \<and> tF s \<and> ftF t \<longrightarrow> s @ t \<in> \<D> P) \<and>
   (\<forall>s r X. s \<in> \<D> P \<longrightarrow> (s, X) \<in> \<F> P) \<and> (\<forall>s. s @ [\<checkmark>(r)] \<in> \<D> P \<longrightarrow> s \<in> \<D> P)\<close>
  by transfer (unfold is_process_def, fast)

text \<open>When the second type is set to \<^typ>\<open>unit\<close>, we recover the classical definition
      as defined in the book by Roscoe.\<close>

lemma is_processT_unit:
  \<open>([], {}) \<in> \<F> P \<and>
   (\<forall>s X. (s, X) \<in> \<F> P \<longrightarrow> ftF s) \<and>
   (\<forall>s t. (s @ t, {}) \<in> \<F> P \<longrightarrow> (s, {}) \<in> \<F> P) \<and>
   (\<forall>s X Y. (s, Y) \<in> \<F> P \<and> X \<subseteq> Y \<longrightarrow> (s, X) \<in> \<F> P) \<and>
   (\<forall>s X Y. (s, X) \<in> \<F> P \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> \<F> P) \<longrightarrow> (s, X \<union> Y) \<in> \<F> P) \<and>
   (\<forall>s X. (s @ [\<checkmark>], {}) \<in> \<F> P \<longrightarrow> (s, X - {\<checkmark>}) \<in> \<F> P) \<and>
   (\<forall>s t. s \<in> \<D> P \<and> tF s \<and> ftF t \<longrightarrow> s @ t \<in> \<D> P) \<and>
   (\<forall>s X. s \<in> \<D> P \<longrightarrow> (s, X) \<in> \<F> P) \<and> (\<forall>s. s @ [\<checkmark>] \<in> \<D> P \<longrightarrow> s \<in> \<D> P)\<close>
  by transfer (unfold is_process_def, fast)


lemma process_charn:
  \<open>([], {}) \<in> \<F> P \<and>
   (\<forall>s X. (s, X) \<in> \<F> P \<longrightarrow> ftF s) \<and>
   (\<forall>s t. (s @ t, {}) \<notin> \<F> P \<or> (s, {}) \<in> \<F> P) \<and>
   (\<forall>s X Y. (s, Y) \<notin> \<F> P \<or> \<not> X \<subseteq> Y \<or> (s, X) \<in> \<F> P) \<and>
   (\<forall>s X Y. (s, X) \<in> \<F> P \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> \<F> P) \<longrightarrow> (s, X \<union> Y) \<in> \<F> P) \<and>
   (\<forall>s r X. (s @ [\<checkmark>(r)], {}) \<in> \<F> P \<longrightarrow> (s, X - {\<checkmark>(r)}) \<in> \<F> P) \<and>
   (\<forall>s t. s \<notin> \<D> P \<or> \<not> tF s \<or> \<not> ftF t \<or> s @ t \<in> \<D> P) \<and>
   (\<forall>s r X. s \<notin> \<D> P \<or> (s, X) \<in> \<F> P) \<and> (\<forall>s. s @ [\<checkmark>(r)] \<notin> \<D> P \<or> s \<in> \<D> P)\<close>
  by (meson is_processT)



text\<open> split of \verb+is_processT+: \<close>

lemma is_processT1          : \<open>([], {}) \<in> \<F> P\<close>
  and is_processT1_TR       : \<open>[] \<in> \<T> P\<close>
  and is_processT2          : \<open>(s, X) \<in> \<F> P \<Longrightarrow> ftF s\<close>
  and is_processT2_TR       : \<open>s \<in> \<T> P \<Longrightarrow> ftF s\<close>
  and is_processT3          : \<open>(s @ t, {}) \<in> \<F> P \<Longrightarrow> (s, {}) \<in> \<F> P\<close>
  and is_processT3_pref     : \<open>(t, {}) \<in> \<F> P \<Longrightarrow> s \<le> t \<Longrightarrow> (s, {}) \<in> \<F> P\<close>
  and is_processT3_TR       : \<open>t \<in> \<T> P \<Longrightarrow> s \<le> t \<Longrightarrow> s \<in> \<T> P\<close>
  and is_processT3_TR_pref  : \<open>(t, {}) \<in> \<F> P \<Longrightarrow> s \<le> t \<Longrightarrow> (s, {}) \<in> \<F> P\<close>
  and is_processT4          : \<open>(s, Y) \<in> \<F> P \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> (s, X) \<in> \<F> P\<close> 
  and is_processT5          : \<open>(s, X) \<in> \<F> P \<Longrightarrow> \<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> \<F> P
                               \<Longrightarrow> (s, X \<union> Y) \<in> \<F> P\<close>
  and is_processT6          : \<open>(s @ [\<checkmark>(r)], {}) \<in> \<F> P \<Longrightarrow> (s, X - {\<checkmark>(r)}) \<in> \<F> P\<close>
  and is_processT6_TR       : \<open>s @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> (s, X - {\<checkmark>(r)}) \<in> \<F> P\<close>
  and is_processT7          : \<open>s \<in> \<D> P \<Longrightarrow> tF s \<Longrightarrow> ftF t \<Longrightarrow> s @ t \<in> \<D> P\<close>
  and is_processT8          : \<open>s \<in> \<D> P \<Longrightarrow> (s, X) \<in> \<F> P\<close>
  and is_processT9          : \<open>s @ [\<checkmark>(r)] \<in> \<D> P \<Longrightarrow> s \<in> \<D> P\<close>
  by (fold T_F_spec)
    (use is_processT in \<open>metis [[metis_verbose=false]] prefixE\<close>)+

lemma is_processT6_notin    : \<open>(s @ [\<checkmark>(r)], {}) \<in> \<F> P \<Longrightarrow> \<checkmark>(r) \<notin> X \<Longrightarrow> (s, X) \<in> \<F> P\<close>
  and is_processT6_TR_notin : \<open>s @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> \<checkmark>(r) \<notin> X \<Longrightarrow> (s, X) \<in> \<F> P\<close>
  by (metis Diff_insert_absorb is_processT6)
    (metis Diff_insert_absorb is_processT6_TR)

lemma is_processT3_TR_append : \<open>t @ u \<in> \<T> P \<Longrightarrow> t \<in> \<T> P\<close>
  using is_processT3_TR by fastforce

lemma nonempty_divE : 
  \<open>\<D> P \<noteq> {} \<Longrightarrow> (\<And>t. tF t \<Longrightarrow> t \<in> \<D> P \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  by (metis ex_in_conv front_tickFree_nonempty_append_imp is_processT2 is_processT8
      is_processT9 neq_Nil_conv nonTickFree_n_frontTickFree)


lemma div_butlast_when_non_tickFree_iff :
  \<open>ftF s \<Longrightarrow> (if tF s then s else butlast s) \<in> \<D> P \<longleftrightarrow> s \<in> \<D> P\<close>
  by (cases s rule: rev_cases; simp add: front_tickFree_iff_tickFree_butlast)
    (metis front_tickFree_Cons_iff is_processT7 is_processT9 is_tick_def)


(* lemma is_processT8_Pair: \<open>fst s \<in> \<D> P \<Longrightarrow> s \<in> \<F> P\<close>
  by (metis eq_fst_iff is_processT8)

lemma is_processT9: \<open>s @ [tick] \<in> \<D> P \<Longrightarrow> s \<in> \<D> P\<close>
  by (insert process_charn[of P], metis)

  by (simp add:process_charn)

lemma is_processT2: \<open>(s, X) \<in> \<F> P \<Longrightarrow> front_tickFree s\<close>
by(simp add:process_charn)

lemma is_processT2_TR : \<open>s \<in> \<T> P \<Longrightarrow> front_tickFree s\<close>
  by (simp add: Traces.rep_eq Traces_def TRACES_def Failures.rep_eq[symmetric])
     (use is_processT2 in blast)
  
(* 
lemma is_proT2: \<open>(s, X) \<in> \<F> P \<Longrightarrow> s \<noteq> [] \<Longrightarrow> tick \<notin> set (tl (rev s))\<close>
  using front_tickFree_def is_processT2 tickFree_def by blast
 *)

lemma is_processT3 : \<open>(s @ t, {}) \<in> \<F> P \<Longrightarrow> (s, {}) \<in> \<F> P\<close>
  by (metis process_charn)

lemma is_processT3_S_pref : \<open>(t, {}) \<in> \<F> P \<Longrightarrow> s \<le> t \<Longrightarrow> (s, {}) \<in> \<F> P\<close>
  by (metis is_processT3 le_list_def)


lemma  is_processT4 : \<open>(s, Y) \<in> \<F> P \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> (s, X) \<in> \<F> P\<close>
  by (meson process_charn)

lemma is_processT4_S1 : \<open>x \<in> \<F> P \<Longrightarrow> X \<subseteq> snd x \<Longrightarrow> (fst x, X) \<in> \<F> P\<close>
  by (metis is_processT4 prod.collapse)

lemma is_processT5:
  \<open>(s, X) \<in> \<F> P \<Longrightarrow> \<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> \<F> P \<Longrightarrow> (s, X \<union> Y) \<in> \<F> P\<close>
  by (simp add: process_charn)

lemma is_processT5_S1: 
  \<open>(s, X) \<in> \<F> P \<Longrightarrow> (s, X \<union> Y) \<notin> \<F> P \<Longrightarrow> \<exists>c. c \<in> Y \<and> (s @ [c], {}) \<in> \<F> P\<close>
  by (erule contrapos_np, simp add: is_processT5)

lemma is_processT5_S2: \<open>(s, X) \<in> \<F> P \<Longrightarrow> (s @ [c], {}) \<notin> \<F> P \<Longrightarrow> (s, X \<union> {c}) \<in> \<F> P\<close>
  using is_processT5_S1 by blast

lemma is_processT5_S2a: \<open>(s, X) \<in> \<F> P \<Longrightarrow> (s, X \<union> {c}) \<notin> \<F> P \<Longrightarrow> (s @ [c], {}) \<in> \<F> P\<close>
  using is_processT5_S2 by blast

lemma  is_processT5_S3: \<open>(s, {}) \<in> \<F> P \<Longrightarrow> (s @ [c], {}) \<notin> \<F> P \<Longrightarrow> (s, {c}) \<in> \<F> P\<close>
  using is_processT5_S2a by auto

   
lemma is_processT5_S4: \<open>(s, {}) \<in> \<F> P \<Longrightarrow> (s, {c}) \<notin> \<F> P \<Longrightarrow> (s @ [c], {}) \<in> \<F> P\<close>
  by (erule contrapos_np, simp add: is_processT5_S3)


lemma is_processT5_S5:
  \<open>(s, X) \<in> \<F> P \<Longrightarrow> \<forall>c. c \<in> Y \<longrightarrow> (s, X \<union> {c}) \<notin> \<F> P \<Longrightarrow>
    \<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<in> \<F> P\<close>
  by (simp add: is_processT5_S2a)

lemma is_processT5_S6: \<open>([], {c}) \<notin> \<F> P \<Longrightarrow> ([c], {}) \<in> \<F> P\<close>
  by (metis append_self_conv2 is_processT1 is_processT5_S4)

lemma is_processT6: \<open>(s @ [tick], {}) \<in> \<F> P \<Longrightarrow> (s, X - {tick}) \<in> \<F> P\<close>
  by (simp add: process_charn)

lemma is_processT7: \<open>s \<in> \<D> P \<Longrightarrow> tickFree s \<Longrightarrow> front_tickFree t \<Longrightarrow> s @ t \<in> \<D> P\<close>
  by (insert process_charn[of P], metis)

lemma is_processT8: \<open>s \<in> \<D> P \<Longrightarrow> (s, X) \<in> \<F> P\<close>
  by (insert process_charn[of P], metis)

lemma is_processT8_Pair: \<open>fst s \<in> \<D> P \<Longrightarrow> s \<in> \<F> P\<close>
  by (metis eq_fst_iff is_processT8)

lemma is_processT9: \<open>s @ [tick] \<in> \<D> P \<Longrightarrow> s \<in> \<D> P\<close>
  by (insert process_charn[of P], metis)

lemma is_processT9_S_swap: \<open>s \<notin> \<D> P \<Longrightarrow> s @ [tick] \<notin> \<D> P\<close>
  by (erule contrapos_nn, simp add: is_processT9)
 *)

section\<open> Some Consequences of the Process Characterization\<close>

lemma F_T: \<open>(s, X) \<in> \<F> P \<Longrightarrow> s \<in> \<T> P\<close>
  by (simp add: T_def_spec split_def, metis)

lemma T_F: \<open>s \<in> \<T> P \<Longrightarrow> (s, {}) \<in> \<F> P\<close>
  using is_processT4 by (auto simp add: T_def_spec)

lemmas D_T = is_processT8 [THEN F_T]

lemmas is_processT4_empty [elim!] = F_T [THEN T_F]


(* 
lemma no_Trace_implies_no_Failure: \<open>s \<notin> \<T> P \<Longrightarrow> (s, {}) \<notin> \<F> P\<close>
  by (simp add: T_F_spec)

lemmas  NT_NF = no_Trace_implies_no_Failure



lemma D_T_subset : \<open>\<D> P \<subseteq> \<T> P\<close> by(auto intro!:D_T)

lemma NF_ND : \<open>(s, X) \<notin> \<F> P \<Longrightarrow> s \<notin> \<D> P\<close>
  by (erule contrapos_nn, simp add: is_processT8)

lemmas NT_ND = D_T_subset[THEN Set.contra_subsetD]

lemma F_T1: \<open>a \<in> \<F> P \<Longrightarrow> fst a \<in> \<T> P\<close>
  by (rule_tac X=\<open>snd a\<close> in F_T, simp)



lemma NF_NT: \<open>(s, {}) \<notin> \<F> P \<Longrightarrow> s \<notin> \<T> P\<close>
  by (erule contrapos_nn, simp only: T_F)

lemma  is_processT6_S1: \<open>\<checkmark>(r) \<notin> X \<Longrightarrow> (s @ [\<checkmark>(r)], {}) \<in> \<F> P \<Longrightarrow> (s, X) \<in> \<F> P\<close>
  by (metis Diff_insert_absorb is_processT6)

lemmas is_processT3_ST = T_F [THEN is_processT3, THEN F_T]

lemmas is_processT3_ST_pref = T_F [THEN is_processT3_S_pref, THEN F_T]

lemmas is_processT3_SR = F_T [THEN T_F, THEN is_processT3]
 *)




lemma is_processT5_S7: \<open>t \<in> \<T> P \<Longrightarrow> (t, A) \<notin> \<F> P \<Longrightarrow> \<exists>x. x \<in> A \<and> t @ [x] \<in> \<T> P\<close>
  by (metis T_F_spec is_processT5 sup_bot_left)

lemma is_processT5_S7': 
  \<open>(t, X) \<in> \<F> P \<Longrightarrow> (t, X \<union> A) \<notin> \<F> P \<Longrightarrow> \<exists>x. x \<in> A \<and> x \<notin> X \<and> t @ [x] \<in> \<T> P\<close>
  by (erule contrapos_np, subst Un_Diff_cancel[symmetric])
    (rule is_processT5, auto simp: T_F_spec)

lemma trace_tick_continuation_or_all_tick_failuresE:
  \<open>\<lbrakk>(s, {}) \<in> \<F> P; \<And>r. s @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> thesis; (s, range tick) \<in> \<F> P \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close>
  by (metis F_T f_inv_into_f is_processT5_S7)

(* lemma Nil_subset_T: \<open>{[]} \<subseteq> \<T> P\<close>
  by (auto simp: T_F_spec[symmetric] is_processT1) *)

lemmas Nil_elem_T [simp] = is_processT1_TR

lemmas F_imp_front_tickFree = is_processT2
  and D_imp_front_tickFree = is_processT8[THEN is_processT2]
  and T_imp_front_tickFree = T_F[THEN is_processT2]


lemma D_front_tickFree_subset : \<open>\<D> P \<subseteq> Collect ftF\<close>
  by (auto simp: D_imp_front_tickFree)

lemma F_D_part : \<open>\<F> P = {(s, x). s \<in> \<D> P} \<union> {(s, x). s \<notin> \<D> P \<and> (s, x) \<in> \<F> P}\<close>
  by (auto simp add: is_processT8)

lemma D_F : \<open>{(s, x). s \<in> \<D> P} \<subseteq> \<F> P\<close>
  using F_D_part by blast

lemma append_T_imp_tickFree:  \<open>t @ s \<in> \<T> P \<Longrightarrow> s \<noteq> [] \<Longrightarrow> tF t\<close>
  by (meson front_tickFree_append_iff is_processT2_TR)

lemma tick_T_F: \<open>t @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> (t @ [\<checkmark>(r)], X) \<in> \<F> P\<close>
  by (meson append_T_imp_tickFree is_processT5_S7 list.discI non_tickFree_tick tickFree_append_iff)

(* corollary append_single_T_imp_tickFree : \<open>t @ [a] \<in> \<T> P \<Longrightarrow> tickFree t\<close>
  by (simp add: append_T_imp_tickFree) *)

(* lemma F_subset_imp_T_subset: \<open>\<F> P \<subseteq> \<F> Q \<Longrightarrow> \<T> P \<subseteq> \<T> Q\<close>
  by (auto simp: subsetD T_F_spec[symmetric]) *)

(* lemma is_processT6_S2: \<open>\<checkmark>(r) \<notin> X \<Longrightarrow> [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> ([], X) \<in> \<F> P\<close>
  by (metis Diff_insert_absorb append_Nil is_processT6_TR) *)

lemma is_processT9_tick: \<open>[\<checkmark>(r)] \<in> \<D> P \<Longrightarrow> ftF s \<Longrightarrow> s \<in> \<D> P\<close>
  by (metis append_Nil is_processT7 is_processT9 tickFree_Nil)

lemma T_nonTickFree_imp_decomp: \<open>t \<in> \<T> P \<Longrightarrow> \<not> tF t \<Longrightarrow> \<exists>s r. t = s @ [\<checkmark>(r)]\<close>
  by (simp add: is_processT2_TR nonTickFree_n_frontTickFree)



section\<open> Process Approximation is a Partial Ordering, a Cpo, and a Pcpo \<close>
text\<open>The Failure/Divergence Model of CSP Semantics provides two orderings:
The \emph{approximation ordering} (also called \emph{process ordering})
will be used for giving semantics to recursion (fixpoints) over processes,
the \emph{refinement ordering} captures our intuition that a more concrete
process is more deterministic and more defined than an abstract one.

We start with the key-concepts of the approximation ordering, namely
the predicates $min\_elems$ and \<open>\<R>\<^sub>a\<close> (abbreviating \emph{refusals after}).
The former provides just a set of minimal elements from a given set
of elements of type-class $ord$ \ldots \<close>

definition min_elems :: \<open>('s::ord) set \<Rightarrow> 's set\<close>
  where   \<open>min_elems X \<equiv> {s \<in> X. \<forall>t \<in> X. \<not> (t < s)}\<close>

lemma Nil_min_elems : \<open>[] \<in> A \<Longrightarrow> [] \<in> min_elems A\<close>
  by (simp add: min_elems_def)

lemma min_elems_le_self[simp] : \<open>(min_elems A) \<subseteq> A\<close>
  by (auto simp: min_elems_def)

lemmas elem_min_elems = Set.set_mp[OF min_elems_le_self]

lemma min_elems_Collect_ftF_is_Nil : \<open>min_elems (Collect ftF) = {[]}\<close>
  by (simp add: min_elems_def less_eq_list_def set_eq_iff)
    (metis front_tickFree_charn nil_less nil_less2)

lemma min_elems5 : \<open>(s :: 'a list) \<in> A \<Longrightarrow> \<exists>t\<le>s. t \<in> min_elems A\<close>
proof -
  have * : \<open>x \<in> A \<Longrightarrow> length x \<le> n \<Longrightarrow> \<exists>s\<le>x. s \<in> min_elems A\<close> for x :: \<open>'a list\<close> and A n
  proof (induct n arbitrary: x rule: nat_induct)
    show \<open>x \<in> A \<Longrightarrow> length x \<le> 0 \<Longrightarrow> \<exists>s\<le>x. s \<in> min_elems A\<close> for x by (simp add: Nil_min_elems)
  next
    fix n x
    assume \<open>x \<in> A\<close> \<open>length x \<le> Suc n\<close>
    assume hyp : \<open>x \<in> A \<Longrightarrow> length x \<le> n \<Longrightarrow> \<exists>s\<le>x. s \<in> min_elems A\<close> for x
    show \<open>\<exists>s\<le>x. s \<in> min_elems A\<close>
    proof (cases \<open>\<exists>y \<in> A. y < x\<close>)
      show \<open>\<exists>y\<in>A. y < x \<Longrightarrow> \<exists>s\<le>x. s \<in> min_elems A\<close>
        by (elim bexE, frule hyp, drule less_length_mono, use \<open>length x \<le> Suc n\<close> in simp)
          (meson dual_order.strict_trans2 less_list_def)
    next
      show \<open>\<not> (\<exists>y\<in>A. y < x) \<Longrightarrow> \<exists>s\<le>x. s \<in> min_elems A\<close>
        using \<open>x \<in> A\<close> unfolding min_elems_def by auto
    qed
  qed
  thus \<open>s \<in> A \<Longrightarrow> \<exists>t\<le>s. t \<in> min_elems A\<close> by auto
qed

lemma min_elems4: \<open>A \<noteq> {} \<Longrightarrow> \<exists>s. (s :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<in> min_elems A\<close>
  by (auto dest: min_elems5)

lemma min_elems_charn: \<open>t \<in> A \<Longrightarrow> \<exists> t' r. t = (t' @ r) \<and> t' \<in> min_elems A\<close>
  by (meson prefixE min_elems5)

lemma min_elems_no: \<open>(s::'a list) \<in> min_elems A \<Longrightarrow> t \<in> A \<Longrightarrow> t \<le> s \<Longrightarrow> s = t\<close>
  by (metis (mono_tags, lifting) mem_Collect_eq min_elems_def order_neq_le_trans)

text\<open> \ldots while the second returns the set of possible
refusal sets after a given trace $s$ and a given process
$P$: \<close>

definition Refusals_after :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close> (\<open>\<R>\<^sub>a\<close>)
  where   \<open>\<R>\<^sub>a P tr \<equiv> {ref. (tr, ref) \<in> \<F> P}\<close>

text\<open> In the following, we link the process theory to the underlying 
fixpoint/domain theory of HOLCF by identifying the approximation ordering 
with HOLCF's pcpo's. \<close>

instantiation 
  process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k  ::  (type, type) below     
begin
text\<open> declares approximation ordering $\_ \sqsubseteq \_$ also written 
        \verb+_ << _+. \<close>

(* TODO: rename this with \<open>below\<close> ? *)

definition le_approx_def : \<open>P \<sqsubseteq> Q \<equiv> \<D> Q \<subseteq> \<D> P \<and>
                                    (\<forall>s. s \<notin> \<D> P \<longrightarrow> \<R>\<^sub>a P s = \<R>\<^sub>a Q s) \<and> 
                                     min_elems (\<D> P) \<subseteq> \<T> Q\<close>

text\<open> The approximation ordering captures the fact that more concrete
processes should be more defined by ordering the divergence sets
appropriately. For defined positions in a process, the failure
sets must coincide pointwise; moreover, the minimal elements
(wrt.~prefix ordering on traces, i.e.~lists) must be contained in
the trace set of the more concrete process.\<close>

instance ..

end


lemma le_approx1: \<open>P \<sqsubseteq> Q \<Longrightarrow> \<D> Q \<subseteq> \<D> P\<close>
  by (simp add: le_approx_def)


lemma le_approx2: \<open>P \<sqsubseteq> Q \<Longrightarrow> s \<notin> \<D> P \<Longrightarrow> ((s, X) \<in> \<F> Q) = ((s, X) \<in> \<F> P)\<close>
  by (auto simp: Refusals_after_def le_approx_def)


lemma le_approx3: \<open>P \<sqsubseteq> Q \<Longrightarrow> min_elems(\<D> P) \<subseteq> \<T> Q\<close>
  by (simp add: le_approx_def)

lemma le_approx2T: \<open>P \<sqsubseteq> Q \<Longrightarrow> s \<notin> \<D> P \<Longrightarrow> s \<in> \<T> Q \<longleftrightarrow> s \<in> \<T> P\<close>
  by (auto simp: le_approx2 T_F_spec[symmetric])

lemma le_approx_lemma_F : \<open>P \<sqsubseteq> Q \<Longrightarrow> \<F> Q \<subseteq> \<F> P\<close>
  by (meson le_approx2 process_charn subrelI)

lemmas order_lemma = le_approx_lemma_F

lemma le_approx_lemma_T: \<open>P \<sqsubseteq> Q \<Longrightarrow> \<T> Q \<subseteq> \<T> P\<close>
  by(auto dest!:le_approx_lemma_F simp: T_F_spec[symmetric])

lemma proc_ord2a : \<open>P \<sqsubseteq> Q \<Longrightarrow> s \<notin> \<D> P \<Longrightarrow> (s, X) \<in> \<F> P \<longleftrightarrow> (s, X) \<in> \<F> Q\<close>
  by (auto simp: le_approx_def Refusals_after_def)


instance process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: (type, type) po
proof intro_classes
  show \<open>P \<sqsubseteq> P\<close> for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (metis D_T elem_min_elems le_approx_def subsetI)
next
  show \<open>P \<sqsubseteq> Q \<Longrightarrow> Q \<sqsubseteq> P \<Longrightarrow> P = Q\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (simp add: Process_eq_spec le_approx1 le_approx_lemma_F subset_antisym)
next
  fix P Q R :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assume \<open>P \<sqsubseteq> Q\<close> and \<open>Q \<sqsubseteq> R\<close>
  show \<open>P \<sqsubseteq> R\<close> 
  proof (unfold le_approx_def, intro conjI allI impI)
    show \<open>\<D> R \<subseteq> \<D> P\<close> by (meson \<open>P \<sqsubseteq> Q\<close> \<open>Q \<sqsubseteq> R\<close> dual_order.trans le_approx1)
  next
    show \<open>s \<notin> \<D> P \<Longrightarrow> \<R>\<^sub>a P s = \<R>\<^sub>a R s\<close> for s
      by (metis \<open>P \<sqsubseteq> Q\<close> \<open>Q \<sqsubseteq> R\<close> le_approx_def subsetD)
  next
    from \<open>P \<sqsubseteq> Q\<close>[THEN le_approx1]  \<open>P \<sqsubseteq> Q\<close>[THEN le_approx3]
      \<open>Q \<sqsubseteq> R\<close>[THEN le_approx2T] \<open>Q \<sqsubseteq> R\<close>[THEN le_approx3]
    show \<open>min_elems (\<D> P) \<subseteq> \<T> R\<close>
      by (simp add: min_elems_def subset_iff) blast
  qed
qed


text\<open> At this point, we inherit quite a number of facts from the underlying
HOLCF theory, which comprises a library of facts such as \verb+chain+,
\verb+directed+(sets), upper bounds and least upper bounds, etc. \<close>

text\<open>
Some facts from the theory of complete partial orders:
\begin{itemize}
\item \verb+po_class.chainE+ : @{thm po_class.chainE}
\item \verb+po_class.chain_mono+ : @{thm po_class.chain_mono}
\item \verb+po_class.is_ubD+ : @{thm po_class.is_ubD}
\item \verb+po_class.ub_rangeI+ : \\ @{thm po_class.ub_rangeI}
\item \verb+po_class.ub_imageD+ : @{thm po_class.ub_imageD}
\item \verb+po_class.is_ub_upward+ : @{thm po_class.is_ub_upward}
\item \verb+po_class.is_lubD1+ : @{thm po_class.is_lubD1}
\item \verb+po_class.is_lubI+ : @{thm po_class.is_lubI}
\item \verb+po_class.is_lub_maximal+ : @{thm po_class.is_lub_maximal}
\item \verb+po_class.is_lub_lub+ : @{thm po_class.is_lub_lub}
\item \verb+po_class.is_lub_range_shift+: \\ @{thm po_class.is_lub_range_shift}
\item \verb+po_class.is_lub_rangeD1+: @{thm po_class.is_lub_rangeD1}
\item \verb+po_class.lub_eqI+: @{thm po_class.lub_eqI}
\item \verb+po_class.is_lub_unique+:@{thm po_class.is_lub_unique}
\end{itemize}
\<close>


lemma min_elems3: \<open>s @ [c] \<in> \<D> P \<Longrightarrow> s @ [c] \<notin> min_elems (\<D> P) \<Longrightarrow> s \<in> \<D> P\<close>
  by (simp add: min_elems_def less_eq_list_def less_list_def)
    (metis D_imp_front_tickFree append.right_neutral front_tickFree_append_iff
      front_tickFree_dw_closed is_processT7 prefix_def)


lemma min_elems1: \<open>s \<notin> \<D> P \<Longrightarrow> s @ [c] \<in> \<D> P \<Longrightarrow> s @ [c] \<in> min_elems (\<D> P)\<close>
  using min_elems3 by blast

lemma min_elems2: \<open>s \<notin> \<D> P \<Longrightarrow> s @ [c] \<in> \<D> P \<Longrightarrow> P \<sqsubseteq> S \<Longrightarrow> Q \<sqsubseteq> S \<Longrightarrow> (s @ [c], {}) \<in> \<F> Q\<close>
  by (meson T_F in_mono le_approx3 le_approx_lemma_F min_elems3)

lemma min_elems6: \<open>s \<notin> \<D> P \<Longrightarrow> s @ [c] \<in> \<D> P \<Longrightarrow> P \<sqsubseteq> S \<Longrightarrow> (s @ [c], {}) \<in> \<F> S\<close>
  by (auto intro!: min_elems2)

lemma ND_F_dir2: \<open>s \<notin> \<D> P \<Longrightarrow> (s, {}) \<in> \<F> P \<Longrightarrow> P \<sqsubseteq> S \<Longrightarrow> Q \<sqsubseteq> S \<Longrightarrow> (s, {}) \<in> \<F> Q\<close>
  by (meson is_processT8 le_approx2)

lemma ND_F_dir2': \<open>s \<notin> \<D> P \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> P \<sqsubseteq> S \<Longrightarrow> Q \<sqsubseteq> S \<Longrightarrow> s \<in> \<T> Q\<close>
  by (meson D_T le_approx2T)


lemma chain_lemma: \<open>chain S \<Longrightarrow> S i \<sqsubseteq> S k \<or> S k \<sqsubseteq> S i\<close>
  by (metis chain_mono_less not_le_imp_less po_class.chain_mono)


context fixes S :: \<open>nat \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assumes \<open>chain S\<close>
begin

lift_definition lim_proc :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  is \<open>(\<Inter> (\<F> ` range S), \<Inter> (\<D> ` range S))\<close>
proof (unfold is_process_def FAILURES_def DIVERGENCES_def fst_conv snd_conv, intro conjI allI impI)
  show \<open>([], {}) \<in> \<Inter> (\<F> ` range S)\<close> by (simp add: is_processT)
next
  show \<open>(s, X) \<in> \<Inter> (\<F> ` range S) \<Longrightarrow> ftF s\<close> for s X
    by (meson INT_iff UNIV_I image_eqI is_processT2)
next
  show \<open>(s @ t, {}) \<in> \<Inter> (\<F> ` range S) \<Longrightarrow>
        (s, {}) \<in> \<Inter> (\<F> ` range S)\<close> for s t by (auto intro: is_processT3)
next
  show \<open>(s, Y) \<in> \<Inter> (\<F> ` range S) \<and> X \<subseteq> Y \<Longrightarrow> (s, X) \<in> \<Inter> (\<F> ` range S)\<close> for s X Y
    by (metis (full_types) INT_iff is_processT4)
next
  show \<open>(s, X \<union> Y) \<in> \<Inter> (\<F> ` range S)\<close>
    if assm : \<open>(s, X) \<in> \<Inter> (\<F> ` range S) \<and>
               (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> \<Inter> (\<F> ` range S))\<close> for s X Y
  proof (rule ccontr)
    assume \<open>(s, X \<union> Y) \<notin> \<Inter> (\<F> ` range S)\<close>
    then obtain i where \<open>(s, X \<union> Y) \<notin> \<F> (S i)\<close> by blast
    moreover have \<open>(s, X) \<in> \<F> (S j)\<close> for j using assm by blast
    ultimately obtain c where \<open>c \<in> Y\<close> and * : \<open>(s @ [c], {}) \<in> \<F> (S i)\<close> 
      using is_processT5 by blast
    from \<open>(s, X \<union> Y) \<notin> \<F> (S i)\<close> is_processT8 have \<open>s \<notin> \<D> (S i)\<close> by blast
    from assm \<open>c \<in> Y\<close> obtain j where ** : \<open>(s @ [c], {}) \<notin> \<F> (S j)\<close> by blast

    from chain_lemma[OF \<open>chain S\<close>, of i j] "*" "**" show False
      by (elim disjE; use \<open>s \<notin> \<D> (S i)\<close> is_processT8 min_elems6 proc_ord2a in blast)
  qed
next
  show \<open>(s @ [\<checkmark>(r)], {}) \<in> \<Inter> (\<F> ` range S) \<Longrightarrow>
        (s, X - {\<checkmark>(r)}) \<in> \<Inter> (\<F> ` range S)\<close> for s r X by (simp add: is_processT6)
next
  show \<open>s \<in> \<Inter> (\<D> ` range S) \<and> tF s \<and> ftF t \<Longrightarrow>
        s @ t \<in> \<Inter> (\<D> ` range S)\<close> for s t by (simp add: is_processT7)
next
  show \<open>s \<in> \<Inter> (\<D> ` range S) \<Longrightarrow> (s, X) \<in> \<Inter> (\<F> ` range S)\<close> for s X
    by (simp add: is_processT8)
next
  show \<open>s @ [\<checkmark>(r)] \<in> \<Inter> (\<D> ` range S) \<Longrightarrow> s \<in> \<Inter> (\<D> ` range S)\<close> for s r
    by (auto intro: is_processT9)
qed


lemma F_LUB: \<open>\<F> lim_proc = \<Inter> (\<F> ` range S)\<close>
  by (metis Failures.rep_eq lim_proc.rep_eq process_surj_pair prod.sel(1))

lemma D_LUB: \<open>\<D> lim_proc = \<Inter> (\<D> ` range S)\<close>
  by (metis Divergences.rep_eq lim_proc.rep_eq process_surj_pair prod.inject)

lemma T_LUB: \<open>\<T> lim_proc = \<Inter> (\<T> ` range S)\<close>
  by (insert F_LUB, auto simp add: T_def_spec) (meson F_T T_F)

lemmas LUB_projs = F_LUB D_LUB T_LUB

lemma Refusals_LUB: \<open>\<R> lim_proc = \<Inter> (\<R> ` range S)\<close>
  by (auto simp add: Refusals_def_bis F_LUB)

lemma Refusals_after_LUB: \<open>\<R>\<^sub>a lim_proc s = (\<Inter>i. (\<R>\<^sub>a (S i) s))\<close>
  by (auto simp add: Refusals_after_def F_LUB)

lemma F_LUB_2: \<open>(s, X) \<in> \<F> lim_proc \<longleftrightarrow> (\<forall>i. (s, X) \<in> \<F> (S i))\<close> 
  and D_LUB_2: \<open>t \<in> \<D> lim_proc \<longleftrightarrow> (\<forall>i. t \<in> \<D> (S i))\<close>
  and T_LUB_2: \<open>t \<in> \<T> lim_proc \<longleftrightarrow> (\<forall>i. t \<in> \<T> (S i))\<close>
  and Refusals_LUB_2: \<open>X \<in> \<R> lim_proc \<longleftrightarrow> (\<forall>i. X \<in> \<R> (S i))\<close>
  and Refusals_after_LUB_2: \<open>X \<in> \<R>\<^sub>a lim_proc s \<longleftrightarrow> (\<forall>i. X \<in> \<R>\<^sub>a (S i) s)\<close>
  by (simp_all add: F_LUB D_LUB T_LUB Refusals_LUB Refusals_after_LUB)

end


text \<open>By exiting the context, terms like \<open>\<F> lim_proc\<close> will become \<^term>\<open>\<F> (lim_proc S)\<close>
      and the assumption \<^term>\<open>chain S\<close> will be added.\<close>


section\<open> Process Refinement is a Partial Ordering\<close>

text\<open> The following type instantiation declares the refinement order
$\_ \le \_ $ written \verb+_  <= _+. It captures the intuition that more
concrete processes should be more deterministic and more defined.\<close>

instantiation process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: (type, type) ord
begin

definition less_eq_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>
  where \<open>less_eq_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P Q \<equiv> \<D> Q \<subseteq> \<D> P \<and> \<F> Q \<subseteq> \<F> P\<close>

definition less_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>
  where \<open>less_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P Q \<equiv> P \<le> Q \<and> P \<noteq> Q\<close>

instance ..

end



text\<open>Note that this just another syntax to our standard process refinement order 
     defined in the theory Process. \<close> 


lemma le_ref1  : \<open>P \<le> Q \<Longrightarrow> \<D> Q \<subseteq> \<D> P\<close>
  and le_ref2  : \<open>P \<le> Q \<Longrightarrow> \<F> Q \<subseteq> \<F> P\<close>
  and le_ref2T : \<open>P \<le> Q \<Longrightarrow> \<T> Q \<subseteq> \<T> P\<close>
  and le_approx_imp_le_ref: \<open>(P::('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<sqsubseteq> Q \<Longrightarrow> P \<le> Q\<close>
  by (simp_all add: less_eq_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def le_approx1 le_approx_lemma_F)
    (use T_F_spec in blast)

lemma F_subset_imp_T_subset : \<open>\<F> P \<subseteq> \<F> Q \<Longrightarrow> \<T> P \<subseteq> \<T> Q\<close>
  using T_F_spec by blast

lemma D_extended_is_D :
  \<open>{t @ u |t u. t \<in> \<D> P \<and> tF t \<and> ftF u} = \<D> P\<close>
  by (auto simp add: is_processT7)
    (metis D_imp_front_tickFree append.right_neutral butlast_snoc front_tickFree_append_iff
      front_tickFree_charn is_processT9 nonTickFree_n_frontTickFree tickFree_Nil)


lemma Process_eq_optimizedI :
  \<open>\<lbrakk>\<And>t. t \<in> \<D> P \<Longrightarrow> t \<in> \<D> Q; \<And>t. t \<in> \<D> Q \<Longrightarrow> t \<in> \<D> P;
    \<And>t X. (t, X) \<in> \<F> P \<Longrightarrow> t \<notin> \<D> P \<Longrightarrow> t \<notin> \<D> Q \<Longrightarrow> (t, X) \<in> \<F> Q;
    \<And>t X. (t, X) \<in> \<F> Q \<Longrightarrow> t \<notin> \<D> Q \<Longrightarrow> t \<notin> \<D> P \<Longrightarrow> (t, X) \<in> \<F> P\<rbrakk> \<Longrightarrow> P = Q\<close>
  by (simp add: Process_eq_spec_optimized, safe, auto intro: is_processT8)



instance  process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: (type, type) order
  by intro_classes (auto simp: less_eq_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def less_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def Process_eq_spec)


lemma lim_proc_is_ub: \<open>chain S \<Longrightarrow> range S <| lim_proc S\<close>
  by (simp add: is_ub_def le_approx_def F_LUB D_LUB T_LUB Refusals_after_def)
    (intro allI conjI, blast, use chain_lemma is_processT8 le_approx2 in blast,
      use D_T chain_lemma le_approx2T le_approx_def in blast)


(* 
lemma lim_proc_is_lub3a: \<open>front_tickFree s \<Longrightarrow> s \<notin> \<D> P \<Longrightarrow> t \<in> \<D> P \<Longrightarrow> \<not> t < s @ [c]\<close>
  by (auto simp: le_list_def  less_list_def)
     (metis butlast_append butlast_snoc front_tickFree_append_iff process_charn self_append_conv)
 *)


lemma chain_min_elem_div_is_min_for_sequel:
  \<open>chain S \<Longrightarrow> s \<in> min_elems (\<D> (S i)) \<Longrightarrow> i \<le> j \<Longrightarrow> s \<in> \<D> (S j) \<Longrightarrow> s \<in> min_elems (\<D> (S j))\<close>
  by (metis elem_min_elems insert_absorb insert_subset le_approx1 
      min_elems5 min_elems_no po_class.chain_mono)


lemma limproc_is_lub: \<open>range S <<| lim_proc S\<close> if \<open>chain S\<close>
proof (unfold is_lub_def, intro conjI allI impI)
  show \<open>range S <| lim_proc S\<close> by (simp add: lim_proc_is_ub \<open>chain S\<close>)
next
  show \<open>lim_proc S \<sqsubseteq> P\<close> if \<open>range S <| P\<close> for P
  proof (unfold le_approx_def, intro conjI allI impI subsetI)
    show \<open>s \<in> \<D> P \<Longrightarrow> s \<in> \<D> (lim_proc S)\<close> for s
      by (meson D_LUB_2 \<open>chain S\<close> \<open>range S <| P\<close> is_ub_def le_approx1 rangeI subsetD)
  next
    show \<open>s \<notin> \<D> (lim_proc S) \<Longrightarrow> \<R>\<^sub>a (lim_proc S) s = \<R>\<^sub>a P s\<close> for s
      by (metis \<open>chain S\<close> \<open>range S <| P\<close> D_LUB_2 le_approx_def lim_proc_is_ub ub_rangeD)
  next
    fix s
    assume \<open>s \<in> min_elems (\<D> (lim_proc S))\<close>
    from elem_min_elems[OF this] have \<open>\<forall>i. s \<in> \<D> (S i)\<close>
      by (simp add: \<open>chain S\<close> D_LUB)
    have \<open>\<exists>i. \<forall>j\<ge>i. s \<in> min_elems (\<D> (S j))\<close>
    proof (rule ccontr)
      assume \<open>\<nexists>i. \<forall>j\<ge>i. s \<in> min_elems (\<D> (S j))\<close>
      hence \<open>\<forall>i. \<exists>j\<ge>i. s \<notin> min_elems (\<D> (S j))\<close> by simp
      with \<open>\<forall>i. s \<in> \<D> (S i)\<close> chain_min_elem_div_is_min_for_sequel \<open>chain S\<close>
      have \<open>\<forall>j. s \<notin> min_elems (\<D> (S j))\<close> by blast
      from \<open>s \<in> min_elems (\<D> (lim_proc S))\<close> \<open>\<forall>i. s \<in> \<D> (S i)\<close> show False
        by (cases s rule: rev_cases; simp add: min_elems_def D_LUB \<open>chain S\<close>)
          (use Nil_min_elems \<open>\<forall>j. s \<notin> min_elems (\<D> (S j))\<close> in blast,
            metis (no_types, lifting) INT_iff \<open>\<forall>j. s \<notin> min_elems (\<D> (S j))\<close> less_self min_elems3)
    qed
    thus \<open>s \<in> \<T> P\<close> by (meson le_approx3 order.refl subset_eq \<open>range S <| P\<close> ub_rangeD)
  qed
qed


lemma limproc_is_thelub: \<open>chain S \<Longrightarrow> (\<Squnion>i. S i) = lim_proc S\<close>
  by (frule limproc_is_lub, frule po_class.lub_eqI, simp)


instance process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: (type, type) cpo
  by intro_classes (use limproc_is_lub in blast)



instance process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: (type, type) pcpo
proof
  define bot\<^sub>0 :: \<open>('a, 'r) process\<^sub>0\<close> where \<open>bot\<^sub>0 \<equiv> ({(s, X). ftF s}, {d. ftF d})\<close>
  define bot :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>bot \<equiv> process_of_process\<^sub>0 bot\<^sub>0\<close>

  have \<open>is_process bot\<^sub>0\<close>
    unfolding is_process_def bot\<^sub>0_def
    by (simp add: FAILURES_def DIVERGENCES_def)
      (meson front_tickFree_append_iff front_tickFree_dw_closed)
  have F_bot : \<open>\<F> bot = {(s, X). ftF s}\<close>
    by (metis CollectI FAILURES_def Failures.rep_eq \<open>is_process bot\<^sub>0\<close> 
        bot\<^sub>0_def bot_def fst_eqD process_of_process\<^sub>0_inverse)
  have D_bot : \<open>\<D> bot = {d. ftF d}\<close>
    by (metis CollectI DIVERGENCES_def Divergences.rep_eq \<open>is_process bot\<^sub>0\<close>
        bot\<^sub>0_def bot_def process_of_process\<^sub>0_inverse prod.sel(2))

  show \<open>\<exists>x :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k. \<forall> y. x \<sqsubseteq> y\<close> 
  proof (intro exI allI)
    show \<open>bot \<sqsubseteq> y\<close> for y
    proof (unfold le_approx_def, intro conjI allI impI subsetI)
      show \<open>s \<in> \<D> y \<Longrightarrow> s \<in> \<D> bot\<close> for s
        by (simp add: D_bot D_imp_front_tickFree)
    next
      from F_imp_front_tickFree show \<open>s \<notin> \<D> bot \<Longrightarrow> \<R>\<^sub>a bot s = \<R>\<^sub>a y s\<close> for s
        by (auto simp add: D_bot Refusals_after_def F_bot)
    next
      show \<open>s \<in> min_elems (\<D> bot) \<Longrightarrow> s \<in> \<T> y\<close> for s
        by (simp add: D_bot min_elems_Collect_ftF_is_Nil)
    qed
  qed
qed



section\<open> Process Refinement is Admissible \<close>

lemma le_FD_adm : \<open>cont (u :: ('b::cpo) \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<Longrightarrow> monofun v \<Longrightarrow> adm (\<lambda>x. u x \<le> v x)\<close>
  apply (unfold less_eq_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def adm_def)
  apply (simp add: cont2contlubE D_LUB F_LUB ch2ch_cont limproc_is_thelub monofun_def)
  by (meson INF_greatest dual_order.trans is_ub_thelub le_approx1 le_approx_lemma_F)

lemmas le_FD_adm_cont[simp] = le_FD_adm[OF _ cont2mono]

section\<open> The Conditional Statement is Continuous \<close>
text\<open>The conditional operator of CSP is obtained by a direct shallow embedding. Here we prove it continuous\<close>

lemma if_then_else_cont[simp]:
  \<open>\<lbrakk>\<And>x. P x \<Longrightarrow> cont (f x); \<And>x. \<not> P x \<Longrightarrow> cont (g x)\<rbrakk> \<Longrightarrow>
   cont (\<lambda>y. if P x then f x y else g x y)\<close>
  for f :: \<open>'c \<Rightarrow> 'b :: cpo \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  by (auto simp: cont_def)


section \<open>Tools for proving continuity\<close>

\<comment> \<open>The following result is very useful (especially for ProcOmata).\<close>

lemma cont_process_rec: \<open>P = (\<mu> X. f X) \<Longrightarrow> cont f \<Longrightarrow> P = f P\<close>
  by (simp add: def_cont_fix_eq)


lemma Inter_nonempty_finite_chained_sets: \<open>(\<Inter>i. S i) \<noteq> {}\<close>
  if \<open>\<And>i. j \<le> i \<Longrightarrow> S i \<noteq> {}\<close> \<open>finite (S j)\<close> \<open>\<And>i. S (Suc i) \<subseteq> S i\<close> for S :: \<open>nat \<Rightarrow> 'a set\<close>
proof -
  have * : \<open>\<forall>i. S i \<noteq> {} \<Longrightarrow> finite (S 0) \<Longrightarrow> \<forall>i. S (Suc i) \<subseteq> S i \<Longrightarrow> (\<Inter>i. S i) \<noteq> {}\<close>
    for S :: \<open>nat \<Rightarrow> 'a set\<close>
  proof (induct \<open>card (S 0)\<close> arbitrary: S rule: nat_less_induct)
    case 1
    show ?case
    proof (cases \<open>\<forall>i. S i = S 0\<close>)
      case True
      thus ?thesis by (metis "1.prems"(1) INT_iff ex_in_conv)
    next 
      case False
      have f1: \<open>i \<le> j \<Longrightarrow> S j \<subseteq> S i\<close> for i j by (simp add: "1.prems"(3) lift_Suc_antimono_le)
      with False obtain j m where f2: \<open>m < card (S 0)\<close> and f3: \<open>m = card (S j)\<close>
        by (metis "1.prems"(2) psubsetI psubset_card_mono zero_le)
      define T where \<open>T i \<equiv> S (i + j)\<close> for i
      have f4: \<open>m = card (T 0)\<close> unfolding T_def by (simp add: f3)
      from f1 have f5: \<open>(\<Inter>i. S i) = (\<Inter>i. T i)\<close> unfolding T_def by (auto intro: le_add1)
      show ?thesis
        apply (subst f5)
        apply (rule "1.hyps"[rule_format, OF f2, of T, OF f4], unfold T_def)
        by (simp_all add: "1.prems"(1, 3) lift_Suc_antimono_le)
          (metis "1.prems"(2) add_0 f1 finite_subset le_add1)
    qed
  qed
  define S' where \<open>S' i \<equiv> S (j + i)\<close> for i
  have \<open>\<forall>i. S' i \<noteq> {}\<close> by (simp add: S'_def \<open>\<And>i. j \<le> i \<Longrightarrow> S i \<noteq> {}\<close>)
  moreover have \<open>finite (S' 0)\<close> by (simp add: \<open>S' \<equiv> \<lambda>i. S (j + i)\<close> \<open>finite (S j)\<close>)
  moreover have \<open>\<forall>i. S' (Suc i) \<subseteq> S' i\<close> by (simp add: S'_def \<open>\<And>i. S (Suc i) \<subseteq> S i\<close>)
  ultimately have \<open>(\<Inter>i. S' i) \<noteq> {}\<close> by (fact "*")
  also from lift_Suc_antimono_le[where f = S, OF \<open>\<And>i. S (Suc i) \<subseteq> S i\<close>]
  have \<open>(\<Inter>i. S' i) = (\<Inter>i. S i)\<close>
    by (simp add: INF_greatest INF_lower INF_mono' S'_def equalityI)
  finally show \<open>(\<Inter>i. S i) \<noteq> {}\<close> .
qed


method prove_finite_subset_of_prefixes for t :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> =
  \<comment>\<open>Useful for establishing the second hypothesis\<close>
  solves \<open>(rule finite_UnI; prove_finite_subset_of_prefixes t) |
          (rule finite_subset[of _ \<open>{u. u \<le> t}\<close>],
           use prefixI in blast, simp add: prefixes_fin)\<close>


(*<*)
end
  (*>*)