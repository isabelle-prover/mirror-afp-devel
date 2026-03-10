(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
 *         CNRS, ENS Paris-Saclay, LMF
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)


chapter \<open>Some Work on Renaming\<close>

(*<*)
theory CSP_PTick_Renaming
  imports "HOL-CSPM" Synchronization_Product_Generalized
begin
  (*>*)

unbundle option_type_syntax


text \<open>
This chapter contains several developments related to the \<^const>\<open>Renaming\<close> operator.
Some are not directly related to this session and may be moved
to \<^session>\<open>HOL-CSP\<close> or \<^session>\<open>HOL-CSPM\<close> in the future,
while others specifically concern the operator \<^const>\<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>. 
\<close>


section \<open>Tick Swap Operator\<close>

text \<open>We want to define an operator for swapping the values inside termination.
      Intuitively, we want \<^term>\<open>TickSwap (SKIP (r, s)) = SKIP (s, r)\<close>.\<close>

subsection \<open>Preliminaries\<close>

subsubsection \<open>Swapping an Event\<close>

text \<open>We start by defining \<^term>\<open>tick_swap\<close>, which is swapping the values inside termination
      but only for an event. Then this will be generalized to a trace, a refusal and a failure.\<close>


fun tick_swap :: \<open>('a, 'r \<times> 's) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 's \<times> 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>tick_swap (ev a) = ev a\<close>
  |     \<open>tick_swap \<checkmark>((r, s)) = \<checkmark>((s, r))\<close>


lemma tick_swap_tick : \<open>tick_swap \<checkmark>(r_s) = (case r_s of (r, s) \<Rightarrow> \<checkmark>((s, r)))\<close>
  by (cases r_s) simp


lemma tick_swap_tick_swap [simp] : \<open>tick_swap (tick_swap e) = e\<close>
proof (cases e)
  show \<open>e = ev a \<Longrightarrow> tick_swap (tick_swap e) = e\<close> for a by simp
next
  show \<open>e = \<checkmark>(r_s) \<Longrightarrow> tick_swap (tick_swap e) = e\<close> for r_s
    by (cases r_s) simp_all
qed

lemma tick_swap_comp_tick_swap [simp] : \<open>tick_swap \<circ> tick_swap = id\<close>
  by (rule ext) simp

lemma inj_tick_swap [simp] : \<open>inj tick_swap\<close>
  by (metis injI tick_swap_tick_swap)

lemma surj_tick_swap [simp] : \<open>surj tick_swap\<close>
  by (metis surjI tick_swap_tick_swap)

lemma bij_tick_swap [simp] : \<open>bij tick_swap\<close>
  by (simp add: bij_betw_def)

lemma bij_betw_tick_swap :
  \<open>bij_betw tick_swap (range ev  ) (range ev  )\<close>
  \<open>bij_betw tick_swap (range tick) (range tick)\<close>
  by (auto simp add: bij_betw_def inj_on_def set_eq_iff image_iff)


lemma ev_eq_tick_swap_iff   [simp] : \<open>ev a = tick_swap e \<longleftrightarrow> e = ev a\<close>
  and tick_swap_eq_ev_iff   [simp] : \<open>tick_swap e = ev a \<longleftrightarrow> e = ev a\<close>
  and tick_eq_tick_swap_iff [simp] : \<open>\<checkmark>((r, s)) = tick_swap e \<longleftrightarrow> e = \<checkmark>((s, r))\<close>
  and tick_swap_eq_tick_iff [simp] : \<open>tick_swap e = \<checkmark>((r, s)) \<longleftrightarrow> e = \<checkmark>((s, r))\<close>
  by (cases e, auto)+



subsubsection \<open>Swapping a Trace\<close>

fun trace_tick_swap :: \<open>('a, ('r \<times> 's)) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, ('s \<times> 'r)) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>trace_tick_swap [] = []\<close>
  |     \<open>trace_tick_swap (ev a # t) = ev a # trace_tick_swap t\<close>
  |     \<open>trace_tick_swap (\<checkmark>((r, s)) # t) = \<checkmark>((s, r)) # trace_tick_swap t\<close>


lemma trace_tick_swap_tick_Cons :
  \<open>trace_tick_swap (\<checkmark>(r_s) # t) = (case r_s of (r, s) \<Rightarrow> \<checkmark>((s, r)) # trace_tick_swap t)\<close>
  by (cases r_s) simp


lemma trace_tick_swap_def : \<open>trace_tick_swap = map tick_swap\<close>
proof (rule ext)
  show \<open>trace_tick_swap t = map tick_swap t\<close> for t :: \<open>('a, ('r \<times> 's)) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (induct t rule: trace_tick_swap.induct) simp_all
qed

lemma trace_tick_swap_append : \<open>trace_tick_swap (t @ u) = trace_tick_swap t @ trace_tick_swap u\<close>
  by (simp add: trace_tick_swap_def)

lemma trace_tick_swap_singl [simp] : \<open>trace_tick_swap [e] = [tick_swap e]\<close>
  by (cases e) auto

lemma trace_tick_swap_comp_trace_tick_swap [simp] : \<open>trace_tick_swap \<circ> trace_tick_swap = id\<close>
  by (simp add: trace_tick_swap_def)

lemma trace_tick_swap_trace_tick_swap [simp] : \<open>trace_tick_swap (trace_tick_swap t) = t\<close>
  by (metis comp_def id_apply trace_tick_swap_comp_trace_tick_swap)


lemma inj_trace_tick_swap [simp] : \<open>inj trace_tick_swap\<close>
  by (metis injI trace_tick_swap_trace_tick_swap)

lemma surj_trace_tick_swap [simp] : \<open>surj trace_tick_swap\<close>
  by (metis surjI trace_tick_swap_trace_tick_swap)

lemma bij_trace_tick_swap [simp] : \<open>bij trace_tick_swap\<close>
  by (simp add: bij_betw_def)

lemma strict_mono_trace_tick_swap : \<open>strict_mono trace_tick_swap\<close>
  by (unfold trace_tick_swap_def)
    (rule strict_mono_map, simp add: strict_monoI)

lemma image_trace_tick_swap_min_elems :
  \<open>trace_tick_swap ` (min_elems T) = min_elems (trace_tick_swap ` T)\<close>
proof (intro subset_antisym subsetI)
  show \<open>t \<in> trace_tick_swap ` min_elems T \<Longrightarrow> t \<in> min_elems (trace_tick_swap ` T)\<close> for t
    by (auto simp add: min_elems_def less_list_def less_eq_list_def prefix_def)
      (metis Prefix_Order.prefixI Prefix_Order.same_prefix_nil
        trace_tick_swap_append trace_tick_swap_trace_tick_swap)
next
  show \<open>t \<in> min_elems (trace_tick_swap ` T) \<Longrightarrow> t \<in> trace_tick_swap ` min_elems T\<close> for t
    by (auto simp add: min_elems_def less_list_def less_eq_list_def prefix_def image_iff)
      (metis trace_tick_swap_append trace_tick_swap_trace_tick_swap)   
qed


lemma Nil_eq_trace_tick_swap_iff [iff] : \<open>[] = trace_tick_swap t \<longleftrightarrow> t = []\<close>
  and trace_tick_swap_eq_Nil_iff [iff] : \<open>trace_tick_swap t = [] \<longleftrightarrow> t = []\<close>
  by (metis trace_tick_swap.simps(1) trace_tick_swap_trace_tick_swap)+


lemma ev_Cons_eq_trace_tick_swap_iff [iff] :
  \<open>ev a # t = trace_tick_swap u \<longleftrightarrow> u = ev a # trace_tick_swap t\<close>
  and trace_tick_swap_eq_ev_Cons_iff [iff] :
  \<open>trace_tick_swap u = ev a # t \<longleftrightarrow> u = ev a # trace_tick_swap t\<close>
  by (metis trace_tick_swap.simps(2) trace_tick_swap_trace_tick_swap)+

lemma tick_Cons_eq_trace_tick_swap_iff [iff] :
  \<open>\<checkmark>((r, s)) # t = trace_tick_swap u \<longleftrightarrow> u = \<checkmark>((s, r)) # trace_tick_swap t\<close>
  and trace_tick_swap_eq_tick_Cons_iff [iff] :
  \<open>trace_tick_swap u = \<checkmark>((r, s)) # t \<longleftrightarrow> u = \<checkmark>((s, r)) # trace_tick_swap t\<close>
  by (metis trace_tick_swap.simps(3) trace_tick_swap_trace_tick_swap)+


lemma snoc_ev_eq_trace_tick_swap_iff [iff] :
  \<open>t @ [ev a] = trace_tick_swap u \<longleftrightarrow> u = trace_tick_swap t @ [ev a]\<close>
  and trace_tick_swap_eq_snoc_ev_iff [iff] :
  \<open>trace_tick_swap u = t @ [ev a] \<longleftrightarrow> u = trace_tick_swap t @ [ev a]\<close>
  by (metis trace_tick_swap_append trace_tick_swap.simps(1, 2) trace_tick_swap_trace_tick_swap)+

lemma snoc_tick_eq_trace_tick_swap_iff [iff] :
  \<open>t @ [\<checkmark>((r, s))] = trace_tick_swap u \<longleftrightarrow> u = trace_tick_swap t @ [\<checkmark>((s, r))]\<close>
  and trace_tick_swap_eq_snoc_tick_iff [iff] :
  \<open>trace_tick_swap u = t @ [\<checkmark>((r, s))] \<longleftrightarrow> u = trace_tick_swap t @ [\<checkmark>((s, r))]\<close>
  by (metis trace_tick_swap_append trace_tick_swap.simps(1, 3) trace_tick_swap_trace_tick_swap)+


lemma trace_tick_swap_eq_ev_ConsE :
  \<open>trace_tick_swap u = ev a # t \<Longrightarrow> (\<And>u'. u = ev a # u' \<Longrightarrow> t = trace_tick_swap u' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  and trace_tick_swap_eq_tick_ConsE :
  \<open>trace_tick_swap u = \<checkmark>((r, s)) # t \<Longrightarrow> (\<And>u'. u = \<checkmark>((s, r)) # u' \<Longrightarrow> t = trace_tick_swap u' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  and trace_tick_swap_eq_snoc_evE :
  \<open>trace_tick_swap u = t @ [ev a] \<Longrightarrow> (\<And>u'. u = u' @ [ev a] \<Longrightarrow> t = trace_tick_swap u' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  and trace_tick_swap_eq_snoc_tickE :
  \<open>trace_tick_swap u = t @ [\<checkmark>((r, s))] \<Longrightarrow> (\<And>u'. u = u' @ [\<checkmark>((s, r))] \<Longrightarrow> t = trace_tick_swap u' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  by (simp, metis trace_tick_swap_trace_tick_swap)+


lemma trace_tick_swap_tickFree :
  \<open>tF t \<Longrightarrow> trace_tick_swap t = map (ev \<circ> of_ev) t\<close> for t :: \<open>('a, ('r \<times> 's)) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (induct t)
  show \<open>trace_tick_swap [] = map (ev \<circ> of_ev) []\<close> by simp
next
  fix e and t :: \<open>('a, ('r \<times> 's)) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assume \<open>tF (e # t)\<close> and \<open>tF t \<Longrightarrow> trace_tick_swap t = map (ev \<circ> of_ev) t\<close>
  moreover from \<open>tF (e # t)\<close> obtain a where \<open>e = ev a\<close> \<open>tF t\<close>
    by (meson is_ev_def tickFree_Cons_iff)
  ultimately show  \<open>trace_tick_swap (e # t) = map (ev \<circ> of_ev) (e # t)\<close> by simp
qed

lemma trace_tick_swap_front_tickFree :
  \<open>trace_tick_swap t = (  if tF t then map (ev \<circ> of_ev) t
                  else map (ev \<circ> of_ev) (butlast t) @ [case last t of \<checkmark>((r, s)) \<Rightarrow> \<checkmark>((s, r))])\<close>
  if \<open>ftF t\<close> for t :: \<open>('a, ('r \<times> 's)) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof -
  show ?thesis
  proof (split if_split, intro conjI impI)
    show \<open>tF t \<Longrightarrow> trace_tick_swap t = map (ev \<circ> of_ev) t\<close>
      by (simp add: trace_tick_swap_tickFree)
  next
    assume \<open>\<not> tF t\<close>
    with \<open>ftF t\<close> obtain t' r s where \<open>t = t' @ [\<checkmark>((r, s))]\<close> \<open>tF t'\<close>
      by (metis front_tickFree_append_iff nonTickFree_n_frontTickFree not_Cons_self2 surj_pair)
    hence \<open>trace_tick_swap t = trace_tick_swap t' @ [\<checkmark>((s, r))]\<close>
      by (metis trace_tick_swap_append trace_tick_swap.simps(1, 3))
    also from \<open>tF t'\<close> \<open>t = t' @ [\<checkmark>((r, s))]\<close>
    have \<open>trace_tick_swap t' = map (ev \<circ> of_ev) (butlast t)\<close> by (simp add: trace_tick_swap_tickFree)
    also from \<open>t = t' @ [\<checkmark>((r, s))]\<close>
    have \<open>[\<checkmark>((s, r))] = [case last t of \<checkmark>((r, s)) \<Rightarrow> \<checkmark>((s, r))]\<close> by simp
    finally show \<open>trace_tick_swap t = map (ev \<circ> of_ev) (butlast t) @
                                [case last t of \<checkmark>((r, s)) \<Rightarrow> \<checkmark>((s, r))]\<close> .
  qed
qed


lemma tickFree_trace_tick_swap_iff [simp] : \<open>tF (trace_tick_swap t) \<longleftrightarrow> tF t\<close>
  by (metis tickFree_map_ev_comp trace_tick_swap_tickFree trace_tick_swap_trace_tick_swap)

lemma front_tickFree_trace_tick_swap_iff [simp] : \<open>ftF (trace_tick_swap t) \<longleftrightarrow> ftF t\<close>
  by (metis (no_types, lifting) front_tickFree_iff_tickFree_butlast map_butlast
      tickFree_trace_tick_swap_iff trace_tick_swap_def)



subsubsection \<open>Swapping a Refusal\<close>

definition refusal_tick_swap :: \<open>('a, ('r \<times> 's)) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, ('s \<times> 'r)) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>refusal_tick_swap X = tick_swap ` X\<close>

lemma refusal_tick_swap_empty  [simp] : \<open>refusal_tick_swap {} = {}\<close>
  by (simp add: refusal_tick_swap_def)

lemma refusal_tick_swap_insert [simp] :
  \<open>refusal_tick_swap (insert x X) = insert (tick_swap x) (refusal_tick_swap X)\<close>
  by (simp add: refusal_tick_swap_def)

lemma refusal_tick_swap_union :
  \<open>refusal_tick_swap (X \<union> Y) = refusal_tick_swap X \<union> refusal_tick_swap Y\<close>
  by (simp add: refusal_tick_swap_def image_Un)

lemma refusal_tick_swap_diff :
  \<open>refusal_tick_swap (X - Y) = refusal_tick_swap X - refusal_tick_swap Y\<close>
  by (simp add: refusal_tick_swap_def image_set_diff)

lemma refusal_tick_swap_inter :
  \<open>refusal_tick_swap (X \<inter> Y) = refusal_tick_swap X \<inter> refusal_tick_swap Y\<close>
  by (simp add: refusal_tick_swap_def image_Int)

lemma refusal_tick_swap_singl : \<open>refusal_tick_swap {e} = {tick_swap e}\<close> by simp

lemma refusal_tick_swap_comp_refusal_tick_swap [simp] :
  \<open>refusal_tick_swap \<circ> refusal_tick_swap = id\<close>
  by (auto simp add: refusal_tick_swap_def image_iff)

lemma refusal_tick_swap_refusal_tick_swap [simp] :
  \<open>refusal_tick_swap (refusal_tick_swap X) = X\<close>
  by (simp add: comp_eq_dest_lhs)


lemma inj_refusal_tick_swap [simp] : \<open>inj refusal_tick_swap\<close>
  by (metis injI refusal_tick_swap_refusal_tick_swap)

lemma surj_refusal_tick_swap [simp] : \<open>surj refusal_tick_swap\<close>
  by (metis surjI refusal_tick_swap_refusal_tick_swap)

lemma bij_refusal_tick_swap [simp] : \<open>bij refusal_tick_swap\<close>
  by (simp add: bij_betw_def)

lemma strict_mono_refusal_tick_swap : \<open>strict_mono refusal_tick_swap\<close>
  by (rule strict_monoI)
    (metis refusal_tick_swap_refusal_tick_swap sup.strict_order_iff refusal_tick_swap_union)


lemma empty_eq_refusal_tick_swap_iff [iff] : \<open>{} = refusal_tick_swap X \<longleftrightarrow> X = {}\<close>
  and refusal_tick_swap_eq_empty_iff [iff] : \<open>refusal_tick_swap X = {} \<longleftrightarrow> X = {}\<close>
  by (simp_all add: refusal_tick_swap_def)

lemma insert_ev_eq_refusal_tick_swap_iff [iff] :
  \<open>insert (ev a) X = refusal_tick_swap Y \<longleftrightarrow> Y = insert (ev a) (refusal_tick_swap X)\<close>
  and refusal_tick_swap_eq_insert_ev_iff [iff] :
  \<open>refusal_tick_swap Y =insert (ev a) X \<longleftrightarrow> Y = insert (ev a) (refusal_tick_swap X)\<close>
  by (metis refusal_tick_swap_insert refusal_tick_swap_refusal_tick_swap tick_swap.simps(1))+

lemma insert_tick_eq_refusal_tick_swap_iff [iff] :
  \<open>insert \<checkmark>((r, s)) X = refusal_tick_swap Y \<longleftrightarrow> Y = insert \<checkmark>((s, r)) (refusal_tick_swap X)\<close>
  and refusal_tick_swap_eq_insert_tick_iff [iff] :
  \<open>refusal_tick_swap Y = insert \<checkmark>((r, s)) X \<longleftrightarrow> Y = insert \<checkmark>((s, r)) (refusal_tick_swap X)\<close>
  by (metis refusal_tick_swap_insert refusal_tick_swap_refusal_tick_swap tick_swap.simps(2))+


lemma refusal_tick_swap_eq_insert_evE :
  \<open>refusal_tick_swap Y = insert (ev a) X \<Longrightarrow> (\<And>Y'. Y = insert (ev a) Y' \<Longrightarrow> X = refusal_tick_swap Y' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  and refusal_tick_swap_eq_insert_tickE :
  \<open>refusal_tick_swap Y = insert \<checkmark>((r, s)) X \<Longrightarrow> (\<And>Y'. Y = insert \<checkmark>((s, r)) Y' \<Longrightarrow> X = refusal_tick_swap Y' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  by (simp, metis refusal_tick_swap_refusal_tick_swap)+

lemma refusal_tick_swap_tickFree :
  \<open>X \<subseteq> range ev \<Longrightarrow> refusal_tick_swap X = (ev \<circ> of_ev) ` X\<close>
  by (force simp add: refusal_tick_swap_def)

lemma tickFree_refusal_tick_swap_iff :
  \<open>refusal_tick_swap X \<subseteq> range ev \<longleftrightarrow> X \<subseteq> range ev\<close>
  by (simp add: refusal_tick_swap_def subset_iff image_def)
    (metis tick_swap.simps(1) tick_swap_tick_swap)


text \<open>The old version of interleaving of traces is not affected.\<close>

lemma setinterleaves_imp_setinterleaves_trace_tick_swap :
  \<open>t setinterleaves ((u, v), S) \<Longrightarrow>
   trace_tick_swap t setinterleaves ((trace_tick_swap u, trace_tick_swap v), refusal_tick_swap S)\<close>
proof (induct \<open>(u, S, v)\<close> arbitrary: t u v rule: setinterleaving.induct)
  case 1 thus ?case by simp
next
  case (2 y v)
  from "2.prems" obtain t' where \<open>y \<notin> S\<close> \<open>t = y # t'\<close> \<open>t' setinterleaves (([], v), S)\<close>
    by (auto split: if_split_asm)
  from "2.hyps"[OF \<open>y \<notin> S\<close> \<open>t' setinterleaves (([], v), S)\<close>]
  have \<open>trace_tick_swap t' setinterleaves (([], trace_tick_swap v), refusal_tick_swap S)\<close> by simp
  with \<open>y \<notin> S\<close> show ?case by (cases y) (auto simp add: \<open>t = y # t'\<close> refusal_tick_swap_def split: prod.split)
next
  case (3 x u)
  from "3.prems" obtain t' where \<open>x \<notin> S\<close> \<open>t = x # t'\<close> \<open>t' setinterleaves ((u, []), S)\<close>
    by (auto split: if_split_asm)
  from "3.hyps"[OF \<open>x \<notin> S\<close> \<open>t' setinterleaves ((u, []), S)\<close>]
  have \<open>trace_tick_swap t' setinterleaves ((trace_tick_swap u, []), refusal_tick_swap S)\<close> by simp
  with \<open>x \<notin> S\<close> show ?case by (cases x) (auto simp add: \<open>t = x # t'\<close> refusal_tick_swap_def split: prod.split)
next
  case (4 x u y v)
  from "4.prems"
  consider (both_in)   t' where \<open>x \<in> S\<close> \<open>y \<in> S\<close> \<open>x = y\<close> \<open>t = x # t'\<close> \<open>t' setinterleaves ((u, v), S)\<close>
    |      (inR_mvL)   t' where \<open>x \<notin> S\<close> \<open>y \<in> S\<close> \<open>t = x # t'\<close> \<open>t' setinterleaves ((u, y # v), S)\<close>
    |      (inL_mvR)   t' where \<open>x \<in> S\<close> \<open>y \<notin> S\<close> \<open>t = y # t'\<close> \<open>t' setinterleaves ((x # u, v), S)\<close>
    |      (notin_mvL) t' where \<open>x \<notin> S\<close> \<open>y \<notin> S\<close> \<open>t = x # t'\<close> \<open>t' setinterleaves ((u, y # v), S)\<close>
    |      (notin_mvR) t' where \<open>x \<notin> S\<close> \<open>y \<notin> S\<close> \<open>t = y # t'\<close> \<open>t' setinterleaves ((x # u, v), S)\<close>
    by (auto split: if_split_asm)
  thus ?case
  proof cases
    case both_in
    from "4.hyps"(1)[OF both_in(1-3, 5)] both_in(1-3)
    show ?thesis by (cases y, auto simp add: both_in(4) refusal_tick_swap_def split: prod.split)
  next
    case inR_mvL
    have \<open>\<not> y \<notin> S\<close> by (simp add: inR_mvL(2))
    from "4.hyps"(5)[OF inR_mvL(1) \<open>\<not> y \<notin> S\<close> inR_mvL(4)] inR_mvL(1, 2)
    show ?thesis by (cases x, auto simp add: inR_mvL(3) refusal_tick_swap_def SyncSingleHeadAdd image_iff split: prod.split)
  next
    case inL_mvR
    have * : \<open>a setinterleaves ((t, u), tick_swap ` S) \<Longrightarrow> h \<notin> tick_swap ` S \<Longrightarrow>
              (h # a) setinterleaves ((t, h # u), tick_swap ` S)\<close> for a t h u
      by (cases t, auto split: if_split_asm)
    from "4.hyps"(2)[OF inL_mvR(1, 2, 4)] inL_mvR(1, 2)
    show ?thesis by (cases y, auto simp add: inL_mvR(3) refusal_tick_swap_def image_iff "*" split: prod.split)
  next
    case notin_mvL
    from "4.hyps"(3)[OF notin_mvL(1, 2, 4)] notin_mvL(1, 2)
    show ?thesis by (cases y, auto simp add: notin_mvL(3) refusal_tick_swap_def split: prod.split)
        (simp_all add: inj_image_mem_iff trace_tick_swap_def)
  next
    case notin_mvR
    from "4.hyps"(4)[OF notin_mvR(1, 2, 4)] notin_mvR(1, 2)
    show ?thesis by (cases x, auto simp add: notin_mvR(3) refusal_tick_swap_def split: prod.split)
        (simp_all add: inj_image_mem_iff trace_tick_swap_def)
  qed
qed


lemma trace_tick_swap_setinterleaves_iff :
  \<open>trace_tick_swap t setinterleaves ((u, v), S) \<longleftrightarrow>
   t setinterleaves ((trace_tick_swap u, trace_tick_swap v), refusal_tick_swap S)\<close>
  by (metis refusal_tick_swap_refusal_tick_swap trace_tick_swap_trace_tick_swap
      setinterleaves_imp_setinterleaves_trace_tick_swap)



subsubsection \<open>Swapping a Failure\<close>

definition failure_tick_swap :: \<open>('a, ('r \<times> 's)) failure\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, ('s \<times> 'r)) failure\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>failure_tick_swap F \<equiv> case F of (t, X) \<Rightarrow> (trace_tick_swap t, refusal_tick_swap X)\<close>

lemma failure_tick_swap_empty [simp] : \<open>failure_tick_swap ([], {}) = ([], {})\<close>
  by (simp add: failure_tick_swap_def)


lemma failure_tick_swap_comp_failure_tick_swap [simp] :
  \<open>failure_tick_swap \<circ> failure_tick_swap = id\<close>
  by (auto simp add: failure_tick_swap_def)

lemma failure_tick_swap_failure_tick_swap [simp] :
  \<open>failure_tick_swap (failure_tick_swap F) = F\<close>
  by (simp add: comp_eq_dest_lhs)


lemma inj_failure_tick_swap [simp] : \<open>inj failure_tick_swap\<close>
  by (metis injI failure_tick_swap_failure_tick_swap)

lemma surj_failure_tick_swap [simp] : \<open>surj failure_tick_swap\<close>
  by (metis surjI failure_tick_swap_failure_tick_swap)

lemma bij_failure_tick_swap [simp] : \<open>bij failure_tick_swap\<close>
  by (simp add: bij_betw_def)


lemma empty_eq_failure_tick_swap_iff [iff] : \<open>([], {}) = failure_tick_swap F \<longleftrightarrow> F = ([], {})\<close>
  and failure_tick_swap_eq_empty_iff [iff] : \<open>failure_tick_swap F = ([], {}) \<longleftrightarrow> F = ([], {})\<close>
  by (auto simp add: failure_tick_swap_def split: prod.split)



subsection \<open>The Operator\<close>

subsubsection \<open>Definition\<close>

lift_definition TickSwap :: \<open>('a, 'r \<times> 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 's \<times> 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  is \<open>\<lambda>P. ({(t, X). failure_tick_swap (t, X) \<in> \<F> P}, {t. trace_tick_swap t \<in> \<D> P})\<close>
  \<comment> \<open>One might expect \<^term>\<open>\<lambda>P. (failure_tick_swap ` \<F> P, trace_tick_swap ` \<D> P)\<close> instead.
      This is equivalent, see the projections below, but easier for the following proof obligation.\<close>
proof -
  show \<open>?thesis P\<close> (is \<open>is_process (?f, ?d)\<close>) for P
  proof (unfold is_process_def FAILURES_def DIVERGENCES_def fst_conv snd_conv,
      intro conjI impI allI)
    show \<open>([], {}) \<in> ?f\<close> by (simp add: is_processT1)
  next
    show \<open>(t, X) \<in> ?f \<Longrightarrow> ftF t\<close> for t X
      by (simp add: failure_tick_swap_def)
        (use is_processT2 front_tickFree_trace_tick_swap_iff in blast)
  next
    show \<open>(t @ u, {}) \<in> ?f \<Longrightarrow> (t, {}) \<in> ?f\<close> for t u
      by (simp add: failure_tick_swap_def) (metis trace_tick_swap_append is_processT3)
  next
    show \<open>(t, Y) \<in> ?f \<and> X \<subseteq> Y \<Longrightarrow> (t, X) \<in> ?f\<close> for t X Y
      by (simp add: failure_tick_swap_def)
        (metis is_processT4 le_iff_sup refusal_tick_swap_union)
  next
    fix t X Y assume \<open>(t, X) \<in> ?f \<and> (\<forall>e. e \<in> Y \<longrightarrow> (t @ [e], {}) \<notin> ?f)\<close>
    hence \<open>(trace_tick_swap t, refusal_tick_swap X) \<in> \<F> P \<and>
           (\<forall>e. e \<in> refusal_tick_swap Y \<longrightarrow> (trace_tick_swap t @ [e], {}) \<notin> \<F> P)\<close>
      by (auto simp add: failure_tick_swap_def refusal_tick_swap_def trace_tick_swap_append)
    thus \<open>(t, X \<union> Y) \<in> ?f\<close>
      by (simp add: failure_tick_swap_def is_processT5 refusal_tick_swap_union)
  next
    show \<open>(t @ [\<checkmark>(s_r)], {}) \<in> ?f \<Longrightarrow> (t, X - {\<checkmark>(s_r)}) \<in> ?f\<close> for t X s_r
      by (cases s_r) (simp add: failure_tick_swap_def trace_tick_swap_append
          is_processT6 refusal_tick_swap_diff)
  next
    show \<open>t \<in> ?d \<and> tF t \<and> ftF u \<Longrightarrow> t @ u \<in> ?d\<close> for t u
      by (simp add: trace_tick_swap_append is_processT7)
  next
    show \<open>t \<in> ?d \<Longrightarrow> (t, X) \<in> ?f\<close> for t X
      by (simp add: failure_tick_swap_def is_processT8)
  next  
    show \<open>t @ [\<checkmark>(s_r)] \<in> ?d \<Longrightarrow> t \<in> ?d\<close> for t s_r
      by (cases s_r) (auto simp add: trace_tick_swap_append intro: is_processT9)
  qed
qed



subsubsection \<open>Projections\<close>

lemma F_TickSwap' : \<open>\<F> (TickSwap P) = {(t, X). failure_tick_swap (t, X) \<in> \<F> P}\<close>
  by (simp add: Failures.rep_eq TickSwap.rep_eq FAILURES_def)

lemma D_TickSwap' : \<open>\<D> (TickSwap P) = {t. trace_tick_swap t \<in> \<D> P}\<close>
  by (simp add: Divergences.rep_eq TickSwap.rep_eq DIVERGENCES_def)

lemma T_TickSwap' : \<open>\<T> (TickSwap P) = {t. trace_tick_swap t \<in> \<T> P}\<close>
  by (simp add: set_eq_iff F_TickSwap' failure_tick_swap_def flip: T_F_spec)

lemmas TickSwap_projs' = F_TickSwap' D_TickSwap' T_TickSwap'


text \<open>This is not very intuitive. The following lemmas are more intuitive.\<close>

lemma F_TickSwap : \<open>\<F> (TickSwap P) = failure_tick_swap ` \<F> P\<close>
  by (simp add: set_eq_iff F_TickSwap')
    (metis (no_types, lifting) failure_tick_swap_failure_tick_swap imageE image_eqI)

lemma D_TickSwap : \<open>\<D> (TickSwap P) = trace_tick_swap ` \<D> P\<close>
  by (simp add: set_eq_iff D_TickSwap')
    (metis (no_types, lifting) trace_tick_swap_trace_tick_swap imageE image_eqI)

lemma T_TickSwap : \<open>\<T> (TickSwap P) = trace_tick_swap ` \<T> P\<close>
  by (simp add: set_eq_iff T_TickSwap')
    (metis (no_types, lifting) trace_tick_swap_trace_tick_swap imageE image_eqI)

lemmas TickSwap_projs = F_TickSwap D_TickSwap T_TickSwap


text \<open>We finally give the following versions, sometimes more convenient to use.\<close>

lemma F_TickSwap'' : \<open>\<F> (TickSwap P) = {(trace_tick_swap t, refusal_tick_swap X)| t X. (t, X) \<in> \<F> P}\<close>
  by (auto simp add: F_TickSwap failure_tick_swap_def)

lemma D_TickSwap'' : \<open>\<D> (TickSwap P) = {trace_tick_swap t| t. t \<in> \<D> P}\<close>
  by (auto simp add: D_TickSwap)

lemma T_TickSwap'' : \<open>\<T> (TickSwap P) = {trace_tick_swap t| t. t \<in> \<T> P}\<close>
  by (auto simp add: T_TickSwap)

lemmas TickSwap_projs'' = F_TickSwap'' D_TickSwap'' T_TickSwap''



subsubsection \<open>Properties\<close>

lemma events_TickSwap [simp] : \<open>events_of (TickSwap P) = events_of P\<close>
  by (auto simp add: events_of_def T_TickSwap trace_tick_swap_def)

lemma ticks_TickSwap  [simp] : \<open>ticks_of  (TickSwap P) = {(s, r). (r, s) \<in> ticks_of P}\<close>
  by (auto simp add: ticks_of_def T_TickSwap' trace_tick_swap_append)
    (metis trace_tick_swap_trace_tick_swap)

lemma strict_ticks_TickSwap [simp] :
  \<open>strict_ticks_of  (TickSwap P) = {(s, r). (r, s) \<in> strict_ticks_of P}\<close>
  by (auto simp add: strict_ticks_of_def TickSwap_projs' trace_tick_swap_append)
    (metis trace_tick_swap_trace_tick_swap)

lemma trace_tick_swap_image_setinterleaving\<^sub>P\<^sub>a\<^sub>i\<^sub>r :
  \<open>trace_tick_swap ` setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<lambda>r s. \<lfloor>(r, s)\<rfloor>, u, A, v) =
   setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<lambda>r s. \<lfloor>(r, s)\<rfloor>, v, A, u)\<close>
  for u :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and v :: \<open>('a, 's) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  by (rule sym, induct \<open>(\<lambda>r :: 'r. \<lambda>s :: 's. \<lfloor>(r, s)\<rfloor>, u, A, v)\<close>
      arbitrary: u v) (simp_all, safe, auto)

lemma trace_tick_swap_setinterleaves\<^sub>P\<^sub>a\<^sub>i\<^sub>r_iff [iff] :
  \<open>trace_tick_swap t setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. \<lfloor>(r, s)\<rfloor>\<^esub> ((u, v), A) \<longleftrightarrow>
   t setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. \<lfloor>(r, s)\<rfloor>\<^esub> ((v, u), A)\<close>
  by (metis (mono_tags, lifting) image_eqI trace_tick_swap_image_setinterleaving\<^sub>P\<^sub>a\<^sub>i\<^sub>r
      trace_tick_swap_trace_tick_swap)



text \<open>The following theorem is a bridge with the existing operators:
      \<^const>\<open>TickSwap\<close> can be expressed via the \<^const>\<open>Renaming\<close> operator.\<close>

lemma tick_swap_is_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>tick_swap = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id prod.swap\<close>
proof (rule ext)
  show \<open>tick_swap e = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id prod.swap e\<close> for e :: \<open>('a, 'r \<times> 's) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (cases e) (auto split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.splits prod.splits)
qed

lemma trace_tick_swap_is_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>trace_tick_swap = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id prod.swap)\<close>
  by (simp add: tick_swap_is_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k trace_tick_swap_def)

lemma refusal_tick_swap_is_image_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>refusal_tick_swap = (`) (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id prod.swap)\<close>
  by (rule ext) (simp add: refusal_tick_swap_def tick_swap_is_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)


theorem TickSwap_is_Renaming :
  \<open>TickSwap P = Renaming P id prod.swap\<close> (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec_optimized, safe)
  fix t assume \<open>t \<in> \<D> ?lhs\<close>
  with D_imp_front_tickFree have \<open>ftF t\<close> by blast
  define t1 where \<open>t1 \<equiv> trace_tick_swap (if tF t then t else butlast t)\<close>
  define t2 where \<open>t2 \<equiv> if tF t then [] else [last t]\<close>
  have \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id prod.swap) t1 @ t2\<close>
    by (simp add: t1_def t2_def flip: trace_tick_swap_is_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      (metis append_butlast_last_id tickFree_Nil)
  moreover from \<open>ftF t\<close> front_tickFree_iff_tickFree_butlast t1_def have \<open>tF t1\<close> by auto
  moreover have \<open>ftF t2\<close> by (simp add: t2_def)
  moreover from t1_def D_TickSwap' \<open>ftF t\<close> \<open>t \<in> \<D> ?lhs\<close>
    div_butlast_when_non_tickFree_iff have \<open>t1 \<in> \<D> P\<close> by blast
  ultimately show \<open>t \<in> \<D> ?rhs\<close> unfolding D_Renaming by blast
next
  fix t assume \<open>t \<in> \<D> ?rhs\<close>
  then obtain t1 t2
    where \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id prod.swap) t1 @ t2\<close> \<open>tF t1\<close> \<open>ftF t2\<close> \<open>t1 \<in> \<D> P\<close>
    unfolding D_Renaming by blast
  thus \<open>t \<in> \<D> ?lhs\<close> by (simp add: D_TickSwap' trace_tick_swap_append is_processT7
        flip: trace_tick_swap_is_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
next
  fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close>
  then obtain t' X' where \<open>t = trace_tick_swap t'\<close> \<open>X = refusal_tick_swap X'\<close> \<open>(t', X') \<in> \<F> P\<close>
    unfolding F_TickSwap failure_tick_swap_def by auto
  moreover have \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id prod.swap -` refusal_tick_swap X' = X'\<close>
    by (simp add: set_eq_iff) (metis inj_image_mem_iff inj_tick_swap
        refusal_tick_swap_def tick_swap_is_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  ultimately show \<open>(t, X) \<in> \<F> ?rhs\<close>
    by (auto simp add: F_Renaming simp flip: trace_tick_swap_is_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
next
  fix t X assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(t, X) \<in> \<F> ?rhs\<close>
  then consider \<open>t \<in> \<D> ?rhs\<close>
    | t' where \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id prod.swap) t'\<close> \<open>(t', map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id prod.swap -` X) \<in> \<F> P\<close>
    unfolding Renaming_projs by blast
  thus \<open>(t, X) \<in> \<F> ?lhs\<close>
  proof cases
    from same_div D_F show \<open>t \<in> \<D> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> by blast
  next
    fix t' assume * : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id prod.swap) t'\<close>
      \<open>(t', map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id prod.swap -` X) \<in> \<F> P\<close>
    from "*"(1) have \<open>(t, X) = failure_tick_swap (t', map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id prod.swap -` X)\<close>
      by (simp add: failure_tick_swap_def refusal_tick_swap_def trace_tick_swap_def
          flip: tick_swap_is_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    with "*"(2) show \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_TickSwap)
  qed
qed



lemma TickSwap_TickSwap [simp] : \<open>TickSwap (TickSwap P) = P\<close>
  by (simp add: Process_eq_spec TickSwap_projs')

lemma TickSwap_comp_TickSwap [simp] : \<open>TickSwap \<circ> TickSwap = id\<close>
  by (rule ext) simp

lemma TickSwap_eq_iff_eq_TickSwap : \<open>TickSwap P = Q \<longleftrightarrow> P = TickSwap Q\<close> by auto

lemma inj_TickSwap [simp] : \<open>inj TickSwap\<close>
  by (metis injI TickSwap_TickSwap)

lemma surj_TickSwap [simp] : \<open>surj TickSwap\<close>
  by (metis surjI TickSwap_TickSwap)

lemma bij_TickSwap [simp] : \<open>bij TickSwap\<close>
  by (simp add: bij_betw_def)

lemma strict_mono_TickSwap : \<open>strict_mono TickSwap\<close>
  by (rule strict_monoI) 
    (metis D_TickSwap F_TickSwap failure_refine_def image_mono injD inj_TickSwap
      nless_le failure_divergence_refine_def divergence_refine_def)



subsubsection \<open>Monotonicity Properties\<close>

lemma mono_TickSwap : \<open>P \<sqsubseteq> Q \<Longrightarrow> TickSwap P \<sqsubseteq> TickSwap Q\<close>
  by (simp add: TickSwap_is_Renaming mono_Renaming)

lemma mono_TickSwap_FD : \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> TickSwap P \<sqsubseteq>\<^sub>F\<^sub>D TickSwap Q\<close>
  and mono_TickSwap_DT : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> TickSwap P \<sqsubseteq>\<^sub>D\<^sub>T TickSwap Q\<close>
  and mono_TickSwap_F  : \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> TickSwap P \<sqsubseteq>\<^sub>F TickSwap Q\<close>
  and mono_TickSwap_D  : \<open>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> TickSwap P \<sqsubseteq>\<^sub>D TickSwap Q\<close>
  and mono_TickSwap_T  : \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> TickSwap P \<sqsubseteq>\<^sub>T TickSwap Q\<close>
  by (simp_all add: TickSwap_projs refine_defs image_mono)

lemmas monos_TickSwap = mono_TickSwap mono_TickSwap_FD mono_TickSwap_DT
  mono_TickSwap_F mono_TickSwap_D mono_TickSwap_T


lemma le_approx_TickSwap_iff : \<open>TickSwap P \<sqsubseteq>  TickSwap Q \<longleftrightarrow> P \<sqsubseteq> Q\<close>
  and        FD_TickSwap_iff : \<open>TickSwap P \<sqsubseteq>\<^sub>F\<^sub>D TickSwap Q \<longleftrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  and        DT_TickSwap_iff : \<open>TickSwap P \<sqsubseteq>\<^sub>D\<^sub>T TickSwap Q \<longleftrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  and         F_TickSwap_iff : \<open>TickSwap P \<sqsubseteq>\<^sub>F  TickSwap Q \<longleftrightarrow> P \<sqsubseteq>\<^sub>F Q\<close>
  and         D_TickSwap_iff : \<open>TickSwap P \<sqsubseteq>\<^sub>D  TickSwap Q \<longleftrightarrow> P \<sqsubseteq>\<^sub>D Q\<close>
  and         T_TickSwap_iff : \<open>TickSwap P \<sqsubseteq>\<^sub>T  TickSwap Q \<longleftrightarrow> P \<sqsubseteq>\<^sub>T Q\<close>
  by (rule iffI; drule monos_TickSwap, simp add: monos_TickSwap)+

lemmas le_TickSwap_iff = le_approx_TickSwap_iff FD_TickSwap_iff DT_TickSwap_iff
  F_TickSwap_iff D_TickSwap_iff T_TickSwap_iff



subsubsection \<open>Continuity\<close>

text \<open>Continuity is a direct corollary of the continuity of \<^const>\<open>Renaming\<close>.\<close>

lemma TickSwap_cont[simp] : \<open>cont P \<Longrightarrow> cont (\<lambda>x. TickSwap (P x))\<close>
  by (simp add: TickSwap_is_Renaming)



subsubsection \<open>Algebraic Laws\<close>

paragraph \<open>Constant Processes\<close>

lemma TickSwap_STOP [simp] : \<open>TickSwap STOP = STOP\<close>
  by (simp add: STOP_iff_T T_TickSwap T_STOP)

lemma TickSwap_is_STOP_iff [simp] : \<open>TickSwap P = STOP \<longleftrightarrow> P = STOP\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_BOT [simp] : \<open>TickSwap \<bottom> = \<bottom>\<close>
  by (simp add: BOT_iff_Nil_D D_TickSwap D_BOT)

lemma TickSwap_is_BOT_iff [simp] : \<open>TickSwap P = \<bottom> \<longleftrightarrow> P = \<bottom>\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_SKIP [simp] : \<open>TickSwap (SKIP (r, s)) = SKIP (s, r)\<close>
  by (simp add: TickSwap_is_Renaming)

lemma TickSwap_is_SKIP_iff [simp] : \<open>TickSwap P = SKIP (r, s) \<longleftrightarrow> P = SKIP (s, r)\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_SKIPS [simp] : \<open>TickSwap (SKIPS R_S) = SKIPS {(s, r). (r, s) \<in> R_S}\<close>
  by (auto simp add: Process_eq_spec TickSwap_projs' SKIPS_projs)
    (auto simp add: failure_tick_swap_def refusal_tick_swap_def)

lemma TickSwap_is_SKIPS_iff [simp] :
  \<open>TickSwap P = SKIPS R_S \<longleftrightarrow> P = SKIPS {(s, r). (r, s) \<in> R_S}\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


paragraph \<open>Binary (or less) Operators\<close>

lemma TickSwap_Ndet [simp] : \<open>TickSwap (P \<sqinter> Q) = TickSwap P \<sqinter> TickSwap Q\<close>
  by (simp add: Process_eq_spec TickSwap_projs Ndet_projs image_Un)

lemma TickSwap_is_Ndet_iff [simp] : \<open>TickSwap P = Q \<sqinter> R \<longleftrightarrow> P = TickSwap Q \<sqinter> TickSwap R\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_Det [simp] :
  \<open>TickSwap (P \<box> Q) = TickSwap P \<box> TickSwap Q\<close>
  by (simp add: TickSwap_is_Renaming Renaming_Det)

lemma TickSwap_is_Det_iff [simp] : \<open>TickSwap P = Q \<box> R \<longleftrightarrow> P = TickSwap Q \<box> TickSwap R\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_Sliding [simp] : \<open>TickSwap (P \<rhd> Q) = TickSwap P \<rhd> TickSwap Q\<close>
  by (simp add: Sliding_def)

lemma TickSwap_is_Sliding_iff [simp] : \<open>TickSwap P = Q \<rhd> R \<longleftrightarrow> P = TickSwap Q \<rhd> TickSwap R\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_Sync [simp] :
  \<open>TickSwap (P \<lbrakk>S\<rbrakk> Q) = TickSwap P \<lbrakk>S\<rbrakk> TickSwap Q\<close>
  by (simp add: TickSwap_is_Renaming bij_Renaming_Sync)

lemma TickSwap_is_Sync_iff [simp] :
  \<open>TickSwap P = Q \<lbrakk>S\<rbrakk> R \<longleftrightarrow> P = TickSwap Q \<lbrakk>S\<rbrakk> TickSwap R\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_Seq [simp] :
  \<open>TickSwap (P \<^bold>; Q) = TickSwap P \<^bold>; TickSwap Q\<close>
  by (simp add: Renaming_Seq TickSwap_is_Renaming)

lemma TickSwap_is_Seq_iff [simp] :
  \<open>TickSwap P = Q \<^bold>; R \<longleftrightarrow> P = TickSwap Q \<^bold>; TickSwap R\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_Renaming [simp] :
  \<open>TickSwap (Renaming P f g) =
   Renaming (TickSwap P) f (prod.swap \<circ> g \<circ> prod.swap)\<close>
  by (simp add: TickSwap_is_Renaming flip: Renaming_comp)
    (metis comp_apply swap_swap)

lemma TickSwap_Renaming' : 
  \<open>TickSwap (Renaming P f g) = Renaming P f (prod.swap \<circ> g)\<close>
  by (simp add: TickSwap_is_Renaming flip: Renaming_comp)

lemma TickSwap_is_Renaming_iff [simp] :
  \<open>TickSwap P = Renaming Q f g \<longleftrightarrow> P = Renaming (TickSwap Q) f (prod.swap \<circ> g \<circ> prod.swap)\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_Hiding [simp] : \<open>TickSwap (P \ S) = TickSwap P \ S\<close>
  by (simp add: TickSwap_is_Renaming bij_Renaming_Hiding)

lemma TickSwap_is_Hiding_iff [simp] : \<open>TickSwap P = Q \ S \<longleftrightarrow> P = TickSwap Q \ S\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_Interrupt [simp] :
  \<open>TickSwap (P \<triangle> Q) = TickSwap P \<triangle> TickSwap Q\<close>
  by (simp add: TickSwap_is_Renaming Renaming_Interrupt)

lemma TickSwap_is_Interrupt_iff [simp] :
  \<open>TickSwap P = Q \<triangle> R \<longleftrightarrow> P = TickSwap Q \<triangle> TickSwap R\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_Throw [simp] :
  \<open>TickSwap (P \<Theta> a \<in> A. Q a) = TickSwap P \<Theta> a \<in> A. TickSwap (Q a)\<close>
  by (simp add: TickSwap_is_Renaming inj_on_Renaming_Throw)
    (rule mono_Throw_eq, metis id_apply inj_on_id inv_into_f_f)

lemma TickSwap_is_Throw_iff [simp] :
  \<open>TickSwap P = Q \<Theta> a \<in> A. R a \<longleftrightarrow> P = TickSwap Q \<Theta> a \<in> A. TickSwap (R a)\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


paragraph \<open>Architectural Operators\<close>

lemma TickSwap_GlobalNdet [simp] :
  \<open>TickSwap (\<sqinter>a \<in> A. P a) = \<sqinter>a \<in> A. TickSwap (P a)\<close>
  by (simp add: TickSwap_is_Renaming Renaming_distrib_GlobalNdet)

lemma TickSwap_is_GlobalNdet_iff [simp] :
  \<open>TickSwap P = \<sqinter>a \<in> A. Q a \<longleftrightarrow> P = \<sqinter>a \<in> A. TickSwap (Q a)\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_GlobalDet [simp] :
  \<open>TickSwap (\<box>a \<in> A. P a) = \<box>a \<in> A. TickSwap (P a)\<close>
  by (simp add: TickSwap_is_Renaming Renaming_distrib_GlobalDet)

lemma TickSwap_is_GlobalDet_iff [simp] :
  \<open>TickSwap P = \<box>a \<in> A. Q a \<longleftrightarrow> P = \<box>a \<in> A. TickSwap (Q a)\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_MultiSync [simp] :
  \<open>TickSwap (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. P m) = \<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. TickSwap (P m)\<close>
  by (induct M rule: induct_subset_mset_empty_single) simp_all

lemma TickSwap_is_TickSwap_MultiSync_iff [simp] :
  \<open>TickSwap P = \<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. Q m \<longleftrightarrow> P = \<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. TickSwap (Q m)\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_MultiSeq [simp] :
  \<open>L \<noteq> [] \<Longrightarrow> TickSwap (SEQ l \<in>@ L. P l) = SEQ l \<in>@ L. TickSwap (P l)\<close>
  by (induct L rule: rev_induct, simp_all) 
    (metis MultiSeq_Nil SKIP_Seq TickSwap_Seq)

lemma TickSwap_is_MultiSeq_iff [simp] :
  \<open>L \<noteq> [] \<Longrightarrow> TickSwap P = SEQ l \<in>@ L. Q l \<longleftrightarrow> P = SEQ l \<in>@ L. TickSwap (Q l)\<close>
  by (metis TickSwap_MultiSeq TickSwap_TickSwap)


paragraph \<open>Communications\<close>

lemma TickSwap_write0 [simp] : \<open>TickSwap (e \<rightarrow> P) = e \<rightarrow> TickSwap P\<close>
  by (simp add: TickSwap_is_Renaming Renaming_write0)

lemma TickSwap_is_write0_iff [simp] : \<open>TickSwap P = e \<rightarrow> Q \<longleftrightarrow> P = e \<rightarrow> TickSwap Q\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_write [simp] : \<open>TickSwap (c\<^bold>!e \<rightarrow> P) = c\<^bold>!e \<rightarrow> TickSwap P\<close>
  by (simp add: TickSwap_is_Renaming Renaming_write)

lemma TickSwap_is_write_iff [simp] : \<open>TickSwap P = c\<^bold>!e \<rightarrow> Q \<longleftrightarrow> P = c\<^bold>!e \<rightarrow> TickSwap Q\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_Mprefix [simp] :
  \<open>TickSwap (\<box>a \<in> A \<rightarrow> P a) = \<box>a \<in> A \<rightarrow> TickSwap (P a)\<close> 
  by (simp add: Mprefix_GlobalDet)

lemma TickSwap_is_Mprefix_iff [simp] :
  \<open>TickSwap P = (\<box>a \<in> A \<rightarrow> Q a) \<longleftrightarrow> P = \<box>a \<in> A \<rightarrow> TickSwap (Q a)\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_read [simp] : \<open>TickSwap (c\<^bold>?a\<in>A \<rightarrow> P a) = c\<^bold>?a\<in>A \<rightarrow> TickSwap (P a)\<close>
  by (simp add: read_def comp_def)

lemma TickSwap_is_read_iff [simp] :
  \<open>TickSwap P = c\<^bold>?a\<in>A \<rightarrow> Q a \<longleftrightarrow> P = c\<^bold>?a\<in>A \<rightarrow> TickSwap (Q a)\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_Mndetprefix [simp] :
  \<open>TickSwap (\<sqinter>a \<in> A \<rightarrow> P a) = \<sqinter>a \<in> A \<rightarrow> TickSwap (P a)\<close>
  by (simp add: Mndetprefix_GlobalNdet)

lemma TickSwap_is_Mndetprefix_iff [simp] :
  \<open>TickSwap P = (\<sqinter>a \<in> A \<rightarrow> Q a) \<longleftrightarrow> P = \<sqinter>a \<in> A \<rightarrow> TickSwap (Q a)\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)


lemma TickSwap_ndet_write [simp] : \<open>TickSwap (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) = c\<^bold>!\<^bold>!a\<in>A \<rightarrow> TickSwap (P a)\<close>
  by (simp add: ndet_write_def comp_def)

lemma TickSwap_is_ndet_write_iff [simp] :
  \<open>TickSwap P = c\<^bold>!\<^bold>!a\<in>A \<rightarrow> Q a \<longleftrightarrow> P = c\<^bold>!\<^bold>!a\<in>A \<rightarrow> TickSwap (Q a)\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)



section \<open>Splitting the Renaming Operator\<close>

text \<open>
We split the \<^const>\<open>Renaming\<close> operator in two: the first one only renames
the ``regular'' events, the second one only the ticks.
\<close>

subsection \<open>Renaming only Events\<close>

abbreviation RenamingEv :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a \<Rightarrow> 'b] \<Rightarrow> ('b, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>RenamingEv P f \<equiv> Renaming P f id\<close>

lemma RenamingEv_id_unfolded [iff] :
  \<open>Renaming P f (\<lambda>r. r) = RenamingEv P f\<close> by (simp add: id_def)


lemmas strict_ticks_of_RenamingEv_subset = strict_ticks_of_Renaming_subset [where g = id, simplified]
  and strict_ticks_of_inj_on_RenamingEv = strict_ticks_of_inj_on_Renaming [where g = id, simplified]


lemmas monos_RenamingEv = monos_Renaming[where g = id]

lemma RenamingEv_SKIP : \<open>RenamingEv (SKIP r) f = SKIP r\<close> by simp

lemma RenamingEv_cont :
  \<open>cont P \<Longrightarrow> finitary f \<Longrightarrow> cont (\<lambda>x. RenamingEv (P x) f)\<close> by simp


lemma RenamingEv_Seq :
  \<open>RenamingEv (P \<^bold>; Q) f = RenamingEv P f \<^bold>; RenamingEv Q f\<close>
  by (simp add: Renaming_Seq)


declare Renaming_id [simp]



lemmas RenamingEv_id          = Renaming_id
  and RenamingEv_STOP        = Renaming_STOP        [where g = id]
  and RenamingEv_BOT         = Renaming_BOT         [where g = id]
  and RenamingEv_is_STOP_iff = Renaming_is_STOP_iff [where g = id]
  and RenamingEv_is_BOT_iff  = Renaming_is_BOT_iff  [where g = id]

lemmas RenamingEv_Det       = Renaming_Det       [where g = id]
  and RenamingEv_Ndet      = Renaming_Ndet      [where g = id]
  and RenamingEv_Sliding   = Renaming_Sliding   [where g = id]
  and RenamingEv_Interrupt = Renaming_Interrupt [where g = id]
  and RenamingEv_write0    = Renaming_write0    [where g = id]
  and RenamingEv_write     = Renaming_write     [where g = id]
  and RenamingEv_comp      = Renaming_comp      [of _ _ _ id id, simplified]
  and RenamingEv_inv       = Renaming_inv       [where g = id,   simplified]
  and inv_RenamingEv       = inv_Renaming       [where g = id,   simplified]


lemmas bij_RenamingEv_Sync     = bij_Renaming_Sync     [where g = id, simplified]
  and bij_RenamingEv_Hiding   = bij_Renaming_Hiding   [where g = id, simplified]
  and inj_on_RenamingEv_Throw = inj_on_Renaming_Throw [where g = id]
  and RenamingEv_fix          = Renaming_fix          [where g = id, simplified]


lemmas RenamingEv_distrib_GlobalDet  = Renaming_distrib_GlobalDet  [where g = id]
  and RenamingEv_distrib_GlobalNDet = Renaming_distrib_GlobalNdet [where g = id]
  and RenamingEv_Mprefix            = Renaming_Mprefix            [where g = id]
  and RenamingEv_Mndetprefix        = Renaming_Mndetprefix        [where g = id]
  and RenamingEv_read               = Renaming_read               [where g = id]
  and RenamingEv_ndet_write         = Renaming_ndet_write         [where g = id]



subsection \<open>Renaming only Ticks\<close>

abbreviation RenamingTick :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r \<Rightarrow> 's] \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>RenamingTick P g \<equiv> Renaming P id g\<close>

lemma RenamingTick_id_unfolded [iff] :
  \<open>Renaming P (\<lambda>a. a) g = RenamingTick P g\<close> by (simp add: id_def)


lemmas strict_ticks_of_RenamingTick_subset = strict_ticks_of_Renaming_subset [where f = id]
  and strict_ticks_of_inj_on_RenamingTick = strict_ticks_of_inj_on_Renaming [where f = id, simplified]

lemmas monos_RenamingTick = monos_Renaming[where f = id]

lemma RenamingTick_cont :
  \<open>cont P \<Longrightarrow> finitary g \<Longrightarrow> cont (\<lambda>x. RenamingTick (P x) g)\<close> by simp


lemmas RenamingTick_id          = Renaming_id
  and RenamingTick_STOP        = Renaming_STOP        [where f = id]
  and RenamingTick_SKIP        = Renaming_SKIP        [where f = id]
  and RenamingTick_BOT         = Renaming_BOT         [where f = id]
  and RenamingTick_is_STOP_iff = Renaming_is_STOP_iff [where f = id]
  and RenamingTick_is_BOT_iff  = Renaming_is_BOT_iff  [where f = id]

lemmas RenamingTick_Seq = Renaming_Seq[where f = id]
  and RenamingTick_Det       = Renaming_Det        [where f = id]
  and RenamingTick_Ndet      = Renaming_Ndet       [where f = id]
  and RenamingTick_Sliding   = Renaming_Sliding    [where f = id]
  and RenamingTick_Interrupt = Renaming_Interrupt  [where f = id]
  and RenamingTick_write0    = Renaming_write0     [where f = id, simplified]
  and RenamingTick_write     = Renaming_write      [where f = id, simplified]
  and RenamingTick_comp      = Renaming_comp       [of _ id id  , simplified]
  and RenamingTick_inv       = Renaming_inv        [where f = id, simplified]
  and inv_RenamingTick       = inv_Renaming        [where f = id, simplified]


lemmas bij_RenamingTick_Sync     = bij_Renaming_Sync     [where f = id, simplified]
  (* and bij_RenamingTick_Hiding   = bij_Renaming_Hiding   [where f = id, simplified] *)
  and RenamingTick_fix          = Renaming_fix          [where f = id, simplified]

\<comment> \<open>The assumption \<^term>\<open>bij g\<close> is actually not necessary
    for \<^term>\<open>RenamingTick\<close> and \<^const>\<open>Hiding\<close>, see below.\<close>

lemma RenamingTick_Throw :
  \<open>RenamingTick (P \<Theta> a\<in>A. Q a) g = RenamingTick P g \<Theta> a\<in>A. RenamingTick (Q a) g\<close>
proof (subst inj_on_Renaming_Throw)
  show \<open>inj_on id (events_of P \<union> A)\<close> by simp
next
  show \<open>RenamingTick P g \<Theta> b\<in>id ` A. RenamingTick (Q (inv_into A id b)) g =
        RenamingTick P g \<Theta> a\<in>A. RenamingTick (Q a) g\<close>
    by (simp, rule mono_Throw_eq)
      (metis f_inv_into_f id_apply image_id)
qed


lemmas RenamingTick_distrib_GlobalDet  = Renaming_distrib_GlobalDet  [where f = id]
  and RenamingTick_distrib_GlobalNDet = Renaming_distrib_GlobalNdet [where f = id]
  and RenamingTick_Mprefix            = Renaming_Mprefix_image_inj  [where f = id, simplified]
  and RenamingTick_Mndetprefix        = Renaming_Mndetprefix_inj    [where f = id, simplified]
  and RenamingTick_read               = Renaming_read               [where f = id, simplified]
  and RenamingTick_ndet_write         = Renaming_ndet_write         [where f = id, simplified] 




lemma RenamingEv_RenamingTick_is_Renaming :
  \<open>RenamingEv (RenamingTick P g) f = Renaming P f g\<close>
  and RenamingTick_RenamingEv_is_Renaming :
  \<open>RenamingTick (RenamingEv P f) g = Renaming P f g\<close>
  by (metis Renaming_comp comp_id fun.map_id)+



subsection \<open>Properties\<close>

lemma isInfHidden_seqRun_imp_tickFree_seqRun :
  \<open>isInfHidden_seqRun x P A t \<Longrightarrow> tF (seqRun t x i)\<close>
  by (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) image_iff isInfHidden_seqRun_imp_tickFree tickFree_seqRun_iff)

lemma tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is :
  \<open>tF t \<Longrightarrow> map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t = map (ev \<circ> f \<circ> of_ev) t\<close>
  by (induct t) (auto simp add: is_ev_def)

lemma RenamingTick_Hiding :
  \<open>RenamingTick (P \ A) g = RenamingTick P g \ A\<close>
  (is \<open>?lhs = ?rhs\<close>) for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof -
  let ?RT = \<open>\<lambda>P. RenamingTick P g\<close>
  let ?th_A = \<open>\<lambda>t. trace_hide t (ev ` A)\<close>
  let ?map  = \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g)\<close>
  have $ : \<open>?th_A (?map t) = ?map (?th_A t)\<close> for t
    by (induct t) (simp_all add: image_iff map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_ev_iff)
  have $$ : \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X \<union> ev ` A =
             map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X \<union> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` ev ` A\<close> for X
    by (auto simp add: map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_ev_iff)
  show \<open>?lhs = ?rhs\<close>
  proof (rule Process_eq_optimizedI)
    fix t assume \<open>t \<in> \<D> ?lhs\<close>
    then obtain t1 t2 where * : \<open>t = ?map t1 @ t2\<close>
      \<open>tF t1\<close> \<open>ftF t2\<close> \<open>t1 \<in> \<D> (P \ A)\<close> unfolding D_Renaming by blast
    from "*"(4) obtain u v where ** : \<open>ftF v\<close> \<open>tF u\<close> \<open>t1 = ?th_A u @ v\<close>
      \<open>u \<in> \<D> P \<or> (\<exists>x. isInfHidden_seqRun_strong x P A u)\<close>
      by (blast elim: D_Hiding_seqRunE)
    from "**"(4) show \<open>t \<in> \<D> ?rhs\<close>
    proof (elim disjE exE)
      assume \<open>u \<in> \<D> P\<close>
      with "**"(2) have \<open>?map u \<in> \<D> (?RT P)\<close>
        by (auto simp add: D_Renaming intro: front_tickFree_Nil)
      thus \<open>t \<in> \<D> ?rhs\<close>
        by (simp add: D_Hiding "*"(1) "**"(3) flip: "$")
          (metis "*"(2, 3) "**"(2, 3) front_tickFree_append
            map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_append_iff)
    next
      fix x assume *** : \<open>isInfHidden_seqRun_strong x P A u\<close>
      have \<open>isInfHidden_seqRun (ev \<circ> of_ev \<circ> x) (?RT P) A (?map u)\<close>
      proof (intro allI conjI)
        fix i
        have \<open>seqRun (?map u) (ev \<circ> of_ev \<circ> x) i = ?map (seqRun u x i)\<close>
          by (simp add: seqRun_def image_iff ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
            (metis "***" event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) imageE)
        also have \<open>?map (seqRun u x i) \<in> \<T> (?RT P)\<close>
          unfolding T_Renaming using "***" Un_iff by blast
        finally show \<open>seqRun (?map u) (ev \<circ> of_ev \<circ> x) i \<in> \<T> (?RT P)\<close> .
      next
        show \<open>(ev \<circ> of_ev \<circ> x) i \<in> ev ` A\<close> for i
          by (metis "***" comp_apply event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) image_iff)
      qed
      thus \<open>t \<in> \<D> ?rhs\<close>
        by (simp (no_asm) add: D_Hiding_seqRun "*"(1) "**"(3) flip: "$")
          (metis "*"(2, 3) "**"(2, 3) front_tickFree_append
            map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_append_iff)
    qed
  next
    fix t assume \<open>t \<in> \<D> ?rhs\<close>
    then obtain u v where * : \<open>ftF v\<close> \<open>tF u\<close> \<open>t = ?th_A u @ v\<close>
      \<open>u \<in> \<D> (?RT P) \<or> (\<exists>x. isInfHidden_seqRun_strong x (?RT P) A u)\<close>
      by (blast elim: D_Hiding_seqRunE)
    from "*"(4) show \<open>t \<in> \<D> ?lhs\<close>
    proof (elim disjE exE)
      assume \<open>u \<in> \<D> (?RT P)\<close>
      then obtain u1 u2 where ** : \<open>u = ?map u1 @ u2\<close>
        \<open>tF u1\<close> \<open>ftF u2\<close> \<open>u1 \<in> \<D> P\<close> unfolding D_Renaming by blast
      from mem_D_imp_mem_D_Hiding "**"(4) have \<open>?th_A u1 \<in> \<D> (P \ A)\<close> .
      thus \<open>t \<in> \<D> ?lhs\<close>
        by (simp add: D_Renaming "*"(3) "**"(1) "$")
          (metis "*"(1, 2) "**"(1, 2) Hiding_tickFree
            front_tickFree_append tickFree_append_iff)
    next
      fix x assume ** : \<open>isInfHidden_seqRun_strong x (?RT P) A u\<close>
      hence \<open>\<forall>i. \<exists>v. seqRun u x i = ?map v \<and> v \<in> \<T> P\<close>
        unfolding Renaming_projs by blast
      then obtain f where *** : \<open>seqRun u x i = ?map (f i)\<close> \<open>f i \<in> \<T> P\<close> for i by metis
      have \<open>tF (f i)\<close> for i
        by (metis isInfHidden_seqRun_imp_tickFree_seqRun
            "**" "***"(1) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
      hence \<open>?map (f i) = map (ev \<circ> of_ev) (f i)\<close> for i
        by (simp add: tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is)
      from "***"(1)[unfolded this]
      have \<open>map (ev \<circ> of_ev) (seqRun u x i) =
            (map (ev \<circ> of_ev) (map (ev \<circ> of_ev) (f i)) :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)\<close> for i by simp
      also have \<open>map (ev \<circ> of_ev) (map (ev \<circ> of_ev) (f i)) = f i\<close> for i
        using \<open>\<And>i. tF (f i)\<close>[of i] 
        by (auto simp add: tickFree_iff_is_map_ev)
      finally have \<open>f i = map (ev \<circ> of_ev) (seqRun u x i)\<close> for i by (rule sym)
      hence **** : \<open>f i = seqRun (f 0) (ev \<circ> of_ev \<circ> x) i\<close> for i
        by (simp add: seqRun_def "***"(1))
      have \<open>isInfHidden_seqRun (ev \<circ> of_ev \<circ> x) P A (f 0)\<close>
      proof (intro allI conjI)
        show \<open>seqRun (f 0) (ev \<circ> of_ev \<circ> x) i \<in> \<T> P\<close> for i by (metis "***"(2) "****")
      next
        show \<open>(ev \<circ> of_ev \<circ> x) i \<in> ev ` A\<close> for i
          using "**"[THEN spec, of i] by auto
      qed
      with \<open>\<And>i. tF (f i)\<close> have \<open>?th_A (f 0) \<in> \<D> (P \ A)\<close>
        by (simp add: D_Hiding_seqRun)
          (metis append.right_neutral comp_apply front_tickFree_Nil)
      moreover have \<open>?th_A u = ?map (?th_A (f 0))\<close>
        by (metis "$" "***"(1) seqRun_0)
      ultimately show \<open>t \<in> \<D> ?lhs\<close>
        by (simp add: D_Renaming "*"(3))
          (use "*"(1) Hiding_tickFree \<open>\<And>i. tF (f i)\<close> in blast)
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    then obtain t' where * : \<open>t = ?map t'\<close>
      \<open>(t', map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X) \<in> \<F> (P \ A)\<close>
      unfolding Renaming_projs by blast
    from "*"(2) consider \<open>t' \<in> \<D> (P \ A)\<close>
      | ("**") t'' where \<open>t' = ?th_A t''\<close>
        \<open>(t'', map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X \<union> ev ` A) \<in> \<F> P\<close>
      unfolding F_Hiding D_Hiding by blast
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
    proof cases
      assume \<open>t' \<in> \<D> (P \ A)\<close>
      hence \<open>tF t' \<or> (\<exists>t'' r. t' = t'' @ [\<checkmark>(r)] \<and> tF t'')\<close>
        by (metis D_imp_front_tickFree front_tickFree_append_iff
            nonTickFree_n_frontTickFree not_Cons_self2)
      with \<open>t' \<in> \<D> (P \ A)\<close> \<open>t \<notin> \<D> ?lhs\<close> have False
        by (elim disjE exE conjE, simp_all add: D_Renaming "*"(1))
          (use front_tickFree_Nil in blast, metis front_tickFree_single is_processT9)
      thus \<open>(t, X) \<in> \<F> ?rhs\<close> ..
    next
      case "**"
      from "**"(2) have \<open>(?map t'', X \<union> ev ` A) \<in> \<F> (?RT P)\<close>
        by (auto simp add: F_Renaming "$$")
      thus \<open>(t, X) \<in> \<F> ?rhs\<close> by (simp add: F_Hiding "*"(1) "**"(1)) (metis "$")
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
    then obtain t' where * : \<open>t = ?th_A t'\<close> \<open>(t', X \<union> ev ` A) \<in> \<F> (?RT P)\<close>
      unfolding F_Hiding D_Hiding by blast
    from "*"(2) consider \<open>t' \<in> \<D> (?RT P)\<close>
      | ("**") t'' where \<open>t' = ?map t''\<close>
        \<open>(t'', map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X \<union> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` ev ` A) \<in> \<F> P\<close>
      by (auto simp add: Renaming_projs)
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>t' \<in> \<D> (?RT P)\<close>
      hence \<open>tF t' \<or> (\<exists>t'' r. t' = t'' @ [\<checkmark>(r)] \<and> tF t'')\<close>
        by (metis D_imp_front_tickFree front_tickFree_append_iff
            nonTickFree_n_frontTickFree not_Cons_self2)
      with \<open>t' \<in> \<D> (?RT P)\<close> \<open>t \<notin> \<D> ?rhs\<close> have False
        by (elim disjE exE, auto simp add: D_Hiding_seqRun "*"(1) image_iff
            intro: front_tickFree_single is_processT9)
      thus \<open>(t, X) \<in> \<F> ?lhs\<close> ..
    next
      case "**"
      from "**"(2) have \<open>(?th_A t'', map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X) \<in> \<F> (P \ A)\<close>
        by (auto simp add: F_Hiding "$$")
      thus \<open>(t, X) \<in> \<F> ?lhs\<close>
        by (auto simp add: F_Renaming "*"(1) "**"(1) "$")
    qed
  qed
qed


corollary bij_Renaming_Hiding :
  \<open>Renaming (P \ S) f g = Renaming P f g \ f ` S\<close> (is \<open>?lhs = ?rhs\<close>) if \<open>bij f\<close>
  \<comment> \<open>We already have @{thm bij_Renaming_Hiding[no_vars]},
      but he assumption \<^term>\<open>bij g\<close> is actually not necessary.\<close>
proof -
  have \<open>?lhs = RenamingTick (RenamingEv (P \ S) f) g\<close>
    by (simp only: RenamingTick_RenamingEv_is_Renaming)
  also have \<open>\<dots> = RenamingTick (RenamingEv P f \ f ` S) g\<close>
    by (simp only: bij_RenamingEv_Hiding[OF \<open>bij f\<close>])
  also have \<open>\<dots> = RenamingTick (RenamingEv P f) g \ f ` S\<close>
    by (simp only: RenamingTick_Hiding)
  also have \<open>\<dots> = ?rhs\<close>
    by (simp only: RenamingTick_RenamingEv_is_Renaming)
  finally show \<open>?lhs = ?rhs\<close> .
qed



lemma Renaming_is_restrictable_on_events_of_strict_ticks_of :
  \<open>Renaming P f g = Renaming P f' g'\<close>
  if fun_hyps : \<open>\<And>a. a \<in> \<alpha>(P) \<Longrightarrow> f a = f' a\<close>
    \<open>\<And>r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> g r = g' r\<close>
  for f f' :: \<open>'a \<Rightarrow> 'b\<close> and g g' :: \<open>'r \<Rightarrow> 't\<close>
    \<comment> \<open>probably also possible to strengthen with \<^const>\<open>strict_events_of\<close>\<close>
proof -
  have * : \<open>Renaming P f g \<sqsubseteq>\<^sub>F\<^sub>D Renaming P f' g'\<close>
    if fun_hyps_bis : \<open>\<And>a. a \<in> \<alpha>(P) \<Longrightarrow> f a = f' a\<close> \<open>\<And>r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> g r = g' r\<close>
    for f f' :: \<open>'a \<Rightarrow> 'b\<close> and g g' :: \<open>'r \<Rightarrow> 't\<close>
  proof -
    have $ : \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g') u\<close>
      if \<open>u \<in> \<T> P\<close> and \<open>tF u\<close> for u
    proof -
      from \<open>u \<in> \<T> P\<close> have \<open>ev a \<in> set u \<Longrightarrow> a \<in> \<alpha>(P)\<close> for a
        by (meson events_of_memI)
      with \<open>tF u\<close> show \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g') u\<close>
        by (induct u, simp_all)
          (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(9) fun_hyps_bis(1))
    qed
    have \<open>(\<forall>t. t \<in> \<D> (Renaming P f' g') \<longrightarrow> t \<in> \<D> (Renaming P f g)) \<and>
          (\<forall>t X. (t, X) \<in> \<F> (Renaming P f' g') \<longrightarrow> t \<notin> \<D> (Renaming P f' g') \<longrightarrow> (t, X) \<in> \<F> (Renaming P f g))\<close>
    proof (intro conjI allI impI)
      fix t assume \<open>t \<in> \<D> (Renaming P f' g')\<close>
      then obtain u1 u2 where * : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g') u1 @ u2\<close>
        \<open>tF u1\<close> \<open>ftF u2\<close> \<open>u1 \<in> \<D> P\<close> unfolding D_Renaming by blast
      have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g') u1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1\<close>
        by (simp add: \<open>tF u1\<close> "$" "*"(4) D_T)
      with "*" show \<open>t \<in> \<D> (Renaming P f g)\<close>
        by (auto simp add: D_Renaming)
    next
      fix t X assume \<open>(t, X) \<in> \<F> (Renaming P f' g')\<close> \<open>t \<notin> \<D> (Renaming P f' g')\<close>
      then obtain u where * : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g') u\<close>
        \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g' -` X) \<in> \<F> P\<close>
        unfolding Renaming_projs by blast
      show \<open>(t, X) \<in> \<F> (Renaming P f g)\<close>
      proof (cases \<open>tF u\<close>)
        assume \<open>tF u\<close>
        have \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g' -` X \<union> {ev a |a. a \<notin> \<alpha>(P)} \<union>
              {\<checkmark>(r) |r. r \<notin> \<^bold>\<checkmark>\<^bold>s(P)}) \<in> \<F> P\<close> (is \<open>(u, ?Y) \<in> \<F> P\<close>)
          by (intro is_processT5, simp_all add: "*"(2))
            (meson T_F_spec events_of_memI in_set_conv_decomp,
              metis (mono_tags, lifting) "*"(1) D_Renaming F_imp_front_tickFree T_F_spec
              \<open>t \<notin> \<D> (Renaming P f' g')\<close> append_Nil2 append_T_imp_tickFree is_processT1
              is_processT9 list.simps(3) mem_Collect_eq strict_ticks_of_memI)
        moreover from fun_hyps_bis
        have \<open>e \<in> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<Longrightarrow> e \<in> ?Y\<close> for e
          by (cases e) auto
        ultimately have \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> P\<close>
          by (meson is_processT4 subset_eq)
        moreover have \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close>
          by (metis "$" "*" F_T \<open>tF u\<close>)
        ultimately show \<open>(t, X) \<in> \<F> (Renaming P f g)\<close>
          by (auto simp add: F_Renaming)
      next
        assume \<open>\<not> tF u\<close>
        then obtain u' r where \<open>tF u'\<close> \<open>u = u' @ [\<checkmark>(r)]\<close>
          by (metis "*"(2) F_imp_front_tickFree front_tickFree_append_iff
              nonTickFree_n_frontTickFree not_Cons_self2)
        from "*"(2) F_T \<open>u = u' @ [\<checkmark>(r)]\<close> have \<open>u' @ [\<checkmark>(r)] \<in> \<T> P\<close> by blast
        have $$ : \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g') u' = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u'\<close>
          by (metis "$" "*"(2) F_T \<open>tF u'\<close> \<open>u = u' @ [\<checkmark>(r)]\<close> is_processT3_TR_append)
        have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g') u' @ [\<checkmark>(g' r)] \<in> \<T> (Renaming P f g)\<close>
        proof (cases \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close>)
          assume \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close>
          hence \<open>g' r = g r\<close> by (simp add: fun_hyps_bis(2))
          with "$$" show \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g') u' @ [\<checkmark>(g' r)] \<in> \<T> (Renaming P f g)\<close>
            by (simp add: T_Renaming) (use \<open>u' @ [\<checkmark>(r)] \<in> \<T> P\<close> in auto)
        next
          assume \<open>r \<notin> \<^bold>\<checkmark>\<^bold>s(P)\<close>
          hence \<open>u' \<in> \<D> P\<close>
            by (metis \<open>u' @ [\<checkmark>(r)] \<in> \<T> P\<close> is_processT9 strict_ticks_of_memI)
          hence \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u' \<in> \<D> (Renaming P f g)\<close>
            using D_Renaming F_imp_front_tickFree \<open>tF u'\<close> is_processT1 by blast
          with "$$" have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g') u' \<in> \<D> (Renaming P f g)\<close> by presburger
          hence \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g') u' @ [\<checkmark>(g' r)] \<in> \<D> (Renaming P f g)\<close>
            by (simp add: \<open>tF u'\<close> is_processT7 map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
          thus \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g') u' @ [\<checkmark>(g' r)] \<in> \<T> (Renaming P f g)\<close>
            by (simp add: D_T)
        qed
        hence \<open>(map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g') u' @ [\<checkmark>(g' r)], X) \<in> \<F> (Renaming P f g)\<close>
          by (simp add: tick_T_F)
        also have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g') u' @ [\<checkmark>(g' r)] = t\<close>
          by (simp add: "*"(1) \<open>u = u' @ [\<checkmark>(r)]\<close>)
        finally show \<open>(t, X) \<in> \<F> (Renaming P f g)\<close> .
      qed
    qed
    thus \<open>Renaming P f g \<sqsubseteq>\<^sub>F\<^sub>D Renaming P f' g'\<close>
      by (auto simp add: refine_defs intro: is_processT8) 
  qed
  show \<open>Renaming P f g = Renaming P f' g'\<close>
  proof (rule FD_antisym)
    show \<open>Renaming P f g \<sqsubseteq>\<^sub>F\<^sub>D Renaming P f' g'\<close> \<open>Renaming P f' g' \<sqsubseteq>\<^sub>F\<^sub>D Renaming P f g\<close>
      by (simp_all add: "*" fun_hyps)
  qed
qed


corollary Renaming_is_restrictable_on_events_of_ticks_of :
  \<open>\<lbrakk>\<And>a. a \<in> \<alpha>(P) \<Longrightarrow> f a = f' a; \<And>r. r \<in> \<checkmark>s(P) \<Longrightarrow> g r = g' r\<rbrakk>
   \<Longrightarrow> Renaming P f g = Renaming P f' g'\<close>
  by (rule Renaming_is_restrictable_on_events_of_strict_ticks_of)
    (simp_all add: ticks_of_is_strict_ticks_of_or_UNIV)


corollary RenamingEv_is_restrictable_on_events_of :
  \<open>(\<And>a. a \<in> \<alpha>(P) \<Longrightarrow> f a = f' a) \<Longrightarrow> RenamingEv P f = RenamingEv P f'\<close>
  by (fact Renaming_is_restrictable_on_events_of_ticks_of
      [of P f f' id id, simplified])


corollary RenamingTick_is_restrictable_on_strict_ticks_of :
  \<open>(\<And>r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> g r = g' r) \<Longrightarrow> RenamingTick P g = RenamingTick P g'\<close>
  by (fact Renaming_is_restrictable_on_events_of_strict_ticks_of
      [of P id id g g', simplified])


corollary RenamingTick_is_restrictable_on_ticks_of :
  \<open>(\<And>r. r \<in> \<checkmark>s(P) \<Longrightarrow> g r = g' r) \<Longrightarrow> RenamingTick P g = RenamingTick P g'\<close>
  by (fact Renaming_is_restrictable_on_events_of_ticks_of
      [of P id id g g', simplified])





section \<open>Renaming and Generalized Synchronization Product\<close>

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) inj_on_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>RenamingTick (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) g =
   Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<lambda>r s. case r \<otimes>\<checkmark> s of \<lfloor>r_s\<rfloor> \<Rightarrow> \<lfloor>g r_s\<rfloor> | \<diamond> \<Rightarrow> \<diamond>) P S Q\<close>
  (is \<open>?lhs = ?rhs\<close>)
  if inj_on_g : \<open>inj_on g range_tick_join\<close>
proof -
  let ?map_evt = \<open>\<lambda>g. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g)\<close>
  let ?tick_join' = \<open>\<lambda>r s. case r \<otimes>\<checkmark> s of \<lfloor>r_s\<rfloor> \<Rightarrow> \<lfloor>g r_s\<rfloor> | \<diamond> \<Rightarrow> \<diamond>\<close>
  interpret Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k' : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale ?tick_join'
    by (intro interpretable_inj_on_range_tick_join inj_on_g)
      \<comment>\<open>Thus \<^term>\<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ?tick_join' P S Q\<close> is well defined.\<close>
  have inj_on_inv_into_g :
    \<open>inj_on (inv_into range_tick_join g) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k'.range_tick_join\<close>
    by (rule inj_onI, simp split: option.split_asm)
      (metis (mono_tags, lifting) f_inv_into_f image_eqI mem_Collect_eq)
  from inv_into_f_f inj_on_g have expanded_tick_join :
    \<open>(\<otimes>\<checkmark>) = (\<lambda>r s. case ?tick_join' r s of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>r_s\<rfloor> \<Rightarrow> \<lfloor>inv_into range_tick_join g r_s\<rfloor>)\<close>
    by (fastforce split: split: option.split)
  show \<open>?lhs = ?rhs\<close>
  proof (rule Process_eq_optimizedI)
    fix t assume \<open>t \<in> \<D> ?lhs\<close>
    then obtain u1 u2 where * : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g) u1 @ u2\<close>
      \<open>tF u1\<close> \<open>ftF u2\<close> \<open>u1 \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      unfolding D_Renaming by blast
    from "*"(4) obtain v1 w1 t_P t_Q
      where ** : \<open>u1 = v1 @ w1\<close> \<open>tF v1\<close> \<open>ftF w1\<close>
        \<open>v1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
        \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
      unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    from inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_g "**"(4)]
    have \<open>?map_evt g v1 setinterleaves\<^sub>\<checkmark>\<^bsub>?tick_join'\<^esub> ((t_P, t_Q), S)\<close> .
    moreover from "*"(1-3) "**"(1, 2)
    have \<open>t = ?map_evt g v1 @ (?map_evt g w1 @ u2) \<and>
          tF (?map_evt g v1) \<and> ftF (?map_evt g w1 @ u2)\<close>
      by (simp add: front_tickFree_append_iff map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
    ultimately show \<open>t \<in> \<D> ?rhs\<close>
      using "**"(5) by (simp (no_asm) add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k'.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
  next
    fix t assume \<open>t \<in> \<D> ?rhs\<close>
    then obtain u v t_P t_Q
      where * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
        \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>?tick_join'\<^esub> ((t_P, t_Q), S)\<close>
        \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k'.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    from \<open>tF u\<close> have \<open>e \<in> set u \<Longrightarrow> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id (g \<circ> inv_into range_tick_join g) e = e\<close> for e
      by (cases e) (simp_all add: tickFree_def disjoint_iff)
    hence \<open>t = ?map_evt g (?map_evt (inv_into range_tick_join g) u) @ v\<close>
      by (simp add: "*"(1) flip: map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comp)
        (induct u, simp_all)
    moreover have \<open>tF (?map_evt (inv_into range_tick_join g) u)\<close>
      by (simp add: "*"(2) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
    moreover
    {
      have \<open>?map_evt (inv_into range_tick_join g) u =
            ?map_evt (inv_into range_tick_join g) u @ []\<close> by simp
      moreover have \<open>tF ((map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id (inv_into range_tick_join g))) u)\<close>
        by (simp add: "*"(2) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
      moreover have \<open>ftF []\<close> by simp
      moreover from Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k'.inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
        [OF inj_on_inv_into_g "*"(4), folded expanded_tick_join]
      have \<open>?map_evt (inv_into range_tick_join g) u
            setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close> .
      ultimately have \<open>?map_evt (inv_into range_tick_join g) u \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
        unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k using "*"(5) by blast
    }
    ultimately show \<open>t \<in> \<D> ?lhs\<close>
      unfolding D_Renaming using "*"(3) by blast
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    then obtain u
      where * : \<open>t = ?map_evt g u\<close> \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      unfolding Renaming_projs by blast
    with \<open>t \<notin> \<D> ?lhs\<close> obtain t_P t_Q X_P X_Q
      where ** : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
        \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P S X_Q\<close>
      by (auto simp add: D_Renaming Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
        (metis append.right_neutral front_tickFree_Nil map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree)+
    have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>?tick_join'\<^esub> ((t_P, t_Q), S)\<close>
      using "*"(1) "**"(3) inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k inj_on_g by blast
    moreover from vimage_inj_on_subset_super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff[OF inj_on_g, THEN iffD1, OF "**"(4)]
    have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ?tick_join' X_P S X_Q\<close> .
    ultimately show \<open>(t, X) \<in> \<F> ?rhs\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k'.F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k using "**"(1, 2) by fast
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
    then obtain t_P t_Q X_P X_Q
      where * : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>?tick_join'\<^esub> ((t_P, t_Q), S)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ?tick_join' X_P S X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k'.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    from Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k'.setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_imp_set_range_tick_join[OF "*"(3)]
    have \<open>{r_s. \<checkmark>(r_s) \<in> set t} \<subseteq> Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k'.range_tick_join\<close> .
    hence \<open>e \<in> set t \<Longrightarrow> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id (g \<circ> inv_into range_tick_join g) e = e\<close> for e
      by (cases e, auto simp add: subset_iff split: option.split_asm)
        (metis (mono_tags, lifting) inv_into_f_f mem_Collect_eq inj_on_g)
    hence \<open>t = ?map_evt g (?map_evt (inv_into range_tick_join g) t)\<close>
      by (simp add: "*"(1) flip: map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comp)
        (induct t, simp_all)
    moreover
    { from Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k'.inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
        [OF inj_on_inv_into_g "*"(3), folded expanded_tick_join]
      have \<open>?map_evt (inv_into range_tick_join g) t
            setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close> .
      moreover from vimage_inj_on_subset_super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff
        [OF inj_on_g, THEN iffD2, OF "*"(4)]
      have \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X \<subseteq>
            super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P S X_Q\<close> .
      ultimately have \<open>(?map_evt (inv_into range_tick_join g) t,
                        map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
        by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k "*"(1, 2))
    }
    ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close> unfolding F_Renaming by blast
  qed
qed



lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) inj_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_RenamingTick :
  \<open>RenamingTick P g \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> RenamingTick Q h =
   Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<lambda>r s. g r \<otimes>\<checkmark> h s) P S Q\<close> (is \<open>?lhs = ?rhs\<close>)
  if \<open>inj g\<close> and \<open>inj h\<close>
    (* is \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<lambda>r s. g r \<otimes>\<checkmark> h s)\<close> \<open>inj_on g \<^bold>\<checkmark>\<^bold>s(P)\<close> \<open>inj_on h \<^bold>\<checkmark>\<^bold>s(Q)\<close> enough ? *)
  for P :: \<open>('a, 'r') process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and Q :: \<open>('a, 's') process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof -
  interpret tjoin_interpreted : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. g r \<otimes>\<checkmark> h s\<close>
    by unfold_locales (meson injD inj_tick_join \<open>inj g\<close> \<open>inj h\<close>)
  let ?map_evt = \<open>\<lambda>g. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g)\<close>
  let ?map_ev  = \<open>\<lambda>t. map ev (map of_ev t)\<close>
  let ?RT      = RenamingTick
  have  * : \<open>tF t \<Longrightarrow> ?map_evt g t = ?map_ev t\<close> for t :: \<open>('a, 'r') trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (induct t) (auto simp add: is_ev_def)
  have ** : \<open>tF t \<Longrightarrow> ?map_evt h t = ?map_ev t\<close> for t :: \<open>('a, 's') trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (induct t) (auto simp add: is_ev_def)
  have *** : \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map_evt g u, ?map_evt h v), S)
       \<longleftrightarrow> t setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. g r \<otimes>\<checkmark> h s\<^esub> ((u, v), S)\<close> for t u v
    by (induct \<open>(\<lambda>r s. g r \<otimes>\<checkmark> h s, u, S, v)\<close> arbitrary: t u v) (auto split: option.split)
  have **** : \<open>?map_evt g t = ?map_evt g t' \<longleftrightarrow> t = t'\<close> for t t' :: \<open>('a, 'r') trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (rule iffI, induct t arbitrary: t', auto)
      (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inj_map id_apply inj_def \<open>inj g\<close>)
  have ***** : \<open>?map_evt h t = ?map_evt h t' \<longleftrightarrow> t = t'\<close> for t t' :: \<open>('a, 's') trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (rule iffI, induct t arbitrary: t', auto)
      (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inj_map id_apply inj_def \<open>inj h\<close>)
  show \<open>?lhs = ?rhs\<close>
  proof (rule Process_eq_optimizedI)
    fix t assume \<open>t \<in> \<D> ?lhs\<close>
    then obtain u v t_P' t_Q' where $ : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
      \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P', t_Q'), S)\<close>
      \<open>t_P' \<in> \<D> (?RT P g) \<and> t_Q' \<in> \<T> (?RT Q h) \<and> t_Q' \<notin> \<D> (?RT Q h) \<or>
     t_P' \<in> \<T> (?RT P g) \<and> t_P' \<notin> \<D> (?RT P g) \<and> t_Q' \<in> \<D> (?RT Q h) \<or>
     t_P' \<in> \<D> (?RT P g) \<and> t_Q' \<in> \<D> (?RT Q h)\<close>
      unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    from "$"(5) show \<open>t \<in> \<D> ?rhs\<close>
    proof (elim disjE conjE)
      assume \<open>t_P' \<in> \<D> (?RT P g)\<close> \<open>t_Q' \<in> \<T> (?RT Q h)\<close> \<open>t_Q' \<notin> \<D> (?RT Q h)\<close>
      then obtain t_P\<^sub>1 t_P\<^sub>2 t_Q
        where $$ : \<open>t_P' = ?map_evt g t_P\<^sub>1 @ t_P\<^sub>2\<close> \<open>tF t_P\<^sub>1\<close> \<open>ftF t_P\<^sub>2\<close> \<open>t_P\<^sub>1 \<in> \<D> P\<close>
          \<open>t_Q' = ?map_evt h t_Q\<close> \<open>t_Q \<in> \<T> Q\<close> unfolding Renaming_projs by blast
      from "$"(4)[unfolded "$$"(1), THEN setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL]
      obtain u\<^sub>1 u\<^sub>2 t_Q'\<^sub>1 t_Q'\<^sub>2 where $$$ : \<open>u = u\<^sub>1 @ u\<^sub>2\<close> \<open>t_Q' = t_Q'\<^sub>1 @ t_Q'\<^sub>2\<close>
        \<open>u\<^sub>1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map_evt g t_P\<^sub>1, t_Q'\<^sub>1), S)\<close> by blast
      obtain t_Q\<^sub>1 t_Q\<^sub>2 where \<open>t_Q = t_Q\<^sub>1 @ t_Q\<^sub>2\<close> \<open>t_Q'\<^sub>1 = ?map_evt h t_Q\<^sub>1\<close>
        by (metis "$$"(5) "$$$"(2) map_eq_append_conv)
      from "$$$"(3)[unfolded this(2), THEN "***"[THEN iffD1]]
      have \<open>u\<^sub>1 setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. g r \<otimes>\<checkmark> h s\<^esub> ((t_P\<^sub>1, t_Q\<^sub>1), S)\<close> .
      moreover from \<open>t_Q = t_Q\<^sub>1 @ t_Q\<^sub>2\<close> is_processT3_TR_append "$$"(6)
      have \<open>t_Q\<^sub>1 \<in> \<T> Q\<close> by blast
      ultimately show \<open>t \<in> \<D> ?rhs\<close>
        using "$"(1-3) "$$"(4) "$$$"(1) front_tickFree_append
        by (auto simp add: tjoin_interpreted.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    next
      assume \<open>t_Q' \<in> \<D> (?RT Q h)\<close> \<open>t_P' \<in> \<T> (?RT P g)\<close> \<open>t_P' \<notin> \<D> (?RT P g)\<close>
      then obtain t_Q\<^sub>1 t_Q\<^sub>2 t_P
        where $$ : \<open>t_Q' = ?map_evt h t_Q\<^sub>1 @ t_Q\<^sub>2\<close> \<open>tF t_Q\<^sub>1\<close> \<open>ftF t_Q\<^sub>2\<close> \<open>t_Q\<^sub>1 \<in> \<D> Q\<close>
          \<open>t_P' = ?map_evt g t_P\<close> \<open>t_P \<in> \<T> P\<close> unfolding Renaming_projs by blast
      from "$"(4)[unfolded "$$"(1), THEN setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendR]
      obtain u\<^sub>1 u\<^sub>2 t_P'\<^sub>1 t_P'\<^sub>2 where $$$ : \<open>u = u\<^sub>1 @ u\<^sub>2\<close> \<open>t_P' = t_P'\<^sub>1 @ t_P'\<^sub>2\<close>
        \<open>u\<^sub>1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P'\<^sub>1, ?map_evt h t_Q\<^sub>1), S)\<close> by blast
      obtain t_P\<^sub>1 t_P\<^sub>2 where \<open>t_P = t_P\<^sub>1 @ t_P\<^sub>2\<close> \<open>t_P'\<^sub>1 = ?map_evt g t_P\<^sub>1\<close>
        by (metis "$$"(5) "$$$"(2) map_eq_append_conv)
      from "$$$"(3)[unfolded this(2), THEN "***"[THEN iffD1]]
      have \<open>u\<^sub>1 setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. g r \<otimes>\<checkmark> h s\<^esub> ((t_P\<^sub>1, t_Q\<^sub>1), S)\<close> .
      moreover from \<open>t_P = t_P\<^sub>1 @ t_P\<^sub>2\<close> is_processT3_TR_append "$$"(6)
      have \<open>t_P\<^sub>1 \<in> \<T> P\<close> by blast
      ultimately show \<open>t \<in> \<D> ?rhs\<close>
        using "$"(1-3) "$$"(4) "$$$"(1) front_tickFree_append
        by (auto simp add: tjoin_interpreted.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    next
      assume \<open>t_P' \<in> \<D> (?RT P g)\<close> \<open>t_Q' \<in> \<D> (?RT Q h)\<close>
      then obtain t_P\<^sub>1 t_P\<^sub>2 t_Q\<^sub>1 t_Q\<^sub>2
        where $$ : \<open>t_P' = ?map_evt g t_P\<^sub>1 @ t_P\<^sub>2\<close> \<open>tF t_P\<^sub>1\<close> \<open>ftF t_P\<^sub>2\<close> \<open>t_P\<^sub>1 \<in> \<D> P\<close>
          \<open>t_Q' = ?map_evt h t_Q\<^sub>1 @ t_Q\<^sub>2\<close> \<open>tF t_Q\<^sub>1\<close> \<open>ftF t_Q\<^sub>2\<close> \<open>t_Q\<^sub>1 \<in> \<D> Q\<close>
        unfolding D_Renaming by blast
      from "$"(4)[unfolded "$$"(1, 5), THEN setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL]
      obtain u\<^sub>1 u\<^sub>2 t_Q\<^sub>1_bis t_Q\<^sub>2_bis
        where $$$ : \<open>u = u\<^sub>1 @ u\<^sub>2\<close> \<open>?map_evt h t_Q\<^sub>1 @ t_Q\<^sub>2 = t_Q\<^sub>1_bis @ t_Q\<^sub>2_bis\<close>
          \<open>u\<^sub>1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map_evt g t_P\<^sub>1, t_Q\<^sub>1_bis), S)\<close> by blast
      from "$$$"(2) have \<open>t_Q\<^sub>1_bis = ?map_evt h (take (length t_Q\<^sub>1_bis) t_Q\<^sub>1) \<or>
        t_Q\<^sub>1_bis = ?map_evt h t_Q\<^sub>1 @ take (length t_Q\<^sub>1_bis - length t_Q\<^sub>1) t_Q\<^sub>2\<close>
        by (cases \<open>length t_Q\<^sub>1_bis \<le> length t_Q\<^sub>1\<close>)
          (simp_all add: append_eq_append_conv_if take_map split: if_split_asm)
      thus \<open>t \<in> \<D> ?rhs\<close>
      proof (elim disjE)
        assume \<open>t_Q\<^sub>1_bis = ?map_evt h (take (length t_Q\<^sub>1_bis) t_Q\<^sub>1)\<close>
        hence \<open>u\<^sub>1 setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. g r \<otimes>\<checkmark> h s\<^esub> ((t_P\<^sub>1, take (length t_Q\<^sub>1_bis) t_Q\<^sub>1), S)\<close>
          by (metis "$$$"(3) "***")  
        moreover have \<open>take (length t_Q\<^sub>1_bis) t_Q\<^sub>1 \<in> \<T> Q\<close>
          by (metis "$$"(8) D_T append_take_drop_id is_processT3_TR_append)
        ultimately show \<open>t \<in> \<D> ?rhs\<close>
          using "$"(1-3) "$$"(4) "$$$"(1) front_tickFree_append
          by (auto simp add: tjoin_interpreted.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      next
        assume \<open>t_Q\<^sub>1_bis = ?map_evt h t_Q\<^sub>1 @ take (length t_Q\<^sub>1_bis - length t_Q\<^sub>1) t_Q\<^sub>2\<close>
        with "$$$"(3)
        have \<open>u\<^sub>1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map_evt g t_P\<^sub>1,
                 ?map_evt h t_Q\<^sub>1 @ take (length t_Q\<^sub>1_bis - length t_Q\<^sub>1) t_Q\<^sub>2), S)\<close> by simp
        from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendR[OF this] obtain u\<^sub>1\<^sub>1 u\<^sub>1\<^sub>2 t_P\<^sub>1\<^sub>1 t_P\<^sub>1\<^sub>2
          where $$$$ : \<open>u\<^sub>1 = u\<^sub>1\<^sub>1 @ u\<^sub>1\<^sub>2\<close> \<open>?map_evt g t_P\<^sub>1 = t_P\<^sub>1\<^sub>1 @ t_P\<^sub>1\<^sub>2\<close>
            \<open>u\<^sub>1\<^sub>1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P\<^sub>1\<^sub>1, ?map_evt h t_Q\<^sub>1), S)\<close> by blast
        have \<open>t_P\<^sub>1\<^sub>1 = ?map_evt g (take (length t_P\<^sub>1\<^sub>1) t_P\<^sub>1)\<close>
          by (metis "$$$$"(2) append_eq_conv_conj take_map)
        hence \<open>u\<^sub>1\<^sub>1 setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. g r \<otimes>\<checkmark> h s\<^esub>((take (length t_P\<^sub>1\<^sub>1) t_P\<^sub>1, t_Q\<^sub>1), S)\<close>
          by (metis "$$$$"(3) "***")
        moreover have \<open>take (length t_P\<^sub>1\<^sub>1) t_P\<^sub>1 \<in> \<T> P\<close>
          by (metis "$$"(4) D_T append_take_drop_id is_processT3_TR_append)
        ultimately show \<open>t \<in> \<D> ?rhs\<close>
          by (simp add: tjoin_interpreted.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
            (metis (no_types, lifting) "$"(1,2,3) "$$"(8) "$$$"(1) "$$$$"(1)
              append.assoc front_tickFree_append tickFree_append_iff)
      qed
    qed
  next
    fix t assume \<open>t \<in> \<D> ?rhs\<close>
    then obtain u v t_P t_Q where $ : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
      \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. g r \<otimes>\<checkmark> h s\<^esub> ((t_P, t_Q), S)\<close>
      \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
      unfolding tjoin_interpreted.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    from tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff[THEN iffD1, OF "$"(4, 2)]
    have \<open>tF t_P\<close> \<open>tF t_Q\<close> by simp_all

    with "$"(5) have \<open>?map_evt g t_P \<in> \<D> (?RT P g) \<and> ?map_evt h t_Q \<in> \<T> (?RT Q h) \<or>
                    ?map_evt g t_P \<in> \<T> (?RT P g) \<and> ?map_evt h t_Q \<in> \<D> (?RT Q h)\<close>
      by (simp add: Renaming_projs) (metis append.right_neutral front_tickFree_Nil)
    moreover from "***"[THEN iffD2, OF "$"(4)]
    have \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map_evt g t_P, ?map_evt h t_Q), S)\<close> .
    ultimately show \<open>t \<in> \<D> ?lhs\<close>
      using "$"(1-3) by (auto simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    then obtain t_P' X_P' t_Q' X_Q'
      where $ : \<open>(t_P', X_P') \<in> \<F> (?RT P g)\<close> \<open>(t_Q', X_Q') \<in> \<F> (?RT Q h)\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P', t_Q'), S)\<close> \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P' S X_Q'\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    from \<open>t \<notin> \<D> ?lhs\<close> "$"(1, 2)[THEN F_T] "$"(3)
    have \<open>t_P' \<notin> \<D> (?RT P g) \<and> t_Q' \<notin> \<D> (?RT Q h)\<close>
      by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k') (metis append_self_conv front_tickFree_Nil)
    with "$"(1, 2) obtain t_P t_Q
      where $$ : \<open>t_P' = ?map_evt g t_P\<close> \<open>(t_P, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X_P') \<in> \<F> P\<close>
        \<open>t_Q' = ?map_evt h t_Q\<close> \<open>(t_Q, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id h -` X_Q') \<in> \<F> Q\<close>
      unfolding Renaming_projs by blast
    from "$"(3)[unfolded "$$"(1, 3), THEN "***"[THEN iffD1]]
    have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. g r \<otimes>\<checkmark> h s\<^esub> ((t_P, t_Q), S)\<close> .
    moreover from "$"(4) inj_tick_join
    have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<lambda>r s. g r \<otimes>\<checkmark> h s)
            (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X_P') S (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id h -` X_Q')\<close>
      by (simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def, safe) blast
    ultimately show \<open>(t, X) \<in> \<F> ?rhs\<close>
      using "$$"(2, 4) by (auto simp add: tjoin_interpreted.F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
    then obtain t_P t_Q X_P X_Q
      where $ : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. g r \<otimes>\<checkmark> h s\<^esub> ((t_P, t_Q), S)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<lambda>r s. g r \<otimes>\<checkmark> h s) X_P S X_Q\<close>
      unfolding tjoin_interpreted.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    from \<open>t \<notin> \<D> ?rhs\<close> have \<open>t_P \<notin> \<D> P \<and> t_Q \<notin> \<D> Q\<close>
      by (simp add: tjoin_interpreted.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k')
        (metis "$"(1-3) F_T append.right_neutral front_tickFree_Nil)
    hence $$ : \<open>t_P @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close>
      \<open>t_Q @ [\<checkmark>(s)] \<in> \<T> Q \<Longrightarrow> s \<in> \<^bold>\<checkmark>\<^bold>s(Q)\<close> for r s
      by (meson is_processT9 strict_ticks_of_memI)+
    have $$$ : \<open>?map_evt g t_P @ [\<checkmark>(g_r)] \<in> \<T> (?RT P g) \<longleftrightarrow> (\<exists>r. g_r = g r \<and> t_P @ [\<checkmark>(r)] \<in> \<T> P)\<close> for g_r
    proof (rule iffI)
      from \<open>t_P \<notin> \<D> P \<and> t_Q \<notin> \<D> Q\<close> have \<open>?map_evt g t_P \<notin> \<D> (?RT P g)\<close>
        by (simp add: D_Renaming map_eq_append_conv "****")
          (use is_processT7 map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree in blast)
      hence \<open>?map_evt g t_P @ [\<checkmark>(g_r)] \<notin> \<D> (?RT P g)\<close> by (meson is_processT9)
      moreover assume \<open>?map_evt g t_P @ [\<checkmark>(g_r)] \<in> \<T> (?RT P g)\<close>
      ultimately show \<open>?map_evt g t_P @ [\<checkmark>(g_r)] \<in> \<T> (?RT P g) \<Longrightarrow> \<exists>r. g_r = g r \<and> t_P @ [\<checkmark>(r)] \<in> \<T> P\<close>
        by (auto simp add: Renaming_projs append_eq_map_conv tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff "****")
    next
      show \<open>\<exists>r. g_r = g r \<and> t_P @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> ?map_evt g t_P @ [\<checkmark>(g_r)] \<in> \<T> (?RT P g)\<close>
        by (auto simp add: T_Renaming)
    qed
    have $$$$ : \<open>?map_evt h t_Q @ [\<checkmark>(h_s)] \<in> \<T> (?RT Q h) \<longleftrightarrow> (\<exists>s. h_s = h s \<and> t_Q @ [\<checkmark>(s)] \<in> \<T> Q)\<close> for h_s
    proof (rule iffI)
      from \<open>t_P \<notin> \<D> P \<and> t_Q \<notin> \<D> Q\<close> have \<open>?map_evt h t_Q \<notin> \<D> (?RT Q h)\<close>
        by (simp add: D_Renaming map_eq_append_conv "*****")
          (use is_processT7 map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree in blast)
      hence \<open>?map_evt h t_Q @ [\<checkmark>(h_s)] \<notin> \<D> (?RT Q h)\<close> by (meson is_processT9)
      moreover assume \<open>?map_evt h t_Q @ [\<checkmark>(h_s)] \<in> \<T> (?RT Q h)\<close>
      ultimately show \<open>?map_evt h t_Q @ [\<checkmark>(h_s)] \<in> \<T> (?RT Q h) \<Longrightarrow> \<exists>s. h_s = h s \<and> t_Q @ [\<checkmark>(s)] \<in> \<T> Q\<close>
        by (auto simp add: Renaming_projs append_eq_map_conv tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff "*****")
    next
      show \<open>\<exists>s. h_s = h s \<and> t_Q @ [\<checkmark>(s)] \<in> \<T> Q \<Longrightarrow> ?map_evt h t_Q @ [\<checkmark>(h_s)] \<in> \<T> (?RT Q h)\<close>
        by (auto simp add: T_Renaming)
    qed

    define X_P' where \<open>X_P' \<equiv> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g ` X_P \<union> {\<checkmark>(g_r) |g_r. ?map_evt g t_P @ [\<checkmark>(g_r)] \<notin> \<T> (?RT P g)}\<close>
    define X_Q' where \<open>X_Q' \<equiv> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id h ` X_Q \<union> {\<checkmark>(h_s) |h_s. ?map_evt h t_Q @ [\<checkmark>(h_s)] \<notin> \<T> (?RT Q h)}\<close>

    have \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g ` X_P) = X_P\<close>
      \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id h -` (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id h ` X_Q) = X_Q\<close>
      by (simp_all add: set_eq_iff image_iff) 
        (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inj_map injD inj_on_id \<open>inj g\<close>,
          metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inj_map injD inj_on_id \<open>inj h\<close>)
    with "$"(1, 2) have \<open>(?map_evt g t_P, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g ` X_P) \<in> \<F> (?RT P g)\<close>
      \<open>(?map_evt h t_Q, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id h ` X_Q) \<in> \<F> (?RT Q h)\<close>
      by (auto simp add: F_Renaming)
    hence \<open>(?map_evt g t_P, X_P') \<in> \<F> (?RT P g)\<close>
      \<open>(?map_evt h t_Q, X_Q') \<in> \<F> (?RT Q h)\<close>
      by (auto simp add: X_P'_def X_Q'_def intro: is_processT5 F_T)
    moreover have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map_evt g t_P, ?map_evt h t_Q), S)\<close>
      by (simp add: "$"(3) "***")
    moreover have \<open>e \<in> X \<Longrightarrow> e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P' S X_Q'\<close> for e
      using "$"(4)[THEN set_mp, of e]
      by (cases e,
          simp_all add: X_P'_def X_Q'_def super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def image_iff
          ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff "$$$" "$$$$")
        metis
    ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
  qed
qed



(*<*)
end
  (*>*)
