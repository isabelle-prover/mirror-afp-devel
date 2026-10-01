(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Events and ticks of a process
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

chapter \<open>Events and Ticks of a Process\<close>

(*<*)
theory Events_Ticks_CSP_Laws
  imports Constant_Processes Deterministic_Choice Non_Deterministic_Choice
    Global_Non_Deterministic_Choice Sliding_Choice
    Multi_Deterministic_Prefix_Choice Multi_Non_Deterministic_Prefix_Choice
    Sequential_Composition Synchronization_Product Hiding Renaming CSP_Refinements
begin
  (*>*)

section \<open>Definitions\<close>

subsection \<open>Events of a Process\<close>

definition events_of :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'a set\<close> (\<open>\<alpha>'(_')\<close>)
  \<comment>\<open>\<^term>\<open>\<alpha>(P)\<close> for ``alphabet of \<^term>\<open>P\<close>''\<close>
  where \<open>\<alpha>(P) \<equiv> \<Union>t\<in>\<T> P. {a. ev a \<in> set t}\<close>

lemma events_of_memI : \<open>t \<in> \<T> P \<Longrightarrow> ev a \<in> set t \<Longrightarrow> a \<in> \<alpha>(P)\<close>
  unfolding events_of_def by blast

lemma events_of_memD : \<open>a \<in> \<alpha>(P) \<Longrightarrow> \<exists>t \<in> \<T> P. ev a \<in> set t\<close>
  unfolding events_of_def by blast

lemma events_of_memE :
  \<open>a \<in> \<alpha>(P) \<Longrightarrow> (\<And>t. t \<in> \<T> P \<Longrightarrow> ev a \<in> set t \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  by (meson events_of_memD)

lemma events_of_memE_optimized_tF :
  \<open>(\<And>t. t \<in> \<T> P \<Longrightarrow> ev a \<in> set t \<Longrightarrow> tF t \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> if \<open>a \<in> \<alpha>(P)\<close>
proof -
  from \<open>a \<in> \<alpha>(P)\<close> obtain t where \<open>t \<in> \<T> P\<close> \<open>ev a \<in> set t\<close>
    by (meson events_of_memE)
  have \<open>(if tF t then t else butlast t) \<in> \<T> P\<close>
    by simp (metis \<open>t \<in> \<T> P\<close> append_butlast_last_id is_processT3_TR_append tF_Nil)
  moreover from T_not_tF_imp_decomp \<open>ev a \<in> set t\<close> \<open>t \<in> \<T> P\<close>
  have \<open>ev a \<in> set (if tF t then t else butlast t)\<close> by force
  moreover from T_imp_ftF \<open>t \<in> \<T> P\<close> ftF_iff_tF_butlast
  have \<open>tF (if tF t then t else butlast t)\<close> by (metis (full_types))
  ultimately show \<open>(\<And>t. t \<in> \<T> P \<Longrightarrow> ev a \<in> set t \<Longrightarrow> tF t \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
qed



definition strict_events_of :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'a set\<close> (\<open>\<^bold>\<alpha>'(_')\<close>)
  where \<open>\<^bold>\<alpha>(P) \<equiv> \<Union>t\<in>\<T> P - \<D> P. {a. ev a \<in> set t}\<close>

lemma strict_events_of_memI :
  \<open>t \<in> \<T> P \<Longrightarrow> t \<notin> \<D> P \<Longrightarrow> ev a \<in> set t \<Longrightarrow> a \<in> \<^bold>\<alpha>(P)\<close>
  unfolding strict_events_of_def by blast

lemma strict_events_of_memD : \<open>a \<in> \<^bold>\<alpha>(P) \<Longrightarrow> \<exists>t \<in> \<T> P. t \<notin> \<D> P \<and> ev a \<in> set t\<close>
  unfolding strict_events_of_def by blast

lemma strict_events_of_memE :
  \<open>a \<in> \<^bold>\<alpha>(P) \<Longrightarrow> (\<And>t. t \<in> \<T> P \<Longrightarrow> t \<notin> \<D> P \<Longrightarrow> ev a \<in> set t \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  by (meson strict_events_of_memD)

lemma strict_events_of_memE_optimized_tF :
  \<open>(\<And>t. t \<in> \<T> P \<Longrightarrow> t \<notin> \<D> P \<Longrightarrow> ev a \<in> set t \<Longrightarrow> tF t \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> if \<open>a \<in> \<^bold>\<alpha>(P)\<close>
proof -
  from \<open>a \<in> \<^bold>\<alpha>(P)\<close> obtain t where \<open>t \<in> \<T> P\<close> \<open>t \<notin> \<D> P\<close> \<open>ev a \<in> set t\<close>
    by (meson strict_events_of_memE)
  have \<open>(if tF t then t else butlast t) \<in> \<T> P\<close>
    by simp (metis \<open>t \<in> \<T> P\<close> append_butlast_last_id is_processT3_TR_append tF_Nil)
  moreover have \<open>(if tF t then t else butlast t) \<notin> \<D> P\<close>
    using T_imp_ftF \<open>t \<in> \<T> P\<close> \<open>t \<notin> \<D> P\<close> div_butlast_when_non_tF_iff by blast
  moreover from T_not_tF_imp_decomp \<open>ev a \<in> set t\<close> \<open>t \<in> \<T> P\<close>
  have \<open>ev a \<in> set (if tF t then t else butlast t)\<close> by force
  moreover from T_imp_ftF \<open>t \<in> \<T> P\<close> ftF_iff_tF_butlast
  have \<open>tF (if tF t then t else butlast t)\<close> by (metis (full_types))
  ultimately show \<open>(\<And>t. t \<in> \<T> P \<Longrightarrow> t \<notin> \<D> P \<Longrightarrow> ev a \<in> set t \<Longrightarrow> tF t \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
qed


lemma events_of_is_strict_events_of_or_UNIV :
  \<open>\<alpha>(P) = (if \<D> P = {} then \<^bold>\<alpha>(P) else UNIV)\<close>
proof (split if_split, intro conjI impI)
  show \<open>\<D> P = {} \<Longrightarrow> \<alpha>(P) = \<^bold>\<alpha>(P)\<close> by (simp add: events_of_def strict_events_of_def)
next
  assume \<open>\<D> P \<noteq> {}\<close>
  with nonempty_divE obtain t where \<open>tF t\<close> \<open>t \<in> \<D> P\<close> by blast
  hence \<open>t @ [ev a] \<in> \<D> P\<close> for a by (simp add: is_processT7)
  thus \<open>\<alpha>(P) = UNIV\<close> by (metis D_T UNIV_eq_I events_of_memI in_set_conv_decomp)
qed

lemma strict_events_of_subset_events_of : \<open>\<^bold>\<alpha>(P) \<subseteq> \<alpha>(P)\<close>
  by (simp add: events_of_is_strict_events_of_or_UNIV)



text \<open>
New in Isabelle26; we already had the notions of \<^const>\<open>events_of\<close> (alphabet),
and the stronger notion \<^const>\<open>strict_events_of\<close> (strict alphabet), but this is not enough.
The issue is simple: \<^term>\<open>\<alpha>(P)\<close> is too big (is the process \<^term>\<open>P\<close> diverges, \<^prop>\<open>\<alpha>(P) = UNIV\<close>)
and \<^term>\<open>\<^bold>\<alpha>(P)\<close> is too small (we lose all information about divergences).

We therefore introduce something in between.
\<close>


definition minimal_events_of :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'a set\<close> (\<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n'(_')\<close>)
  where \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<equiv> \<^bold>\<alpha>(P) \<union> (\<Union>t\<in>\<D>\<^sub>m\<^sub>i\<^sub>n P. {a. ev a \<in> set t})\<close>

lemma no_div_imp_strict_events_of_is_minimal_events_of :
  \<open>\<D> P = {} \<Longrightarrow> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) = \<^bold>\<alpha>(P)\<close>
  by (auto simp add: minimal_events_of_def dest: D\<^sub>m\<^sub>i\<^sub>n_D)

lemma minimal_events_of_def_bis :
  \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) = \<^bold>\<alpha>(P) \<union> {a. \<exists>t. t @ [ev a] \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P}\<close>
  by (auto simp add: minimal_events_of_def strict_events_of_def Divergences\<^sub>m\<^sub>i\<^sub>n_def_bis)
    (metis (no_types) D_T Diff_iff Un_iff append_butlast_last_id empty_iff
      empty_set is_processT3_TR_append list.simps(15) set_append singleton_iff)


lemma minimal_events_of_memI :
  \<open>t \<in> \<T> P \<Longrightarrow> t \<notin> \<D> P \<Longrightarrow> ev a \<in> set t \<Longrightarrow> a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)\<close>
  \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<Longrightarrow> ev a \<in> set t \<Longrightarrow> a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)\<close>
  unfolding minimal_events_of_def strict_events_of_def by auto

lemma minimal_events_of_memD :
  \<open>a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<Longrightarrow> \<exists>t \<in> \<T> P. tF t \<and> ev a \<in> set t \<and> (t \<notin> \<D> P \<or> t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P)\<close>
  by (simp add: minimal_events_of_def)
    (metis Divergences\<^sub>m\<^sub>i\<^sub>n_def tF_mem_D\<^sub>m\<^sub>i\<^sub>n
      strict_events_of_memE_optimized_tF D_T elem_min_elems)

lemma minimal_events_of_memE :
  \<open>\<lbrakk>a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P); \<And>t. tF t \<Longrightarrow> t \<in> \<T> P \<Longrightarrow> t \<notin> \<D> P \<Longrightarrow> ev a \<in> set t \<Longrightarrow> thesis;
    \<And>t. tF t \<Longrightarrow> t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<Longrightarrow> ev a \<in> set t \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close>
  by (metis minimal_events_of_memD)


lemma minimal_events_of_subset_events_of : \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<subseteq> \<alpha>(P)\<close>
  by (simp add: events_of_is_strict_events_of_or_UNIV
      no_div_imp_strict_events_of_is_minimal_events_of)




subsection \<open>Ticks of a Process\<close>

definition ticks_of :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'r set\<close> (\<open>\<checkmark>s'(_')\<close>)
  where \<open>\<checkmark>s(P) \<equiv> {r. \<exists>t. t @ [\<checkmark>(r)] \<in> \<T> P}\<close>

lemma ticks_of_memI : \<open>t @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> r \<in> \<checkmark>s(P)\<close>
  unfolding ticks_of_def by blast

lemma ticks_of_memD : \<open>r \<in> \<checkmark>s(P) \<Longrightarrow> \<exists>t. t @ [\<checkmark>(r)] \<in> \<T> P\<close>
  unfolding ticks_of_def by blast

lemma ticks_of_memE :
  \<open>r \<in> \<checkmark>s(P) \<Longrightarrow> (\<And>t. t @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  by (meson ticks_of_memD)


definition strict_ticks_of :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'r set\<close> (\<open>\<^bold>\<checkmark>\<^bold>s'(_')\<close>)
  where \<open>\<^bold>\<checkmark>\<^bold>s(P) \<equiv> {r. \<exists>s. s @ [\<checkmark>(r)] \<in> \<T> P - \<D> P}\<close>

lemma strict_ticks_of_memI :
  \<open>t @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> t @ [\<checkmark>(r)] \<notin> \<D> P \<Longrightarrow> r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close>
  unfolding strict_ticks_of_def by blast

lemma strict_ticks_of_memD :
  \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> \<exists>t. t @ [\<checkmark>(r)] \<in> \<T> P \<and> t \<notin> \<D> P\<close>
  by (simp add: strict_ticks_of_def)
    (metis T_imp_ftF butlast_snoc
      ftF_iff_tF_butlast ftF_single is_processT7)

lemma strict_ticks_of_memE :
  \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> (\<And>t. t @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> t \<notin> \<D> P \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  by (meson strict_ticks_of_memD)


lemma ticks_of_is_strict_ticks_of_or_UNIV :
  \<open>\<checkmark>s(P) = (if \<D> P = {} then \<^bold>\<checkmark>\<^bold>s(P) else UNIV)\<close>
proof (split if_split, intro conjI impI)
  show \<open>\<D> P = {} \<Longrightarrow> \<checkmark>s(P) = \<^bold>\<checkmark>\<^bold>s(P)\<close> by (simp add: ticks_of_def strict_ticks_of_def)
next
  assume \<open>\<D> P \<noteq> {}\<close>
  with nonempty_divE obtain t where \<open>tF t\<close> \<open>t \<in> \<D> P\<close> by blast
  hence \<open>t @ [\<checkmark>(r)] \<in> \<D> P\<close> for r by (simp add: is_processT7)
  thus \<open>\<checkmark>s(P) = UNIV\<close> by (metis D_T UNIV_eq_I ticks_of_memI)
qed

lemma strict_ticks_of_subset_ticks_of : \<open>\<^bold>\<checkmark>\<^bold>s(P) \<subseteq> \<checkmark>s(P)\<close>
  by (simp add: ticks_of_is_strict_ticks_of_or_UNIV)



section \<open>Laws\<close>

subsection \<open>Preliminaries\<close>

lemma inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T_tF :
  \<open>inj_on (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) {t \<in> \<T> P. tF t}\<close> if \<open>inj_on f \<alpha>(P)\<close>
proof (rule inj_onI)
  have * : \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g \<circ> ev = ev \<circ> f\<close> by (rule ext) simp
  have ** : \<open>map ev v \<in> \<T> P \<Longrightarrow> map ev v' \<in> \<T> P \<Longrightarrow>
             map (ev \<circ> f) v = map (ev \<circ> f) v' \<Longrightarrow> v = v'\<close> for v v'
  proof (induct v arbitrary: v' rule: rev_induct)
    case Nil thus ?case by simp
  next
    case (snoc a v)
    from snoc.prems(3) obtain a' v'' where \<open>v' = v'' @ [a']\<close>
      by (metis list.map_disc_iff rev_exhaust)
    from snoc.prems(1-3) have \<open>a = a'\<close>
      by (auto simp add: \<open>v' = v'' @ [a']\<close>
          intro!: inj_onD[OF \<open>inj_on f \<alpha>(P)\<close>] events_of_memI)
    from is_processT3_TR_append snoc.prems(1, 2)
    have \<open>map ev v \<in> \<T> P\<close> \<open>map ev v'' \<in> \<T> P\<close> by (simp_all add: \<open>v' = v'' @ [a']\<close>)
    with \<open>a = a'\<close> \<open>v' = v'' @ [a']\<close> snoc.hyps snoc.prems(3) show ?case
      by (metis append_same_eq map_append)
  qed

  fix t t' assume $ : \<open>t \<in> {t \<in> \<T> P. tF t}\<close> \<open>t' \<in> {t \<in> \<T> P. tF t}\<close>
    \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t'\<close>
  from "$"(1, 2) obtain v v' where \<open>t = map ev v\<close> \<open>t' = map ev v'\<close>
    by (auto simp add: tF_iff_is_map_ev)
  with "$" "*" "**" show \<open>t = t'\<close> by auto
qed


lemma inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T :
  \<open>inj_on (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) (\<T> P)\<close> if \<open>inj_on f \<alpha>(P)\<close> \<open>inj_on g \<checkmark>s(P)\<close>
proof (rule inj_onI)
  fix t t' assume $ : \<open>t \<in> \<T> P\<close> \<open>t' \<in> \<T> P\<close> \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t'\<close>
  then consider \<open>tF t\<close> \<open>tF t'\<close>
    | r r' u u' where \<open>t = u @ [\<checkmark>(r)]\<close> \<open>t' = u' @ [\<checkmark>(r')]\<close> \<open>tF u\<close> \<open>tF u'\<close>
      \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u'\<close>
    by (cases t rule: rev_cases; cases t' rule: rev_cases, simp_all)
      (metis append_T_imp_tF event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_disc_iff(1) neq_Nil_conv)
  thus \<open>t = t'\<close>
  proof cases
    show \<open>t = t'\<close> if \<open>tF t\<close> \<open>tF t'\<close>
      by (rule inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T_tF
          [OF \<open>inj_on f \<alpha>(P)\<close>, THEN inj_onD, OF "$"(3)])
        (simp_all add: "$"(1, 2) \<open>tF t\<close> \<open>tF t'\<close>)
  next
    fix r r' u u' assume $$ : \<open>t = u @ [\<checkmark>(r)]\<close> \<open>t' = u' @ [\<checkmark>(r')]\<close> \<open>tF u\<close> \<open>tF u'\<close>
      \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u'\<close>
    from "$$"(1, 2) "$"(1, 2) have \<open>u \<in> \<T> P\<close> \<open>u' \<in> \<T> P\<close>
      by (meson is_processT3_TR_append)+
    have \<open>u = u'\<close>
      by (rule inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T_tF
          [OF \<open>inj_on f \<alpha>(P)\<close>, THEN inj_onD, OF "$$"(5)])
        (simp_all add: \<open>u \<in> \<T> P\<close> \<open>u' \<in> \<T> P\<close> \<open>tF u\<close> \<open>tF u'\<close>)
    moreover from "$"(1-3) "$$"(1, 2) have \<open>r = r'\<close>
      by (auto intro: inj_onD[OF \<open>inj_on g \<checkmark>s(P)\<close>] ticks_of_memI)
    ultimately show \<open>t = t'\<close> by (simp add: "$$")
  qed
qed


lemma inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T_diff_D_tF :
  \<open>inj_on (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) {t \<in> \<T> P - \<D> P. tF t}\<close> if \<open>inj_on f \<^bold>\<alpha>(P)\<close>
proof (rule inj_onI)
  have * : \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g \<circ> ev = ev \<circ> f\<close> by (rule ext) simp
  have ** : \<open>\<lbrakk>map ev v \<in> \<T> P; map ev v \<notin> \<D> P;
             map ev v' \<in> \<T> P; map ev v' \<notin> \<D> P;
             map (ev \<circ> f) v = map (ev \<circ> f) v'\<rbrakk> \<Longrightarrow> v = v'\<close> for v v'
  proof (induct v arbitrary: v' rule: rev_induct)
    case Nil thus ?case by simp
  next
    case (snoc a v)
    from snoc.prems(5) obtain a' v'' where \<open>v' = v'' @ [a']\<close>
      by (metis list.map_disc_iff rev_exhaust)
    from snoc.prems(1-5) have \<open>a = a'\<close>
      by (auto simp add: \<open>v' = v'' @ [a']\<close>
          intro!: inj_onD[OF \<open>inj_on f \<^bold>\<alpha>(P)\<close>] strict_events_of_memI)
    from is_processT3_TR_append is_processT7 snoc.prems(1-4)
    have \<open>map ev v \<in> \<T> P\<close> \<open>map ev v \<notin> \<D> P\<close>
      \<open>map ev v'' \<in> \<T> P\<close> \<open>map ev v'' \<notin> \<D> P\<close>
      by (fastforce simp add: \<open>v' = v'' @ [a']\<close>)+
    with \<open>a = a'\<close> \<open>v' = v'' @ [a']\<close> snoc.hyps snoc.prems(5) show ?case
      by (metis append_same_eq map_append)
  qed

  fix t t' assume $ : \<open>t \<in> {t \<in> \<T> P - \<D> P. tF t}\<close> \<open>t' \<in> {t \<in> \<T> P - \<D> P. tF t}\<close>
    \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t'\<close>
  from "$"(1, 2) obtain v v' where \<open>t = map ev v\<close> \<open>t' = map ev v'\<close>
    by (auto simp add: tF_iff_is_map_ev)
  with "$" "*" "**" show \<open>t = t'\<close> by auto
qed


lemma inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T_diff_D :
  \<open>inj_on (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) (\<T> P - \<D> P)\<close> if \<open>inj_on f \<^bold>\<alpha>(P)\<close> and \<open>inj_on g \<^bold>\<checkmark>\<^bold>s(P)\<close>
proof (rule inj_onI)
  fix t t' assume $ : \<open>t \<in> \<T> P - \<D> P\<close> \<open>t' \<in> \<T> P - \<D> P\<close>
    \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t'\<close>
  then consider \<open>tF t\<close> \<open>tF t'\<close>
    | r r' u u' where \<open>t = u @ [\<checkmark>(r)]\<close> \<open>t' = u' @ [\<checkmark>(r')]\<close> \<open>tF u\<close> \<open>tF u'\<close>
      \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u'\<close>
    by (cases t rule: rev_cases; cases t' rule: rev_cases, simp_all)
      (metis append_T_imp_tF event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_disc_iff(1) neq_Nil_conv)
  thus \<open>t = t'\<close>
  proof cases
    show \<open>t = t'\<close> if \<open>tF t\<close> \<open>tF t'\<close>
      by (rule inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T_diff_D_tF
          [OF \<open>inj_on f \<^bold>\<alpha>(P)\<close>, THEN inj_onD, OF "$"(3)])
        (use "$"(1, 2) in \<open>simp_all add: \<open>tF t\<close> \<open>tF t'\<close>\<close>)
  next
    fix r r' u u' assume $$ : \<open>t = u @ [\<checkmark>(r)]\<close> \<open>t' = u' @ [\<checkmark>(r')]\<close> \<open>tF u\<close> \<open>tF u'\<close>
      \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u'\<close>
    from "$$"(1-4) "$"(1, 2) have \<open>u \<in> \<T> P\<close> \<open>u \<notin> \<D> P\<close> \<open>u' \<in> \<T> P\<close> \<open>u' \<notin> \<D> P\<close>
      by (auto intro: is_processT3_TR_append is_processT7)
    have \<open>u = u'\<close>
      by (rule inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T_diff_D_tF
          [OF \<open>inj_on f \<^bold>\<alpha>(P)\<close>, THEN inj_onD, OF "$$"(5)])
        (simp_all add: \<open>u \<in> \<T> P\<close> \<open>u \<notin> \<D> P\<close> \<open>u' \<in> \<T> P\<close> \<open>u' \<notin> \<D> P\<close> \<open>tF u\<close> \<open>tF u'\<close>)
    moreover from "$"(1-3) "$$"(1, 2) have \<open>r = r'\<close>
      by (auto intro: inj_onD[OF \<open>inj_on g \<^bold>\<checkmark>\<^bold>s(P)\<close>] strict_ticks_of_memI)
    ultimately show \<open>t = t'\<close> by (simp add: "$$")
  qed
qed



lemma add_Compl_minimal_events_of_Compl_strict_events_of_in_F :
  \<open>(t, X \<union> ev ` (- \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)) \<union> tick ` (- \<^bold>\<checkmark>\<^bold>s(P))) \<in> \<F> P\<close> if \<open>(t, X) \<in> \<F> P\<close>
for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  \<comment>\<open>very powerful result\<close>
proof (cases \<open>t \<in> \<D> P\<close>)
  show \<open>t \<in> \<D> P \<Longrightarrow> ?thesis\<close> by (fact is_processT8)
next
  assume \<open>t \<notin> \<D> P\<close>
  from \<open>(t, X) \<in> \<F> P\<close> have \<open>(t, X \<union> (ev ` (- \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)) \<union> tick ` (- \<^bold>\<checkmark>\<^bold>s(P)))) \<in> \<F> P\<close>
  proof (rule is_processT5, intro allI impI)
    fix e :: \<open>('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> assume \<open>e \<in> ev ` (- \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)) \<union> tick ` (- \<^bold>\<checkmark>\<^bold>s(P))\<close>
    then consider a where \<open>e = ev a\<close> \<open>a \<notin> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)\<close>
      | r where \<open>e = \<checkmark>(r)\<close> \<open>r \<notin> \<^bold>\<checkmark>\<^bold>s(P)\<close> by blast
    thus \<open>(t @ [e], {}) \<notin> \<F> P\<close>
    proof cases
      from \<open>t \<notin> \<D> P\<close> show \<open>e = ev a \<Longrightarrow> a \<notin> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<Longrightarrow> (t @ [e], {}) \<notin> \<F> P\<close> for a
        by (metis F_T Un_iff list.set_intros(1)
            min_elems3 minimal_events_of_memI set_append)
    next
      from \<open>t \<notin> \<D> P\<close> show \<open>e = \<checkmark>(r) \<Longrightarrow> r \<notin> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> (t @ [e], {}) \<notin> \<F> P\<close> for r
        by (meson F_T is_processT9 strict_ticks_of_memI)
    qed
  qed
  also have \<open>X \<union> (ev ` (- \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)) \<union> tick ` (- \<^bold>\<checkmark>\<^bold>s(P))) =
             X \<union> ev ` (- \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)) \<union> tick ` (- \<^bold>\<checkmark>\<^bold>s(P))\<close> by blast
  finally show ?thesis .
qed


lemma mem_D\<^sub>m\<^sub>i\<^sub>n_Un_T_Diff_D_imp_set_subset :
  \<open>set t \<subseteq> ev ` \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> tick ` \<^bold>\<checkmark>\<^bold>s(P)\<close> if \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<union> (\<T> P - \<D> P)\<close>
  \<comment>\<open>very powerful result\<close>
proof (rule subsetI)
  show \<open>e \<in> ev ` \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> tick ` \<^bold>\<checkmark>\<^bold>s(P)\<close> if \<open>e \<in> set t\<close> for e
  proof (cases e)
    from \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<union> (\<T> P - \<D> P)\<close> \<open>e \<in> set t\<close>
    show \<open>e = ev a \<Longrightarrow> e \<in> ev ` \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> tick ` \<^bold>\<checkmark>\<^bold>s(P)\<close> for a
      by (auto intro: minimal_events_of_memI)
  next
    fix r assume \<open>e = \<checkmark>(r)\<close>
    from \<open>e \<in> set t\<close> have \<open>t \<notin> \<D>\<^sub>m\<^sub>i\<^sub>n P\<close>
      by (auto dest: tF_mem_D\<^sub>m\<^sub>i\<^sub>n simp add: \<open>e = \<checkmark>(r)\<close> tickFree_def disjoint_iff)
    with \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<union> (\<T> P - \<D> P)\<close> have \<open>t \<in> \<T> P - \<D> P\<close> by simp
    with T_imp_ftF have \<open>ftF t\<close> by blast
    with \<open>e \<in> set t\<close> obtain t' where \<open>t = t' @ [\<checkmark>(r)]\<close>
      by (auto simp add: \<open>e = \<checkmark>(r)\<close> in_set_conv_decomp
          ftF_append_iff ftF_Cons_iff)
    with \<open>t \<in> \<T> P - \<D> P\<close> have \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close>
      by (auto intro: strict_ticks_of_memI)
    thus \<open>e \<in> ev ` \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> tick ` \<^bold>\<checkmark>\<^bold>s(P)\<close>
      by (simp add: \<open>e = \<checkmark>(r)\<close>)
  qed
qed


lemma inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_D\<^sub>m\<^sub>i\<^sub>n_Un_T_diff_D :
  \<open>inj_on (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) (\<D>\<^sub>m\<^sub>i\<^sub>n P \<union> (\<T> P - \<D> P))\<close>
  if \<open>inj_on f \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)\<close> and \<open>inj_on g \<^bold>\<checkmark>\<^bold>s(P)\<close>
proof (rule inj_onI, (drule mem_D\<^sub>m\<^sub>i\<^sub>n_Un_T_Diff_D_imp_set_subset)+)
  show \<open>\<lbrakk>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u;
         set t \<subseteq> ev ` \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> tick ` \<^bold>\<checkmark>\<^bold>s(P); set u \<subseteq> ev ` \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> tick ` \<^bold>\<checkmark>\<^bold>s(P)\<rbrakk>
        \<Longrightarrow> t = u\<close> for t u
    by (induct t arbitrary: u, simp_all)
      (safe, use that in \<open>auto dest: inj_onD\<close>)
qed



subsection \<open>Events of a Process\<close>

lemma events_of_BOT  [simp] : \<open>\<alpha>(\<bottom>) = UNIV\<close>
  and events_of_SKIP [simp] : \<open>\<alpha>(SKIP r) = {}\<close>
  and events_of_STOP [simp] : \<open>\<alpha>(STOP) = {}\<close>
  by (auto simp add: events_of_def T_BOT T_SKIP T_STOP)
    (meson ftF_single list.set_intros(1))

lemma anti_mono_events_of_T: \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> \<alpha>(Q) \<subseteq> \<alpha>(P)\<close>
  unfolding trace_refine_def events_of_def by blast

lemma anti_mono_events_of_F: \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> \<alpha>(Q) \<subseteq> \<alpha>(P)\<close>
  by (intro anti_mono_events_of_T leF_imp_leT)

lemma anti_mono_events_of_FD: \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> \<alpha>(Q) \<subseteq> \<alpha>(P)\<close>
  by (intro anti_mono_events_of_F leFD_imp_leF)

lemma anti_mono_events_of_DT: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> \<alpha>(Q) \<subseteq> \<alpha>(P)\<close>
  by (intro anti_mono_events_of_T leDT_imp_leT)

lemma anti_mono_events_of : \<open>P \<sqsubseteq> Q \<Longrightarrow> \<alpha>(Q) \<subseteq> \<alpha>(P)\<close>
  by (intro anti_mono_events_of_FD le_approx_imp_le_FD)



lemma events_of_GlobalNdet: \<open>\<alpha>(\<sqinter>a \<in> A. P a) = (\<Union>a\<in>A. \<alpha>(P a))\<close>
  by (simp add: events_of_def T_GlobalNdet)


lemma events_of_write0 : \<open>\<alpha>(a \<rightarrow> P) = insert a \<alpha>(P)\<close>
  by (fastforce simp add: events_of_def write0_def T_Mprefix)

lemma events_of_Mndetprefix: \<open>\<alpha>(\<sqinter>a\<in>A \<rightarrow> P a) = A \<union> (\<Union>a\<in>A. \<alpha>(P a))\<close>
  by (auto simp add: Mndetprefix_GlobalNdet events_of_GlobalNdet events_of_write0)

lemma events_of_Mprefix: \<open>\<alpha>(\<box>a\<in>A \<rightarrow> P a) = A \<union> (\<Union>a\<in>A. \<alpha>(P a))\<close>
  by (simp add: events_of_def write0_def T_Mprefix set_eq_iff)
    (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1) is_processT1_TR list.set_intros set_ConsD)


lemma events_of_read :
  \<open>\<alpha>(c\<^bold>?a\<in>A \<rightarrow> P a) = c ` A \<union> (\<Union>a\<in>c ` A. \<alpha>(P (inv_into A c a)))\<close>
  by (simp add: read_def events_of_Mprefix)

lemma events_of_inj_on_read :
  \<open>inj_on c A \<Longrightarrow> \<alpha>(c\<^bold>?a\<in>A \<rightarrow> P a) = c ` A \<union> (\<Union>a\<in>A. \<alpha>(P a))\<close>
  by (simp add: events_of_read)

lemma events_of_ndet_write :
  \<open>\<alpha>(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) = c ` A \<union> (\<Union>a\<in>c ` A. \<alpha>(P (inv_into A c a)))\<close>
  by (simp add: ndet_write_def events_of_Mndetprefix)

lemma events_of_inj_on_ndet_write :
  \<open>inj_on c A \<Longrightarrow> \<alpha>(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) = c ` A \<union> (\<Union>a\<in>A. \<alpha>(P a))\<close>
  by (simp add: events_of_ndet_write)

lemma events_of_write : \<open>\<alpha>(c\<^bold>!a \<rightarrow> P) = insert (c a) \<alpha>(P)\<close>
  by (simp add: write_def events_of_Mprefix)



lemma events_of_Ndet: \<open>\<alpha>(P \<sqinter> Q) = \<alpha>(P) \<union> \<alpha>(Q)\<close>
  unfolding events_of_def by (simp add: T_Ndet)

lemma events_of_Det: \<open>\<alpha>(P \<box> Q) = \<alpha>(P) \<union> \<alpha>(Q)\<close>
  unfolding events_of_def by (simp add: T_Det)

lemma events_of_Sliding: \<open>\<alpha>(P \<rhd> Q) = \<alpha>(P) \<union> \<alpha>(Q)\<close>
  unfolding Sliding_def by (simp add: events_of_Ndet events_of_Det)


lemma events_of_Renaming:
  \<open>\<alpha>(Renaming P f g) = (if \<D> P = {} then f ` \<alpha>(P) else UNIV)\<close>
proof (simp, intro conjI impI)
  show \<open>\<D> P \<noteq> {} \<Longrightarrow> \<alpha>(Renaming P f g) = UNIV\<close>
    by (simp add: events_of_is_strict_events_of_or_UNIV D_Renaming)
      (metis ftF_Nil nonempty_divE)
next
  show \<open>\<D> P = {} \<Longrightarrow> \<alpha>(Renaming P f g) = f ` \<alpha>(P)\<close>
    by (auto simp add: events_of_def T_Renaming image_UN image_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.case_eq_if)
      (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_disc_iff(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(9) is_ev_def,
        metis (mono_tags, lifting) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(9) image_iff list.set_map)
qed


lemma events_of_Seq : \<open>\<alpha>(P \<^bold>; Q) = \<alpha>(P) \<union> (if \<^bold>\<checkmark>\<^bold>s(P) = {} then {} else \<alpha>(Q))\<close> (is \<open>_ = ?A\<close>)
proof (intro subset_antisym subsetI)
  show \<open>a \<in> \<alpha>(P \<^bold>; Q) \<Longrightarrow> a \<in> ?A\<close> for a
  proof (elim events_of_memE, unfold T_Seq, elim UnE disjE conjE exE)
    show \<open>ev a \<in> set t \<Longrightarrow> t \<in> {t \<in> \<T> P. tF t} \<Longrightarrow> a \<in> ?A\<close> for t
      by (auto intro: events_of_memI)
  next
    show \<open>ev a \<in> set t \<Longrightarrow> t \<in> {t @ u |t u r. t @ [\<checkmark>(r)] \<in> \<T> P \<and> u \<in> \<T> Q} \<Longrightarrow> a \<in> ?A\<close> for t
      by simp (metis UNIV_I UnE UnI1 empty_iff events_of_is_strict_events_of_or_UNIV
          events_of_memI set_append strict_ticks_of_memI)
  next
    show \<open>ev a \<in> set t \<Longrightarrow> t \<in> \<D> P \<Longrightarrow> a \<in> ?A\<close> for t
      by simp (metis UNIV_I empty_iff events_of_is_strict_events_of_or_UNIV)
  qed
next
  show \<open>a \<in> ?A \<Longrightarrow> a \<in> \<alpha>(P \<^bold>; Q)\<close> for a
    by (elim UnE events_of_memE, simp_all add: events_of_def T_Seq split: if_split_asm)
      (metis T_not_tF_imp_decomp Un_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) is_processT1_TR set_ConsD set_append,
        metis Un_iff ex_in_conv set_append strict_ticks_of_memD)
qed



lemma events_of_Sync_subset : \<open>\<alpha>(P \<lbrakk>S\<rbrakk> Q) \<subseteq> \<alpha>(P) \<union> \<alpha>(Q)\<close>
  by (subst events_of_def, simp add: T_Sync subset_iff)
    (metis UNIV_I empty_iff events_of_is_strict_events_of_or_UNIV events_of_memI ftf_Sync1)


lemma events_of_Inter: \<open>\<alpha>((P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) ||| Q) = \<alpha>(P) \<union> \<alpha>(Q)\<close>
proof (rule subset_antisym[OF events_of_Sync_subset])
  have \<open>\<alpha>(P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<subseteq> \<alpha>(P ||| Q)\<close> for P Q
  proof (auto simp add: events_of_def T_Sync, goal_cases)
    case (1 e t_P)
    show ?case 
    proof (cases \<open>tF t_P\<close>)
      case True
      thus ?thesis 
        by (metis "1"(1) "1"(3) emptyLeftSelf insert_absorb insert_disjoint(2)
            is_processT1_TR setinterleaving_dual tickFree_def)
    next
      case False
      then obtain t_P' r where \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> \<open>tF t_P'\<close> \<open>t_P' \<in> \<T> P\<close>
        by (metis "1"(1) prefixI T_not_tF_imp_decomp
            append_T_imp_tF is_processT3_TR not_Cons_self)
      moreover have \<open>ev e \<in> set t_P'\<close>
        using "1"(3) calculation(1) by auto
      ultimately show ?thesis
        apply (rule_tac x = t_P' in exI, simp)
        apply (rule_tac x = t_P' in exI, simp)
        apply (rule_tac x = \<open>[]\<close> in exI, simp)
        by (metis disjoint_iff emptyLeftSelf setinterleaving_dual tickFree_def)
    qed
  qed
  thus \<open>\<alpha>(P) \<union> \<alpha>(Q) \<subseteq> \<alpha>(P ||| Q)\<close> by (metis Sync_commute Un_least)
qed



lemma events_of_Par_div    :
  \<open>\<D> P \<inter> \<T> Q \<union> \<D> Q \<inter> \<T> P \<noteq> {} \<Longrightarrow> \<alpha>(P || Q) = UNIV\<close>
  and events_of_Par_subset :
  \<open>\<D> P \<inter> \<T> Q \<union> \<D> Q \<inter> \<T> P = {} \<Longrightarrow> \<alpha>(P || Q) \<subseteq> \<alpha>(P) \<inter> \<alpha>(Q)\<close>
proof -
  assume \<open>\<D> P \<inter> \<T> Q \<union> \<D> Q \<inter> \<T> P \<noteq> {}\<close>
  hence \<open>\<D> (P || Q) \<noteq> {}\<close> by (simp add: D_Sync setinterleaving_UNIV_iff)
      (use ftF_Nil in blast)
  thus \<open>\<alpha>(P || Q) = UNIV\<close> by (simp add: events_of_is_strict_events_of_or_UNIV)
next
  show \<open>\<D> P \<inter> \<T> Q \<union> \<D> Q \<inter> \<T> P = {} \<Longrightarrow> \<alpha>(P || Q) \<subseteq> \<alpha>(P) \<inter> \<alpha>(Q)\<close>
    by (auto simp add: events_of_def T_Par)
qed


lemma events_of_Hiding:
  \<open>\<alpha>(P \ B) = (if \<D> (P \ B) = {} then \<alpha>(P) - B else UNIV)\<close>
proof (split if_split, intro conjI impI)
  show \<open>\<D> (P \ B) \<noteq> {} \<Longrightarrow> \<alpha>(P \ B) = UNIV\<close>
    by (simp add: events_of_is_strict_events_of_or_UNIV)
next
  show \<open>\<alpha>(P \ B) = \<alpha>(P) - B\<close> if \<open>\<D> (P \ B) = {}\<close>
  proof (intro subset_antisym subsetI)
    from \<open>\<D> (P \ B) = {}\<close> have \<open>div_hide P B = {}\<close> unfolding D_Hiding by blast
    fix a assume \<open>a \<in> \<alpha>(P \ B)\<close>
    then obtain t where \<open>ev a \<in> set (trace_hide t (ev ` B))\<close> \<open>(t, ev ` B) \<in> \<F> P\<close>
      by (elim events_of_memE, unfold T_Hiding \<open>div_hide P B = {}\<close>, blast)
    thus \<open>a \<in> \<alpha>(P) - B\<close>
      using F_T events_of_memI by fastforce
  next
    fix a assume \<open>a \<in> \<alpha>(P) - B\<close>
    then obtain t where \<open>ev a \<in> set t\<close> \<open>t \<in> \<T> P\<close> \<open>a \<notin> B\<close>
      by (metis DiffE events_of_memD)
    hence \<open>ev a \<in> set (trace_hide t (ev ` B))\<close> \<open>trace_hide t (ev ` B) \<in> \<T> (P \ B)\<close>
      by (auto intro: mem_T_imp_mem_T_Hiding)
    thus \<open>a \<in> events_of (P \ B)\<close> by (simp add: events_of_memI)
  qed
qed


subsection \<open>Strict Events of a Process\<close>

lemma strict_events_of_BOT  [simp] : \<open>\<^bold>\<alpha>(\<bottom>) = {}\<close>
  and strict_events_of_SKIP [simp] : \<open>\<^bold>\<alpha>(SKIP r) = {}\<close>
  and strict_events_of_STOP [simp] : \<open>\<^bold>\<alpha>(STOP) = {}\<close>
  by (auto simp add: strict_events_of_def T_BOT T_SKIP T_STOP D_BOT)


lemma strict_events_of_GlobalNdet_subset : \<open>\<^bold>\<alpha>(\<sqinter>a \<in> A. P a) \<subseteq> (\<Union>a\<in>A. \<^bold>\<alpha>(P a))\<close>
  by (auto simp add: strict_events_of_def GlobalNdet_projs)


lemma strict_events_of_Mprefix:
  \<open>\<^bold>\<alpha>(\<box>a\<in>A \<rightarrow> P a) = {a\<in>A. P a \<noteq> \<bottom>} \<union> (\<Union>a\<in>{a\<in>A. P a \<noteq> \<bottom>}. \<^bold>\<alpha>(P a))\<close>
proof -
  have \<open>(\<Union>a\<in>{a\<in>A. P a \<noteq> \<bottom>}. \<^bold>\<alpha>(P a)) = (\<Union>a\<in>A. \<^bold>\<alpha>(P a))\<close> by auto
  show \<open>\<^bold>\<alpha>(\<box>a\<in>A \<rightarrow> P a) = {a\<in>A. P a \<noteq> \<bottom>} \<union> (\<Union>a\<in>{a\<in>A. P a \<noteq> \<bottom>}. \<^bold>\<alpha>(P a))\<close>
  proof (unfold \<open>?this\<close>, safe)
    show \<open>a \<in> \<^bold>\<alpha>(\<box>a\<in>A \<rightarrow> P a) \<Longrightarrow> a \<notin> (\<Union>a\<in>A. \<^bold>\<alpha>(P a)) \<Longrightarrow> a \<in> A\<close> for a
      by (auto simp add: strict_events_of_def Mprefix_projs) blast
  next
    show \<open>a \<in> \<^bold>\<alpha>(\<box>a\<in>A \<rightarrow> P a) \<Longrightarrow> a \<notin> (\<Union>a\<in>A. \<^bold>\<alpha>(P a)) \<Longrightarrow> P a = \<bottom> \<Longrightarrow> False\<close> for a
      by (auto simp add: strict_events_of_def Mprefix_projs BOT_projs) blast
  next
    fix a assume \<open>a \<in> A\<close> \<open>P a \<noteq> \<bottom>\<close>
    hence * : \<open>\<exists>t\<in>insert [] {ev a # s |a s. a \<in> A \<and> s \<in> \<T> (P a)} -
                  {ev a # s |a s. a \<in> A \<and> s \<in> \<D> (P a)}. ev a \<in> set t\<close>
      by (intro bexI[where x = \<open>[ev a]\<close>]) (simp_all add: BOT_iff_Nil_D)
    show \<open>a \<in> \<^bold>\<alpha>(\<box>a\<in>A \<rightarrow> P a)\<close>
      by (auto simp add: strict_events_of_def Mprefix_projs intro: "*")
  next
    fix a b assume \<open>a \<in> A\<close> \<open>b \<in> \<^bold>\<alpha>(P a)\<close>
    then obtain t where \<open>t \<in> \<T> (P a)\<close> \<open>t \<notin> \<D> (P a)\<close> \<open>ev b \<in> set t\<close>
      by (meson strict_events_of_memE)
    hence * : \<open>\<exists>u\<in>insert [] {ev a # s |a s. a \<in> A \<and> s \<in> \<T> (P a)} -
                  {ev a # s |a s. a \<in> A \<and> s \<in> \<D> (P a)}. ev b \<in> set u\<close>
      by (intro bexI[where x = \<open>ev a # t\<close>]) (simp_all add: \<open>a \<in> A\<close>)
    show \<open>b \<in> \<^bold>\<alpha>(\<box>a\<in>A \<rightarrow> P a)\<close>
      by (auto simp add: strict_events_of_def Mprefix_projs intro: "*")
  qed
qed

lemma strict_events_of_Mndetprefix:
  \<open>\<^bold>\<alpha>(\<sqinter>a\<in>A \<rightarrow> P a) = {a\<in>A. P a \<noteq> \<bottom>} \<union> (\<Union>a\<in>{a\<in>A. P a \<noteq> \<bottom>}. \<^bold>\<alpha>(P a))\<close>
proof -
  have \<open>\<T> (\<sqinter>a\<in>A \<rightarrow> P a) = \<T> (\<box>a\<in>A \<rightarrow> P a)\<close> by (simp add: T_Mndetprefix' T_Mprefix)
  moreover have \<open>\<D> (\<sqinter>a\<in>A \<rightarrow> P a) = \<D> (\<box>a\<in>A \<rightarrow> P a)\<close> by (simp add: D_Mndetprefix' D_Mprefix)
  ultimately have \<open>\<^bold>\<alpha>(\<sqinter>a\<in>A \<rightarrow> P a) = \<^bold>\<alpha>(\<box>a\<in>A \<rightarrow> P a)\<close> by (simp add: strict_events_of_def)
  thus \<open>\<^bold>\<alpha>(\<sqinter>a\<in>A \<rightarrow> P a) = {a\<in>A. P a \<noteq> \<bottom>} \<union> (\<Union>a\<in>{a\<in>A. P a \<noteq> \<bottom>}. \<^bold>\<alpha>(P a))\<close>
    by (simp add: strict_events_of_Mprefix)
qed

lemma strict_events_of_write0 : \<open>\<^bold>\<alpha>(a \<rightarrow> P) = (if P = \<bottom> then {} else insert a \<^bold>\<alpha>(P))\<close>
  by (simp add: write0_def strict_events_of_Mprefix)

lemma strict_events_of_read :
  \<open>\<^bold>\<alpha>(c\<^bold>?a\<in>A \<rightarrow> P a) = {c a |a. a \<in> A \<and> P (inv_into A c (c a)) \<noteq> \<bottom>} \<union>
                      (\<Union>a\<in>{a \<in> A. P (inv_into A c (c a)) \<noteq> \<bottom>}. \<^bold>\<alpha>(P (inv_into A c (c a))))\<close>
  by (auto simp add: read_def strict_events_of_Mprefix)

lemma strict_events_of_inj_on_read :
  \<open>inj_on c A \<Longrightarrow> \<^bold>\<alpha>(c\<^bold>?a\<in>A \<rightarrow> P a) = {c a |a. a \<in> A \<and> P a \<noteq> \<bottom>} \<union>
                                    (\<Union>a\<in>{a \<in> A. P a \<noteq> \<bottom>}. \<^bold>\<alpha>(P a))\<close>
  by (auto simp add: strict_events_of_read)

lemma strict_events_of_ndet_write :
  \<open>\<^bold>\<alpha>(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) = {c a |a. a \<in> A \<and> P (inv_into A c (c a)) \<noteq> \<bottom>} \<union>
                       (\<Union>a\<in>{a \<in> A. P (inv_into A c (c a)) \<noteq> \<bottom>}. \<^bold>\<alpha>(P (inv_into A c (c a))))\<close>
  by (auto simp add: ndet_write_def strict_events_of_Mndetprefix)

lemma strict_events_of_inj_on_ndet_write :
  \<open>inj_on c A \<Longrightarrow> \<^bold>\<alpha>(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) = {c a |a. a \<in> A \<and> P a \<noteq> \<bottom>} \<union>
                                      (\<Union>a\<in>{a \<in> A. P a \<noteq> \<bottom>}. \<^bold>\<alpha>(P a))\<close>
  by (auto simp add: strict_events_of_ndet_write)

lemma strict_events_of_write : \<open>\<^bold>\<alpha>(c\<^bold>!a \<rightarrow> P) = (if P = \<bottom> then {} else insert (c a) \<^bold>\<alpha>(P))\<close>
  by (simp add: write_def strict_events_of_Mprefix)



lemma strict_events_of_Ndet_subset : \<open>\<^bold>\<alpha>(P \<sqinter> Q) \<subseteq> \<^bold>\<alpha>(P) \<union> \<^bold>\<alpha>(Q)\<close>
  unfolding strict_events_of_def by (auto simp add: Ndet_projs)

lemma strict_events_of_Det_subset : \<open>\<^bold>\<alpha>(P \<box> Q) \<subseteq> \<^bold>\<alpha>(P) \<union> \<^bold>\<alpha>(Q)\<close>
  unfolding strict_events_of_def by (auto simp add: Det_projs)

lemma strict_events_of_Sliding_subset : \<open>\<^bold>\<alpha>(P \<rhd> Q) \<subseteq> \<^bold>\<alpha>(P) \<union> \<^bold>\<alpha>(Q)\<close>
  unfolding strict_events_of_def by (auto simp add: Sliding_projs)


lemma strict_events_of_Renaming_subset : \<open>\<^bold>\<alpha>(Renaming P f g) \<subseteq> f ` \<^bold>\<alpha>(P)\<close>
proof (intro subsetI)
  show \<open>b \<in> \<^bold>\<alpha>(Renaming P f g) \<Longrightarrow> b \<in> f ` \<^bold>\<alpha>(P)\<close> for b
  proof (elim strict_events_of_memE)
    fix u assume \<open>u \<in> \<T> (Renaming P f g)\<close> \<open>u \<notin> \<D> (Renaming P f g)\<close> \<open>ev b \<in> set u\<close>
    then obtain u' where \<open>tF u'\<close> \<open>u' \<in> \<T> (Renaming P f g)\<close> \<open>u' \<notin> \<D> (Renaming P f g)\<close> \<open>ev b \<in> set u'\<close>
      by (cases u rule: rev_cases, simp_all)
        (metis prefixI \<open>ev b \<in> set u\<close> append_T_imp_tF event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) ftF_single
          is_processT3_TR is_processT7 not_Cons_self2 tF_Cons_iff tF_Nil tF_append_iff)
    from this(1-3) ftF_Nil tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff obtain t
      where \<open>u' = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t\<close> \<open>t \<in> \<T> P\<close> \<open>t \<notin> \<D> P\<close> unfolding Renaming_projs by blast
    from this(1) \<open>ev b \<in> set u'\<close> obtain a where \<open>b = f a\<close> \<open>ev a \<in> set t\<close>
      by (auto simp add: in_set_conv_decomp)
        (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_disc_iff(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_sel(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) is_ev_def)
    with \<open>t \<in> \<T> P\<close> \<open>t \<notin> \<D> P\<close> show \<open>b \<in> f ` \<^bold>\<alpha>(P)\<close> by (auto intro: strict_events_of_memI)
  qed
qed


lemma strict_events_of_inj_on_Renaming :
  \<open>\<^bold>\<alpha>(Renaming P f g) = f ` \<^bold>\<alpha>(P)\<close> if \<open>inj_on f \<alpha>(P)\<close>
proof (rule subset_antisym)
  show \<open>\<^bold>\<alpha>(Renaming P f g) \<subseteq> f ` \<^bold>\<alpha>(P)\<close> by (fact strict_events_of_Renaming_subset)
next
  show \<open>f ` \<^bold>\<alpha>(P) \<subseteq> \<^bold>\<alpha>(Renaming P f g)\<close>
  proof (rule subsetI, elim imageE strict_events_of_memE)
    fix b a t assume \<open>b = f a\<close> \<open>t \<in> \<T> P\<close> \<open>t \<notin> \<D> P\<close> \<open>ev a \<in> set t\<close>
    from \<open>t \<in> \<T> P\<close> \<open>t \<notin> \<D> P\<close> \<open>ev a \<in> set t\<close> obtain t'
      where \<open>tF t'\<close> \<open>t' \<in> \<T> P\<close> \<open>t' \<notin> \<D> P\<close> \<open>ev a \<in> set t'\<close>
      by (cases t rule: rev_cases, simp_all)
        (metis prefixI \<open>ev a \<in> set t\<close> append_T_imp_tF event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) ftF_single
          is_processT3_TR is_processT7 not_Cons_self2 tF_Cons_iff tF_Nil tF_append_iff)
    from \<open>t' \<in> \<T> P\<close> have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t' \<in> \<T> (Renaming P f g)\<close>
      by (auto simp add: T_Renaming)
    have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t' \<notin> \<D> (Renaming P f g)\<close>
    proof (rule ccontr)
      assume \<open>\<not> map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t' \<notin> \<D> (Renaming P f g)\<close>
      then obtain u1 u2 where * : \<open>ftF u2\<close> \<open>tF u1\<close> \<open>u1 \<in> \<D> P\<close>
        \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t' = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ u2\<close>
        unfolding D_Renaming by blast
      from this(4) obtain t1 t2
        where ** : \<open>t' = t1 @ t2\<close> \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t2 = u2\<close>
          \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1\<close>
        by (metis (no_types) append_eq_map_conv)
      from "**"(1) \<open>t' \<in> \<T> P\<close> \<open>tF t'\<close> is_processT3_TR_append tF_append_iff
      have \<open>t1 \<in> {t \<in> \<T> P. tF t}\<close> by auto
      moreover have \<open>u1 \<in> {t \<in> \<T> P. tF t}\<close> by (simp add: D_T \<open>tF u1\<close> \<open>u1 \<in> \<D> P\<close>)
      ultimately have \<open>t1 = u1\<close> by (intro inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T_tF
            [THEN inj_onD, OF \<open>inj_on f \<alpha>(P)\<close> "**"(3)])
      with "*"(1-3) "**"(1, 2) \<open>t' \<notin> \<D> P\<close> is_processT7
        ftF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff show False by blast
    qed
    moreover from \<open>ev a \<in> set t'\<close> \<open>b = f a\<close> have \<open>ev b \<in> set (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t')\<close> by force
    ultimately show \<open>b \<in> \<^bold>\<alpha>(Renaming P f g)\<close>
      using \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t' \<in> \<T> (Renaming P f g)\<close> by (auto intro: strict_events_of_memI)
  qed
qed



lemma strict_events_of_Seq_subset :
  \<open>\<^bold>\<alpha>(P \<^bold>; Q) \<subseteq> \<^bold>\<alpha>(P) \<union> (if \<^bold>\<checkmark>\<^bold>s(P) = {} then {} else \<^bold>\<alpha>(Q))\<close>
  by (rule subsetI, elim strict_events_of_memE, simp add: Seq_projs)
    (metis T_imp_ftF Un_iff append_T_imp_tF empty_iff is_processT7
      is_processT9 not_Cons_self2 set_append strict_events_of_memI strict_ticks_of_memI)


lemma strict_events_of_Sync_subset : \<open>\<^bold>\<alpha>(P \<lbrakk>S\<rbrakk> Q) \<subseteq> \<^bold>\<alpha>(P) \<union> \<^bold>\<alpha>(Q)\<close>
  by (subst strict_events_of_def, auto simp add: Sync_projs subset_iff)
    (metis (full_types) append_Nil2 ftF_Nil ftf_Sync1
      setinterleaving_dual strict_events_of_memI)





subsection \<open>Minimal Events of a Process\<close>

lemma minimal_events_of_BOT   [simp] : \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(\<bottom>) = {}\<close>
  and minimal_events_of_STOP  [simp] : \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(STOP) = {}\<close>
  and minimal_events_of_SKIP  [simp] : \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(SKIP r) = {}\<close>
  by (auto simp add: minimal_events_of_def D\<^sub>m\<^sub>i\<^sub>n_BOT D\<^sub>m\<^sub>i\<^sub>n_SKIP D\<^sub>m\<^sub>i\<^sub>n_STOP)


lemma minimal_events_of_Mprefix:
  \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(\<box>a\<in>A \<rightarrow> P a) = A \<union> (\<Union>a\<in>A. \<alpha>\<^sub>m\<^sub>i\<^sub>n(P a))\<close>
  by (simp add: set_eq_iff minimal_events_of_def strict_events_of_Mprefix D\<^sub>m\<^sub>i\<^sub>n_Mprefix)
    (use D\<^sub>m\<^sub>i\<^sub>n_BOT in fastforce)

lemma minimal_events_of_Mndetprefix:
  \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(\<sqinter>a\<in>A \<rightarrow> P a) = A \<union> (\<Union>a\<in>A. \<alpha>\<^sub>m\<^sub>i\<^sub>n(P a))\<close>
  by (simp add: set_eq_iff minimal_events_of_def strict_events_of_Mndetprefix D\<^sub>m\<^sub>i\<^sub>n_Mndetprefix)
    (use D\<^sub>m\<^sub>i\<^sub>n_BOT in fastforce)


corollary minimal_events_of_write0 : \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(a \<rightarrow> P) = insert a \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)\<close>
  by (simp add: write0_def minimal_events_of_Mprefix)

corollary minimal_events_of_write : \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(c\<^bold>!a \<rightarrow> P) = insert (c a) \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)\<close>
  by (simp add: write_def minimal_events_of_Mprefix)

corollary minimal_events_of_read :
  \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(c\<^bold>?a\<in>A \<rightarrow> P a) = c ` A \<union> (\<Union>a\<in>A. \<alpha>\<^sub>m\<^sub>i\<^sub>n(P (inv_into A c (c a))))\<close>
  by (auto simp add: read_def minimal_events_of_Mprefix)

corollary minimal_events_of_ndet_write :
  \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) = c ` A \<union> (\<Union>a\<in>A. \<alpha>\<^sub>m\<^sub>i\<^sub>n(P (inv_into A c (c a))))\<close>
  by (auto simp add: ndet_write_def minimal_events_of_Mndetprefix)


lemma minimal_events_of_GlobalNdet_subset : \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(\<sqinter>a \<in> A. P a) \<subseteq> (\<Union>a\<in>A. \<alpha>\<^sub>m\<^sub>i\<^sub>n(P a))\<close>
  by (auto simp add: minimal_events_of_def
      dest!: strict_events_of_GlobalNdet_subset[THEN set_mp] D\<^sub>m\<^sub>i\<^sub>n_GlobalNdet_subset[THEN set_mp])


lemma minimal_events_of_Ndet_subset : \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P \<sqinter> Q) \<subseteq> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)\<close>
  by (auto simp add: minimal_events_of_def
      dest!: strict_events_of_Ndet_subset[THEN set_mp] D\<^sub>m\<^sub>i\<^sub>n_Ndet_subset[THEN set_mp])

lemma minimal_events_of_Det_subset : \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P \<box> Q) \<subseteq> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)\<close>
  by (auto simp add: minimal_events_of_def
      dest!: strict_events_of_Det_subset[THEN set_mp] D\<^sub>m\<^sub>i\<^sub>n_Det_subset[THEN set_mp])

lemma minimal_events_of_Sliding_subset : \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P \<rhd> Q) \<subseteq> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)\<close>
  by (auto simp add: minimal_events_of_def
      dest!: strict_events_of_Sliding_subset[THEN set_mp] D\<^sub>m\<^sub>i\<^sub>n_Sliding_subset[THEN set_mp])


lemma minimal_events_of_Renaming_subset : \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(Renaming P f g) \<subseteq> f ` \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)\<close>
  by (auto simp add: minimal_events_of_def append_eq_map_conv ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff image_iff
      dest!: strict_events_of_Renaming_subset[THEN set_mp] D\<^sub>m\<^sub>i\<^sub>n_Renaming_subset[THEN set_mp]) blast
    (* TODO: make an injective version ? *)


lemma minimal_events_of_Seq_subset :
  \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P \<^bold>; Q) \<subseteq> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> (\<Union>r\<in>\<^bold>\<checkmark>\<^bold>s(P). \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q))\<close>
  oops (* proven in HOL-CSP_PTick *)

lemma minimal_events_of_Sync_subset :
  \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P \<lbrakk>S\<rbrakk> Q) \<subseteq> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)\<close>
  oops (* proven in HOL-CSP_PTick *)


lemma minimal_events_of_Hiding_subset : \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P \ A) \<subseteq> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) - A\<close>
proof (rule subsetI)
  show \<open>a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P \ A) \<Longrightarrow> a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) - A\<close> for a
  proof (elim minimal_events_of_memE)
    fix t assume * : \<open>t \<in> \<T> (P \ A)\<close> \<open>t \<notin> \<D> (P \ A)\<close> \<open>ev a \<in> set t\<close>
    from "*"(1, 2) obtain u where ** : \<open>t = trace_hide u (ev ` A)\<close> \<open>(u, ev ` A) \<in> \<F> P\<close>
      unfolding T_Hiding D_Hiding by blast
    from "*"(2) "**"(1) have \<open>u \<notin> \<D> P\<close> by (metis mem_D_imp_mem_D_Hiding)
    with "*"(3) "**" show \<open>a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) - A\<close>
      by (auto intro: minimal_events_of_memI(1) dest: F_T)
  next
    fix t assume * : \<open>tF t\<close> \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (P \ A)\<close> \<open>ev a \<in> set t\<close>
    from "*"(2) obtain u x
      where ** : \<open>tF u\<close> \<open>t = trace_hide u (ev ` A)\<close>
        \<open>u \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<or> isInfHidden_seqRun_strong x P A u\<close>
      by (blast dest: D\<^sub>m\<^sub>i\<^sub>n_Hiding_subset[THEN set_mp])
    from "**"(3) show \<open>a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) - A\<close>
    proof (elim disjE)
      from "*"(3) "**"(2) show \<open>u \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<Longrightarrow> a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) - A\<close>
        by (auto intro: minimal_events_of_memI(2))
    next
      assume \<open>isInfHidden_seqRun_strong x P A u\<close>
      from this[THEN spec, of 0] "*"(3) "**"(2)
      show \<open>a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) - A\<close> by (auto intro: minimal_events_of_memI(1))
    qed
  qed
qed




section \<open>Ticks of a Process\<close>

lemma ticks_of_BOT  [simp] : \<open>\<checkmark>s(\<bottom>) = UNIV\<close>
  and ticks_of_SKIP [simp] : \<open>\<checkmark>s(SKIP r) = {r}\<close>
  and ticks_of_STOP [simp] : \<open>\<checkmark>s(STOP) = {}\<close>
  by (simp_all add: set_eq_iff ticks_of_def T_BOT T_SKIP T_STOP)
    (metis append_Nil ftF_single)

lemma anti_mono_ticks_of_T: \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> \<checkmark>s(Q) \<subseteq> \<checkmark>s(P)\<close>
  unfolding trace_refine_def ticks_of_def by blast

lemma anti_mono_ticks_of_F: \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> \<checkmark>s(Q) \<subseteq> \<checkmark>s(P)\<close>
  by (intro anti_mono_ticks_of_T leF_imp_leT)

lemma anti_mono_ticks_of_FD: \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> \<checkmark>s(Q) \<subseteq> \<checkmark>s(P)\<close>
  by (intro anti_mono_ticks_of_F leFD_imp_leF)

lemma anti_mono_ticks_of_DT: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> \<checkmark>s(Q) \<subseteq> \<checkmark>s(P)\<close>
  by (intro anti_mono_ticks_of_T leDT_imp_leT)

lemma anti_mono_ticks_of : \<open>P \<sqsubseteq> Q \<Longrightarrow> \<checkmark>s(Q) \<subseteq> \<checkmark>s(P)\<close>
  by (intro anti_mono_ticks_of_FD le_approx_imp_le_FD)



lemma ticks_of_GlobalNdet: \<open>\<checkmark>s(\<sqinter>a \<in> A. P a) = (\<Union>a\<in>A. \<checkmark>s(P a))\<close>
  by (auto simp add: ticks_of_def T_GlobalNdet)


lemma ticks_of_Mprefix: \<open>\<checkmark>s(\<box>a\<in>A \<rightarrow> P a) = (\<Union>a\<in>A. \<checkmark>s(P a))\<close>
  by (auto simp add: set_eq_iff ticks_of_def T_Mprefix)
    (metis append_butlast_last_id event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) last.simps last_snoc, meson append_Cons)

lemma ticks_of_write0 : \<open>\<checkmark>s(a \<rightarrow> P) = \<checkmark>s(P)\<close>
  by (simp add: write0_def ticks_of_Mprefix)

lemma ticks_of_Mndetprefix: \<open>\<checkmark>s(\<sqinter>a\<in>A \<rightarrow> P a) = (\<Union>a\<in>A. \<checkmark>s(P a))\<close>
  by (simp add: Mndetprefix_GlobalNdet ticks_of_GlobalNdet ticks_of_write0)



lemma ticks_of_read :
  \<open>\<checkmark>s(c\<^bold>?a\<in>A \<rightarrow> P a) = (\<Union>a\<in>c ` A. \<checkmark>s(P (inv_into A c a)))\<close>
  by (simp add: read_def ticks_of_Mprefix)

lemma ticks_of_inj_on_read :
  \<open>inj_on c A \<Longrightarrow> \<checkmark>s(c\<^bold>?a\<in>A \<rightarrow> P a) = (\<Union>a\<in>A. \<checkmark>s(P a))\<close>
  by (simp add: ticks_of_read)

lemma ticks_of_ndet_write :
  \<open>\<checkmark>s(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) = (\<Union>a\<in>c ` A. \<checkmark>s(P (inv_into A c a)))\<close>
  by (simp add: ndet_write_def ticks_of_Mndetprefix)

lemma ticks_of_inj_on_ndet_write :
  \<open>inj_on c A \<Longrightarrow> \<checkmark>s(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) = (\<Union>a\<in>A. \<checkmark>s(P a))\<close>
  by (simp add: ticks_of_ndet_write)

lemma ticks_of_write : \<open>\<checkmark>s(c\<^bold>!a \<rightarrow> P) = \<checkmark>s(P)\<close>
  by (simp add: write_def ticks_of_Mprefix)



lemma ticks_of_Ndet: \<open>\<checkmark>s(P \<sqinter> Q) = \<checkmark>s(P) \<union> \<checkmark>s(Q)\<close>
  by (auto simp add: ticks_of_def T_Ndet)

lemma ticks_of_Det: \<open>\<checkmark>s(P \<box> Q) = \<checkmark>s(P) \<union> \<checkmark>s(Q)\<close>
  by (auto simp add: ticks_of_def T_Det)

lemma ticks_of_Sliding: \<open>\<checkmark>s(P \<rhd> Q) = \<checkmark>s(P) \<union> \<checkmark>s(Q)\<close>
  by (auto simp add: ticks_of_def T_Sliding)


lemma ticks_of_Renaming:
  \<open>\<checkmark>s(Renaming P f g) = (if \<D> P = {} then g ` \<checkmark>s(P) else UNIV)\<close>
proof (simp, intro conjI impI)
  show \<open>\<D> P \<noteq> {} \<Longrightarrow> \<checkmark>s(Renaming P f g) = UNIV\<close>
    by (simp add: ticks_of_is_strict_ticks_of_or_UNIV D_Renaming)
      (meson ftF_Nil nonempty_divE)
next
  show \<open>\<checkmark>s(Renaming P f g) = g ` \<checkmark>s(P)\<close> if \<open>\<D> P = {}\<close>
  proof (intro subset_antisym subsetI)
    show \<open>r \<in> \<checkmark>s(Renaming P f g) \<Longrightarrow> r \<in> g ` \<checkmark>s(P)\<close> for r
      by (auto simp add: T_Renaming \<open>\<D> P = {}\<close> append_eq_map_conv tick_eq_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff
          intro!: ticks_of_memI elim!: ticks_of_memE)
  next
    show \<open>r \<in> g ` \<checkmark>s(P) \<Longrightarrow> r \<in> \<checkmark>s(Renaming P f g)\<close> for r
      by (simp add: ticks_of_def T_Renaming \<open>\<D> P = {}\<close>
          append_eq_map_conv tick_eq_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff) blast
  qed
qed


lemma ticks_of_Seq :
  \<open>\<checkmark>s(P \<^bold>; Q) = (if \<D> P = {} then if \<checkmark>s(P) = {} then {} else \<checkmark>s(Q) else UNIV)\<close> (is \<open>?lhs = ?rhs\<close>)
proof (intro subset_antisym subsetI)
  show \<open>a \<in> ?lhs \<Longrightarrow> a \<in> ?rhs\<close> for a
    by (elim ticks_of_memE, auto simp add: T_Seq ticks_of_def)
      (metis T_not_tF_imp_decomp append_T_imp_tF event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2)
        last_appendR last_snoc tF_Cons_iff tF_Nil tF_append_iff)
next
  show \<open>a \<in> ?rhs \<Longrightarrow> a \<in> ?lhs\<close> for a
    by (auto simp add: ticks_of_def T_Seq split: if_split_asm)
      (meson append_assoc, metis all_not_in_conv ftF_single is_processT7 nonempty_divE)
qed


lemma ticks_of_Sync_subset : \<open>\<checkmark>s(P \<lbrakk>S\<rbrakk> Q) \<subseteq> \<checkmark>s(P) \<union> \<checkmark>s(Q)\<close>
  by (auto simp add: T_Sync elim!: ticks_of_memE)
    (metis SyncWithTick_imp_NTF T_imp_ftF ticks_of_memI,
      (metis UNIV_I empty_iff ticks_of_is_strict_ticks_of_or_UNIV)+)

lemma ticks_of_no_div_Sync_subset :
  \<open>\<checkmark>s(P \<lbrakk>S\<rbrakk> Q) \<subseteq> \<checkmark>s(P) \<inter> \<checkmark>s(Q)\<close> if \<open>\<D> (P \<lbrakk>S\<rbrakk> Q) = {}\<close>
proof (rule subsetI)
  fix r assume \<open>r \<in> \<checkmark>s(P \<lbrakk>S\<rbrakk> Q)\<close>
  with \<open>\<D> (P \<lbrakk>S\<rbrakk> Q) = {}\<close> obtain t t_P t_Q
    where * : \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close>
      \<open>(t @ [\<checkmark>(r)]) setinterleaves ((t_P, t_Q), range tick \<union> ev ` S)\<close>
    by (elim ticks_of_memE, unfold Sync_projs, blast)
  from SyncWithTick_imp_NTF[OF "*"(3) "*"(1, 2)[THEN is_processT2_TR]]
  obtain t_P' t_Q' where \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q' @ [\<checkmark>(r)]\<close> by blast
  with "*"(1, 2) show \<open>r \<in> \<checkmark>s(P) \<inter> \<checkmark>s(Q)\<close> by (auto intro: ticks_of_memI)
qed

lemma ticks_of_Par_div :
  \<open>\<D> P \<inter> \<T> Q \<union> \<D> Q \<inter> \<T> P \<noteq> {} \<Longrightarrow> \<checkmark>s(P || Q) = UNIV\<close>
  and ticks_of_no_div_Par_subset :
  \<open>\<D> P \<inter> \<T> Q \<union> \<D> Q \<inter> \<T> P = {} \<Longrightarrow> \<checkmark>s(P || Q) \<subseteq> \<checkmark>s(P) \<inter> \<checkmark>s(Q)\<close>
proof -
  assume \<open>\<D> P \<inter> \<T> Q \<union> \<D> Q \<inter> \<T> P \<noteq> {}\<close>
  hence \<open>\<D> (P || Q) \<noteq> {}\<close> by (simp add: D_Sync setinterleaving_UNIV_iff)
      (use ftF_Nil in blast)
  thus \<open>\<checkmark>s(P || Q) = UNIV\<close> by (simp add: ticks_of_is_strict_ticks_of_or_UNIV)
next
  show \<open>\<D> P \<inter> \<T> Q \<union> \<D> Q \<inter> \<T> P = {} \<Longrightarrow> \<checkmark>s(P || Q) \<subseteq> \<checkmark>s(P) \<inter> \<checkmark>s(Q)\<close>
    by (rule ticks_of_no_div_Sync_subset) (auto simp add: D_Par)
qed





lemma ticks_of_Hiding:
  \<open>\<checkmark>s(P \ B) = (if \<D> (P \ B) = {} then \<checkmark>s(P) else UNIV)\<close>
proof (split if_split, intro conjI impI)
  show \<open>\<D> (P \ B) \<noteq> {} \<Longrightarrow> \<checkmark>s(P \ B) = UNIV\<close>
    by (simp add: ticks_of_is_strict_ticks_of_or_UNIV)
next
  show \<open>\<checkmark>s(P \ B) = \<checkmark>s(P)\<close> if \<open>\<D> (P \ B) = {}\<close>
  proof (intro subset_antisym subsetI)
    fix r assume \<open>r \<in> \<checkmark>s(P \ B)\<close>
    then obtain u where \<open>u @ [\<checkmark>(r)] \<in> \<T> (P \ B)\<close> by (meson ticks_of_memE)
    with \<open>\<D> (P \ B) = {}\<close> obtain t
      where \<open>u @ [\<checkmark>(r)] = trace_hide t (ev ` B)\<close> \<open>(t, ev ` B) \<in> \<F> P\<close>
      unfolding T_Hiding D_Hiding by blast
    then obtain t' where \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close>
      by (cases t rule: rev_cases, auto split: if_split_asm intro: F_T)
        (metis F_T Hiding_tF append_T_imp_tF event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2)
          not_Cons_self2 tF_Cons_iff tF_append_iff)
    thus \<open>r \<in> \<checkmark>s(P)\<close> by (simp add: ticks_of_memI)
  next
    fix r assume \<open>r \<in> \<checkmark>s(P)\<close>
    then obtain t where \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close> by (metis ticks_of_memD)
    hence \<open>trace_hide (t @ [\<checkmark>(r)]) (ev ` B) \<in> \<T> (P \ B)\<close>
      by (fact mem_T_imp_mem_T_Hiding)
    thus \<open>r \<in> \<checkmark>s(P \ B)\<close> by (auto intro: ticks_of_memI split: if_split_asm)
  qed
qed



lemma tF_traces_iff_empty_ticks_of : \<open>(\<forall>t \<in> \<T> P. tF t) \<longleftrightarrow> \<checkmark>s(P) = {}\<close>
  using T_not_tF_imp_decomp unfolding ticks_of_def by auto



subsection \<open>Strict Events of a Process\<close>

lemma strict_ticks_of_BOT  [simp] : \<open>\<^bold>\<checkmark>\<^bold>s(\<bottom>) = {}\<close>
  and strict_ticks_of_SKIP [simp] : \<open>\<^bold>\<checkmark>\<^bold>s(SKIP r) = {r}\<close>
  and strict_ticks_of_STOP [simp] : \<open>\<^bold>\<checkmark>\<^bold>s(STOP) = {}\<close>
  by (auto simp add: strict_ticks_of_def BOT_projs SKIP_projs T_STOP)


lemma strict_ticks_of_GlobalNdet_subset : \<open>\<^bold>\<checkmark>\<^bold>s(\<sqinter>a \<in> A. P a) \<subseteq> (\<Union>a\<in>A. \<^bold>\<checkmark>\<^bold>s(P a))\<close>
  by (auto simp add: strict_ticks_of_def GlobalNdet_projs)


lemma strict_ticks_of_Mprefix:
  \<open>\<^bold>\<checkmark>\<^bold>s(\<box>a\<in>A \<rightarrow> P a) = (\<Union>a\<in>{a\<in>A. P a \<noteq> \<bottom>}. \<^bold>\<checkmark>\<^bold>s(P a))\<close>
proof -
  have \<open>(\<Union>a\<in>{a\<in>A. P a \<noteq> \<bottom>}. \<^bold>\<checkmark>\<^bold>s(P a)) = (\<Union>a\<in>A. \<^bold>\<checkmark>\<^bold>s(P a))\<close>
    by (auto intro: strict_ticks_of_memI is_processT9 elim!: strict_ticks_of_memE)
      (metis D_BOT T_BOT is_processT9 strict_ticks_of_memI)
  show \<open>\<^bold>\<checkmark>\<^bold>s(\<box>a\<in>A \<rightarrow> P a) = (\<Union>a\<in>{a\<in>A. P a \<noteq> \<bottom>}. \<^bold>\<checkmark>\<^bold>s(P a))\<close>
  proof (unfold \<open>?this\<close>, safe elim!: strict_ticks_of_memE)
    show \<open>t @ [\<checkmark>(r)] \<in> \<T> (\<box>a\<in>A \<rightarrow> P a) \<Longrightarrow> t \<notin> \<D> (\<box>a\<in>A \<rightarrow> P a)
          \<Longrightarrow> r \<in> (\<Union>a\<in>A. \<^bold>\<checkmark>\<^bold>s(P a))\<close> for t r
      by (auto simp add: strict_ticks_of_def Mprefix_projs)
        (metis append_butlast_last_id butlast.simps(2) butlast_snoc
          event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) is_processT9 last.simps last_snoc)
  next
    fix a t r assume \<open>a \<in> A\<close> \<open>t @ [\<checkmark>(r)] \<in> \<T> (P a)\<close> \<open>t \<notin> \<D> (P a)\<close>
    hence \<open>(ev a # t) @ [\<checkmark>(r)] \<in> \<T> (\<box>a\<in>A \<rightarrow> P a)\<close>
      \<open>(ev a # t) \<notin> \<D> (\<box>a\<in>A \<rightarrow> P a)\<close>
      by (auto simp add: strict_ticks_of_def Mprefix_projs)
    thus \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(\<box>a\<in>A \<rightarrow> P a)\<close> by (meson strict_ticks_of_memI is_processT9)
  qed
qed

lemma strict_ticks_of_Mndetprefix:
  \<open>\<^bold>\<checkmark>\<^bold>s(\<sqinter>a\<in>A \<rightarrow> P a) = (\<Union>a\<in>{a\<in>A. P a \<noteq> \<bottom>}. \<^bold>\<checkmark>\<^bold>s(P a))\<close>
proof -
  have \<open>\<T> (\<sqinter>a\<in>A \<rightarrow> P a) = \<T> (\<box>a\<in>A \<rightarrow> P a)\<close> by (simp add: T_Mndetprefix' T_Mprefix)
  moreover have \<open>\<D> (\<sqinter>a\<in>A \<rightarrow> P a) = \<D> (\<box>a\<in>A \<rightarrow> P a)\<close> by (simp add: D_Mndetprefix' D_Mprefix)
  ultimately have \<open>\<^bold>\<checkmark>\<^bold>s(\<sqinter>a\<in>A \<rightarrow> P a) = \<^bold>\<checkmark>\<^bold>s(\<box>a\<in>A \<rightarrow> P a)\<close> by (simp add: strict_ticks_of_def)
  thus \<open>\<^bold>\<checkmark>\<^bold>s(\<sqinter>a\<in>A \<rightarrow> P a) = (\<Union>a\<in>{a\<in>A. P a \<noteq> \<bottom>}. \<^bold>\<checkmark>\<^bold>s(P a))\<close> by (simp add: strict_ticks_of_Mprefix)
qed

lemma strict_ticks_of_write0 : \<open>\<^bold>\<checkmark>\<^bold>s(a \<rightarrow> P) = (if P = \<bottom> then {} else \<^bold>\<checkmark>\<^bold>s(P))\<close>
  by (simp add: write0_def strict_ticks_of_Mprefix)

lemma strict_ticks_of_read :
  \<open>\<^bold>\<checkmark>\<^bold>s(c\<^bold>?a\<in>A \<rightarrow> P a) = (\<Union>a\<in>{a \<in> A. P (inv_into A c (c a)) \<noteq> \<bottom>}. \<^bold>\<checkmark>\<^bold>s(P (inv_into A c (c a))))\<close>
  by (auto simp add: read_def strict_ticks_of_Mprefix)

lemma strict_ticks_of_inj_on_read :
  \<open>inj_on c A \<Longrightarrow> \<^bold>\<checkmark>\<^bold>s(c\<^bold>?a\<in>A \<rightarrow> P a) = (\<Union>a\<in>{a \<in> A. P a \<noteq> \<bottom>}. \<^bold>\<checkmark>\<^bold>s(P a))\<close>
  by (auto simp add: strict_ticks_of_read)

lemma strict_ticks_of_ndet_write :
  \<open>\<^bold>\<checkmark>\<^bold>s(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) = (\<Union>a\<in>{a \<in> A. P (inv_into A c (c a)) \<noteq> \<bottom>}. \<^bold>\<checkmark>\<^bold>s(P (inv_into A c (c a))))\<close>
  by (auto simp add: ndet_write_def strict_ticks_of_Mndetprefix)

lemma strict_ticks_of_inj_on_ndet_write :
  \<open>inj_on c A \<Longrightarrow> \<^bold>\<checkmark>\<^bold>s(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) = (\<Union>a\<in>{a \<in> A. P a \<noteq> \<bottom>}. \<^bold>\<checkmark>\<^bold>s(P a))\<close>
  by (auto simp add: strict_ticks_of_ndet_write)

lemma strict_ticks_of_write : \<open>\<^bold>\<checkmark>\<^bold>s(c\<^bold>!a \<rightarrow> P) = (if P = \<bottom> then {} else \<^bold>\<checkmark>\<^bold>s(P))\<close>
  unfolding write_def by (simp add: strict_ticks_of_Mprefix)



lemma strict_ticks_of_Ndet_subset : \<open>\<^bold>\<checkmark>\<^bold>s(P \<sqinter> Q) \<subseteq> \<^bold>\<checkmark>\<^bold>s(P) \<union> \<^bold>\<checkmark>\<^bold>s(Q)\<close>
  unfolding strict_ticks_of_def by (auto simp add: Ndet_projs)

lemma strict_ticks_of_Det_subset : \<open>\<^bold>\<checkmark>\<^bold>s(P \<box> Q) \<subseteq> \<^bold>\<checkmark>\<^bold>s(P) \<union> \<^bold>\<checkmark>\<^bold>s(Q)\<close>
  unfolding strict_ticks_of_def by (auto simp add: Det_projs)

lemma strict_ticks_of_Sliding_subset : \<open>\<^bold>\<checkmark>\<^bold>s(P \<rhd> Q) \<subseteq> \<^bold>\<checkmark>\<^bold>s(P) \<union> \<^bold>\<checkmark>\<^bold>s(Q)\<close>
  unfolding strict_ticks_of_def by (auto simp add: Sliding_projs)


lemma strict_ticks_of_Renaming_subset : \<open>\<^bold>\<checkmark>\<^bold>s(Renaming P f g) \<subseteq> g ` \<^bold>\<checkmark>\<^bold>s(P)\<close>
proof (intro subsetI)
  fix s assume \<open>s \<in> \<^bold>\<checkmark>\<^bold>s(Renaming P f g)\<close>
  then obtain u where \<open>u @ [\<checkmark>(s)] \<in> \<T> (Renaming P f g)\<close>
    \<open>u \<notin> \<D> (Renaming P f g)\<close> by (meson strict_ticks_of_memD)
  then obtain t r where \<open>s = g r\<close> \<open>u = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t\<close> \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>t \<notin> \<D> P\<close>
    by (auto simp add: Renaming_projs append_eq_map_conv tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
      (use append_T_imp_tF ftF_Nil in blast,metis (lifting) butlast_append butlast_snoc event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) ftF_charn
        ftF_dw_closed tF_Cons_iff tF_append_iff tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
  thus \<open>s \<in> g ` \<^bold>\<checkmark>\<^bold>s(P)\<close> by (auto intro: strict_ticks_of_memI is_processT9)
qed


lemma strict_ticks_of_inj_on_Renaming :
  \<open>\<^bold>\<checkmark>\<^bold>s(Renaming P f g) = g ` \<^bold>\<checkmark>\<^bold>s(P)\<close> if \<open>inj_on f \<alpha>(P)\<close>
proof (rule subset_antisym)
  show \<open>\<^bold>\<checkmark>\<^bold>s(Renaming P f g) \<subseteq> g ` \<^bold>\<checkmark>\<^bold>s(P)\<close> by (fact strict_ticks_of_Renaming_subset)
next
  show \<open>g ` \<^bold>\<checkmark>\<^bold>s(P) \<subseteq> \<^bold>\<checkmark>\<^bold>s(Renaming P f g)\<close>
  proof (rule subsetI, elim imageE strict_ticks_of_memE)
    fix s r t assume \<open>s = g r\<close> \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>t \<notin> \<D> P\<close>
    from \<open>s = g r\<close> \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close>
    have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t @ [\<checkmark>(s)] \<in> \<T> (Renaming P f g)\<close>
      by (auto simp add: T_Renaming)
    moreover have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t @ [\<checkmark>(s)] \<notin> \<D> (Renaming P f g)\<close>
    proof (rule ccontr)
      assume \<open>\<not> map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t @ [\<checkmark>(s)] \<notin> \<D> (Renaming P f g)\<close>
      then obtain u1 u2 where * : \<open>ftF u2\<close> \<open>tF u1\<close> \<open>u1 \<in> \<D> P\<close>
        \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t @ [\<checkmark>(s)] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ u2\<close>
        by (auto simp add: D_Renaming)
      from "*"(1, 2, 4) obtain u2' where \<open>u2 = u2' @ [\<checkmark>(s)]\<close>
        by (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) last_appendR last_snoc
            not_tF_and_ftF tF_Cons_iff tF_Nil tF_append_iff tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
      obtain t1 t2 where ** : \<open>t = t1 @ t2\<close> \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1\<close>
        by (metis "*"(4) \<open>u2 = u2' @ [\<checkmark>(s)]\<close> append.assoc append_eq_map_conv butlast_snoc)
      moreover from "*"(2) \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close> calculation have \<open>t1 \<in> {t \<in> \<T> P. tF t}\<close>
        by simp (metis is_processT3_TR_append tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
      moreover have \<open>u1 \<in> {t \<in> \<T> P. tF t}\<close> by (simp add: "*"(2) "*"(3) D_T)
      ultimately have \<open>t1 = u1\<close>
        by (intro inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T_tF[THEN inj_onD, OF \<open>inj_on f \<alpha>(P)\<close>])
      with "*"(2, 3) "**"(1) \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>t \<notin> \<D> P\<close> show False
        using T_imp_ftF ftF_dw_closed
          ftF_nonempty_append_imp is_processT7 by simp blast
    qed
    ultimately show \<open>s \<in> \<^bold>\<checkmark>\<^bold>s(Renaming P f g)\<close> by (simp add: strict_ticks_of_memI)
  qed
qed



lemma strict_ticks_of_Seq_subset : \<open>\<^bold>\<checkmark>\<^bold>s(P \<^bold>; Q) \<subseteq> (if \<^bold>\<checkmark>\<^bold>s(P) = {} then {} else \<^bold>\<checkmark>\<^bold>s(Q))\<close>
proof (rule subsetI, elim strict_ticks_of_memE)
  show \<open>t @ [\<checkmark>(r)] \<in> \<T> (P \<^bold>; Q) \<Longrightarrow> t \<notin> \<D> (P \<^bold>; Q) \<Longrightarrow>
        r \<in> (if \<^bold>\<checkmark>\<^bold>s(P) = {} then {} else \<^bold>\<checkmark>\<^bold>s(Q))\<close> for r t
    by (auto simp add: Seq_projs strict_ticks_of_def intro: is_processT9)
      (metis butlast_snoc ftF_iff_tF_butlast is_processT2_TR is_processT7 is_processT9,
        metis (no_types, lifting) T_not_tF_imp_decomp append1_eq_conv
        append_T_imp_tF append_assoc butlast_snoc div_butlast_when_non_tF_iff
        event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) is_processT2_TR not_Cons_self2 tF_Cons_iff tF_append_iff)
qed


lemma strict_ticks_of_Sync_subset : \<open>\<^bold>\<checkmark>\<^bold>s(P \<lbrakk>S\<rbrakk> Q) \<subseteq> \<^bold>\<checkmark>\<^bold>s(P) \<inter> \<^bold>\<checkmark>\<^bold>s(Q)\<close>
proof (rule subsetI)
  fix r assume \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P \<lbrakk>S\<rbrakk> Q)\<close>
  then obtain t where \<open>t @ [\<checkmark>(r)] \<in> \<T> (P \<lbrakk>S\<rbrakk> Q)\<close> \<open>t @ [\<checkmark>(r)] \<notin> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close> \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
    by (meson strict_ticks_of_memE is_processT9)
  from this(1, 2) obtain t_P t_Q
    where \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close>
      \<open>(t @ [\<checkmark>(r)]) setinterleaves ((t_P, t_Q), range tick \<union> ev ` S)\<close>
    unfolding Sync_projs by blast
  then obtain t_P' t_Q'
    where * : \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q' @ [\<checkmark>(r)]\<close> \<open>t_P' \<in> \<T> P\<close> \<open>t_Q' \<in> \<T> Q\<close>
      \<open>t setinterleaves ((t_P', t_Q'), range tick \<union> ev ` S)\<close>
    by (metis SyncWithTick_imp_NTF T_imp_ftF is_processT3_TR_append)
  have \<open>t_P' \<notin> \<D> P\<close>
  proof (rule ccontr)
    assume \<open>\<not> t_P' \<notin> \<D> P\<close>
    with "*"(4, 5) have \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
      by (simp add: D_Sync) (use ftF_Nil in blast)
    with \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close> show False ..
  qed
  moreover have \<open>t_Q' \<notin> \<D> Q\<close>
  proof (rule ccontr)
    assume \<open>\<not> t_Q' \<notin> \<D> Q\<close>
    with "*"(3, 5) have \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
      by (simp add: D_Sync) (use ftF_Nil setinterleaving_dual in blast)
    with \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close> show False ..
  qed
  ultimately show \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<inter> \<^bold>\<checkmark>\<^bold>s(Q)\<close>
    using "*"(1, 2) \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> 
    by (meson IntI is_processT9 strict_ticks_of_memI)
qed


lemma strict_ticks_of_Hiding_subset : \<open>\<^bold>\<checkmark>\<^bold>s(P \ B) \<subseteq> \<^bold>\<checkmark>\<^bold>s(P)\<close>
proof (intro subsetI)
  fix r assume \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P \ B)\<close>
  then obtain t where \<open>t @ [\<checkmark>(r)] \<in> \<T> (P \ B)\<close> \<open>t @ [\<checkmark>(r)] \<notin> \<D> (P \ B)\<close>
    by (meson is_processT9 strict_ticks_of_memD)
  then obtain u where * : \<open>t @ [\<checkmark>(r)] = trace_hide u (ev ` B)\<close> \<open>u \<in> \<T> P\<close>
    unfolding D_Hiding T_Hiding using F_T by fast
  from "*"(1) \<open>t @ [\<checkmark>(r)] \<notin> \<D> (P \ B)\<close> have \<open>u \<notin> \<D> P\<close>
    by (metis mem_D_imp_mem_D_Hiding)
  from "*" obtain u' where \<open>u = u' @ [\<checkmark>(r)]\<close>
    by (cases u rule: rev_cases, auto dest!: trace_hide_append
        split: if_split_asm simp add: Cons_eq_filter_iff)
      (metis Nil_is_append_conv event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) ftF_Cons_iff
        ftF_nonempty_append_imp is_processT2_TR list.distinct(1))
  with \<open>u \<in> \<T> P\<close> \<open>u \<notin> \<D> P\<close> show \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close>
    by (simp add: strict_ticks_of_memI)
qed



section \<open>Restriction of the Events\<close>

text \<open>This is the main motivation behind the introduction of \<^term>\<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P)\<close> in Isabelle26:
we can obtain powerful theorems for restricting the set of events that we have to consider
for some operators.\<close>

subsection \<open>Hiding\<close>

theorem Hiding_is_restrictable_on_superset_minimal_events_of:
  fixes S :: \<open>'a set\<close> and P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assumes superset : \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<subseteq> A\<close>
  defines \<open>S' \<equiv> S \<inter> A\<close>
  shows \<open>P \ S = P \ S'\<close>
proof -
  from superset
  have \<open>set t \<subseteq> tick ` \<^bold>\<checkmark>\<^bold>s(P) \<union> ev ` \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<Longrightarrow>
        trace_hide t (ev ` S) = trace_hide t (ev ` S')\<close> for t :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (induct t) (auto simp add: S'_def image_iff subset_iff)
  with mem_D\<^sub>m\<^sub>i\<^sub>n_Un_T_Diff_D_imp_set_subset have same_trace_hide :
    \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<union> (\<T> P - \<D> P) \<Longrightarrow> trace_hide t (ev ` S) = trace_hide t (ev ` S')\<close> for t by blast

  have seqRun_mem_T_Diff_D :
    \<open>isInfHidden_seqRun_strong x P S t \<Longrightarrow> seqRun t x i \<in> \<T> P - \<D> P\<close> for x t S i by simp
  from mem_D\<^sub>m\<^sub>i\<^sub>n_Un_T_Diff_D_imp_set_subset[OF UnI2[OF this]]
  have \<open>isInfHidden_seqRun_strong x P S t \<Longrightarrow> x i \<in> ev ` \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)\<close> for x t S i
    by (simp add: seqRun_def subset_iff image_iff)
      (metis atLeastLessThan_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(4) le0 lessI)
  moreover have \<open>isInfHidden_seqRun_strong x P S t \<Longrightarrow>
                 trace_hide t (ev ` S) = trace_hide t (ev ` S')\<close> for x t
    by (metis Diff_iff UnI2 same_trace_hide seqRun_0)
  ultimately have IH_strong_iff :
    \<open>isInfHidden_seqRun_strong x P S t \<longleftrightarrow> isInfHidden_seqRun_strong x P S' t\<close> for x t
    using superset
    by (safe, simp_all add: S'_def subset_iff image_iff)
      (metis (no_types, lifting) IntI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1), blast)

  show \<open>P \ S = P \ S'\<close>
  proof (rule Process_eqI_D\<^sub>m\<^sub>i\<^sub>n_version)
    fix t assume \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (P \ S)\<close>
    then obtain u x where * : \<open>tF u\<close> \<open>t = trace_hide u (ev ` S)\<close>
      \<open>u \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<or> isInfHidden_seqRun_strong x P S u\<close>
      by (blast dest: D\<^sub>m\<^sub>i\<^sub>n_Hiding_subset[THEN set_mp])
    from "*"(2, 3) have \<open>t = trace_hide u (ev ` S')\<close>
      by (metis Diff_iff Un_iff same_trace_hide seqRun_0)
    moreover from "*"(3) have \<open>u \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<or> isInfHidden_seqRun_strong x P S' u\<close>
      by (simp add: IH_strong_iff)
    ultimately show \<open>t \<in> \<D> (P \ S')\<close>
      by (simp add: D_Hiding_seqRun)
        (use "*"(1) in \<open>blast dest: D\<^sub>m\<^sub>i\<^sub>n_D intro: ftF_Nil\<close>)
  next
    fix t assume \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (P \ S')\<close>
    then obtain u x where * : \<open>tF u\<close> \<open>t = trace_hide u (ev ` S')\<close>
      \<open>u \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<or> isInfHidden_seqRun_strong x P S' u\<close>
      by (blast dest: D\<^sub>m\<^sub>i\<^sub>n_Hiding_subset[THEN set_mp])
    from "*"(2, 3) have \<open>t = trace_hide u (ev ` S)\<close>
      by (metis Diff_iff Un_iff same_trace_hide seqRun_0)
    moreover from "*"(3) have \<open>u \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<or> isInfHidden_seqRun_strong x P S u\<close>
      by (simp add: IH_strong_iff)
    ultimately show \<open>t \<in> \<D> (P \ S)\<close>
      by (simp add: D_Hiding_seqRun)
        (use "*"(1) in \<open>blast dest: D\<^sub>m\<^sub>i\<^sub>n_D intro: ftF_Nil\<close>)
  next
    fix t X assume \<open>(t, X) \<in> \<F> (P \ S)\<close> \<open>t \<notin> \<D> (P \ S)\<close>
    then obtain u where * : \<open>t = trace_hide u (ev ` S)\<close> \<open>(u, X \<union> ev ` S) \<in> \<F> P\<close>
      unfolding F_Hiding D_Hiding by blast
    from "*" \<open>t \<notin> \<D> (P \ S)\<close> have \<open>u \<in> \<T> P\<close> \<open>u \<notin> \<D> P\<close>
      by (auto dest: F_T intro: mem_D_imp_mem_D_Hiding)
    with "*"(1) have \<open>t = trace_hide u (ev ` S')\<close>
      by (simp add: same_trace_hide)
    moreover have \<open>(u, X \<union> ev ` S') \<in> \<F> P\<close>
    proof (rule is_processT4)
      show \<open>(u, X \<union> ev ` S) \<in> \<F> P\<close> by (fact "*"(2))
    next
      show \<open>X \<union> ev ` S' \<subseteq> X \<union> ev ` S\<close> by (auto simp add: S'_def)
    qed
    ultimately show \<open>(t, X) \<in> \<F> (P \ S')\<close>
      by (auto simp add: F_Hiding)
  next
    fix t X assume \<open>(t, X) \<in> \<F> (P \ S')\<close> \<open>t \<notin> \<D> (P \ S')\<close>
    then obtain u where * : \<open>t = trace_hide u (ev ` S')\<close> \<open>(u, X \<union> ev ` S') \<in> \<F> P\<close>
      unfolding F_Hiding D_Hiding by blast
    from "*" \<open>t \<notin> \<D> (P \ S')\<close> have \<open>u \<in> \<T> P\<close> \<open>u \<notin> \<D> P\<close>
      by (auto dest: F_T intro: mem_D_imp_mem_D_Hiding)
    with "*"(1) have \<open>t = trace_hide u (ev ` S)\<close>
      by (simp add: same_trace_hide)
    moreover have \<open>(u, X \<union> ev ` S) \<in> \<F> P\<close>
    proof (rule is_processT4[OF add_Compl_minimal_events_of_Compl_strict_events_of_in_F])
      show \<open>(u, X \<union> ev ` S') \<in> \<F> P\<close> by (fact "*"(2))
    next
      from superset show \<open>X \<union> ev ` S \<subseteq> X \<union> ev ` S' \<union> ev ` (- \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)) \<union> tick ` (- \<^bold>\<checkmark>\<^bold>s(P))\<close>
        by (auto simp add: S'_def)
    qed
    ultimately show \<open>(t, X) \<in> \<F> (P \ S)\<close>
      by (auto simp add: F_Hiding)
  qed
qed


corollary Hiding_is_restrictable_on_minimal_events_of : \<open>P \ S = P \ S \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)\<close>
  by (simp add: Hiding_is_restrictable_on_superset_minimal_events_of)

text \<open>This version is closer to the intuition that we may have, but the first one would be more
useful if we don't want to compute the events of a process but know a superset approximation.\<close>



subsection \<open>Renaming\<close>

lemma Renaming_is_restrictable_on_minimal_events_of_strict_ticks_of :
  \<open>Renaming P f g = Renaming P f' g'\<close>
  if fun_hyps : \<open>\<And>a. a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<Longrightarrow> f a = f' a\<close>
    \<open>\<And>r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> g r = g' r\<close>
  for f f' :: \<open>'a \<Rightarrow> 'b\<close> and g g' :: \<open>'r \<Rightarrow> 't\<close>
proof -
  have * : \<open>Renaming P f g \<sqsubseteq>\<^sub>F\<^sub>D Renaming P f' g'\<close>
    if fun_hyps_bis : \<open>\<And>a. a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<Longrightarrow> f a = f' a\<close> \<open>\<And>r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> g r = g' r\<close>
    for f f' :: \<open>'a \<Rightarrow> 'b\<close> and g g' :: \<open>'r \<Rightarrow> 't\<close>
  proof -
    have $ : \<open>u \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<union> (\<T> P - \<D> P) \<Longrightarrow>
              map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g') u\<close> for u
      by (drule mem_D\<^sub>m\<^sub>i\<^sub>n_Un_T_Diff_D_imp_set_subset)
        (induct u, auto simp add: fun_hyps_bis)
    show \<open>Renaming P f g \<sqsubseteq>\<^sub>F\<^sub>D Renaming P f' g'\<close>
    proof (rule failure_divergence_refineI_D\<^sub>m\<^sub>i\<^sub>n_version)
      fix t assume \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (Renaming P f' g')\<close>
      then obtain u where * : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g') u\<close> \<open>u \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P\<close>
        by (blast dest: D\<^sub>m\<^sub>i\<^sub>n_Renaming_subset[THEN set_mp])
      have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g') u = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close>
        by (metis "$" "*"(2) Un_iff)
      with "*" show \<open>t \<in> \<D> (Renaming P f g)\<close>
        by  (auto simp add: D_Renaming intro: D\<^sub>m\<^sub>i\<^sub>n_D ftF_Nil tF_mem_D\<^sub>m\<^sub>i\<^sub>n)
    next
      fix t X assume \<open>(t, X) \<in> \<F> (Renaming P f' g')\<close> \<open>t \<notin> \<D> (Renaming P f' g')\<close>
      then obtain u where * : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g') u\<close>
        \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g' -` X) \<in> \<F> P\<close>
        unfolding Renaming_projs by blast
      with \<open>t \<notin> \<D> (Renaming P f' g')\<close> have \<open>u \<notin> \<D> P\<close>
        by (simp add: Renaming_projs)
          (metis (no_types, lifting) D_imp_ftF Nil_is_map_conv append.right_neutral
            div_butlast_when_non_tF_iff ftF_Nil ftF_iff_tF_butlast
            ftF_single map_butlast snoc_eq_iff_butlast tF_Nil)
      with "*" "$" have \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close>
        by (metis F_T Un_Diff_cancel Un_iff)
      moreover have \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> P\<close>
      proof (rule is_processT4)
        show \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g' -` X \<union> ev ` (- \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)) \<union> tick ` (- \<^bold>\<checkmark>\<^bold>s(P))) \<in> \<F> P\<close>
          by (fact add_Compl_minimal_events_of_Compl_strict_events_of_in_F[OF "*"(2)])
      next
        show \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<subseteq> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f' g' -` X \<union> ev ` (- \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)) \<union> tick ` (- \<^bold>\<checkmark>\<^bold>s(P))\<close> (is \<open>?ref1 \<subseteq> ?ref2\<close>)
        proof (rule subsetI)
          show \<open>e \<in> ?ref1 \<Longrightarrow> e \<in> ?ref2\<close> for e
            by (cases e) (auto simp add: fun_hyps_bis)
        qed
      qed
      ultimately show \<open>(t, X) \<in> \<F> (Renaming P f g)\<close>
        by (auto simp add: F_Renaming)
    qed
  qed
  show \<open>Renaming P f g = Renaming P f' g'\<close>
  proof (rule FD_antisym)
    show \<open>Renaming P f g \<sqsubseteq>\<^sub>F\<^sub>D Renaming P f' g'\<close> \<open>Renaming P f' g' \<sqsubseteq>\<^sub>F\<^sub>D Renaming P f g\<close>
      by (simp_all add: "*" fun_hyps)
  qed
qed



subsection \<open>Synchronization Product\<close>

lemma Sync_is_restrictable_on_minimal_events_of :
  \<open>P \<lbrakk>S\<rbrakk> Q = P \<lbrakk>S \<inter> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q))\<rbrakk> Q\<close>
  oops (* proven in HOL-CSP_PTick *)

corollary Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_minimal_events_of :
  \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q) \<subseteq> A \<Longrightarrow> P \<lbrakk>S\<rbrakk> Q = P \<lbrakk>S \<inter> A\<rbrakk> Q\<close>
  oops (* proven in HOL-CSP_PTick *)



(*<*)
end
  (*>*)
