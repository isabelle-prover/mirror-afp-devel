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


chapter \<open>Events and Ticks\<close>

(*<*)
theory Events_Ticks_CSP_PTick_Laws
  imports Multi_Sequential_Composition_Generalized
    Multi_Synchronization_Product_Generalized
begin
  (*>*)


section \<open>Preliminaries\<close>

lemma strict_events_of_memE_optimized_tickFree :
  \<open>(\<And>t. t \<in> \<T> P \<Longrightarrow> t \<notin> \<D> P \<Longrightarrow> ev a \<in> set t \<Longrightarrow> tF t \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> if \<open>a \<in> \<^bold>\<alpha>(P)\<close>
proof -
  from \<open>a \<in> \<^bold>\<alpha>(P)\<close> obtain t where \<open>t \<in> \<T> P\<close> \<open>t \<notin> \<D> P\<close> \<open>ev a \<in> set t\<close>
    by (meson strict_events_of_memE)
  have \<open>(if tF t then t else butlast t) \<in> \<T> P\<close>
    by simp (metis \<open>t \<in> \<T> P\<close> append_butlast_last_id is_processT3_TR_append tickFree_Nil)
  moreover have \<open>(if tF t then t else butlast t) \<notin> \<D> P\<close>
    using T_imp_front_tickFree \<open>t \<in> \<T> P\<close> \<open>t \<notin> \<D> P\<close> div_butlast_when_non_tickFree_iff by blast
  moreover from T_nonTickFree_imp_decomp \<open>ev a \<in> set t\<close> \<open>t \<in> \<T> P\<close>
  have \<open>ev a \<in> set (if tF t then t else butlast t)\<close> by force
  moreover from T_imp_front_tickFree \<open>t \<in> \<T> P\<close> front_tickFree_iff_tickFree_butlast
  have \<open>tF (if tF t then t else butlast t)\<close> by (metis (full_types))
  ultimately show \<open>(\<And>t. t \<in> \<T> P \<Longrightarrow> t \<notin> \<D> P \<Longrightarrow> ev a \<in> set t \<Longrightarrow> tF t \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
qed

lemma events_of_memE_optimized_tickFree :
  \<open>(\<And>t. t \<in> \<T> P \<Longrightarrow> ev a \<in> set t \<Longrightarrow> tF t \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> if \<open>a \<in> \<alpha>(P)\<close>
proof -
  from \<open>a \<in> \<alpha>(P)\<close> obtain t where \<open>t \<in> \<T> P\<close> \<open>ev a \<in> set t\<close>
    by (meson events_of_memE)
  have \<open>(if tF t then t else butlast t) \<in> \<T> P\<close>
    by simp (metis \<open>t \<in> \<T> P\<close> append_butlast_last_id is_processT3_TR_append tickFree_Nil)
  moreover from T_nonTickFree_imp_decomp \<open>ev a \<in> set t\<close> \<open>t \<in> \<T> P\<close>
  have \<open>ev a \<in> set (if tF t then t else butlast t)\<close> by force
  moreover from T_imp_front_tickFree \<open>t \<in> \<T> P\<close> front_tickFree_iff_tickFree_butlast
  have \<open>tF (if tF t then t else butlast t)\<close> by (metis (full_types))
  ultimately show \<open>(\<And>t. t \<in> \<T> P \<Longrightarrow> ev a \<in> set t \<Longrightarrow> tF t \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
qed



section \<open>Sequential Composition\<close>

subsection \<open>Events\<close>

lemma events_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>\<alpha>(P \<^bold>;\<^sub>\<checkmark> Q) = \<alpha>(P) \<union> (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P). \<alpha>(Q r))\<close>
proof (intro subset_antisym subsetI)
  show \<open>a \<in> \<alpha>(P \<^bold>;\<^sub>\<checkmark> Q) \<Longrightarrow> a \<in> \<alpha>(P) \<union> (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P). \<alpha>(Q r))\<close> for a
  proof (elim events_of_memE)
    fix t assume \<open>t \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> \<open>ev a \<in> set t\<close>
    from this(1) consider (T_P) t' where \<open>t = map (ev \<circ> of_ev) t'\<close> \<open>t' \<in> \<T> P\<close> \<open>tF t'\<close>
      | (T_Q) t' r u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t'\<close> \<open>u \<in> \<T> (Q r)\<close>
      | (D_P) t' u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' \<in> \<D> P\<close> \<open>tF t'\<close> \<open>ftF u\<close>
      unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    thus \<open>a \<in> \<alpha>(P) \<union> (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P). \<alpha>(Q r))\<close>
    proof cases
      case T_P
      from T_P(1, 3) \<open>ev a \<in> set t\<close> have \<open>ev a \<in> set t'\<close>
        by (meson tickFree_map_ev_of_ev_eq_imp_ev_mem_iff)
      with T_P(2) have \<open>a \<in> \<alpha>(P)\<close> by (rule events_of_memI)
      thus \<open>a \<in> \<alpha>(P) \<union> (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P). \<alpha>(Q r))\<close> by simp
    next
      case T_Q
      have \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<or> \<D> P \<noteq> {}\<close>
        by (metis T_Q(2) empty_iff strict_ticks_of_memI)
      thus \<open>a \<in> \<alpha>(P) \<union> (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P). \<alpha>(Q r))\<close>
      proof (elim disjE)
        from T_Q
        show \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> a \<in> \<alpha>(P) \<union> (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P). \<alpha>(Q r))\<close>
          by simp (metis Un_iff \<open>ev a \<in> set t\<close> events_of_memI set_append
              tickFree_map_ev_of_ev_eq_imp_ev_mem_iff)
      next
        assume \<open>\<D> P \<noteq> {}\<close>
        hence \<open>\<alpha>(P) = UNIV\<close> by (simp add: events_of_is_strict_events_of_or_UNIV)
        thus \<open>a \<in> \<alpha>(P) \<union> (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P). \<alpha>(Q r))\<close> by simp
      qed
    next
      case D_P
      have \<open>\<alpha>(P) = UNIV\<close>
        by (metis D_P(2) empty_iff events_of_is_strict_events_of_or_UNIV)
      thus \<open>a \<in> \<alpha>(P) \<union> (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P). \<alpha>(Q r))\<close> by simp
    qed
  qed
next
  show \<open>a \<in> \<alpha>(P) \<union> (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P). \<alpha>(Q r)) \<Longrightarrow> a \<in> \<alpha>(P \<^bold>;\<^sub>\<checkmark> Q)\<close> for a
  proof (elim UnE UnionE events_of_memE, safe)
    fix t assume \<open>t \<in> \<T> P\<close> \<open>ev a \<in> set t\<close>
    then obtain t' where \<open>t' \<in> \<T> P\<close> \<open>tF t'\<close> \<open>ev a \<in> set t'\<close>
      by (cases t rule: rev_cases, simp_all)
        (metis prefixI \<open>ev a \<in> set t\<close> append_T_imp_tickFree event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) is_processT3_TR
          not_Cons_self2 tickFree_Cons_iff tickFree_Nil tickFree_append_iff)
    thus \<open>a \<in> \<alpha>(P \<^bold>;\<^sub>\<checkmark> Q)\<close> by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs rev_image_eqI intro!: events_of_memI)
  next
    fix a r assume \<open>a \<in> \<alpha>(Q r)\<close> \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close>
    from \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close> obtain t where \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close> by (meson strict_ticks_of_memD)
    moreover from \<open>a \<in> \<alpha>(Q r)\<close> obtain u
      where \<open>u \<in> \<T> (Q r)\<close> \<open>ev a \<in> set u\<close> by (meson events_of_memD)
    ultimately have \<open>map (ev \<circ> of_ev) t @ u \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> \<open>ev a \<in> set (map (ev \<circ> of_ev) t @ u)\<close>
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis append_T_imp_tickFree not_Cons_self2)
    thus \<open>a \<in> \<alpha>(P \<^bold>;\<^sub>\<checkmark> Q)\<close> by (simp add: events_of_memI)
  qed
qed

\<comment> \<open>Big approximation.\<close>
lemma events_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset : \<open>\<alpha>(P \<^bold>;\<^sub>\<checkmark> Q) \<subseteq> \<alpha>(P) \<union> (\<Union>r. \<alpha>(Q r))\<close>
  by (auto simp add: events_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)


\<comment> \<open>Big approximation.\<close>
corollary events_of_Seq_subset : \<open>\<alpha>(P \<^bold>; Q) \<subseteq> \<alpha>(P) \<union> \<alpha>(Q)\<close>
  by (simp add: events_of_Seq)


lemma strict_events_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset : \<open>\<^bold>\<alpha>(P \<^bold>;\<^sub>\<checkmark> Q) \<subseteq> \<^bold>\<alpha>(P) \<union> (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P).\<^bold>\<alpha>(Q r))\<close>
proof (rule subsetI)
  show \<open>a \<in> \<^bold>\<alpha>(P \<^bold>;\<^sub>\<checkmark> Q) \<Longrightarrow> a \<in> \<^bold>\<alpha>(P) \<union> (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P).\<^bold>\<alpha>(Q r))\<close> for a
  proof (elim strict_events_of_memE)
    fix t assume \<open>t \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> \<open>t \<notin> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> \<open>ev a \<in> set t\<close>
    from this(1, 2) consider (T_P) t' where \<open>t = map (ev \<circ> of_ev) t'\<close> \<open>t' \<in> \<T> P\<close> \<open>t' \<notin> \<D> P\<close> \<open>tF t'\<close>
      | (T_Q) t' r u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>t' \<notin> \<D> P\<close> \<open>tF t'\<close> \<open>u \<in> \<T> (Q r)\<close> \<open>u \<notin> \<D> (Q r)\<close>
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis T_imp_front_tickFree)
    thus \<open>a \<in> \<^bold>\<alpha>(P) \<union> (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P).\<^bold>\<alpha>(Q r))\<close>
    proof cases
      case T_P
      have \<open>ev a \<in> set t'\<close>
        by (metis T_P(1, 4) \<open>ev a \<in> set t\<close> tickFree_map_ev_of_ev_eq_imp_ev_mem_iff)
      have \<open>a \<in> \<^bold>\<alpha>(P)\<close>
        by (meson T_P(2, 3) \<open>ev a \<in> set t'\<close> strict_events_of_memI)
      thus \<open>a \<in> \<^bold>\<alpha>(P) \<union> (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P).\<^bold>\<alpha>(Q r))\<close> by simp
    next
      case T_Q
      have \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close> by (meson T_Q(2, 3) is_processT9 strict_ticks_of_memI)
      thus \<open>a \<in> \<^bold>\<alpha>(P) \<union> (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P).\<^bold>\<alpha>(Q r))\<close>
        by simp (metis T_Q UnE \<open>ev a \<in> set t\<close> is_processT3_TR_append set_append
            strict_events_of_memI tickFree_map_ev_of_ev_eq_imp_ev_mem_iff)
    qed
  qed
qed



subsection \<open>Ticks\<close>

lemma ticks_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<checkmark>s(P \<^bold>;\<^sub>\<checkmark> Q) = (if \<D> P = {} then (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P). \<checkmark>s(Q r)) else UNIV)\<close>
proof (split if_split, intro conjI impI)
  show \<open>\<D> P \<noteq> {} \<Longrightarrow> \<checkmark>s(P \<^bold>;\<^sub>\<checkmark> Q) = UNIV\<close>
    by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs ticks_of_is_strict_ticks_of_or_UNIV)
      (metis front_tickFree_Nil nonempty_divE)
next
  show \<open>\<D> P = {} \<Longrightarrow> \<checkmark>s(P \<^bold>;\<^sub>\<checkmark> Q) = (\<Union>r\<in>\<^bold>\<checkmark>\<^bold>s(P). \<checkmark>s(Q r))\<close> if \<open>\<D> P = {}\<close>
  proof (intro subset_antisym subsetI)
    from \<open>\<D> P = {}\<close> ticks_of_memI[of _ _ \<open>Q _\<close>]
    show \<open>s \<in> \<checkmark>s(P \<^bold>;\<^sub>\<checkmark> Q) \<Longrightarrow> s \<in> (\<Union>r\<in>\<^bold>\<checkmark>\<^bold>s(P). \<checkmark>s(Q r))\<close> for s
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs strict_ticks_of_def append_eq_map_conv
          append_eq_append_conv2 Cons_eq_append_conv elim!: ticks_of_memE)
        (blast, metis append_Nil)
  next
    show \<open>s \<in> (\<Union>r\<in>\<^bold>\<checkmark>\<^bold>s(P). \<checkmark>s(Q r)) \<Longrightarrow> s \<in> \<checkmark>s(P \<^bold>;\<^sub>\<checkmark> Q)\<close> for s
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs ticks_of_def elim!: strict_ticks_of_memE)
        (meson append.assoc append_T_imp_tickFree not_Cons_self2)
  qed
qed


lemma \<open>\<^bold>\<checkmark>\<^bold>s(P \<^bold>;\<^sub>\<checkmark> Q) \<subseteq> \<Union> {\<^bold>\<checkmark>\<^bold>s(Q r) |r. r \<in> \<^bold>\<checkmark>\<^bold>s(P)}\<close>
  \<comment> \<open>Already proven earlier in the construction.\<close>
  by (fact strict_ticks_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset)




section \<open>Synchronization Product\<close>

subsection \<open>Events\<close>

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) events_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset : \<open>\<alpha>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) \<subseteq> \<alpha>(P) \<union> \<alpha>(Q)\<close>
  by (subst events_of_def, simp add: T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k subset_iff)
    (metis UNIV_I empty_iff events_of_is_strict_events_of_or_UNIV
      events_of_memI setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_preserves_ev_notin_set)

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) events_of_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k: \<open>\<alpha>(P |||\<^sub>\<checkmark> Q) = \<alpha>(P) \<union> \<alpha>(Q)\<close>
proof (rule subset_antisym[OF events_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset])
  show \<open>\<alpha>(P) \<union> \<alpha>(Q) \<subseteq> \<alpha>(P |||\<^sub>\<checkmark> Q)\<close>
  proof (rule subsetI, elim UnE)
    fix a assume \<open>a \<in> \<alpha>(P)\<close>
    then obtain t_P where \<open>tF t_P\<close> \<open>ev a \<in> set t_P\<close> \<open>t_P \<in> \<T> P\<close>
      by (meson events_of_memE_optimized_tickFree)
    have \<open>map ev (map of_ev t_P) setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, []), {})\<close>
      by (simp add: \<open>tF t_P\<close> setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilR_iff)
    hence \<open>map ev (map of_ev t_P) \<in> \<T> (P |||\<^sub>\<checkmark> Q)\<close>
      by (simp add: T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (metis \<open>t_P \<in> \<T> P\<close> is_processT1_TR)
    moreover from \<open>ev a \<in> set t_P\<close> have \<open>ev a \<in> set (map ev (map of_ev t_P))\<close> by force
    ultimately show \<open>a \<in> \<alpha>(P |||\<^sub>\<checkmark> Q)\<close> by (metis events_of_memI)
  next
    fix a assume \<open>a \<in> \<alpha>(Q)\<close>
    then obtain t_Q where \<open>tF t_Q\<close> \<open>ev a \<in> set t_Q\<close> \<open>t_Q \<in> \<T> Q\<close>
      by (meson events_of_memE_optimized_tickFree)
    have \<open>map ev (map of_ev t_Q) setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (([], t_Q), {})\<close>
      by (simp add: \<open>tF t_Q\<close> setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilL_iff)
    hence \<open>map ev (map of_ev t_Q) \<in> \<T> (P |||\<^sub>\<checkmark> Q)\<close>
      by (simp add: T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (metis \<open>t_Q \<in> \<T> Q\<close> is_processT1_TR)
    moreover from \<open>ev a \<in> set t_Q\<close> have \<open>ev a \<in> set (map ev (map of_ev t_Q))\<close> by force
    ultimately show \<open>a \<in> \<alpha>(P |||\<^sub>\<checkmark> Q)\<close> by (metis events_of_memI)
  qed
qed


lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) strict_events_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset :
  \<open>\<^bold>\<alpha>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) \<subseteq> \<^bold>\<alpha>(P) \<union> \<^bold>\<alpha>(Q)\<close>
proof (rule subsetI)
  fix a assume \<open>a \<in> \<^bold>\<alpha>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  then obtain t where \<open>t \<in> \<T> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>ev a \<in> set t\<close> \<open>tF t\<close> \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    by (blast elim: strict_events_of_memE_optimized_tickFree)
  from \<open>t \<in> \<T> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  obtain t_P t_Q where \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close>
    and setinter : \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
    unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
  from this(3) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_preserves_ev_notin_set \<open>ev a \<in> set t\<close>
  have \<open>ev a \<in> set t_P \<or> ev a \<in> set t_Q\<close> by metis
  moreover have \<open>t_P \<notin> \<D> P \<and> t_Q \<notin> \<D> Q\<close>
  proof (rule ccontr)
    assume \<open>\<not> (t_P \<notin> \<D> P \<and> t_Q \<notin> \<D> Q)\<close>
    with \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> \<open>tF t\<close> front_tickFree_Nil setinter
    have \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    with \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> show False ..
  qed
  ultimately show \<open>a \<in> \<^bold>\<alpha>(P) \<union> \<^bold>\<alpha>(Q)\<close>
    by (meson UnCI \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> strict_events_of_memI)
qed



subsection \<open>Ticks\<close>

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale)
  \<open>\<^bold>\<checkmark>\<^bold>s(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) \<subseteq> {r_s |r_s r s. r \<otimes>\<checkmark> s = Some r_s \<and> r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> s \<in> \<^bold>\<checkmark>\<^bold>s(Q)}\<close>
  \<comment> \<open>Already proven earlier in the construction.\<close>
  by (fact strict_ticks_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset)

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) ticks_of_no_div_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset :
  \<open>\<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) = {} \<Longrightarrow>
   \<checkmark>s(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) \<subseteq> {r_s |r_s r s. tick_join r s = Some r_s \<and> r \<in> \<checkmark>s(P) \<and> s \<in> \<checkmark>s(Q)}\<close>
  using strict_ticks_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset
  by (simp add: ticks_of_is_strict_ticks_of_or_UNIV subset_iff) blast



section \<open>Architectural Operators\<close>

subsection \<open>Events\<close>

lemma events_of_MultiSeq_subset :
  (* Should be in HOL-CSPM *)
  \<open>\<alpha>(SEQ l \<in>@ L. P l) \<subseteq> (\<Union>l \<in> set L. \<Union>r. \<alpha>(P l))\<close>
  by (induct L rule: rev_induct)
    (auto intro!: subset_trans[OF events_of_Seq_subset])

lemma events_of_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset :
  \<open>\<alpha>((SEQ\<^sub>\<checkmark> l \<in>@ L. P l) r) \<subseteq> (\<Union>l \<in> set L. \<Union>r. \<alpha>(P l r))\<close>
  by (induct L arbitrary: r)
    (auto intro!: subset_trans[OF events_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset])

lemma strict_events_of_MultiSeq_subset :
  (* Should be in HOL-CSPM *)
  \<open>\<^bold>\<alpha>(SEQ l \<in>@ L. P l) \<subseteq> (\<Union>l \<in> set L. \<Union>r. \<^bold>\<alpha>(P l))\<close>
  by (induct L rule: rev_induct)
    (auto intro!: subset_trans[OF strict_events_of_Seq_subseteq]
      split: if_split_asm)

lemma strict_events_of_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset :
  \<open>\<^bold>\<alpha>((SEQ\<^sub>\<checkmark> l \<in>@ L. P l) r) \<subseteq> (\<Union>l \<in> set L. \<Union>r. \<^bold>\<alpha>(P l r))\<close>
  by (induct L arbitrary: r, simp)
    (auto intro!: subset_trans[OF strict_events_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset])



lemma events_of_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset :
  \<open>\<alpha>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l) \<subseteq> (\<Union>l \<in> set L. \<alpha>(P l))\<close>
  by (induct L rule: induct_list012, simp_all)
    (metis eq_id_iff events_of_Renaming order.order_iff_strict
      image_id events_of_is_strict_events_of_or_UNIV, 
      use Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.events_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset in fastforce)

lemma events_of_MultiInter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<alpha>(\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ L. P l) = (\<Union>l \<in> set L. \<alpha>(P l))\<close>
  by (induct L rule: induct_list012,
      simp_all add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.events_of_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    (metis events_of_Renaming events_of_is_strict_events_of_or_UNIV id_apply image_id)

lemma strict_events_of_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset : 
  \<open>\<^bold>\<alpha>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l) \<subseteq> (\<Union>l \<in> set L. \<^bold>\<alpha>(P l))\<close>
  by (induct L rule: induct_list012, simp_all add: strict_events_of_inj_on_Renaming)
    (use Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.strict_events_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset in fastforce)



subsection \<open>Ticks\<close>

text \<open>
We only look at \<^const>\<open>strict_ticks_of\<close> lemmas: \<^const>\<open>ticks_of\<close> is harder
to deal with because it requires more control on the divergences. 
\<close>

lemma strict_ticks_of_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset :
  \<open>\<^bold>\<checkmark>\<^bold>s((SEQ\<^sub>\<checkmark> l \<in>@ L. P l) r) \<subseteq> (if L = [] then {r} else (\<Union>r. \<^bold>\<checkmark>\<^bold>s(P (last L) r)))\<close>
proof (induct L arbitrary: r)
  case Nil show ?case by simp
next
  case (Cons l L)
  have \<open>(SEQ\<^sub>\<checkmark> m \<in>@ (l # L). P m) r = P l r \<^bold>;\<^sub>\<checkmark> SEQ\<^sub>\<checkmark> l \<in>@ L. P l\<close> by simp
  also have \<open>\<^bold>\<checkmark>\<^bold>s(\<dots>) \<subseteq> \<Union> {\<^bold>\<checkmark>\<^bold>s((SEQ\<^sub>\<checkmark> l \<in>@ L. P l) r') |r'. r' \<in> \<^bold>\<checkmark>\<^bold>s(P l r)}\<close>
    by (fact strict_ticks_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset)
  also have \<open>\<dots> \<subseteq> \<Union> {if L = [] then {r'} else \<Union>r. \<^bold>\<checkmark>\<^bold>s(P (last L) r) |r'. r' \<in> \<^bold>\<checkmark>\<^bold>s(P l r)}\<close>
    using Cons.hyps by (blast intro: Union_subsetI)
  also have \<open>\<dots> \<subseteq> (if l # L = [] then {r} else \<Union>r. \<^bold>\<checkmark>\<^bold>s(P (last (l # L)) r))\<close> by auto
  finally show ?case .
qed

lemma strict_ticks_of_MultiSeq_subset :
  \<open>\<^bold>\<checkmark>\<^bold>s(SEQ l \<in>@ L. P l) \<subseteq> (if L = [] then {undefined} else (\<Union>r. \<^bold>\<checkmark>\<^bold>s(P (last L))))\<close>
  using strict_ticks_of_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset[of L \<open>\<lambda>l r. P l\<close>]
  unfolding MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_const by auto



lemma strict_ticks_of_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset : 
  \<open>\<^bold>\<checkmark>\<^bold>s(\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l) \<subseteq>
   {l. length l = length L \<and> (\<forall>i < length L. l ! i \<in> \<^bold>\<checkmark>\<^bold>s(P (L ! i)))}\<close>
proof (induct L rule: induct_list012)
  case 1 show ?case by simp
next
  case (2 l0) show ?case
    by (auto intro!: subset_trans[OF strict_ticks_of_RenamingTick_subset])
next
  case (3 l0 l1 L)
  have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). P l = P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). P l\<close> by simp
  also have \<open>\<^bold>\<checkmark>\<^bold>s(\<dots>) \<subseteq> {r # s |r s. r \<in> \<^bold>\<checkmark>\<^bold>s(P l0) \<and> s \<in> \<^bold>\<checkmark>\<^bold>s(\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). P l)}\<close>
    by (rule subset_trans[OF Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.strict_ticks_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset]) blast
  also have \<open>\<dots> \<subseteq>
    {r # s |r s. r \<in> \<^bold>\<checkmark>\<^bold>s(P l0) \<and>
                 s \<in> {l. length l = length (l1 # L) \<and>
                          (\<forall>i<length (l1 # L). l ! i \<in> \<^bold>\<checkmark>\<^bold>s(P ((l1 # L) ! i)))}}\<close>
    using "3.hyps"(2) by blast
  also have \<open>\<dots> = {l. length l = length (l0 # l1 # L) \<and>
                      (\<forall>i<length (l0 # l1 # L). l ! i \<in> \<^bold>\<checkmark>\<^bold>s(P ((l0 # l1 # L) ! i)))}\<close>
    (is \<open>?S1 = ?S2\<close>)
  proof (unfold set_eq_iff, intro allI)
    show \<open>l \<in> ?S1 \<longleftrightarrow> l \<in> ?S2\<close> for l
      by (cases l, auto, metis less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc)
  qed
  finally show ?case .
qed


(*<*)
end
  (*>*)

