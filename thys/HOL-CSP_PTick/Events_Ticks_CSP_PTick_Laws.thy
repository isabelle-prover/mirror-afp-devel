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
        by (meson tF_map_ev_of_ev_eq_imp_ev_mem_iff)
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
              tF_map_ev_of_ev_eq_imp_ev_mem_iff)
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
        (metis prefixI \<open>ev a \<in> set t\<close> append_T_imp_tF event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) is_processT3_TR
          not_Cons_self2 tF_Cons_iff tF_Nil tF_append_iff)
    thus \<open>a \<in> \<alpha>(P \<^bold>;\<^sub>\<checkmark> Q)\<close> by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs rev_image_eqI intro!: events_of_memI)
  next
    fix a r assume \<open>a \<in> \<alpha>(Q r)\<close> \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close>
    from \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close> obtain t where \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close> by (meson strict_ticks_of_memD)
    moreover from \<open>a \<in> \<alpha>(Q r)\<close> obtain u
      where \<open>u \<in> \<T> (Q r)\<close> \<open>ev a \<in> set u\<close> by (meson events_of_memD)
    ultimately have \<open>map (ev \<circ> of_ev) t @ u \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> \<open>ev a \<in> set (map (ev \<circ> of_ev) t @ u)\<close>
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis append_T_imp_tF not_Cons_self2)
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
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis T_imp_ftF)
    thus \<open>a \<in> \<^bold>\<alpha>(P) \<union> (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P).\<^bold>\<alpha>(Q r))\<close>
    proof cases
      case T_P
      have \<open>ev a \<in> set t'\<close>
        by (metis T_P(1, 4) \<open>ev a \<in> set t\<close> tF_map_ev_of_ev_eq_imp_ev_mem_iff)
      have \<open>a \<in> \<^bold>\<alpha>(P)\<close>
        by (meson T_P(2, 3) \<open>ev a \<in> set t'\<close> strict_events_of_memI)
      thus \<open>a \<in> \<^bold>\<alpha>(P) \<union> (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P).\<^bold>\<alpha>(Q r))\<close> by simp
    next
      case T_Q
      have \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close> by (meson T_Q(2, 3) is_processT9 strict_ticks_of_memI)
      thus \<open>a \<in> \<^bold>\<alpha>(P) \<union> (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P).\<^bold>\<alpha>(Q r))\<close>
        by simp (metis T_Q UnE \<open>ev a \<in> set t\<close> is_processT3_TR_append set_append
            strict_events_of_memI tF_map_ev_of_ev_eq_imp_ev_mem_iff)
    qed
  qed
qed


lemma minimal_events_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset : \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P \<^bold>;\<^sub>\<checkmark> Q) \<subseteq> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> (\<Union>r\<in>\<^bold>\<checkmark>\<^bold>s(P). \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q r))\<close>
  by (auto simp add: minimal_events_of_def append_eq_map_conv
      dest!: strict_events_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset[THEN set_mp] D\<^sub>m\<^sub>i\<^sub>n_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset[THEN set_mp])
    (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) in_set_conv_decomp tF_Cons_iff tF_append_iff,
      metis T_imp_ftF event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) ftF_append_iff
      in_set_conv_decomp is_processT3_TR_append is_processT7 not_Cons_self2 strict_events_of_memI
      tF_Cons_iff tF_append_iff, meson strict_ticks_of_memI)

corollary minimal_events_of_Seq_subset : \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P \<^bold>; Q) \<subseteq> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> (\<Union>r\<in>\<^bold>\<checkmark>\<^bold>s(P). \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q))\<close>
  by (metis (no_types, lifting) ext Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_const minimal_events_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset)



subsection \<open>Ticks\<close>

lemma ticks_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<checkmark>s(P \<^bold>;\<^sub>\<checkmark> Q) = (if \<D> P = {} then (\<Union>r \<in> \<^bold>\<checkmark>\<^bold>s(P). \<checkmark>s(Q r)) else UNIV)\<close>
proof (split if_split, intro conjI impI)
  show \<open>\<D> P \<noteq> {} \<Longrightarrow> \<checkmark>s(P \<^bold>;\<^sub>\<checkmark> Q) = UNIV\<close>
    by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs ticks_of_is_strict_ticks_of_or_UNIV)
      (metis ftF_Nil nonempty_divE)
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
        (meson append.assoc append_T_imp_tF not_Cons_self2)
  qed
qed


lemma \<open>\<^bold>\<checkmark>\<^bold>s(P \<^bold>;\<^sub>\<checkmark> Q) \<subseteq> \<Union> {\<^bold>\<checkmark>\<^bold>s(Q r) |r. r \<in> \<^bold>\<checkmark>\<^bold>s(P)}\<close>
  \<comment> \<open>Already proven earlier in the construction.\<close>
  by (fact strict_ticks_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset)




section \<open>Synchronization Product\<close>

subsection \<open>Events\<close>

lemma (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) events_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset : \<open>\<alpha>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) \<subseteq> \<alpha>(P) \<union> \<alpha>(Q)\<close>
  by (subst events_of_def, simp add: T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k subset_iff)
    (metis UNIV_I empty_iff events_of_is_strict_events_of_or_UNIV
      events_of_memI setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev_in_set_iff)

lemma (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) events_of_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k: \<open>\<alpha>(P |||\<^sub>\<checkmark> Q) = \<alpha>(P) \<union> \<alpha>(Q)\<close>
proof (rule subset_antisym[OF events_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset])
  show \<open>\<alpha>(P) \<union> \<alpha>(Q) \<subseteq> \<alpha>(P |||\<^sub>\<checkmark> Q)\<close>
  proof (rule subsetI, elim UnE)
    fix a assume \<open>a \<in> \<alpha>(P)\<close>
    then obtain t_P where \<open>tF t_P\<close> \<open>ev a \<in> set t_P\<close> \<open>t_P \<in> \<T> P\<close>
      by (meson events_of_memE_optimized_tF)
    have \<open>map ev (map of_ev t_P) setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((t_P, []), {})\<close>
      by (simp add: \<open>tF t_P\<close> setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilR_iff)
    hence \<open>map ev (map of_ev t_P) \<in> \<T> (P |||\<^sub>\<checkmark> Q)\<close>
      by (simp add: T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (metis \<open>t_P \<in> \<T> P\<close> is_processT1_TR)
    moreover from \<open>ev a \<in> set t_P\<close> have \<open>ev a \<in> set (map ev (map of_ev t_P))\<close> by force
    ultimately show \<open>a \<in> \<alpha>(P |||\<^sub>\<checkmark> Q)\<close> by (metis events_of_memI)
  next
    fix a assume \<open>a \<in> \<alpha>(Q)\<close>
    then obtain t_Q where \<open>tF t_Q\<close> \<open>ev a \<in> set t_Q\<close> \<open>t_Q \<in> \<T> Q\<close>
      by (meson events_of_memE_optimized_tF)
    have \<open>map ev (map of_ev t_Q) setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> (([], t_Q), {})\<close>
      by (simp add: \<open>tF t_Q\<close> setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilL_iff)
    hence \<open>map ev (map of_ev t_Q) \<in> \<T> (P |||\<^sub>\<checkmark> Q)\<close>
      by (simp add: T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (metis \<open>t_Q \<in> \<T> Q\<close> is_processT1_TR)
    moreover from \<open>ev a \<in> set t_Q\<close> have \<open>ev a \<in> set (map ev (map of_ev t_Q))\<close> by force
    ultimately show \<open>a \<in> \<alpha>(P |||\<^sub>\<checkmark> Q)\<close> by (metis events_of_memI)
  qed
qed


lemma (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) strict_events_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset :
  \<open>\<^bold>\<alpha>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) \<subseteq> (\<^bold>\<alpha>(P) - S) \<union> (\<^bold>\<alpha>(Q) - S) \<union> \<^bold>\<alpha>(P) \<inter> \<^bold>\<alpha>(Q) \<inter> S\<close>
proof (rule subsetI)
  fix a assume \<open>a \<in> \<^bold>\<alpha>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  then obtain t where \<open>t \<in> \<T> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>ev a \<in> set t\<close> \<open>tF t\<close> \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    by (blast elim: strict_events_of_memE_optimized_tF)
  from \<open>t \<in> \<T> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  obtain t_P t_Q where \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> \<open>t_P \<notin> \<D> P\<close> \<open>t_Q \<notin> \<D> Q\<close>
    and setinter : \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((t_P, t_Q), S)\<close>
    by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (use \<open>tF t\<close> ftF_Nil in blast)
  with setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_imp_ev_mem_set_imp_mem_Un_Diff_Int[OF setinter \<open>ev a \<in> set t\<close>]
  show \<open>a \<in> \<^bold>\<alpha>(P) - S \<union> (\<^bold>\<alpha>(Q) - S) \<union> \<^bold>\<alpha>(P) \<inter> \<^bold>\<alpha>(Q) \<inter> S\<close>
    by (blast intro: strict_events_of_memI)
qed


lemma (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) minimal_events_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset :
  \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) \<subseteq> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) - S) \<union> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(Q) - S) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q) \<inter> S\<close>
proof (rule subsetI, elim minimal_events_of_memE)
  fix a t assume \<open>t \<in> \<T> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>ev a \<in> set t\<close>
  hence \<open>a \<in> \<^bold>\<alpha>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> by (simp add: strict_events_of_memI)
  thus \<open>a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) - S \<union> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(Q) - S) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q) \<inter> S\<close>
    by (auto dest!: strict_events_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset[THEN set_mp]
        intro: minimal_events_of_memI dest: strict_events_of_memD)
next
  fix a t assume \<open>tF t\<close> \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>ev a \<in> set t\<close>
  from this(2) D\<^sub>m\<^sub>i\<^sub>n_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset obtain t_P t_Q
    where * : \<open>tF t\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
      \<open>t_P \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<and> t_Q \<in> \<D>\<^sub>m\<^sub>i\<^sub>n Q \<or> t_P \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<and> t_Q \<in> \<T> Q - \<D> Q \<or> t_Q \<in> \<D>\<^sub>m\<^sub>i\<^sub>n Q \<and> t_P \<in> \<T> P - \<D> P\<close> by blast
  from "*"(3) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_imp_ev_mem_set_imp_mem_Un_Diff_Int[OF "*"(2) \<open>ev a \<in> set t\<close>]
  show \<open>a \<in> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) - S) \<union> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(Q) - S) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q) \<inter> S\<close>
    by (auto intro: minimal_events_of_memI)
qed


corollary minimal_events_of_Sync_subset :
  \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P \<lbrakk>S\<rbrakk> Q) \<subseteq> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) - S) \<union> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(Q) - S) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q) \<inter> S\<close>
  by (metis Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c.minimal_events_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_is_Sync)

corollary \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P \<lbrakk>S\<rbrakk> Q) \<subseteq> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)\<close>
  using minimal_events_of_Sync_subset by fastforce



subsection \<open>Ticks\<close>

lemma (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  \<open>\<^bold>\<checkmark>\<^bold>s(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) \<subseteq> {r_s |r_s r s. r \<otimes>\<checkmark> s = Some r_s \<and> r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> s \<in> \<^bold>\<checkmark>\<^bold>s(Q)}\<close>
  \<comment> \<open>Already proven earlier in the construction.\<close>
  by (fact strict_ticks_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset)

lemma (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) ticks_of_no_div_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset :
  \<open>\<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) = {} \<Longrightarrow>
   \<checkmark>s(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) \<subseteq> {r_s |r_s r s. tj r s = Some r_s \<and> r \<in> \<checkmark>s(P) \<and> s \<in> \<checkmark>s(Q)}\<close>
  using strict_ticks_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset
  by (simp add: ticks_of_is_strict_ticks_of_or_UNIV subset_iff) blast



section \<open>Architectural Operators\<close>

subsection \<open>Events\<close>

lemma minimal_events_of_MultiSeq_subset :
  \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(SEQ l \<in>@ L. P l) \<subseteq> (\<Union>l \<in> set L. \<alpha>\<^sub>m\<^sub>i\<^sub>n(P l))\<close>
  by (induct L rule: rev_induct)
    (auto intro!: subset_trans[OF minimal_events_of_Seq_subset]
      split: if_split_asm)


lemma events_of_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset :
  \<open>\<alpha>((SEQ\<^sub>\<checkmark> l \<in>@ L. P l) r) \<subseteq> (\<Union>l \<in> set L. \<Union>r. \<alpha>(P l r))\<close>
  by (induct L arbitrary: r)
    (auto intro!: subset_trans[OF events_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset])

lemma strict_events_of_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset :
  \<open>\<^bold>\<alpha>((SEQ\<^sub>\<checkmark> l \<in>@ L. P l) r) \<subseteq> (\<Union>l \<in> set L. \<Union>r. \<^bold>\<alpha>(P l r))\<close>
  by (induct L arbitrary: r, simp)
    (auto intro!: subset_trans[OF strict_events_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset])

lemma minimal_events_of_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset :
  \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n((SEQ\<^sub>\<checkmark> l \<in>@ L. P l) r) \<subseteq> (\<Union>l \<in> set L. \<Union>r. \<alpha>\<^sub>m\<^sub>i\<^sub>n(P l r))\<close>
  by (induct L arbitrary: r, simp)
    (auto intro!: subset_trans[OF minimal_events_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset])



lemma minimal_events_of_MultiSync_subset : 
  \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> a \<in># M. P a) \<subseteq>
   (\<Union>l \<in> set_mset M. \<alpha>\<^sub>m\<^sub>i\<^sub>n(P l)) - S \<union> ((\<Inter>l \<in> set_mset M. \<alpha>\<^sub>m\<^sub>i\<^sub>n(P l)) \<inter> S)\<close>
  by (induct M rule: induct_subset_mset_empty_single, simp_all)
    (auto intro!: subset_trans[OF minimal_events_of_Sync_subset])


lemma events_of_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset :
  \<open>\<alpha>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l) \<subseteq> (\<Union>l\<in>set L. \<alpha>(P l))\<close>
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
  \<open>\<^bold>\<alpha>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l) \<subseteq> (\<Union>l\<in>set L. \<^bold>\<alpha>(P l)) - S \<union> (\<Inter>l\<in>set L. \<^bold>\<alpha>(P l)) \<inter> S\<close>
  by (induct L rule: induct_list012, simp_all add: strict_events_of_inj_on_Renaming)
    (auto intro!: subset_trans[OF Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.strict_events_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset])

lemma minimal_events_of_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset : 
  \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l) \<subseteq> (\<Union>l\<in>set L. \<alpha>\<^sub>m\<^sub>i\<^sub>n(P l)) - S \<union> (\<Inter>l\<in>set L. \<alpha>\<^sub>m\<^sub>i\<^sub>n(P l)) \<inter> S\<close>
  by (induct L rule: induct_list012, simp_all add: strict_events_of_inj_on_Renaming)
    (auto intro!: subset_trans[OF Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.minimal_events_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset]
      dest: minimal_events_of_Renaming_subset[THEN set_mp])


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
    by (auto intro!: subset_trans[OF Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.strict_ticks_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset]
        simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_tj_def)
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



section \<open>Restriction of the Events\<close>

subsection \<open>Synchronization Product\<close>

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_events_of :
  \<open>{a. ev a \<in> set u \<or> ev a \<in> set v} \<subseteq> A \<Longrightarrow>
   t setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u, v), S) \<longleftrightarrow>
   t setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u, v), S \<inter> A)\<close>
  by (induct \<open>(tj, u, S, v)\<close> arbitrary: t u v)
    (auto simp add: subset_iff split: option.split_asm)


lemma (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_minimal_events_of :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q = P \<lbrakk>S \<inter> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q))\<rbrakk>\<^sub>\<checkmark> Q\<close>
proof -
  have $ : \<open>t_P \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<and> t_Q \<in> \<D>\<^sub>m\<^sub>i\<^sub>n Q \<or> t_P \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<and> t_Q \<in> \<T> Q - \<D> Q \<or> t_Q \<in> \<D>\<^sub>m\<^sub>i\<^sub>n Q \<and> t_P \<in> \<T> P - \<D> P \<Longrightarrow>
    {a. ev a \<in> set t_P \<or> ev a \<in> set t_Q} \<subseteq> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)\<close>
    \<open>t_P \<in> \<T> P - \<D> P \<Longrightarrow> t_Q \<in> \<T> Q - \<D> Q \<Longrightarrow> {a. ev a \<in> set t_P \<or> ev a \<in> set t_Q} \<subseteq> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)\<close> for t_P t_Q
    by (auto intro: minimal_events_of_memI)
  show \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q = P \<lbrakk>S \<inter> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q))\<rbrakk>\<^sub>\<checkmark> Q\<close>
  proof (rule Process_eqI_D\<^sub>m\<^sub>i\<^sub>n_version)
    fix t assume \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    with D\<^sub>m\<^sub>i\<^sub>n_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset obtain t_P t_Q
      where * : \<open>tF t\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
        \<open>t_P \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<and> t_Q \<in> \<D>\<^sub>m\<^sub>i\<^sub>n Q \<or> t_P \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<and> t_Q \<in> \<T> Q - \<D> Q \<or> t_Q \<in> \<D>\<^sub>m\<^sub>i\<^sub>n Q \<and> t_P \<in> \<T> P - \<D> P\<close> by blast
    from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_events_of[THEN iffD1, OF "$"(1)[OF "*"(3)] "*"(2)]
    have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S \<inter> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)))\<close> .
    moreover from "*"(3) have \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
      by (metis D_T Diff_iff Divergences\<^sub>m\<^sub>i\<^sub>n_def elem_min_elems)
    ultimately show \<open>t \<in> \<D> (P \<lbrakk>S \<inter> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q))\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      using "*"(1) append.right_neutral ftF_Nil unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
  next
    fix t assume \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (P \<lbrakk>S \<inter> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q))\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    with D\<^sub>m\<^sub>i\<^sub>n_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset obtain t_P t_Q
      where * : \<open>tF t\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S \<inter> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)))\<close>
        \<open>t_P \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<and> t_Q \<in> \<D>\<^sub>m\<^sub>i\<^sub>n Q \<or> t_P \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<and> t_Q \<in> \<T> Q - \<D> Q \<or> t_Q \<in> \<D>\<^sub>m\<^sub>i\<^sub>n Q \<and> t_P \<in> \<T> P - \<D> P\<close> by blast
    from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_events_of[THEN iffD2, OF "$"(1)[OF "*"(3)] "*"(2)]
    have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close> .
    moreover from "*"(3) have \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
      by (metis D_T Diff_iff Divergences\<^sub>m\<^sub>i\<^sub>n_def elem_min_elems)
    ultimately show \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      using "*"(1) append.right_neutral ftF_Nil unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
  next
    fix t X assume \<open>(t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    then obtain t_P t_Q X_P X_Q
      where * : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>t_P \<notin> \<D> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close> \<open>t_Q \<notin> \<D> Q\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((t_P, t_Q), S)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tj X_P S X_Q\<close>
      by (simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k') (metis (no_types) F_T ftF_Nil self_append_conv)
    from "*"(1-4) have \<open>t_P \<in> \<T> P - \<D> P\<close> \<open>t_Q \<in> \<T> Q - \<D> Q\<close> by (auto dest: F_T)
    from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_events_of[THEN iffD1, OF "$"(2)[OF this] "*"(5)]
    have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S \<inter> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)))\<close> .
    moreover from "*"(1, 2) have \<open>(t_P, X_P \<union> {ev a |a. a \<notin> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)}) \<in> \<F> P\<close>
      by (auto intro!: is_processT5 simp add: minimal_events_of_def strict_events_of_def)
        (metis D\<^sub>m\<^sub>i\<^sub>n_memI Diff_iff F_T append_is_Nil_conv butlast_snoc last_in_set last_snoc not_Cons_self2)
    moreover from "*"(3, 4) have \<open>(t_Q, X_Q \<union> {ev a |a. a \<notin> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)}) \<in> \<F> Q\<close>
      by (auto intro!: is_processT5 simp add: minimal_events_of_def strict_events_of_def)
        (metis D\<^sub>m\<^sub>i\<^sub>n_memI Diff_iff F_T append_is_Nil_conv butlast_snoc last_in_set last_snoc not_Cons_self2)
    moreover from "*"(6)
    have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
              tj (X_P \<union> {ev a |a. a \<notin> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)})
              (S \<inter> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q))) (X_Q \<union> {ev a |a. a \<notin> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)})\<close>
      by (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
    ultimately show \<open>(t, X) \<in> \<F> (P \<lbrakk>S \<inter> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q))\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  next
    fix t X assume \<open>(t, X) \<in> \<F> (P \<lbrakk>S \<inter> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q))\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      \<open>t \<notin> \<D> (P \<lbrakk>S \<inter> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q))\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    then obtain t_P t_Q X_P X_Q
      where * : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>t_P \<notin> \<D> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close> \<open>t_Q \<notin> \<D> Q\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((t_P, t_Q), S \<inter> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)))\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tj X_P (S \<inter> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q))) X_Q\<close>
      by (simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k') (metis (no_types) F_T ftF_Nil self_append_conv)
    from "*"(1-4) have \<open>t_P \<in> \<T> P - \<D> P\<close> \<open>t_Q \<in> \<T> Q - \<D> Q\<close> by (auto dest: F_T)
    from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_events_of[THEN iffD2, OF "$"(2)[OF this] "*"(5)]
    have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close> .
    moreover from "*"(6) have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tj X_P S X_Q\<close>
      by (meson Int_lower1 in_mono subsetI super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_mono)
    ultimately show \<open>(t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      using "*"(1, 3) by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  qed
qed

corollary (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_minimal_events_of :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q = P \<lbrakk>S \<inter> A\<rbrakk>\<^sub>\<checkmark> Q\<close> if \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q) \<subseteq> A\<close>
proof (rule trans[OF Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_minimal_events_of],
    rule trans[OF _ Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_minimal_events_of[symmetric]])
  show \<open>P \<lbrakk>S \<inter> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q))\<rbrakk>\<^sub>\<checkmark> Q = P \<lbrakk>S \<inter> A \<inter> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q))\<rbrakk>\<^sub>\<checkmark> Q\<close>
    using \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q) \<subseteq> A\<close> by (auto intro: arg_cong[where f = \<open>\<lambda>S. P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q\<close>])
qed


corollary Sync_is_restrictable_on_minimal_events_of :
  \<open>P \<lbrakk>S\<rbrakk> Q = P \<lbrakk>S \<inter> (\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q))\<rbrakk> Q\<close>
  by (metis Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_minimal_events_of Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_is_Sync)

corollary Sync_is_restrictable_on_superset_minimal_events_of :
  \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q) \<subseteq> A \<Longrightarrow> P \<lbrakk>S\<rbrakk> Q = P \<lbrakk>S \<inter> A\<rbrakk> Q\<close>
  by (metis Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_minimal_events_of Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_is_Sync)



corollary MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_minimal_events_of :
  \<open>(\<Union>l \<in> set L. \<alpha>\<^sub>m\<^sub>i\<^sub>n(P l)) \<subseteq> A \<Longrightarrow> \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l = \<^bold>\<lbrakk>S \<inter> A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l\<close>
proof (induct L rule: induct_list012)
  case 1 show ?case by simp
next
  case (2 l0) show ?case by simp
next
  case (3 l0 l1 L)
  from "3.prems" show ?case
    by (simp, subst "3.hyps"(2))
      (auto intro!: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_minimal_events_of
        dest!: minimal_events_of_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset[THEN set_mp])+
qed

corollary MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_minimal_events_of :
  \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l = \<^bold>\<lbrakk>S \<inter> (\<Union>l \<in> set L. \<alpha>\<^sub>m\<^sub>i\<^sub>n(P l))\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l\<close>
  using MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_minimal_events_of by blast


corollary MultiSync_is_restrictable_on_superset_minimal_events_of:
  \<open>(\<Union>m \<in> set_mset M. \<alpha>\<^sub>m\<^sub>i\<^sub>n(P m)) \<subseteq> B \<Longrightarrow> \<^bold>\<lbrakk>A\<^bold>\<rbrakk> m \<in># M. P m = \<^bold>\<lbrakk>A \<inter> B\<^bold>\<rbrakk> m \<in># M. P m\<close>
  by (induct M rule: induct_subset_mset_empty_single)
    (auto intro!: Sync_is_restrictable_on_superset_minimal_events_of
      dest!: minimal_events_of_MultiSync_subset[THEN set_mp])

corollary MultiSync_is_restrictable_on_minimal_events_of:
  \<open>\<^bold>\<lbrakk>A\<^bold>\<rbrakk> m \<in># M. P m = \<^bold>\<lbrakk>A \<inter> ((\<Union>m \<in> set_mset M. \<alpha>\<^sub>m\<^sub>i\<^sub>n(P m)))\<^bold>\<rbrakk> m \<in># M. P m\<close>
  by (metis MultiSync_is_restrictable_on_superset_minimal_events_of subsetI)


(*<*)
end
  (*>*)

