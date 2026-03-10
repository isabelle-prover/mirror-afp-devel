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


chapter \<open>Other Laws\<close>


(*<*)
theory CSP_PTick_Laws
  imports Multi_Sequential_Composition_Generalized
    Multi_Synchronization_Product_Generalized
    "HOL-CSP_RS" Step_CSP_PTick_Laws_Extended CSP_PTick_Monotonicities
begin
  (*>*)


declare [[metis_instantiate]]


section \<open>Laws of Renaming\<close>

subsection \<open>Renaming and Sequential Composition\<close>

lemma FD_Renaming_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>Renaming P f g \<^bold>;\<^sub>\<checkmark> (\<lambda>g_r. \<sqinter>r \<in> {r \<in> \<^bold>\<checkmark>\<^bold>s(P). g_r = g r}. Renaming (Q r) f g')
   \<sqsubseteq>\<^sub>F\<^sub>D Renaming (P \<^bold>;\<^sub>\<checkmark> Q) f g'\<close> (is \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
proof (rule failure_divergence_refine_optimizedI)
  fix s assume \<open>s \<in> \<D> ?rhs\<close>
  then obtain s1 s2 where * : \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') s1 @ s2\<close> \<open>tF s1\<close>
    \<open>ftF s2\<close> \<open>s1 \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
    unfolding D_Renaming by blast
  from "*"(4) consider (D_P) t1 t2 where \<open>s1 = map (ev \<circ> of_ev) t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close> \<open>tF t1\<close> \<open>ftF t2\<close>
    | (D_Q) t1 r t2 where \<open>s1 = map (ev \<circ> of_ev) t1 @ t2\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>t1 \<notin> \<D> P\<close> \<open>tF t1\<close> \<open>t2 \<in> \<D> (Q r)\<close>
    by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis D_imp_front_tickFree)
  thus \<open>s \<in> \<D> ?lhs\<close>
  proof cases
    case D_P
    from D_P(2, 3) have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 \<in> \<D> (Renaming P f g)\<close>
      by (auto simp add: D_Renaming intro: front_tickFree_Nil)
    hence \<open>map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) \<in> \<D> ?lhs\<close>
      unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs
      by (metis (mono_tags, lifting) front_tickFree_Nil D_P(3)
          map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree append.right_neutral mem_Collect_eq Un_iff)
    also have \<open>map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) =
               map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1)\<close>
      by (simp add: \<open>tF t1\<close> tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is)
    finally show \<open>s \<in> \<D> ?lhs\<close>
      by (auto simp add: "*"(1) D_P(1) intro!: is_processT7)
        (metis list.map_comp map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_map_ev_comp,
          use "*"(2, 3) D_P(1) front_tickFree_append map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_append_iff in blast)
  next
    case D_Q
    from "*"(2) D_Q(1, 5) have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2 \<in> \<D> (Renaming (Q r) f g')\<close>
      by (auto simp add: D_Renaming intro: front_tickFree_Nil)
    hence \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2 \<in> \<D> (\<sqinter>r' \<in> {r' \<in> \<^bold>\<checkmark>\<^bold>s(P). g r = g r'}. Renaming (Q r') f g')\<close>
      by (simp add: D_GlobalNdet)
        (metis D_Q(2, 3) is_processT9 strict_ticks_of_memI)
    moreover from D_Q(2) have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 @ [\<checkmark>(g r)] \<in> \<T> (Renaming P f g)\<close>
      by (auto simp add: T_Renaming)
    moreover have \<open>tF (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1)\<close>
      by (simp add: D_Q(4) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
    ultimately have \<open>map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) @
                     map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2 \<in> \<D> ?lhs\<close>
      unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    with "*"(2, 3) have \<open>map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) @
                         map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2 @ s2 \<in> \<D> ?lhs\<close>
      by (auto simp add: D_Q(1) comp_assoc map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree
          intro!: is_processT7[of \<open>_ @ _\<close>, simplified])
    also from D_Q(4) have \<open>map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) @
                           map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2 @ s2 = s\<close>
      by (simp add: "*"(1) D_Q(1))
        (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_sel(1) in_set_conv_decomp tickFree_Cons_iff tickFree_append_iff)
    finally show \<open>s \<in> \<D> ?lhs\<close> .
  qed
next
  assume subset_div : \<open>\<D> ?rhs \<subseteq> \<D> ?lhs\<close>
  fix s X assume \<open>(s, X) \<in> \<F> ?rhs\<close>
  then consider \<open>s \<in> \<D> ?rhs\<close>
    | (fail) s1 where \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') s1\<close>
      \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g' -` X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> \<open>s1 \<notin> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
    by (simp add: Renaming_projs)
      (metis (no_types, opaque_lifting) front_tickFree_Nil front_tickFree_iff_tickFree_butlast
        front_tickFree_Cons_iff[of \<open>last s\<close> \<open>[]\<close>] map_butlast[of \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g'\<close>]
        map_is_Nil_conv[of \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g'\<close> \<open>[]\<close>] map_is_Nil_conv[of \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g'\<close>]
        append_self_conv[of \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') _\<close> \<open>[]\<close>] F_imp_front_tickFree
        snoc_eq_iff_butlast[of \<open>butlast s\<close> \<open>last s\<close> s]
        div_butlast_when_non_tickFree_iff non_tickFree_imp_not_Nil)
  thus \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof cases
    from subset_div D_F show \<open>s \<in> \<D> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> by blast
  next
    case fail
    from fail(2, 3)
    consider (F_P) t1 where \<open>s1 = map (ev \<circ> of_ev) t1\<close> \<open>(t1, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g' -` X)) \<in> \<F> P\<close> \<open>tF t1\<close>
      | (F_Q) t1 r t2 where \<open>s1 = map (ev \<circ> of_ev) t1 @ t2\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t1\<close> \<open>t1 \<notin> \<D> P\<close> \<open>(t2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g' -` X) \<in> \<F> (Q r)\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis F_imp_front_tickFree)
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      case F_P
      have \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) = ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g' -` X)\<close> for X
      proof (rule set_eqI)
        show \<open>e \<in> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<longleftrightarrow>
                  e \<in> ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g' -` X)\<close> for e
          by (cases e, auto simp add: ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def image_iff)
            (metis Int_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(9) rangeI vimage_eq,
              metis IntI UNIV_I event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) image_eqI)
      qed
      with F_P(2) have \<open>(map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (Renaming P f g)\<close>
        by (auto simp add: F_Renaming)
      with F_P(3) have \<open>(map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1), X) \<in> \<F> ?lhs\<close>
        by (fastforce simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
      also have \<open>map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) = s\<close>
        by (simp add: fail(1) F_P(1))
          (metis F_P(3) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_sel(1) in_set_conv_decomp tickFree_Cons_iff tickFree_append_iff)
      finally show \<open>(s, X) \<in> \<F> ?lhs\<close> .
    next
      case F_Q
      with F_Q(4) have \<open>(map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2, X) \<in> \<F> (Renaming (Q r) f g')\<close>
        by (auto simp add: F_Renaming)
      hence \<open>(map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2, X) \<in>
             \<F> (\<sqinter>r' \<in> {r' \<in> \<^bold>\<checkmark>\<^bold>s(P). g r = g r'}. Renaming (Q r') f g')\<close>
        by (simp add: F_GlobalNdet)
          (metis F_Q(2, 4) is_processT9 strict_ticks_of_memI)
      moreover from F_Q(2) have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 @ [\<checkmark>(g r)] \<in> \<T> (Renaming P f g)\<close>
        by (auto simp add: T_Renaming)
      moreover have \<open>tF (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1)\<close>
        by (simp add: F_Q(3) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
      ultimately have \<open>(map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) @
                        map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2, X) \<in> \<F> ?lhs\<close>
        unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by fast
      also have \<open>map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) @ map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2 = s\<close>
        by (simp add: fail(1) F_Q(1))
          (metis F_Q(3) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_sel(1) in_set_conv_decomp
            tickFree_Cons_iff tickFree_append_iff)
      finally show \<open>(s, X) \<in> \<F> ?lhs\<close> .
    qed
  qed
qed



lemma inj_on_Renaming_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>Renaming (P \<^bold>;\<^sub>\<checkmark> Q) f g' =
   Renaming P f g \<^bold>;\<^sub>\<checkmark> (\<lambda>g_r. Renaming (Q (THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> g_r = g r)) f g')\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>inj_on g \<^bold>\<checkmark>\<^bold>s(P)\<close>
  \<comment>\<open>This assumption is necessary, otherwise we cannot know which tick triggered \<^term>\<open>Q\<close>.\<close>
proof (rule FD_antisym)
  show \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>
  proof (rule failure_divergence_refine_optimizedI)
    fix s assume \<open>s \<in> \<D> ?rhs\<close>
    then consider (D_P) s1 s2 where \<open>s = map (ev \<circ> of_ev) s1 @ s2\<close> \<open>s1 \<in> \<D> (Renaming P f g)\<close> \<open>tF s1\<close> \<open>ftF s2\<close>
      | (D_Q) s1 g_r s2 where \<open>s = map (ev \<circ> of_ev) s1 @ s2\<close> \<open>s1 @ [\<checkmark>(g_r)] \<in> \<T> (Renaming P f g)\<close>
        \<open>s1 \<notin> \<D> (Renaming P f g)\<close> \<open>tF s1\<close> \<open>s2 \<in> \<D> (Renaming (Q (THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> g_r = g r)) f g')\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (use D_imp_front_tickFree in blast)
    thus \<open>s \<in> \<D> ?lhs\<close>
    proof cases
      case D_P
      from D_P(2) obtain t1 t2
        where * : \<open>s1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 @ t2\<close> \<open>tF t1\<close> \<open>ftF t2\<close> \<open>t1 \<in> \<D> P\<close>
        unfolding D_Renaming by blast
      from "*"(2, 4) have \<open>map (ev \<circ> of_ev) t1 \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs intro: front_tickFree_Nil)
      hence \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1) \<in> \<D> ?lhs\<close>
        unfolding D_Renaming mem_Collect_eq
        by (metis (mono_tags, lifting) front_tickFree_Nil tickFree_map_ev_comp append.right_neutral)
      also have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1) =
                 map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1)\<close>
        by simp (metis "*"(2) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_sel(1) in_set_conv_decomp tickFree_Cons_iff tickFree_append_iff)
      finally show \<open>s \<in> \<D> ?lhs\<close>
        by (auto simp add: D_P(1, 4) "*"(1) front_tickFree_append comp_assoc intro!: is_processT7)
    next
      case D_Q
      have \<open>s1 @ [\<checkmark>(g_r)] \<notin> \<D> (Renaming P f g)\<close> by (meson D_Q(3) is_processT9)
      with D_Q(2-4) obtain t1 r
        where * : \<open>g_r = g r\<close> \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close> \<open>s1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> P\<close>
        by (auto simp add: Renaming_projs append_eq_map_conv tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
          (metis append_Nil2 front_tickFree_Nil is_processT9 map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree strict_ticks_of_memI)
      from "*"(1, 2) \<open>inj_on g \<^bold>\<checkmark>\<^bold>s(P)\<close> have \<open>(THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> g_r = g r) = r\<close>
        by (auto dest: inj_onD)
      with D_Q(5) have \<open>s2 \<in> \<D> (Renaming (Q r) f g')\<close> by simp
      then obtain t2 t3
        where ** : \<open>s2 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2 @ t3\<close> \<open>tF t2\<close> \<open>ftF t3\<close> \<open>t2 \<in> \<D> (Q r)\<close>
        unfolding D_Renaming by blast
      from "*"(4) "**"(4) have \<open>map (ev \<circ> of_ev) t1 @ t2 \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis append_T_imp_tickFree not_Cons_self)
      with "**"(2) have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1 @ t2) \<in> \<D> ?lhs\<close>
        unfolding D_Renaming mem_Collect_eq
        by (metis append.right_neutral front_tickFree_Nil tickFree_append_iff tickFree_map_ev_comp)
      moreover have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1 @ t2) @ t3 = s\<close>
        by (simp add: D_Q(1) "*"(3) "**"(1))
          (metis "*"(3) D_Q(4) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_sel(1) in_set_conv_decomp
            map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_Cons_iff tickFree_append_iff)
      ultimately show \<open>s \<in> \<D> ?lhs\<close>
        by (auto simp add: "**"(3) intro!: is_processT7[of \<open>_ @ _\<close>, simplified])
          (use "**"(1) D_Q(1) in force, use "**"(2) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree in blast)
    qed
  next
    assume subset_div : \<open>\<D> ?rhs \<subseteq> \<D> ?lhs\<close>
    fix s X assume \<open>(s, X) \<in> \<F> ?rhs\<close>
    then consider \<open>s \<in> \<D> ?rhs\<close>
      | (F_P) s1 where \<open>s = map (ev \<circ> of_ev) s1\<close> \<open>(s1, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (Renaming P f g)\<close> \<open>s1 \<notin> \<D> (Renaming P f g)\<close> \<open>tF s1\<close>
      | (F_Q) s1 g_r s2 where \<open>s = map (ev \<circ> of_ev) s1 @ s2\<close> \<open>s1 @ [\<checkmark>(g_r)] \<in> \<T> (Renaming P f g)\<close>
        \<open>s1 \<notin> \<D> (Renaming P f g)\<close> \<open>tF s1\<close> \<open>(s2, X) \<in> \<F> (Renaming (Q (THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> g_r = g r)) f g')\<close>
        \<open>s2 \<notin> \<D> (Renaming (Q (THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> g_r = g r)) f g')\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
        (metis (no_types, lifting) F_imp_front_tickFree front_tickFree_charn self_append_conv)
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      from subset_div D_F show \<open>s \<in> \<D> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> by blast
    next
      case F_P
      from F_P(2, 3) obtain t1
        where * : \<open>s1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1\<close> \<open>(t1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> P\<close>
        unfolding Renaming_projs by blast
      have \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) = ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g' -` X)\<close> for X
      proof (rule set_eqI)
        show \<open>e \<in> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<longleftrightarrow>
              e \<in> ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g' -` X)\<close> for e
          by (cases e, auto simp add: ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def image_iff)
            (metis Int_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(9) rangeI vimage_eq,
              metis IntI UNIV_I event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) image_eqI)
      qed
      with "*"(2) have \<open>(t1, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g' -` X)) \<in> \<F> P\<close> by simp
      hence \<open>(map (ev \<circ> of_ev) t1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g' -` X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          (metis "*"(1) F_P(4) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
      hence \<open>(map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1), X) \<in> \<F> ?lhs\<close>
        unfolding F_Renaming by blast
      also have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1) = s\<close>
        by (simp add: F_P(1) "*"(1))
          (metis "*"(1) F_P(4) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_sel(1) in_set_conv_decomp
            map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_Cons_iff tickFree_append_iff)
      finally show \<open>(s, X) \<in> \<F> ?lhs\<close> .
    next
      case F_Q
      have \<open>s1 @ [\<checkmark>(g_r)] \<notin> \<D> (Renaming P f g)\<close> by (meson F_Q(3) is_processT9)
      with F_Q(2-4) obtain t1 r
        where * : \<open>g_r = g r\<close> \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close> \<open>s1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> P\<close>
        by (auto simp add: Renaming_projs append_eq_map_conv tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
          (metis append_Nil2 front_tickFree_Nil is_processT9 map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree strict_ticks_of_memI)
      from "*"(1, 2) \<open>inj_on g \<^bold>\<checkmark>\<^bold>s(P)\<close> have \<open>(THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> g_r = g r) = r\<close>
        by (auto dest: inj_onD)
      with F_Q(5, 6) have \<open>(s2, X) \<in> \<F> (Renaming (Q r) f g')\<close>
        \<open>s2 \<notin> \<D> (Renaming (Q r) f g')\<close> by simp_all
      then obtain t2 where ** : \<open>s2 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2\<close> \<open>(t2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g' -` X) \<in> \<F> (Q r)\<close>
        unfolding Renaming_projs by blast
      from "*"(4) "**"(2) have \<open>(map (ev \<circ> of_ev) t1 @ t2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g' -` X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis append_T_imp_tickFree not_Cons_self2)
      hence \<open>(map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1 @ t2), X) \<in> \<F> ?lhs\<close>
        unfolding F_Renaming by blast
      also have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1 @ t2) = s\<close>
        by (simp add: F_Q(1) "*"(3) "**"(1))
          (metis "*"(3) F_Q(4) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_sel(1) in_set_conv_decomp
            map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_Cons_iff tickFree_append_iff)
      finally show \<open>(s, X) \<in> \<F> ?lhs\<close> .
    qed
  qed
next

  have \<open>?rhs = Renaming P f g \<^bold>;\<^sub>\<checkmark> (\<lambda>g_r. \<sqinter>r \<in> {r \<in> \<^bold>\<checkmark>\<^bold>s(P). g_r = g r}. Renaming (Q r) f g')\<close>
  proof (rule mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq)
    show \<open>Renaming P f g = Renaming P f g\<close> ..
  next
    fix g_r assume \<open>g_r \<in> \<^bold>\<checkmark>\<^bold>s(Renaming P f g)\<close>
    then obtain s s1 where \<open>s @ [\<checkmark>(g_r)] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close> \<open>s1 \<in> \<T> P\<close> \<open>s1 \<notin> \<D> P\<close>
      by (simp add: strict_ticks_of_def Renaming_projs)
        (metis (no_types, opaque_lifting) T_imp_front_tickFree append_Nil2 butlast_snoc
          div_butlast_when_non_tickFree_iff front_tickFree_Nil
          front_tickFree_iff_tickFree_butlast front_tickFree_single map_butlast)
    from this(1) obtain s1' r where \<open>g_r = g r\<close> \<open>s1 = s1' @ [\<checkmark>(r)]\<close>
      by (cases s1 rule: rev_cases) (auto simp add: tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
    with \<open>s1 \<in> \<T> P\<close> \<open>s1 \<notin> \<D> P\<close> have \<open>s1' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>s1' @ [\<checkmark>(r)] \<notin> \<D> P\<close> by simp_all
    hence \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close> unfolding strict_ticks_of_def by blast
    have \<open>{r \<in> \<^bold>\<checkmark>\<^bold>s(P). g_r = g r} = {r}\<close>
      by (auto simp add: \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close> \<open>g_r = g r\<close> intro: inj_onD[OF \<open>inj_on g \<^bold>\<checkmark>\<^bold>s(P)\<close>])
    moreover have \<open>(THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> g_r = g r) = r\<close>
      using calculation by blast
    ultimately have \<open>Q (THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> g_r = g r) =
                     GlobalNdet {r \<in> \<^bold>\<checkmark>\<^bold>s(P). g_r = g r} Q\<close> by simp
    thus \<open>Renaming (Q (THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> g_r = g r)) f g' =
          (\<sqinter>r \<in> {r \<in> \<^bold>\<checkmark>\<^bold>s(P). g_r = g r}. Renaming (Q r) f g')\<close>
      by (simp flip: Renaming_distrib_GlobalNdet)
  qed
  thus \<open>?rhs \<sqsubseteq>\<^sub>F\<^sub>D ?lhs\<close> by (simp add: FD_Renaming_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
qed


text \<open>When \<^typ>\<open>'r\<close> is set on \<^typ>\<open>unit\<close>, we recover the version that we had before the generalization.\<close>
lemma \<open>Renaming (P \<^bold>;\<^sub>\<checkmark> Q) f g = Renaming P f g \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Renaming (Q ()) f g)\<close>
  by (subst inj_on_Renaming_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[where g = g]) (auto intro: inj_onI)


lemma TickSwap_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [simp] :
  \<open>TickSwap (P \<^bold>;\<^sub>\<checkmark> Q) = TickSwap P \<^bold>;\<^sub>\<checkmark> (\<lambda>(s, r). TickSwap (Q (r, s)))\<close> (is \<open>?lhs = ?rhs\<close>)
proof -
  have \<open>?lhs = Renaming (P \<^bold>;\<^sub>\<checkmark> Q) id prod.swap\<close> by (simp add: TickSwap_is_Renaming)
  also have \<open>\<dots> = Renaming P id prod.swap \<^bold>;\<^sub>\<checkmark>
                  (\<lambda>s_r. Renaming (Q (THE r_s. r_s \<in> strict_ticks_of P \<and>
                                               s_r = prod.swap r_s)) id prod.swap)\<close>
    (is \<open>_ = _ \<^bold>;\<^sub>\<checkmark> ?rhs'\<close>) by (simp add: inj_on_Renaming_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  also have \<open>\<dots> = ?rhs\<close>
  proof (rule mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq, unfold TickSwap_is_Renaming)
    show \<open>Renaming P id prod.swap = Renaming P id prod.swap\<close> ..
  next
    fix s_r assume \<open>s_r \<in> strict_ticks_of (Renaming P id prod.swap)\<close>
    then obtain r s where \<open>(r, s) \<in> strict_ticks_of P\<close> \<open>s_r = (s, r)\<close>
      by (auto simp flip: TickSwap_is_Renaming)
    hence \<open>(THE r_s. r_s \<in> strict_ticks_of P \<and> s_r = prod.swap r_s) = (r, s)\<close> by auto
    thus \<open>Renaming (Q (THE r_s. r_s \<in> strict_ticks_of P \<and> s_r = prod.swap r_s)) id prod.swap =
          (case s_r of (s, r) \<Rightarrow> Renaming (Q (r, s)) id prod.swap)\<close>
      by (simp add: \<open>s_r = (s, r)\<close>)
  qed
  finally show \<open>?lhs = ?rhs\<close> .
qed

lemma TickSwap_is_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff [simp] :
  \<open>TickSwap P = Q \<^bold>;\<^sub>\<checkmark> R \<longleftrightarrow> P = TickSwap Q \<^bold>;\<^sub>\<checkmark> (\<lambda>(r, s). TickSwap (R (s, r)))\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)




subsection \<open>Renaming and Synchronization Product\<close>

theorem (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) inj_RenamingEv_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>RenamingEv (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) f = RenamingEv P f \<lbrakk>f ` S\<rbrakk>\<^sub>\<checkmark> RenamingEv Q f\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>inj f\<close>
proof -
  let ?fun = \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f id\<close>
  let ?map = \<open>map ?fun\<close>
  let ?R   = \<open>\<lambda>P. RenamingEv P f\<close>
  show \<open>?lhs = ?rhs\<close>
  proof (rule Process_eq_optimizedI)
    fix t assume \<open>t \<in> \<D> ?lhs\<close>
    then obtain t1 t2 where * : \<open>t = ?map t1 @ t2\<close>
      \<open>tF t1\<close> \<open>ftF t2\<close> \<open>t1 \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> unfolding D_Renaming by blast
    from "*"(4) obtain u v t_P t_Q where ** : \<open>t1 = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
      \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
      \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
      unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff_weak [THEN iffD2, OF \<open>inj f\<close> "**"(4)]
    have \<open>?map u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map t_P, ?map t_Q), f ` S)\<close> .
    moreover from "**"(5) have \<open>?map t_P \<in> \<D> (?R P) \<and> ?map t_Q \<in> \<T> (?R Q) \<or>
                              ?map t_P \<in> \<T> (?R P) \<and> ?map t_Q \<in> \<D> (?R Q)\<close>
      by (auto simp add: Renaming_projs dest: D_T)
        (metis "**"(2,4) append_self_conv front_tickFree_map_tick_iff
          list.map_disc_iff tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)+
    moreover have \<open>t = ?map u @ (?map v @ t2)\<close> by (simp add: "*"(1) "**"(1))
    moreover have \<open>tF (?map u)\<close> by (simp add: "**"(2) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
    moreover from "*"(2,3) "**"(1) have \<open>ftF (?map v @ t2)\<close>
      using front_tickFree_append map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_append_iff by blast
    ultimately show \<open>t \<in> \<D> ?rhs\<close> unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
  next
    fix t assume \<open>t \<in> \<D> ?rhs\<close>
    then obtain u v t_P t_Q where * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
      \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), f ` S)\<close>
      \<open>t_P \<in> \<D> (?R P) \<and> t_Q \<in> \<T> (?R Q) \<or> t_P \<in> \<T> (?R P) \<and> t_Q \<in> \<D> (?R Q)\<close>
      unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    from "*"(5) show \<open>t \<in> \<D> ?lhs\<close>
    proof (elim disjE conjE)
      assume \<open>t_P \<in> \<D> (?R P)\<close> \<open>t_Q \<in> \<T> (?R Q)\<close>
      from \<open>t_P \<in> \<D> (?R P)\<close> obtain t_P1 t_P2
        where ** : \<open>t_P = ?map t_P1 @ t_P2\<close> \<open>tF t_P1\<close> \<open>ftF t_P2\<close> \<open>t_P1 \<in> \<D> P\<close>
        unfolding D_Renaming by blast
      from \<open>t_Q \<in> \<T> (?R Q)\<close> consider (T_Q) t_Q1 where \<open>t_Q = ?map t_Q1\<close> \<open>t_Q1 \<in> \<T> Q\<close>
        | (D_Q) t_Q1 t_Q2 where \<open>t_Q = ?map t_Q1 @ t_Q2\<close> \<open>tF t_Q1\<close> \<open>ftF t_Q2\<close> \<open>t_Q1 \<in> \<D> Q\<close>
        unfolding T_Renaming by blast
      thus \<open>t \<in> \<D> ?lhs\<close>
      proof cases
        case T_Q
        from "*"(4)[unfolded "**"(1) T_Q(1), THEN setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL]
        obtain u1 u2 t_Q11 t_Q12 where *** : \<open>u = u1 @ u2\<close> \<open>?map t_Q1 = t_Q11 @ t_Q12\<close>
          \<open>u1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map t_P1, t_Q11), f ` S)\<close> by blast
        obtain t_Q11' where \<open>t_Q11' \<le> t_Q1\<close> \<open>t_Q11 = ?map t_Q11'\<close> 
          by (metis "***"(2) map_eq_append_conv Prefix_Order.prefixI)
        from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff_strong
          [THEN iffD1, OF \<open>inj f\<close> "***"(3)[unfolded this]]
        obtain u1' where **** : \<open>u1 = ?map u1'\<close>
          \<open>u1' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P1, t_Q11'), S)\<close> by blast
        from "*"(2) "***"(1) "****"(1) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree
          T_Q(2) \<open>t_Q11' \<le> t_Q1\<close> is_processT3_TR
        have \<open>u1' = u1' @ []\<close> \<open>tF u1'\<close> \<open>ftF []\<close> \<open>t_Q11' \<in> \<T> Q\<close> by simp_all blast
        with "****"(2) "**"(4) have \<open>u1' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
          unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
        moreover have \<open>t = ?map u1' @ (u2 @ v)\<close> by (simp add: "*"(1) "***"(1) "****"(1))
        moreover have \<open>ftF (u2 @ v)\<close>
          using "*"(2,3) "***"(1) front_tickFree_append tickFree_append_iff by blast
        ultimately show \<open>t \<in> \<D> ?lhs\<close> unfolding D_Renaming using \<open>tF u1'\<close> by blast
      next
        case D_Q
        have \<open>?map t_P1 \<le> t_P\<close> \<open>?map t_Q1 \<le> t_Q\<close>
          by (simp_all add: "**"(1) D_Q(1))
        from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_le_prefixLR[OF "*"(4) this] show \<open>t \<in> \<D> ?lhs\<close>
        proof (elim disjE exE conjE)
          fix u1 t_Q1' assume *** : \<open>u1 \<le> u\<close> \<open>t_Q1' \<le> ?map t_Q1\<close>
            \<open>u1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map t_P1, t_Q1'), f ` S)\<close>
          obtain u2 where \<open>u = u1 @ u2\<close> using "***"(1) prefixE by blast
          obtain t_Q1'' where \<open>t_Q1' = ?map t_Q1''\<close> \<open>t_Q1'' \<le> t_Q1\<close>
            by (metis "***"(2) prefixE prefixI map_eq_append_conv)
          from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff_strong
            [THEN iffD1, OF \<open>inj f\<close> "***"(3)[unfolded \<open>t_Q1' = ?map t_Q1''\<close>]]
          obtain u1' where **** : \<open>u1 = ?map u1'\<close>
            \<open>u1' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P1, t_Q1''), S)\<close> by blast
          have \<open>u1' = u1' @ []\<close> \<open>ftF []\<close> by simp_all
          moreover from "**"(2) "****"(2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree_imp
          have \<open>tF u1'\<close> by blast
          moreover from D_Q(4) D_T \<open>t_Q1'' \<le> t_Q1\<close> is_processT3_TR
          have \<open>t_Q1'' \<in> \<T> Q\<close> by blast
          ultimately have \<open>u1' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
            unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k using \<open>t_P1 \<in> \<D> P\<close> "****"(2) by blast
          moreover from "*"(1-3) "****"(1)
          have \<open>t = ?map u1' @ (u2 @ v)\<close> \<open>ftF (u2 @ v)\<close>
            by (auto simp add: \<open>u = u1 @ u2\<close> front_tickFree_append)
          ultimately show \<open>t \<in> \<D> ?lhs\<close>
            unfolding D_Renaming using \<open>tF u1'\<close> by blast
        next
          fix u1 t_P1' assume *** : \<open>u1 \<le> u\<close> \<open>t_P1' \<le> ?map t_P1\<close>
            \<open>u1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P1', ?map t_Q1), f ` S)\<close>
          obtain u2 where \<open>u = u1 @ u2\<close> using "***"(1) prefixE by blast
          obtain t_P1'' where \<open>t_P1' = ?map t_P1''\<close> \<open>t_P1'' \<le> t_P1\<close>
            by (metis "***"(2) prefixE prefixI map_eq_append_conv)
          from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff_strong
            [THEN iffD1, OF \<open>inj f\<close> "***"(3)[unfolded \<open>t_P1' = ?map t_P1''\<close>]]
          obtain u1' where **** : \<open>u1 = ?map u1'\<close>
            \<open>u1' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P1'', t_Q1), S)\<close> by blast
          have \<open>u1' = u1' @ []\<close> \<open>ftF []\<close> by simp_all
          moreover from D_Q(2) "****"(2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree_imp
          have \<open>tF u1'\<close> by blast
          moreover from "**"(4) D_T \<open>t_P1'' \<le> t_P1\<close> is_processT3_TR
          have \<open>t_P1'' \<in> \<T> P\<close> by blast
          ultimately have \<open>u1' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
            unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k using \<open>t_Q1 \<in> \<D> Q\<close> "****"(2) by blast
          moreover from "*"(1-3) "****"(1)
          have \<open>t = ?map u1' @ (u2 @ v)\<close> \<open>ftF (u2 @ v)\<close>
            by (auto simp add: \<open>u = u1 @ u2\<close> front_tickFree_append)
          ultimately show \<open>t \<in> \<D> ?lhs\<close>
            unfolding D_Renaming using \<open>tF u1'\<close> by blast
        qed
      qed
    next
      assume \<open>t_Q \<in> \<D> (?R Q)\<close> \<open>t_P \<in> \<T> (?R P)\<close>
      from \<open>t_Q \<in> \<D> (?R Q)\<close> obtain t_Q1 t_Q2
        where ** : \<open>t_Q = ?map t_Q1 @ t_Q2\<close> \<open>tF t_Q1\<close> \<open>ftF t_Q2\<close> \<open>t_Q1 \<in> \<D> Q\<close>
        unfolding D_Renaming by blast
      from \<open>t_P \<in> \<T> (?R P)\<close> consider (T_P) t_P1 where \<open>t_P = ?map t_P1\<close> \<open>t_P1 \<in> \<T> P\<close>
        | (D_P) t_P1 t_P2 where \<open>t_P = ?map t_P1 @ t_P2\<close> \<open>tF t_P1\<close> \<open>ftF t_P2\<close> \<open>t_P1 \<in> \<D> P\<close>
        unfolding T_Renaming by blast
      thus \<open>t \<in> \<D> ?lhs\<close>
      proof cases
        case T_P
        from "*"(4)[unfolded "**"(1) T_P(1), THEN setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendR]
        obtain u1 u2 t_P11 t_P12 where *** : \<open>u = u1 @ u2\<close> \<open>?map t_P1 = t_P11 @ t_P12\<close>
          \<open>u1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P11, ?map t_Q1), f ` S)\<close> by blast
        obtain t_P11' where \<open>t_P11' \<le> t_P1\<close> \<open>t_P11 = ?map t_P11'\<close> 
          by (metis "***"(2) map_eq_append_conv Prefix_Order.prefixI)
        from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff_strong
          [THEN iffD1, OF \<open>inj f\<close> "***"(3)[unfolded this]]
        obtain u1' where **** : \<open>u1 = ?map u1'\<close>
          \<open>u1' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P11', t_Q1), S)\<close> by blast
        from "*"(2) "***"(1) "****"(1) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree
          T_P(2) \<open>t_P11' \<le> t_P1\<close> is_processT3_TR
        have \<open>u1' = u1' @ []\<close> \<open>tF u1'\<close> \<open>ftF []\<close> \<open>t_P11' \<in> \<T> P\<close> by simp_all blast
        with "****"(2) "**"(4) have \<open>u1' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
          unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
        moreover have \<open>t = ?map u1' @ (u2 @ v)\<close> by (simp add: "*"(1) "***"(1) "****"(1))
        moreover have \<open>ftF (u2 @ v)\<close>
          using "*"(2,3) "***"(1) front_tickFree_append tickFree_append_iff by blast
        ultimately show \<open>t \<in> \<D> ?lhs\<close> unfolding D_Renaming using \<open>tF u1'\<close> by blast
      next
        case D_P
        have \<open>?map t_P1 \<le> t_P\<close> \<open>?map t_Q1 \<le> t_Q\<close>
          by (simp_all add: "**"(1) D_P(1))
        from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_le_prefixLR[OF "*"(4) this] show \<open>t \<in> \<D> ?lhs\<close>
        proof (elim disjE exE conjE)
          fix u1 t_Q1' assume *** : \<open>u1 \<le> u\<close> \<open>t_Q1' \<le> ?map t_Q1\<close>
            \<open>u1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map t_P1, t_Q1'), f ` S)\<close>
          obtain u2 where \<open>u = u1 @ u2\<close> using "***"(1) prefixE by blast
          obtain t_Q1'' where \<open>t_Q1' = ?map t_Q1''\<close> \<open>t_Q1'' \<le> t_Q1\<close>
            by (metis "***"(2) prefixE prefixI map_eq_append_conv)
          from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff_strong
            [THEN iffD1, OF \<open>inj f\<close> "***"(3)[unfolded \<open>t_Q1' = ?map t_Q1''\<close>]]
          obtain u1' where **** : \<open>u1 = ?map u1'\<close>
            \<open>u1' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P1, t_Q1''), S)\<close> by blast
          have \<open>u1' = u1' @ []\<close> \<open>ftF []\<close> by simp_all
          moreover from D_P(2) "****"(2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree_imp
          have \<open>tF u1'\<close> by blast
          moreover from "**"(4) D_T \<open>t_Q1'' \<le> t_Q1\<close> is_processT3_TR
          have \<open>t_Q1'' \<in> \<T> Q\<close> by blast
          ultimately have \<open>u1' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
            unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k using \<open>t_P1 \<in> \<D> P\<close> "****"(2) by blast
          moreover from "*"(1-3) "****"(1)
          have \<open>t = ?map u1' @ (u2 @ v)\<close> \<open>ftF (u2 @ v)\<close>
            by (auto simp add: \<open>u = u1 @ u2\<close> front_tickFree_append)
          ultimately show \<open>t \<in> \<D> ?lhs\<close>
            unfolding D_Renaming using \<open>tF u1'\<close> by blast
        next
          fix u1 t_P1' assume *** : \<open>u1 \<le> u\<close> \<open>t_P1' \<le> ?map t_P1\<close>
            \<open>u1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P1', ?map t_Q1), f ` S)\<close>
          obtain u2 where \<open>u = u1 @ u2\<close> using "***"(1) prefixE by blast
          obtain t_P1'' where \<open>t_P1' = ?map t_P1''\<close> \<open>t_P1'' \<le> t_P1\<close>
            by (metis "***"(2) prefixE prefixI map_eq_append_conv)
          from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff_strong
            [THEN iffD1, OF \<open>inj f\<close> "***"(3)[unfolded \<open>t_P1' = ?map t_P1''\<close>]]
          obtain u1' where **** : \<open>u1 = ?map u1'\<close>
            \<open>u1' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P1'', t_Q1), S)\<close> by blast
          have \<open>u1' = u1' @ []\<close> \<open>ftF []\<close> by simp_all
          moreover from "**"(2) "****"(2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree_imp
          have \<open>tF u1'\<close> by blast
          moreover from D_P(4) D_T \<open>t_P1'' \<le> t_P1\<close> is_processT3_TR
          have \<open>t_P1'' \<in> \<T> P\<close> by blast
          ultimately have \<open>u1' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
            unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k using \<open>t_Q1 \<in> \<D> Q\<close> "****"(2) by blast
          moreover from "*"(1-3) "****"(1)
          have \<open>t = ?map u1' @ (u2 @ v)\<close> \<open>ftF (u2 @ v)\<close>
            by (auto simp add: \<open>u = u1 @ u2\<close> front_tickFree_append)
          ultimately show \<open>t \<in> \<D> ?lhs\<close>
            unfolding D_Renaming using \<open>tF u1'\<close> by blast
        qed
      qed
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    then obtain t' where \<open>t = ?map t'\<close>
      and * : \<open>(t', ?fun -` X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      unfolding Renaming_projs by blast
    have \<open>t' \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    proof (rule notI)
      assume \<open>t' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      hence \<open>t \<in> \<D> ?lhs\<close>
        by (simp add: \<open>t = ?map t'\<close> D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_Renaming)
          (metis (no_types) append_Nil2 front_tickFree_Nil map_append map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree)
      with \<open>t \<notin> \<D> ?lhs\<close> show False ..
    qed
    with "*" obtain t_P t_Q X_P X_Q
      where ** : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
        \<open>?fun -` X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P S X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by fast
    from "**"(2, 3) F_T \<open>t' \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> append_Nil2 front_tickFree_Nil
    have \<open>t_P \<notin> \<D> P\<close> unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k' by blast
    from "**"(1, 3) F_T \<open>t' \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> append_Nil2 front_tickFree_Nil
    have \<open>t_Q \<notin> \<D> Q\<close> unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k' by blast
    have *** : \<open>?fun -` ?fun ` X_P = X_P\<close> \<open>?fun -` ?fun ` X_Q = X_Q\<close>
      by (simp add: set_eq_iff image_iff,
          metis (mono_tags, opaque_lifting) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inj_map_strong id_apply injD \<open>inj f\<close>)+
    from "**"(1) have \<open>(?map t_P, ?fun ` X_P) \<in> \<F> (?R P)\<close>
      by (subst (asm) "***"(1)[symmetric]) (auto simp add: F_Renaming)
    moreover {
      fix a assume \<open>?map t_P @ [ev a] \<in> \<T> (?R P)\<close> \<open>a \<notin> range f\<close>
      then consider t_P1 where \<open>?map t_P @ [ev a] = ?map t_P1\<close> \<open>t_P1 \<in> \<T> P\<close>
        | t_P1 t_P2 where \<open>?map t_P @ [ev a] = ?map t_P1 @ t_P2\<close> \<open>tF t_P1\<close> \<open>t_P1 \<in> \<D> P\<close>
        unfolding T_Renaming by blast
      hence False
      proof cases
        from \<open>a \<notin> range f\<close> show \<open>?map t_P @ [ev a] = ?map t_P1 \<Longrightarrow> False\<close> for t_P1
          by (auto simp add: append_eq_map_conv ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
      next
        fix t_P1 t_P2 assume \<open>?map t_P @ [ev a] = ?map t_P1 @ t_P2\<close> \<open>tF t_P1\<close> \<open>t_P1 \<in> \<D> P\<close>
        from this(1) \<open>a \<notin> range f\<close> have \<open>t_P1 \<le> t_P\<close>
          by (cases t_P2 rule: rev_cases, auto simp add: append_eq_map_conv ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
            (metis prefixI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inj_map inj_map_eq_map inj_on_id map_eq_append_conv \<open>inj f\<close>)
        with \<open>t_P1 \<in> \<D> P\<close> have \<open>t_P \<in> \<D> P\<close>
          by (metis "**"(1) F_imp_front_tickFree prefixE \<open>tF t_P1\<close> front_tickFree_append_iff
              is_processT7 tickFree_Nil tickFree_imp_front_tickFree)
        with \<open>t_P \<notin> \<D> P\<close> show False ..
      qed
    }
    ultimately have $ : \<open>(?map t_P, ?fun ` X_P \<union> {ev a | a. a \<notin> range f}) \<in> \<F> (?R P)\<close>
      using is_processT5_S7' by blast
    from "**"(2) have \<open>(?map t_Q, ?fun ` X_Q) \<in> \<F> (?R Q)\<close>
      by (subst (asm) "***"(2)[symmetric]) (auto simp add: F_Renaming)
    moreover {
      fix a assume \<open>?map t_Q @ [ev a] \<in> \<T> (?R Q)\<close> \<open>a \<notin> range f\<close>
      then consider t_Q1 where \<open>?map t_Q @ [ev a] = ?map t_Q1\<close> \<open>t_Q1 \<in> \<T> Q\<close>
        | t_Q1 t_Q2 where \<open>?map t_Q @ [ev a] = ?map t_Q1 @ t_Q2\<close> \<open>tF t_Q1\<close> \<open>t_Q1 \<in> \<D> Q\<close>
        unfolding T_Renaming by blast
      hence False
      proof cases
        from \<open>a \<notin> range f\<close> show \<open>?map t_Q @ [ev a] = ?map t_Q1 \<Longrightarrow> False\<close> for t_Q1
          by (auto simp add: append_eq_map_conv ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
      next
        fix t_Q1 t_Q2 assume \<open>?map t_Q @ [ev a] = ?map t_Q1 @ t_Q2\<close> \<open>tF t_Q1\<close> \<open>t_Q1 \<in> \<D> Q\<close>
        from this(1) \<open>a \<notin> range f\<close> have \<open>t_Q1 \<le> t_Q\<close>
          by (cases t_Q2 rule: rev_cases, auto simp add: append_eq_map_conv ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
            (metis prefixI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inj_map inj_map_eq_map inj_on_id map_eq_append_conv \<open>inj f\<close>)
        with \<open>t_Q1 \<in> \<D> Q\<close> have \<open>t_Q \<in> \<D> Q\<close>
          by (metis "**"(2) F_imp_front_tickFree prefixE \<open>tF t_Q1\<close> front_tickFree_append_iff
              is_processT7 tickFree_Nil tickFree_imp_front_tickFree)
        with \<open>t_Q \<notin> \<D> Q\<close> show False ..
      qed
    }
    ultimately have $$ : \<open>(?map t_Q, ?fun ` X_Q \<union> {ev a | a. a \<notin> range f}) \<in> \<F> (?R Q)\<close>
      using is_processT5_S7' by blast
    from "**"(3) have $$$ : \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map t_P, ?map t_Q), f ` S)\<close>
      by (simp add: \<open>t = ?map t'\<close> setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff_weak \<open>inj f\<close>)
    have \<open>e \<in> X \<Longrightarrow> e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (?fun ` X_P \<union> {ev a | a. a \<notin> range f}) (f ` S)
                         (?fun ` X_Q \<union> {ev a | a. a \<notin> range f})\<close> for e
      using "**"(4)[THEN set_mp, of \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) id e\<close>] \<open>inj f\<close>
      unfolding super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def
      by (cases e, simp_all add: image_iff tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff) force
    hence $$$$ : \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (?fun ` X_P \<union> {ev a | a. a \<notin> range f}) (f ` S)
                       (?fun ` X_Q \<union> {ev a | a. a \<notin> range f})\<close> by blast
    from "$" "$$" "$$$" "$$$$" show \<open>(t, X) \<in> \<F> ?rhs\<close> unfolding F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by fast
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
    then obtain t_P t_Q X_P X_Q
      where * : \<open>(t_P, X_P) \<in> \<F> (?R P)\<close> \<open>(t_Q, X_Q) \<in> \<F> (?R Q)\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), f ` S)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P (f ` S) X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    have \<open>\<not> (t_P \<in> \<D> (?R P) \<or> t_Q \<in> \<D> (?R Q))\<close>
    proof (rule notI)
      assume \<open>t_P \<in> \<D> (?R P) \<or> t_Q \<in> \<D> (?R Q)\<close>
      hence \<open>t \<in> \<D> ?rhs\<close>
        by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k')
          (metis "*"(1-3) F_T append_Nil2 front_tickFree_Nil)
      with \<open>t \<notin> \<D> ?rhs\<close> show False ..
    qed
    with "*"(1, 2) obtain t_P' t_Q'
      where ** : \<open>t_P = ?map t_P'\<close> \<open>(t_P', ?fun -` X_P) \<in> \<F> P\<close>
        \<open>t_Q = ?map t_Q'\<close> \<open>(t_Q', ?fun -` X_Q) \<in> \<F> Q\<close>
      unfolding Renaming_projs by blast
    from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff_strong
      [THEN iffD1, OF \<open>inj f\<close> "*"(3)[unfolded "**"(1, 3)]] obtain t'
      where *** : \<open>t = ?map t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P', t_Q'), S)\<close> by blast
    have \<open>e \<in> ?fun -` X \<Longrightarrow> e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (?fun -` X_P) S (?fun -` X_Q)\<close> for e
      using "*"(4)[THEN set_mp, of \<open>?fun e\<close>]
      by (cases e) (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def dest: injD[OF \<open>inj f\<close>])
    hence \<open>?fun -` X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (?fun -` X_P) S (?fun -` X_Q)\<close> by blast
    with "**"(2, 4) "***"(2) have \<open>(t', ?fun -` X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      unfolding F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by auto
    thus \<open>(t, X) \<in> \<F> ?lhs\<close> by (auto simp add: "***"(1) F_Renaming)
  qed
qed




section \<open>Laws of Hiding\<close>

section \<open>Hiding and Sequential Composition\<close>

text \<open>We start by giving a counter example when the assumption \<^term>\<open>\<bbbF>\<^sub>\<checkmark>(P)\<close> is not satisfied.\<close>

notepad begin
  define Q :: \<open>nat \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    where \<open>Q r \<equiv> (((\<rightarrow>) undefined) ^^ r) STOP\<close> for r
  have \<open>SKIPS UNIV \ {undefined} = (SKIPS UNIV :: ('a, nat) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)\<close>
    by (simp add: Hiding_SKIPS)
  moreover have \<open>Q r \ {undefined} = STOP\<close> for r
    by (induct r) (simp_all add: Q_def Hiding_write0_non_disjoint)
  ultimately have * : \<open>(SKIPS UNIV \ {undefined}) \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \ {undefined}) = STOP\<close>
    by (simp only: SKIPS_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) simp

  have \<open>SKIPS UNIV \<^bold>;\<^sub>\<checkmark> Q = \<sqinter>r \<in> UNIV. Q r\<close> by simp
  moreover have \<open>[] \<in> \<D> (\<dots> \ {undefined})\<close>
  proof (rule D_Hiding_seqRunI)
    show \<open>ftF []\<close> \<open>tF []\<close> \<open>[] = trace_hide [] (ev ` {undefined}) @ []\<close> by simp_all
  next
    { fix r
      have \<open>replicate r (ev undefined) \<in> \<T> (Q r)\<close>
        by (induct r) (simp_all add: Q_def T_write0)
      also have \<open>replicate r (ev undefined) = map (\<lambda>i. ev undefined) [0..<r]\<close>
        by (simp add: map_replicate_trivial)
      finally have \<open>map (\<lambda>i. ev undefined) [0..<r] \<in> \<T> (Q r)\<close> .
    }
    hence \<open>\<exists>r. map (\<lambda>i. ev undefined) [0..<i] \<in> \<T> (Q r)\<close> for i by blast
    thus \<open>[] \<in> \<D> (\<sqinter>r \<in> UNIV. Q r) \<or> (\<exists>x. isInfHidden_seqRun x (\<sqinter>r \<in> UNIV. Q r) {undefined} [])\<close>
      by (auto simp add: T_GlobalNdet)
  qed
  ultimately have ** : \<open>(SKIPS UNIV \<^bold>;\<^sub>\<checkmark> Q) \ {undefined} = \<bottom>\<close>
    by (simp add: BOT_iff_Nil_D)

  have \<open>(SKIPS UNIV \ {undefined}) \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \ {undefined}) \<noteq> (SKIPS UNIV \<^bold>;\<^sub>\<checkmark> Q) \ {undefined}\<close>
    unfolding "*" "**" by simp

  hence \<open>\<exists>P (Q :: nat \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) S.
         (P \ S) \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \ S) \<noteq> (P \<^bold>;\<^sub>\<checkmark> Q) \ S\<close> by blast

end



text \<open>In general, only one refinement is holding.\<close>

theorem Hiding_Seq_FD_Seq_Hiding :
  \<open>(P \<^bold>;\<^sub>\<checkmark> Q) \ S \<sqsubseteq>\<^sub>F\<^sub>D (P \ S) \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \ S)\<close> (is \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
proof (rule failure_divergence_refine_optimizedI)
  let ?th = \<open>\<lambda>t. trace_hide t (ev ` S)\<close> and ?map = \<open>\<lambda>t. map (ev \<circ> of_ev) t\<close>
  fix t assume \<open>t \<in> \<D> ?rhs\<close>
  with D_imp_front_tickFree is_processT9
  consider (D_P) u v where \<open>t = ?map u @ v\<close> \<open>u \<in> \<D> (P \ S)\<close> \<open>tF u\<close> \<open>ftF v\<close>
    | (D_Q) u r v where \<open>t = ?map u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (P \ S)\<close>
      \<open>u @ [\<checkmark>(r)] \<notin> \<D> (P \ S)\<close> \<open>tF u\<close> \<open>v \<in> \<D> (Q r \ S)\<close>
    by (fastforce simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
  thus \<open>t \<in> \<D> ?lhs\<close>
  proof cases
    case D_P
    from D_P(2) obtain u' v' x where * : \<open>u = ?th u' @ v'\<close> \<open>tF u'\<close> \<open>ftF v'\<close>
      \<open>u' \<in> \<D> P \<or> isInfHidden_seqRun x P S u'\<close>
      by (blast elim: D_Hiding_seqRunE)
    from "*"(4) have \<open>?th (?map u') \<in> \<D> ?lhs\<close>
    proof (elim disjE)
      assume \<open>u' \<in> \<D> P\<close>
      with "*"(2) have \<open>?map u' \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs intro: front_tickFree_Nil)
      with mem_D_imp_mem_D_Hiding show \<open>?th (?map u') \<in> \<D> ?lhs\<close> .
    next
      assume \<open>isInfHidden_seqRun x P S u'\<close>
      from this isInfHidden_seqRun_imp_tickFree_seqRun[OF this]
      have \<open>isInfHidden_seqRun (ev \<circ> of_ev \<circ> x) (P \<^bold>;\<^sub>\<checkmark> Q) S (?map u')\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs image_iff)
          (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) list.map_comp map_append seqRun_def)
      thus \<open>?th (?map u') \<in> \<D> ?lhs\<close>
        by (simp add: D_Hiding_seqRun)
          (metis (no_types) append.right_neutral comp_apply
            front_tickFree_Nil tickFree_map_ev_comp)
    qed
    also have \<open>?th (?map u') = ?map (?th u')\<close>
      by (fact tickFree_trace_hide_map_ev_comp_of_ev[OF \<open>tF u'\<close>])
    finally show \<open>t \<in> \<D> ?lhs\<close>
      by (simp add: D_P(1, 4) "*"(1) front_tickFree_append is_processT7)
  next
    case D_Q
    from D_Q(2, 3) obtain u' where \<open>u @ [\<checkmark>(r)] = ?th u'\<close> \<open>(u', ev ` S) \<in> \<F> P\<close>
      unfolding T_Hiding D_Hiding by fast
    then obtain u' where \<open>u = ?th u'\<close> \<open>(u' @ [\<checkmark>(r)], ev ` S) \<in> \<F> P\<close>
      by (cases u' rule: rev_cases, simp_all split: if_split_asm)
        (metis F_imp_front_tickFree Hiding_tickFree butlast_snoc
          front_tickFree_iff_tickFree_butlast non_tickFree_tick tickFree_append_iff)
    from D_Q(5) obtain v' w' x where * : \<open>v = ?th v' @ w'\<close> \<open>tF v'\<close> \<open>ftF w'\<close>
      \<open>v' \<in> \<D> (Q r) \<or> isInfHidden_seqRun x (Q r) S v'\<close>
      by (blast elim: D_Hiding_seqRunE)
    from "*"(4) have \<open>?th (?map u' @ v') \<in> \<D> ?lhs\<close>
    proof (elim disjE)
      assume \<open>v' \<in> \<D> (Q r)\<close>
      hence \<open>?map u' @ v' \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          (metis F_T \<open>(u' @ [\<checkmark>(r)], ev ` S) \<in> \<F> P\<close> append_T_imp_tickFree not_Cons_self)
      with mem_D_imp_mem_D_Hiding show \<open>?th (?map u' @ v') \<in> \<D> ?lhs\<close> .
    next
      assume \<open>isInfHidden_seqRun x (Q r) S v'\<close>
      hence \<open>isInfHidden_seqRun x (P \<^bold>;\<^sub>\<checkmark> Q) S (?map u' @ v')\<close>
        by (simp add: seqRun_def image_iff Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          (metis F_T \<open>(u' @ [\<checkmark>(r)], ev ` S) \<in> \<F> P\<close> append_T_imp_tickFree list.discI)
      thus \<open>?th (?map u' @ v') \<in> \<D> ?lhs\<close>
        by (simp add: D_Hiding_seqRun)
          (metis append.right_neutral filter_append
            front_tickFree_Nil isInfHidden_seqRun_imp_tickFree)
    qed
    also have \<open>?th (?map u' @ v') = ?map (?th u') @ ?th v'\<close>
      using D_Q(4) Hiding_tickFree \<open>u = ?th u'\<close> tickFree_trace_hide_map_ev_comp_of_ev by auto
    finally have \<open>?map (?th u') @ ?th v' \<in> \<D> ?lhs\<close> .
    moreover have \<open>tF (?map (?th u') @ ?th v')\<close>
      by (simp add: "*"(2) Hiding_tickFree)
    ultimately show \<open>t \<in> \<D> ?lhs\<close>
      unfolding "*"(1) D_Q(1) \<open>u = ?th u'\<close> using \<open>ftF w'\<close>
      by (metis append.assoc is_processT7)
  qed
next

  assume subset_div : \<open>\<D> ?rhs \<subseteq> \<D> ?lhs\<close>
  let ?th = \<open>\<lambda>t. trace_hide t (ev ` S)\<close> and ?map = \<open>\<lambda>t. map (ev \<circ> of_ev) t\<close>
  fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close>
  then consider (div) \<open>t \<in> \<D> ?rhs\<close>
    | (F_P) u where \<open>t = ?map u\<close> \<open>(u, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (P \ S)\<close> \<open>u \<notin> \<D> (P \ S)\<close> \<open>tF u\<close>
    | (F_Q) u r v where \<open>t = ?map u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (P \ S)\<close> \<open>u @ [\<checkmark>(r)] \<notin> \<D> (P \ S)\<close>
      \<open>tF u\<close> \<open>(v, X) \<in> \<F> (Q r \ S)\<close> \<open>v \<notin> \<D> (Q r \ S)\<close>
    by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
      (metis F_T T_imp_front_tickFree front_tickFree_Nil is_processT9 self_append_conv)
  thus \<open>(t, X) \<in> \<F> ?lhs\<close>
  proof cases
    case div with subset_div show \<open>(t, X) \<in> \<F> ?lhs\<close>
      by (simp add: in_mono is_processT8)
  next
    case F_P
    from F_P(2, 3) obtain u' where * : \<open>u = ?th u'\<close> \<open>(u', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X \<union> ev ` S) \<in> \<F> P\<close>
      unfolding F_Hiding D_Hiding by fast
    have \<open>tF u'\<close> using "*"(1) F_P(4) Hiding_tickFree by blast
    have $ : \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (X \<union> ev ` S) = ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X \<union> ev ` S\<close>
      by (auto simp add: image_iff ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
        (metis Int_iff Un_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) image_eqI rangeI)
    from \<open>tF u'\<close> "*"(2) have \<open>(?map u', X \<union> ev ` S) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs "$")
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
      by (simp add: F_Hiding)
        (metis "*"(1) F_P(1) \<open>tF u'\<close> tickFree_trace_hide_map_ev_comp_of_ev)
  next
    case F_Q
    from F_Q(2, 3) obtain u' where \<open>u @ [\<checkmark>(r)] = ?th u'\<close> \<open>(u', ev ` S) \<in> \<F> P\<close>
      unfolding T_Hiding D_Hiding by fast
    then obtain u' where * : \<open>u = ?th u'\<close> \<open>(u' @ [\<checkmark>(r)], ev ` S) \<in> \<F> P\<close>
      by (cases u' rule: rev_cases, simp_all split: if_split_asm)
        (metis F_imp_front_tickFree Hiding_tickFree butlast_snoc
          front_tickFree_iff_tickFree_butlast non_tickFree_tick tickFree_append_iff)
    from F_Q(5, 6) obtain v' where ** : \<open>v = ?th v'\<close> \<open>(v', X \<union> ev ` S) \<in> \<F> (Q r)\<close>
      unfolding F_Hiding D_Hiding by blast
    have \<open>(?map u' @ v', X \<union> ev ` S) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
        (metis "*"(2) "**"(2) F_T append_T_imp_tickFree list.distinct(1))
    with F_Q(4) show \<open>(t, X) \<in> \<F> ?lhs\<close>
      by (simp add: F_Hiding F_Q(1) "*"(1) "**"(1))
        (metis Hiding_tickFree filter_append tickFree_trace_hide_map_ev_comp_of_ev)
  qed
qed



section \<open>Hiding and Synchronization Product\<close>

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_imp_superset_ev :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow>
   {ev a |a. ev a \<in> set u} \<union> {ev a |a. ev a \<in> set v} \<subseteq> {ev a |a. ev a \<in> set t}\<close>
proof (induct t arbitrary: u v)
  case Nil thus ?case by (auto dest: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
next
  case (Cons e t)
  from Cons.prems consider (mv_left) a u' where \<open>e = ev a\<close> \<open>u = ev a # u'\<close>
    \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v), A)\<close>
  | (mv_right) a v' where \<open>e = ev a\<close> \<open>v = ev a # v'\<close>
    \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v'), A)\<close>
  | (mv_both_ev) a u' v' where \<open>e = ev a\<close> \<open>u = ev a # u'\<close> \<open>v = ev a # v'\<close>
    \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
  | (mv_both_tick) r s u' v' where \<open>u = \<checkmark>(r) # u'\<close> \<open>v = \<checkmark>(s) # v'\<close>
    \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
    by (cases e) (auto elim: Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE Cons_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
  thus ?case by cases (auto dest!: Cons.hyps)
qed


lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) disjoint_isInfHidden_seqRunL_to_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  assumes \<open>A \<inter> S = {}\<close> and \<open>isInfHidden_seqRun x P A t_P\<close>
    and \<open>t_Q \<in> \<T> Q\<close> and \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
  shows \<open>isInfHidden_seqRun (ev \<circ> of_ev \<circ> x) (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) A t\<close>
proof -
  have tF_x : \<open>tF (map x [0..<i])\<close> for i
    by (metis assms(2) imageE is_ev_def seqRun_def tickFree_append_iff
        tickFree_map_tick_comp_iff tickFree_seqRun_iff)
  define t' where \<open>t' i \<equiv> t @ map (ev \<circ> of_ev) (map x [0..<i])\<close> for i
  from assms(1, 2) have \<open>{a. ev a \<in> set (map x [0..<i])} \<inter> S = {}\<close> for i
    by (simp add: disjoint_iff image_iff) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1))
  from tickFree_disjoint_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append_tailL[OF tF_x this assms(4)]
  have \<open>seqRun t (ev \<circ> of_ev \<circ> x) i setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((seqRun t_P x i, t_Q), S)\<close> for i
    by (simp add: seqRun_def)
  moreover have \<open>of_ev (x i) \<in> A\<close> for i
    by (metis assms(2) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) image_iff)
  ultimately show \<open>isInfHidden_seqRun (ev \<circ> of_ev \<circ> x) (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) A t\<close>
    using assms(2, 3) by (auto simp add: T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
qed

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) disjoint_isInfHidden_seqRunR_to_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<lbrakk>A \<inter> S = {}; isInfHidden_seqRun x Q A t_Q; t_P \<in> \<T> P;
    t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<rbrakk> \<Longrightarrow>
   isInfHidden_seqRun (ev \<circ> of_ev \<circ> x) (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) A t\<close>
  by (fold Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym, rule Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale.disjoint_isInfHidden_seqRunL_to_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    (use setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym in \<open>blast intro: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_axioms\<close>)+



lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) disjoint_Hiding_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding_aux :
  \<comment> \<open>This lemma avoids duplication of the proof work.\<close>
  assumes \<open>A \<inter> S = {}\<close> \<open>tF u\<close> \<open>ftF v\<close> \<open>t_P \<in> \<D> (P \ A)\<close> \<open>t_Q \<in> \<T> (Q \ A)\<close>
    and * : \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
  shows \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
proof -
  let ?th_A = \<open>\<lambda>t. trace_hide t (ev ` A)\<close>
  from \<open>t_P \<in> \<D> (P \ A)\<close> obtain t_P1 t_P2 
    where D_P : \<open>tF t_P1\<close> \<open>ftF t_P2\<close> \<open>t_P = ?th_A t_P1 @ t_P2\<close>
      \<open>t_P1 \<in> \<D> P \<or> (\<exists>t_P_x. isInfHidden_seqRun_strong t_P_x P A t_P1)\<close>
    by (blast elim: D_Hiding_seqRunE)
  from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL[OF "*"[unfolded D_P(3)]] obtain u1 u2 t_Q1 t_Q2
    where ** : \<open>u = u1 @ u2\<close> \<open>t_Q = t_Q1 @ t_Q2\<close>
      \<open>u1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?th_A t_P1, t_Q1), S)\<close>
      \<open>u2 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P2, t_Q2), S)\<close> by blast
  from \<open>t_Q \<in> \<T> (Q \ A)\<close> consider t_Q1' where \<open>t_Q = ?th_A t_Q1'\<close> \<open>(t_Q1', ev ` A) \<in> \<F> Q\<close>
    | (D_Q) t_Q1' t_Q2' where \<open>tF t_Q1'\<close> \<open>ftF t_Q2'\<close> \<open>t_Q = ?th_A t_Q1' @ t_Q2'\<close>
      \<open>t_Q1' \<in> \<D> Q \<or> (\<exists>t_Q_x. isInfHidden_seqRun_strong t_Q_x Q A t_Q1')\<close>
    by (elim T_Hiding_seqRunE)
  thus \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
  proof cases
    fix t_Q1' assume \<open>t_Q = ?th_A t_Q1'\<close> \<open>(t_Q1', ev ` A) \<in> \<F> Q\<close>
    from \<open>t_Q = ?th_A t_Q1'\<close> "**"(2) obtain t_Q1''
      where \<open>t_Q1 = ?th_A t_Q1''\<close> \<open>t_Q1'' \<le> t_Q1'\<close>
      by (metis Prefix_Order.prefixI le_trace_hide)
    from F_T \<open>(t_Q1', ev ` A) \<in> \<F> Q\<close> \<open>t_Q1'' \<le> t_Q1'\<close> is_processT3_TR
    have \<open>t_Q1'' \<in> \<T> Q\<close> by blast
    from "**"(3)[unfolded \<open>t_Q1 = ?th_A t_Q1''\<close>,
        THEN disjoint_trace_hide_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF \<open>A \<inter> S = {}\<close>]]
    obtain u1' where \<open>u1 = ?th_A u1'\<close> \<open>u1' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P1, t_Q1''), S)\<close> by blast
    from D_P(4) show \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
    proof (elim disjE exE)
      assume \<open>t_P1 \<in> \<D> P\<close>
      with \<open>u1' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P1, t_Q1''), S)\<close> D_P(1) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree_imp
      have \<open>u1' = u1' @ []\<close> \<open>tF u1'\<close> \<open>ftF []\<close>
        \<open>u1' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P1, t_Q1''), S)\<close> \<open>t_P1 \<in> \<D> P\<close>
        by simp_all (blast intro: is_processT3_TR)+
      with \<open>t_Q1'' \<in> \<T> Q\<close> have \<open>u1' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
      moreover have \<open>u @ v = ?th_A u1' @ (u2 @ v)\<close>
        by (simp add: "*"(1) "**"(1) \<open>u1 = ?th_A u1'\<close>)
      ultimately show \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
        unfolding D_Hiding using \<open>tF u\<close> \<open>ftF v\<close> "**"(1) \<open>tF u1'\<close>
        by (auto intro: front_tickFree_append)
    next
      fix t_P_x assume \<open>isInfHidden_seqRun_strong t_P_x P A t_P1\<close>
      hence \<open>isInfHidden_seqRun (ev \<circ> of_ev \<circ> t_P_x) (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) A u1'\<close>
        by (intro disjoint_isInfHidden_seqRunL_to_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
            [OF \<open>A \<inter> S = {}\<close> _ \<open>t_Q1'' \<in> \<T> Q\<close> \<open>u1' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P1, t_Q1''), S)\<close>]) simp
      with "**"(1) \<open>u1 = ?th_A u1'\<close> assms(2, 3) show \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
        unfolding D_Hiding_seqRun by clarify
          (metis append_eq_append_conv2[of u1 \<open>u2 @ v\<close> \<open>u1 @ u2\<close> v]
            isInfHidden_seqRun_imp_tickFree[of u1' \<open>ev \<circ> of_ev \<circ> t_P_x\<close> \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q\<close> A]
            front_tickFree_append[of u2 v] tickFree_append_iff[of u1 u2])
    qed
  next
    case D_Q
    from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_le_prefixLR
      [OF "*"[unfolded D_P(3) D_Q(3)], of \<open>?th_A t_P1\<close> \<open>?th_A t_Q1'\<close>]
    consider (left) u' t_Q1'' where \<open>u' \<le> u\<close> \<open>t_Q1'' \<le> t_Q1'\<close>
      \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?th_A t_P1, ?th_A t_Q1''), S)\<close>
    | (right) u' t_P1' where \<open>u' \<le> u\<close> \<open>t_P1' \<le> t_P1\<close>
      \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?th_A t_P1', ?th_A t_Q1'), S)\<close>
      by (auto dest!: le_trace_hide)
    thus \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
    proof cases
      case left
      have \<open>t_Q1'' \<in> \<T> Q\<close> by (meson D_Q(4) D_T is_processT3_TR left(2) t_le_seqRun)
      from disjoint_trace_hide_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF \<open>A \<inter> S = {}\<close> left(3)]
      obtain u'' where $ : \<open>u' = ?th_A u''\<close>
        \<open>u'' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P1, t_Q1''), S)\<close> by blast
      from D_P(4) show \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
      proof (elim disjE exE)
        assume \<open>t_P1 \<in> \<D> P\<close>
        hence \<open>u'' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
          by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
            (metis "$"(2) D_P(1) \<open>t_Q1'' \<in> \<T> Q\<close> append.right_neutral
              front_tickFree_Nil setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree_imp)
        with left(1) show \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
          by (elim Prefix_Order.prefixE, simp add: D_Hiding "$"(1))
            (metis Hiding_tickFree assms(2, 3) front_tickFree_append tickFree_append_iff)
      next
        fix t_P_x assume \<open>isInfHidden_seqRun_strong t_P_x P A t_P1\<close>
        hence \<open>isInfHidden_seqRun (ev \<circ> of_ev \<circ> t_P_x) (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) A u''\<close>
          by (intro disjoint_isInfHidden_seqRunL_to_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
              [OF \<open>A \<inter> S = {}\<close> _ \<open>t_Q1'' \<in> \<T> Q\<close> "$"(2)]) simp
        from left(1) show \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
          by (elim Prefix_Order.prefixE, simp add: D_Hiding_seqRun "$"(1))
            (metis \<open>?this\<close> assms(2, 3) front_tickFree_append
              isInfHidden_seqRun_imp_tickFree tickFree_append_iff)
      qed
    next
      case right
      have \<open>t_P1' \<in> \<T> P\<close> by (meson D_P(4) D_T is_processT3_TR right(2) t_le_seqRun)
      from disjoint_trace_hide_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF \<open>A \<inter> S = {}\<close> right(3)]
      obtain u'' where $ : \<open>u' = ?th_A u''\<close>
        \<open>u'' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P1', t_Q1'), S)\<close> by blast
      from D_Q(4) show \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
      proof (elim disjE exE)
        assume \<open>t_Q1' \<in> \<D> Q\<close>
        hence \<open>u'' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
          by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
            (metis "$"(2) D_Q(1) \<open>t_P1' \<in> \<T> P\<close> append.right_neutral
              front_tickFree_Nil setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree_imp)
        with right(1) show \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
          by (elim Prefix_Order.prefixE, simp add: D_Hiding "$"(1))
            (metis Hiding_tickFree assms(2, 3) front_tickFree_append tickFree_append_iff)
      next
        fix t_Q_x assume \<open>isInfHidden_seqRun_strong t_Q_x Q A t_Q1'\<close>
        hence \<open>isInfHidden_seqRun (ev \<circ> of_ev \<circ> t_Q_x) (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) A u''\<close>
          by (intro disjoint_isInfHidden_seqRunR_to_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
              [OF \<open>A \<inter> S = {}\<close> _ \<open>t_P1' \<in> \<T> P\<close> "$"(2)]) simp
        from right(1) show \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
          by (elim Prefix_Order.prefixE, simp add: D_Hiding_seqRun "$"(1))
            (metis \<open>?this\<close> assms(2, 3) front_tickFree_append
              isInfHidden_seqRun_imp_tickFree tickFree_append_iff)
      qed
    qed
  qed
qed



theorem (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) disjoint_Hiding_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A \<sqsubseteq>\<^sub>F\<^sub>D (P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A)\<close> if \<open>A \<inter> S = {}\<close>
proof (rule failure_divergence_refine_optimizedI)
  let ?th_A = \<open>\<lambda>t. trace_hide t (ev ` A)\<close>
  fix t assume \<open>t \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A))\<close>
  from this obtain u v t_P t_Q
    where * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
      \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
      \<open>t_P \<in> \<D> (P \ A) \<and> t_Q \<in> \<T> (Q \ A) \<or> t_P \<in> \<T> (P \ A) \<and> t_Q \<in> \<D> (Q \ A)\<close>
    unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
  from "*"(5) show \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
  proof (elim disjE conjE)
    show \<open>t_P \<in> \<D> (P \ A) \<Longrightarrow> t_Q \<in> \<T> (Q \ A) \<Longrightarrow> t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
      by (simp add: "*"(1-4) disjoint_Hiding_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding_aux \<open>A \<inter> S = {}\<close>)
  next
    assume \<open>t_P \<in> \<T> (P \ A)\<close> \<open>t_Q \<in> \<D> (Q \ A)\<close>
    have \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>s r. r \<otimes>\<checkmark> s\<^esub> ((t_Q, t_P), S)\<close>
      using "*"(4) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym by blast
    from Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.disjoint_Hiding_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding_aux
      [OF \<open>A \<inter> S = {}\<close> "*"(2, 3) \<open>t_Q \<in> \<D> (Q \ A)\<close> \<open>t_P \<in> \<T> (P \ A)\<close> this]
    have \<open>u @ v \<in> \<D> (Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Q S P \ A)\<close> .
    also have \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Q S P = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q\<close> by (fact Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
    finally show \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close> unfolding "*"(1) .
  qed
next
  fix t X assume \<open>(t, X) \<in> \<F> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A))\<close>
    and subset_div : \<open>\<D> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A)) \<subseteq> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
  from this(1) consider \<open>t \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A))\<close>
    | (fail_Sync) t_P t_Q X_P X_Q where \<open>(t_P, X_P) \<in> \<F> (P \ A)\<close> \<open>(t_Q, X_Q) \<in> \<F> (Q \ A)\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close> \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P S X_Q\<close>
    unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
  thus \<open>(t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
  proof cases
    from subset_div show \<open>t \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A)) \<Longrightarrow> (t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
      by (simp add: in_mono is_processT8)
  next
    case fail_Sync
    from fail_Sync(1, 2) consider \<open>t_P \<in> \<D> (P \ A) \<or> t_Q \<in> \<D> (Q \ A)\<close>
      | (fail_Hiding) t_P' t_Q' where
        \<open>t_P = trace_hide t_P' (ev ` A)\<close> \<open>(t_P', X_P \<union> ev ` A) \<in> \<F> P\<close>
        \<open>t_Q = trace_hide t_Q' (ev ` A)\<close> \<open>(t_Q', X_Q \<union> ev ` A) \<in> \<F> Q\<close>
      unfolding F_Hiding D_Hiding by blast
    thus \<open>(t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
    proof cases
      assume \<open>t_P \<in> \<D> (P \ A) \<or> t_Q \<in> \<D> (Q \ A)\<close>
      with fail_Sync(1-3) have \<open>t \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A))\<close>
        by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k')
          (metis F_T append_self_conv front_tickFree_Nil)
      with subset_div show \<open>(t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
        by (simp add: in_mono is_processT8)
    next
      case fail_Hiding
      from disjoint_trace_hide_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
        [OF \<open>A \<inter> S = {}\<close> fail_Sync(3)[unfolded fail_Hiding(1, 3)]]
      obtain t' where * : \<open>t = trace_hide t' (ev ` A)\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P', t_Q'), S)\<close> by blast
      from fail_Sync(4) have \<open>X \<union> ev ` A \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (X_P \<union> ev ` A) S (X_Q \<union> ev ` A)\<close>
        by (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def image_iff)
      with "*"(2) fail_Hiding(2, 4) have \<open>(t', X \<union> ev ` A) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
        by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      with "*"(1) show \<open>(t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close> unfolding F_Hiding by blast
    qed
  qed
qed



theorem (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) disjoint_finite_Hiding_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A = (P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A)\<close> if \<open>A \<inter> S = {}\<close> and \<open>finite A\<close>
  \<comment> \<open>Monster theorem!\<close>
proof (rule FD_antisym)
  from disjoint_Hiding_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding[OF \<open>A \<inter> S = {}\<close>]
  show \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A \<sqsubseteq>\<^sub>F\<^sub>D (P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A)\<close> .
next
  let ?th_A = \<open>\<lambda>t. trace_hide t (ev ` A)\<close>
  show \<open>(P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A) \<sqsubseteq>\<^sub>F\<^sub>D P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A\<close>
  proof (rule failure_divergence_refine_optimizedI)
    fix t X assume \<open>(t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
      and subset_div : \<open>\<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A) \<subseteq> \<D> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A))\<close>
    from this(1) consider \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
      | t' where \<open>t = ?th_A t'\<close> \<open>(t', X \<union> ev ` A) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      unfolding F_Hiding D_Hiding by blast
    thus \<open>(t, X) \<in> \<F> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A))\<close>
    proof cases
      show \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A) \<Longrightarrow> (t, X) \<in> \<F> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A))\<close>
        using subset_div is_processT8 by blast
    next
      fix t' assume \<open>t = ?th_A t'\<close> \<open>(t', X \<union> ev ` A) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      from this(2) consider \<open>t' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
        | (fail) t_P X_P t_Q X_Q where \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
          \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
          \<open>X \<union> ev ` A \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P S X_Q\<close>
        unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by auto
      thus \<open>(t, X) \<in> \<F> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A))\<close>
      proof cases
        assume \<open>t' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
        with \<open>t = ?th_A t'\<close> have \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
          by (metis mem_D_imp_mem_D_Hiding)
        with subset_div is_processT8 show \<open>(t, X) \<in> \<F> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A))\<close> by blast
      next
        case fail
        from \<open>A \<inter> S = {}\<close> fail(4) have \<open>X_P = X_P \<union> ev ` A\<close> \<open>X_Q = X_Q \<union> ev ` A\<close>
          \<comment> \<open>i.e. \<^term>\<open>ev ` A \<subseteq> X_P\<close> and \<^term>\<open>ev ` A \<subseteq> X_Q\<close>\<close>
          by (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
        with fail(1, 2) have \<open>(?th_A t_P, X_P) \<in> \<F> (P \ A)\<close>
          \<open>(?th_A t_Q, X_Q) \<in> \<F> (Q \ A)\<close>
          by (auto simp add: F_Hiding)
        moreover from fail(3) have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?th_A t_P, ?th_A t_Q), S)\<close>
          unfolding \<open>t = ?th_A t'\<close> by (fact setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_trace_hide)
        ultimately show \<open>(t, X) \<in> \<F> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A))\<close>
          using fail(4) unfolding F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by fast
      qed
    qed
  next
    fix t assume \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
    then obtain u v where * : \<open>ftF v\<close> \<open>tF u\<close> \<open>t = ?th_A u @ v\<close>
      \<open>u \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) \<or> (\<exists>x. isInfHidden_seqRun_strong x (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) A u)\<close>
      by (blast elim: D_Hiding_seqRunE)
    from "*"(4) show \<open>t \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A))\<close>
    proof (elim disjE exE)
      assume \<open>u \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      then obtain u1 u2 t_P t_Q where ** : \<open>u = u1 @ u2\<close> \<open>tF u1\<close> \<open>ftF u2\<close>
        \<open>u1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
        \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
        unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
      have \<open>t = ?th_A u1 @ (?th_A u2 @ v)\<close>
        by (simp add: "*"(3) "**"(1))
      moreover from "**"(2) have \<open>tF (?th_A u1)\<close> using Hiding_tickFree by blast
      moreover have \<open>ftF (?th_A u2 @ v)\<close>
        by (metis D_imp_front_tickFree \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close> calculation(1)
            front_tickFree_append_iff front_tickFree_charn)
      moreover from "**"(4) have \<open>?th_A u1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?th_A t_P, ?th_A t_Q), S)\<close>
        by (fact setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_trace_hide)
      moreover from "**"(5) have \<open>?th_A t_P \<in> \<D> (P \ A) \<and> ?th_A t_Q \<in> \<T> (Q \ A) \<or>
                                  ?th_A t_P \<in> \<T> (P \ A) \<and> ?th_A t_Q \<in> \<D> (Q \ A)\<close>
        by (metis mem_D_imp_mem_D_Hiding mem_T_imp_mem_T_Hiding)
      ultimately show \<open>t \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A))\<close>
        unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    next
      fix x assume ** : \<open>isInfHidden_seqRun_strong x (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) A u\<close>
      from "**" have *** : \<open>\<exists>t_P t_Q. t_P \<in> \<T> P \<and> t_Q \<in> \<T> Q \<and>
        seqRun u x i setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close> for i
        unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast

      define t_P_t_Q where \<open>t_P_t_Q i \<equiv> SOME (t_P, t_Q). t_P \<in> \<T> P \<and> t_Q \<in> \<T> Q \<and>
      seqRun u x i setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close> for i
      define t_P where \<open>t_P \<equiv> fst \<circ> t_P_t_Q\<close>
      define t_Q where \<open>t_Q \<equiv> snd \<circ> t_P_t_Q\<close>
      have **** : \<open>t_P i \<in> \<T> P\<close> \<open>t_Q i \<in> \<T> Q\<close>
        \<open>seqRun u x i setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P i, t_Q i), S)\<close> for i
        by (use "***"[of i] in \<open>simp add: t_P_def t_Q_def,
                              cases \<open>t_P_t_Q i\<close>, simp add: t_P_t_Q_def,
                              metis (mono_tags, lifting) case_prod_conv someI_ex\<close>)+
      from "*"(2) "**" have \<open>set (seqRun u x i) \<subseteq> {ev a |a. ev a \<in> set u} \<union> ev ` A\<close> for i
        by (simp add: seqRun_def subset_iff)
          (metis image_iff list.set_map tickFree_iff_is_map_ev)
      have ***** : \<open>{ev a |a. ev a \<in> set (t_P i)} \<union> {ev a |a. ev a \<in> set (t_Q i)} \<subseteq>
                      {ev a |a. ev a \<in> set u} \<union> ev ` A\<close> for i
        by (rule subset_trans[OF setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_imp_superset_ev[OF "****"(3)]])
          (use \<open>set (seqRun u x i) \<subseteq> {ev a |a. ev a \<in> set u} \<union> ev ` A\<close> in blast)
      have ****** : \<open>tF (t_P i)\<close> \<open>tF (t_Q i)\<close> for i
        using tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff[OF "****"(3)[of i]]
        by (metis "*"(2) "**" event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) imageE tickFree_seqRun_iff)+

      { fix i
        have \<open>{w. tF w \<and> {ev a |a. ev a \<in> set w} \<subseteq> set u \<union> ev ` A \<and> length w \<le> i} \<subseteq>
                  map (ev \<circ> of_ev) ` {w. set w \<subseteq> set u \<union> ev ` A \<and> length w \<le> i}\<close>
          (is \<open>?S1 \<subseteq> map (ev \<circ> of_ev) ` ?S2\<close>)
        proof (rule subsetI)
          fix w assume \<open>w \<in> ?S1\<close>
          hence \<open>map (ev \<circ> of_ev) (map (ev \<circ> of_ev) w) = w\<close>
            by (induct w) (auto simp add: subset_iff)
          moreover from \<open>w \<in> ?S1\<close> have \<open>map (ev \<circ> of_ev) w \<in> ?S2\<close>
            by (induct w) (auto simp add: subset_iff)
          ultimately show \<open>w \<in> map (ev \<circ> of_ev) ` ?S2\<close>
            by (metis (lifting) image_eqI)
        qed
        moreover have \<open>finite {w. set w \<subseteq> set u \<union> ev ` A \<and> length w \<le> i}\<close>
          by (rule finite_lists_length_le) (simp add: \<open>finite A\<close>)
        ultimately have \<open>finite {w. tF w \<and> {ev a |a. ev a \<in> set w} \<subseteq> set u \<union> ev ` A \<and> length w \<le> i}\<close>
          using finite_subset[OF _ finite_imageI] by blast
      } note \<pounds> = this

      have \<open>inj t_P_t_Q\<close>
      proof (rule injI)
        fix i j assume \<open>t_P_t_Q i = t_P_t_Q j\<close>
        with "****"(3) have \<open>seqRun u x i setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P i, t_Q i), S) \<and>
        seqRun u x j setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P i, t_Q i), S)\<close>
          unfolding t_P_t_Q_def t_P_def t_Q_def by fastforce
        with setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_length
        have \<open>length (seqRun u x i) = length (seqRun u x j)\<close> by blast
        thus \<open>i = j\<close> by simp
      qed
      hence \<open>infinite (range t_P_t_Q)\<close> using finite_imageD by blast
      moreover have \<open>range t_P_t_Q \<subseteq> range t_P \<times> range t_Q\<close>
        by (simp add: t_P_def t_Q_def subset_iff image_iff) (metis fst_conv snd_conv)
      ultimately have \<open>infinite (range t_P) \<or> infinite (range t_Q)\<close> 
        by (meson finite_SigmaI infinite_super)

      thus \<open>t \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A))\<close>
      proof (elim disjE)
        assume \<open>infinite (range t_P)\<close>
        have \<open>finite {w. \<exists>t'\<in>range t_P. w = take i t'}\<close> for i
          using "******"(1) "*****"
          by (auto intro!: finite_subset[OF _ "\<pounds>"[of i]] simp add: image_iff subset_iff)
            (metis append_take_drop_id tickFree_append_iff, metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1) in_set_takeD)
        with \<open>infinite (range t_P)\<close> obtain t_P' :: \<open>nat \<Rightarrow> _\<close>
          where $ : \<open>strict_mono t_P'\<close> \<open>range t_P' \<subseteq> {w. \<exists>t'\<in>range t_P. w \<le> t'}\<close>
          using KoenigLemma by blast
        from "$"(2) "****"(1) is_processT3_TR have \<open>range t_P' \<subseteq> \<T> P\<close> by blast
        define t_P'' where \<open>t_P'' i \<equiv> t_P' (i + length u)\<close> for i
        from \<open>range t_P' \<subseteq> \<T> P\<close> have \<open>range t_P'' \<subseteq> \<T> P\<close> and \<open>strict_mono t_P''\<close>
          by (auto simp add: t_P''_def "$"(1) strict_monoD strict_monoI)
        have $$ : \<open>?th_A (t_P'' i) = ?th_A (t_P'' 0)\<close> for i
        proof -
          have \<open>length u \<le> length (t_P'' 0)\<close>
            by (metis "$"(1) add_0 add_leD1 t_P''_def length_strict_mono)
          obtain t' where \<open>t_P'' i = t_P'' 0 @ t'\<close>
            by (meson prefixE \<open>strict_mono t_P''\<close> strict_mono_less_eq zero_order(1))
          moreover from "$"(2) obtain j where \<open>t_P'' i \<le> t_P j\<close> by (auto simp add: t_P''_def)
          ultimately obtain t'' where \<open>t_P j = t_P'' 0 @ t' @ t''\<close> by (metis prefixE append.assoc)

          have \<open>tF (t' @ t'')\<close>
            by (metis "******"(1) \<open>t_P j = t_P'' 0 @ t' @ t''\<close> tickFree_append_iff)
          with setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_set_subsetL
            [OF "****"(3)[of j], where n = \<open>length (t_P'' 0)\<close>, unfolded \<open>t_P j = t_P'' 0 @ t' @ t''\<close>]
          have \<open>e \<in> set (t' @ t'') \<Longrightarrow> e \<in> {ev a |a. ev a \<in> set (drop (length (t_P'' 0)) (seqRun u x j))}\<close> for e
            by (cases e) (auto simp add: tickFree_def)
          moreover have \<open>{a. ev a \<in> set (drop (length (t_P'' 0)) (seqRun u x j))} \<subseteq>
                       {a. ev a \<in> set (drop (length u) (seqRun u x j))}\<close>
            by (simp add: subset_iff)
              (meson \<open>length u \<le> length (t_P'' 0)\<close> in_mono set_drop_subset_set_drop)
          moreover from "**" have \<open>set (drop (length u) (seqRun u x j)) \<subseteq> ev ` A\<close>
            by (auto simp add: seqRun_def)
          ultimately have \<open>set (t' @ t'') \<subseteq> ev ` A\<close> by blast
          thus \<open>?th_A (t_P'' i) = ?th_A (t_P'' 0)\<close>
            by (simp add: \<open>t_P'' i = t_P'' 0 @ t'\<close> subset_iff)
        qed
        from "$"(2) obtain i where \<open>t_P'' 0 \<le> t_P i\<close> by (auto simp add: t_P''_def)
        with prefixE obtain w where \<open>t_P i = t_P'' 0 @ w\<close> by blast
        have \<open>ftF v\<close> by (fact "*"(1))
        moreover have \<open>tF (?th_A (seqRun u x i))\<close>
          by (metis "*"(2) "**" Hiding_tickFree trace_hide_seqRun_eq_iff)
        moreover have \<open>t = ?th_A (seqRun u x i) @ v\<close>
          by (metis "*"(3) "**" trace_hide_seqRun_eq_iff)
        moreover have \<open>?th_A (seqRun u x i) setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?th_A (t_P i), ?th_A (t_Q i)), S)\<close>
          by (intro setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_trace_hide "****"(3))
        moreover have \<open>?th_A (t_P i) \<in> \<D> (P \ A)\<close>
        proof (unfold D_Hiding, clarify, intro exI conjI)
          show \<open>ftF (?th_A w)\<close>
            by (metis "******"(1) Hiding_front_tickFree \<open>t_P i = t_P'' 0 @ w\<close>
                tickFree_append_iff tickFree_imp_front_tickFree)
        next
          show \<open>tF (t_P'' 0)\<close>
            by (metis "******"(1) \<open>t_P i = t_P'' 0 @ w\<close> tickFree_append_iff)
        next
          show \<open>?th_A (t_P i) = ?th_A (t_P'' 0) @ ?th_A w\<close>
            by (simp add: \<open>t_P i = t_P'' 0 @ w\<close>)
        next
          show \<open>t_P'' 0 \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun f P A \<and> t_P'' 0 \<in> range f)\<close>
            using "$$" \<open>range t_P'' \<subseteq> \<T> P\<close> \<open>strict_mono t_P''\<close> by blast
        qed
        moreover have \<open>?th_A (t_Q i) \<in> \<T> (Q \ A)\<close>
        proof (cases \<open>\<exists>t'. ?th_A t' = ?th_A (t_Q i) \<and> (t', ev ` A) \<in> \<F> Q\<close>)
          assume \<open>\<exists>t'. ?th_A t' = ?th_A (t_Q i) \<and> (t', ev ` A) \<in> \<F> Q\<close>
          then obtain t' where \<open>?th_A (t_Q i) = ?th_A t'\<close> \<open>(t', ev ` A) \<in> \<F> Q\<close> by metis
          thus \<open>?th_A (t_Q i) \<in> \<T> (Q \ A)\<close> unfolding T_Hiding by blast
        next
          assume \<open>\<nexists>t'. ?th_A t' = ?th_A (t_Q i) \<and> (t', ev ` A) \<in> \<F> Q\<close>
          with inf_hidden[OF _ "****"(2)] obtain t_Q' j
            where \<open>isInfHiddenRun t_Q' Q A\<close> \<open>t_Q i = t_Q' j\<close> by blast
          thus \<open>?th_A (t_Q i) \<in> \<T> (Q \ A)\<close>
            unfolding T_Hiding using "******"(2) front_tickFree_Nil by blast
        qed
        ultimately show \<open>t \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A))\<close> unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
      next
        assume \<open>infinite (range t_Q)\<close>
        have \<open>finite {w. \<exists>t'\<in>range t_Q. w = take i t'}\<close> for i
          using "******"(2) "*****"
          by (auto intro!: finite_subset[OF _ "\<pounds>"[of i]] simp add: image_iff subset_iff)
            (metis append_take_drop_id tickFree_append_iff, metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1) in_set_takeD)
        with \<open>infinite (range t_Q)\<close> obtain t_Q' :: \<open>nat \<Rightarrow> _\<close>
          where $ : \<open>strict_mono t_Q'\<close> \<open>range t_Q' \<subseteq> {w. \<exists>t'\<in>range t_Q. w \<le> t'}\<close>
          using KoenigLemma by blast
        from "$"(2) "****"(2) is_processT3_TR have \<open>range t_Q' \<subseteq> \<T> Q\<close> by blast
        define t_Q'' where \<open>t_Q'' i \<equiv> t_Q' (i + length u)\<close> for i
        from \<open>range t_Q' \<subseteq> \<T> Q\<close> have \<open>range t_Q'' \<subseteq> \<T> Q\<close> and \<open>strict_mono t_Q''\<close>
          by (auto simp add: t_Q''_def "$"(1) strict_monoD strict_monoI)
        have $$ : \<open>?th_A (t_Q'' i) = ?th_A (t_Q'' 0)\<close> for i
        proof -
          have \<open>length u \<le> length (t_Q'' 0)\<close>
            by (metis "$"(1) add_0 add_leD1 t_Q''_def length_strict_mono)
          obtain t' where \<open>t_Q'' i = t_Q'' 0 @ t'\<close>
            by (meson prefixE \<open>strict_mono t_Q''\<close> strict_mono_less_eq zero_order(1))
          moreover from "$"(2) obtain j where \<open>t_Q'' i \<le> t_Q j\<close> by (auto simp add: t_Q''_def)
          ultimately obtain t'' where \<open>t_Q j = t_Q'' 0 @ t' @ t''\<close> by (metis prefixE append.assoc)
          have \<open>tF (t' @ t'')\<close>
            by (metis "******"(2) \<open>t_Q j = t_Q'' 0 @ t' @ t''\<close> tickFree_append_iff)
          with setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_set_subsetR
            [OF "****"(3)[of j], where n = \<open>length (t_Q'' 0)\<close>, unfolded \<open>t_Q j = t_Q'' 0 @ t' @ t''\<close>]
          have \<open>e \<in> set (t' @ t'') \<Longrightarrow> e \<in> {ev a |a. ev a \<in> set (drop (length (t_Q'' 0)) (seqRun u x j))}\<close> for e
            by (cases e) (auto simp add: tickFree_def)
          moreover have \<open>{a. ev a \<in> set (drop (length (t_Q'' 0)) (seqRun u x j))} \<subseteq>
                         {a. ev a \<in> set (drop (length u) (seqRun u x j))}\<close>
            by (simp add: subset_iff)
              (meson \<open>length u \<le> length (t_Q'' 0)\<close> in_mono set_drop_subset_set_drop)
          moreover from "**" have \<open>set (drop (length u) (seqRun u x j)) \<subseteq> ev ` A\<close>
            by (auto simp add: seqRun_def)
          ultimately have \<open>set (t' @ t'') \<subseteq> ev ` A\<close> by blast
          thus \<open>?th_A (t_Q'' i) = ?th_A (t_Q'' 0)\<close>
            by (simp add: \<open>t_Q'' i = t_Q'' 0 @ t'\<close> subset_iff)
        qed
        from "$"(2) obtain i where \<open>t_Q'' 0 \<le> t_Q i\<close> by (auto simp add: t_Q''_def)
        with prefixE obtain w where \<open>t_Q i = t_Q'' 0 @ w\<close> by blast
        have \<open>ftF v\<close> by (fact "*"(1))
        moreover have \<open>tF (?th_A (seqRun u x i))\<close>
          by (metis "*"(2) "**" Hiding_tickFree trace_hide_seqRun_eq_iff)
        moreover have \<open>t = ?th_A (seqRun u x i) @ v\<close>
          by (metis "*"(3) "**" trace_hide_seqRun_eq_iff)
        moreover have \<open>?th_A (seqRun u x i) setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?th_A (t_P i), ?th_A (t_Q i)), S)\<close>
          by (intro setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_trace_hide "****"(3))
        moreover have \<open>?th_A (t_Q i) \<in> \<D> (Q \ A)\<close>
        proof (unfold D_Hiding, clarify, intro exI conjI)
          show \<open>ftF (?th_A w)\<close>
            by (metis "******"(2) Hiding_front_tickFree \<open>t_Q i = t_Q'' 0 @ w\<close>
                tickFree_append_iff tickFree_imp_front_tickFree)
        next
          show \<open>tF (t_Q'' 0)\<close>
            by (metis "******"(2) \<open>t_Q i = t_Q'' 0 @ w\<close> tickFree_append_iff)
        next
          show \<open>?th_A (t_Q i) = ?th_A (t_Q'' 0) @ ?th_A w\<close>
            by (simp add: \<open>t_Q i = t_Q'' 0 @ w\<close>)
        next
          show \<open>t_Q'' 0 \<in> \<D> Q \<or> (\<exists>f. isInfHiddenRun f Q A \<and> t_Q'' 0 \<in> range f)\<close>
            using "$$" \<open>range t_Q'' \<subseteq> \<T> Q\<close> \<open>strict_mono t_Q''\<close> by blast
        qed
        moreover have \<open>?th_A (t_P i) \<in> \<T> (P \ A)\<close>
        proof (cases \<open>\<exists>t'. ?th_A t' = ?th_A (t_P i) \<and> (t', ev ` A) \<in> \<F> P\<close>)
          assume \<open>\<exists>t'. ?th_A t' = ?th_A (t_P i) \<and> (t', ev ` A) \<in> \<F> P\<close>
          then obtain t' where \<open>?th_A (t_P i) = ?th_A t'\<close> \<open>(t', ev ` A) \<in> \<F> P\<close> by metis
          thus \<open>?th_A (t_P i) \<in> \<T> (P \ A)\<close> unfolding T_Hiding by blast
        next
          assume \<open>\<nexists>t'. ?th_A t' = ?th_A (t_P i) \<and> (t', ev ` A) \<in> \<F> P\<close>
          with inf_hidden[OF _ "****"(1)] obtain t_P' j
            where \<open>isInfHiddenRun t_P' P A\<close> \<open>t_P i = t_P' j\<close> by blast
          thus \<open>?th_A (t_P i) \<in> \<T> (P \ A)\<close>
            unfolding T_Hiding using "******"(1) front_tickFree_Nil by blast
        qed
        ultimately show \<open>t \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A))\<close> unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
      qed
    qed
  qed
qed



lemma disjoint_Hiding_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding :
  \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l \ A \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. (P l \ A)\<close> if \<open>A \<inter> S = {}\<close>
proof (induct L rule: induct_list012)
  case 1 show ?case by simp
next
  case (2 l0)
  show ?case by (simp add: RenamingTick_Hiding)
next
  case (3 l0 l1 L)
  have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). P l \ A =
        P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). P l \ A\<close> by simp
  also have \<open>\<dots> \<sqsubseteq>\<^sub>F\<^sub>D (P l0 \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). P l \ A)\<close>
    by (simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.disjoint_Hiding_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding \<open>A \<inter> S = {}\<close>)
  also have \<open>\<dots> \<sqsubseteq>\<^sub>F\<^sub>D (P l0 \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). (P l \ A)\<close>
    by (simp add: "3.hyps"(2) Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD)
  also have \<open>\<dots> = \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). (P l \ A)\<close> by simp
  finally show ?case .
qed


lemma disjoint_finite_Hiding_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l \ A = \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. (P l \ A)\<close> if \<open>A \<inter> S = {}\<close> and \<open>finite A\<close>
proof (induct L rule: induct_list012)
  case 1 show ?case by simp
next
  case (2 l0)
  show ?case by (simp add: RenamingTick_Hiding)
next
  case (3 l0 l1 L)
  have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). P l \ A =
        P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). P l \ A\<close> by simp
  also have \<open>\<dots> = (P l0 \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). P l \ A)\<close>
    by (simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.disjoint_finite_Hiding_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>A \<inter> S = {}\<close> \<open>finite A\<close>)
  also have \<open>\<dots> = (P l0 \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). (P l \ A)\<close>
    by (simp add: "3.hyps"(2) Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD)
  also have \<open>\<dots> = \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). (P l \ A)\<close> by simp
  finally show ?case .
qed



section \<open>Other Laws of Synchronization Product\<close>

subsection \<open>Synchronization Set can be restricted\<close>

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_events_of :
  \<open>{a. ev a \<in> set u \<or> ev a \<in> set v} \<subseteq> A \<Longrightarrow>
   t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), S) \<longleftrightarrow>
   t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), S \<inter> A)\<close>
  by (induct \<open>(tick_join, u, S, v)\<close> arbitrary: t u v)
    (auto simp add: subset_iff split: option.split_asm)

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_events_of :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q = P \<lbrakk>S \<inter> (\<alpha>(P) \<union> \<alpha>(Q))\<rbrakk>\<^sub>\<checkmark> Q\<close>
proof -
  have * : \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q \<Longrightarrow>
            {a. ev a \<in> set t_P \<or> ev a \<in> set t_Q} \<subseteq> \<alpha>(P) \<union> \<alpha>(Q)\<close>
    \<open>(t_P, X_P) \<in> \<F> P \<Longrightarrow> (t_Q, X_Q) \<in> \<F> Q \<Longrightarrow>
     {a. ev a \<in> set t_P \<or> ev a \<in> set t_Q} \<subseteq> \<alpha>(P) \<union> \<alpha>(Q)\<close> for t_P t_Q X_P X_Q
    by (auto intro: events_of_memI dest: F_T D_T)
  show \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q = P \<lbrakk>S \<inter> (\<alpha>(P) \<union> \<alpha>(Q))\<rbrakk>\<^sub>\<checkmark> Q\<close>
  proof (rule Process_eq_optimizedI)
    show \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) \<Longrightarrow> t \<in> \<D> (P \<lbrakk>S \<inter> (\<alpha>(P) \<union> \<alpha>(Q))\<rbrakk>\<^sub>\<checkmark> Q)\<close> for t
      using setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_events_of[OF "*"(1)]
      unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
  next
    show \<open>t \<in> \<D> (P \<lbrakk>S \<inter> (\<alpha>(P) \<union> \<alpha>(Q))\<rbrakk>\<^sub>\<checkmark> Q) \<Longrightarrow> t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> for t
      using setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_events_of[OF "*"(1)]
      unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
  next
    fix t X assume \<open>(t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    then obtain t_P t_Q X_P X_Q
      where $ : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P S X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    from "$"(1) have \<open>(t_P, X_P \<union> {ev a |a. a \<notin> \<alpha>(P)}) \<in> \<F> P\<close>
      by (rule is_processT5) (auto intro: events_of_memI dest!: F_T)
    moreover from "$"(2) have \<open>(t_Q, X_Q \<union> {ev a |a. a \<notin> \<alpha>(Q)}) \<in> \<F> Q\<close>
      by (rule is_processT5) (auto intro: events_of_memI dest!: F_T)
    moreover from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_events_of
      [OF "*"(2)[OF "$"(1, 2)]] "$"(3)
    have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S \<inter> (\<alpha>(P) \<union> \<alpha>(Q)))\<close> by blast
    moreover from "$"(4)
    have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
              tick_join (X_P \<union> {ev a |a. a \<notin> \<alpha>(P)})
              (S \<inter> (\<alpha>(P) \<union> \<alpha>(Q))) (X_Q \<union> {ev a |a. a \<notin> \<alpha>(Q)})\<close>
      by (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
    ultimately show \<open>(t, X) \<in> \<F> (P \<lbrakk>S \<inter> (\<alpha>(P) \<union> \<alpha>(Q))\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  next
    fix t X assume \<open>(t, X) \<in> \<F> (P \<lbrakk>S \<inter> (\<alpha>(P) \<union> \<alpha>(Q))\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      \<open>t \<notin> \<D> (P \<lbrakk>S \<inter> (\<alpha>(P) \<union> \<alpha>(Q))\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    then obtain t_P t_Q X_P X_Q
      where $ : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S \<inter> (\<alpha>(P) \<union> \<alpha>(Q)))\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P (S \<inter> (\<alpha>(P) \<union> \<alpha>(Q))) X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_events_of
      [OF "*"(2)[OF "$"(1, 2)]] "$"(3)
    have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close> by blast
    moreover from "$"(4) have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P S X_Q\<close>
      by (meson Int_lower1 in_mono subsetI super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_mono)
    ultimately show \<open>(t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      using "$"(1, 2) by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  qed
qed

corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_events_of :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q = P \<lbrakk>S \<inter> A\<rbrakk>\<^sub>\<checkmark> Q\<close> if \<open>\<alpha>(P) \<union> \<alpha>(Q) \<subseteq> A\<close>
proof (rule trans[OF Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_events_of],
    rule trans[OF _ Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_events_of[symmetric]])
  show \<open>P \<lbrakk>S \<inter> (\<alpha>(P) \<union> \<alpha>(Q))\<rbrakk>\<^sub>\<checkmark> Q = P \<lbrakk>S \<inter> A \<inter> (\<alpha>(P) \<union> \<alpha>(Q))\<rbrakk>\<^sub>\<checkmark> Q\<close>
    using \<open>\<alpha>(P) \<union> \<alpha>(Q) \<subseteq> A\<close> by (auto intro: arg_cong[where f = \<open>\<lambda>S. P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q\<close>])
qed


lemma \<open>tF t \<Longrightarrow> {a. ev a \<in> set u} \<inter> S = {} \<Longrightarrow> a \<in> S \<Longrightarrow>
       \<not> t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, ev a # v), S)\<close>
proof (induct \<open>(tick_join, u, S, v)\<close> arbitrary: t u v)
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil a u)
  thus ?case by (simp add: disjoint_iff) (meson tickFree_Cons_iff)
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev a u b v)
  then show ?case by (simp add: disjoint_iff) (meson tickFree_Cons_iff)
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick a u s v)
  thus ?case
    by (simp add: disjoint_iff)
      (metis empty_iff list.set_intros(1)
        ev_notin_both_sets_imp_empty_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) 
qed simp_all



subsection \<open>Some Refinements\<close>

context Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale begin

lemma Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det_distr_FD :
  \<open>(\<sqinter> a \<in> A \<rightarrow> (P a \<lbrakk> C \<rbrakk>\<^sub>\<checkmark> (\<sqinter> b \<in> B \<rightarrow> Q b))) \<box>
   (\<sqinter> b \<in> B \<rightarrow> ((\<sqinter> a \<in> A \<rightarrow> P a) \<lbrakk> C \<rbrakk>\<^sub>\<checkmark> Q b))
   \<sqsubseteq>\<^sub>F\<^sub>D (\<sqinter> a \<in> A \<rightarrow> P a) \<lbrakk> C \<rbrakk>\<^sub>\<checkmark> (\<sqinter> b \<in> B \<rightarrow> Q b)\<close>
  (is \<open>?lhs1 \<box> ?lhs2 \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
  if \<open>A \<noteq> {}\<close> \<open>B \<noteq> {}\<close> \<open>A \<inter> C = {}\<close> \<open>B \<inter> C = {}\<close>
proof -
  have \<open>?lhs1 = \<sqinter> b\<in>B. \<sqinter> a\<in>A. (a \<rightarrow> (P a \<lbrakk>C\<rbrakk>\<^sub>\<checkmark> (b \<rightarrow> Q b)))\<close> (is \<open>_ = ?lhs1'\<close>)
    by (simp add: \<open>A \<noteq> {}\<close> \<open>B \<noteq> {}\<close> Mndetprefix_GlobalNdet
        Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right
        write0_def GlobalNdet_Mprefix_distr[OF \<open>B \<noteq> {}\<close>, symmetric])
      (subst GlobalNdet_sets_commute, simp)
  moreover have \<open>?lhs2 = \<sqinter> b\<in>B. \<sqinter> a\<in>A. (b \<rightarrow> (a \<rightarrow> P a \<lbrakk>C\<rbrakk>\<^sub>\<checkmark> Q b))\<close> (is \<open>_ = ?lhs2'\<close>)
    by (simp add: \<open>A \<noteq> {}\<close> \<open>B \<noteq> {}\<close> Mndetprefix_GlobalNdet
        Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right
        write0_def GlobalNdet_Mprefix_distr[OF \<open>A \<noteq> {}\<close>, symmetric])
  ultimately have \<open>?lhs1 \<box> ?lhs2 = ?lhs1' \<box> ?lhs2'\<close> by simp
  moreover have \<open>?lhs1' \<box> ?lhs2' \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter> b\<in>B. \<sqinter> a\<in>A.   (a \<rightarrow> (P a \<lbrakk>C\<rbrakk>\<^sub>\<checkmark> (b \<rightarrow> Q b)))
                                                    \<box> (b \<rightarrow> ((a \<rightarrow> P a) \<lbrakk>C\<rbrakk>\<^sub>\<checkmark> Q b))\<close>
    by (auto simp add: \<open>A \<noteq> {}\<close> \<open>B \<noteq> {}\<close> refine_defs GlobalNdet_projs Det_projs write0_def)
  moreover have \<open>\<dots> = \<sqinter> b\<in>B. \<sqinter> a\<in>A. ((a \<rightarrow> P a) \<lbrakk>C\<rbrakk>\<^sub>\<checkmark> (b \<rightarrow> Q b))\<close>
    by (rule mono_GlobalNdet_eq, rule mono_GlobalNdet_eq,
        simp add: write0_def, subst Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_indep)
      (use \<open>A \<inter> C = {}\<close> \<open>B \<inter> C = {}\<close> in auto)
  moreover have \<open>\<dots> = ?rhs\<close>
    by (simp add: \<open>A \<noteq> {}\<close> \<open>B \<noteq> {}\<close> Mndetprefix_GlobalNdet
        Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right)
  ultimately show \<open>?lhs1 \<box> ?lhs2 \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close> by argo
qed


lemmas Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det_distr_F =
  Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det_distr_FD[THEN leFD_imp_leF]

lemmas Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det_distr_D =
  Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det_distr_FD[THEN leFD_imp_leD]

lemmas Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det_distr_T =
  Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det_distr_F[THEN leF_imp_leT]

lemma Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det_distr_DT :
  \<open>\<lbrakk>A \<noteq> {}; B \<noteq> {}; A \<inter> C = {}; B \<inter> C = {}\<rbrakk> \<Longrightarrow>
   (\<sqinter> a \<in> A \<rightarrow> (P a \<lbrakk> C \<rbrakk>\<^sub>\<checkmark> (\<sqinter> b \<in> B \<rightarrow> Q b))) \<box>
   (\<sqinter> b \<in> B \<rightarrow> ((\<sqinter> a \<in> A \<rightarrow> P a) \<lbrakk> C \<rbrakk>\<^sub>\<checkmark> Q b))
   \<sqsubseteq>\<^sub>D\<^sub>T (\<sqinter> a \<in> A \<rightarrow> P a) \<lbrakk> C \<rbrakk>\<^sub>\<checkmark> (\<sqinter> b \<in> B \<rightarrow> Q b)\<close>
  by (simp add: Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det_distr_D
      Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det_distr_T leD_leT_imp_leDT)


end

(*<*)
end
  (*>*)