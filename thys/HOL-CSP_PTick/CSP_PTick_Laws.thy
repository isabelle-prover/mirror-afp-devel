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


unbundle option_type_syntax


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
    by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis D_imp_ftF)
  thus \<open>s \<in> \<D> ?lhs\<close>
  proof cases
    case D_P
    from D_P(2, 3) have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 \<in> \<D> (Renaming P f g)\<close>
      by (auto simp add: D_Renaming intro: ftF_Nil)
    hence \<open>map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) \<in> \<D> ?lhs\<close>
      unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs
      by (metis (mono_tags, lifting) ftF_Nil D_P(3)
          tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff append.right_neutral mem_Collect_eq Un_iff)
    also have \<open>map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) =
               map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1)\<close>
      by (simp add: \<open>tF t1\<close> tF_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is)
    finally show \<open>s \<in> \<D> ?lhs\<close>
      by (auto simp add: "*"(1) D_P(1) intro!: is_processT7)
        (metis list.map_comp tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff tF_map_ev_comp,
          use "*"(2, 3) D_P(1) ftF_append tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff tF_append_iff in blast)
  next
    case D_Q
    from "*"(2) D_Q(1, 5) have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2 \<in> \<D> (Renaming (Q r) f g')\<close>
      by (auto simp add: D_Renaming intro: ftF_Nil)
    hence \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2 \<in> \<D> (\<sqinter>r' \<in> {r' \<in> \<^bold>\<checkmark>\<^bold>s(P). g r = g r'}. Renaming (Q r') f g')\<close>
      by (simp add: D_GlobalNdet)
        (metis D_Q(2, 3) is_processT9 strict_ticks_of_memI)
    moreover from D_Q(2) have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 @ [\<checkmark>(g r)] \<in> \<T> (Renaming P f g)\<close>
      by (auto simp add: T_Renaming)
    moreover have \<open>tF (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1)\<close>
      by (simp add: D_Q(4) tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
    ultimately have \<open>map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) @
                     map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2 \<in> \<D> ?lhs\<close>
      unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    with "*"(2, 3) have \<open>map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) @
                         map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2 @ s2 \<in> \<D> ?lhs\<close>
      by (auto simp add: D_Q(1) comp_assoc tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff
          intro!: is_processT7[of \<open>_ @ _\<close>, simplified])
    also from D_Q(4) have \<open>map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) @
                           map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2 @ s2 = s\<close>
      by (simp add: "*"(1) D_Q(1))
        (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_sel(1) in_set_conv_decomp tF_Cons_iff tF_append_iff)
    finally show \<open>s \<in> \<D> ?lhs\<close> .
  qed
next
  assume subset_div : \<open>\<D> ?rhs \<subseteq> \<D> ?lhs\<close>
  fix s X assume \<open>(s, X) \<in> \<F> ?rhs\<close>
  then consider \<open>s \<in> \<D> ?rhs\<close>
    | (fail) s1 where \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') s1\<close>
      \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g' -` X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> \<open>s1 \<notin> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
    by (simp add: Renaming_projs)
      (metis (no_types, opaque_lifting) ftF_Nil ftF_iff_tF_butlast
        ftF_Cons_iff[of \<open>last s\<close> \<open>[]\<close>] map_butlast[of \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g'\<close>]
        map_is_Nil_conv[of \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g'\<close> \<open>[]\<close>] map_is_Nil_conv[of \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g'\<close>]
        append_self_conv[of \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') _\<close> \<open>[]\<close>] F_imp_ftF
        snoc_eq_iff_butlast[of \<open>butlast s\<close> \<open>last s\<close> s]
        div_butlast_when_non_tF_iff not_tF_imp_not_Nil)
  thus \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof cases
    from subset_div D_F show \<open>s \<in> \<D> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> by blast
  next
    case fail
    from fail(2, 3)
    consider (F_P) t1 where \<open>s1 = map (ev \<circ> of_ev) t1\<close> \<open>(t1, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g' -` X)) \<in> \<F> P\<close> \<open>tF t1\<close>
      | (F_Q) t1 r t2 where \<open>s1 = map (ev \<circ> of_ev) t1 @ t2\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t1\<close> \<open>t1 \<notin> \<D> P\<close> \<open>(t2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g' -` X) \<in> \<F> (Q r)\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis F_imp_ftF)
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
        by (fastforce simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
      also have \<open>map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) = s\<close>
        by (simp add: fail(1) F_P(1))
          (metis F_P(3) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_sel(1) in_set_conv_decomp tF_Cons_iff tF_append_iff)
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
        by (simp add: F_Q(3) tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
      ultimately have \<open>(map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) @
                        map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2, X) \<in> \<F> ?lhs\<close>
        unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by fast
      also have \<open>map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) @ map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2 = s\<close>
        by (simp add: fail(1) F_Q(1))
          (metis F_Q(3) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_sel(1) in_set_conv_decomp
            tF_Cons_iff tF_append_iff)
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
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (use D_imp_ftF in blast)
    thus \<open>s \<in> \<D> ?lhs\<close>
    proof cases
      case D_P
      from D_P(2) obtain t1 t2
        where * : \<open>s1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 @ t2\<close> \<open>tF t1\<close> \<open>ftF t2\<close> \<open>t1 \<in> \<D> P\<close>
        unfolding D_Renaming by blast
      from "*"(2, 4) have \<open>map (ev \<circ> of_ev) t1 \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs intro: ftF_Nil)
      hence \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1) \<in> \<D> ?lhs\<close>
        unfolding D_Renaming mem_Collect_eq
        by (metis (mono_tags, lifting) ftF_Nil tF_map_ev_comp append.right_neutral)
      also have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1) =
                 map (ev \<circ> of_ev) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1)\<close>
        by simp (metis "*"(2) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_sel(1) in_set_conv_decomp tF_Cons_iff tF_append_iff)
      finally show \<open>s \<in> \<D> ?lhs\<close>
        by (auto simp add: D_P(1, 4) "*"(1) ftF_append comp_assoc intro!: is_processT7)
    next
      case D_Q
      have \<open>s1 @ [\<checkmark>(g_r)] \<notin> \<D> (Renaming P f g)\<close> by (meson D_Q(3) is_processT9)
      with D_Q(2-4) obtain t1 r
        where * : \<open>g_r = g r\<close> \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close> \<open>s1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> P\<close>
        by (auto simp add: Renaming_projs append_eq_map_conv tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
          (metis append_Nil2 ftF_Nil is_processT9 tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff strict_ticks_of_memI)
      from "*"(1, 2) \<open>inj_on g \<^bold>\<checkmark>\<^bold>s(P)\<close> have \<open>(THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> g_r = g r) = r\<close>
        by (auto dest: inj_onD)
      with D_Q(5) have \<open>s2 \<in> \<D> (Renaming (Q r) f g')\<close> by simp
      then obtain t2 t3
        where ** : \<open>s2 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2 @ t3\<close> \<open>tF t2\<close> \<open>ftF t3\<close> \<open>t2 \<in> \<D> (Q r)\<close>
        unfolding D_Renaming by blast
      from "*"(4) "**"(4) have \<open>map (ev \<circ> of_ev) t1 @ t2 \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis append_T_imp_tF not_Cons_self)
      with "**"(2) have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1 @ t2) \<in> \<D> ?lhs\<close>
        unfolding D_Renaming mem_Collect_eq
        by (metis append.right_neutral ftF_Nil tF_append_iff tF_map_ev_comp)
      moreover have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1 @ t2) @ t3 = s\<close>
        by (simp add: D_Q(1) "*"(3) "**"(1))
          (metis "*"(3) D_Q(4) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_sel(1) in_set_conv_decomp
            tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff tF_Cons_iff tF_append_iff)
      ultimately show \<open>s \<in> \<D> ?lhs\<close>
        by (auto simp add: "**"(3) intro!: is_processT7[of \<open>_ @ _\<close>, simplified])
          (use "**"(1) D_Q(1) in force, use "**"(2) tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff in blast)
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
        (metis (no_types, lifting) F_imp_ftF ftF_charn self_append_conv)
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
          (metis "*"(1) F_P(4) tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
      hence \<open>(map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1), X) \<in> \<F> ?lhs\<close>
        unfolding F_Renaming by blast
      also have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1) = s\<close>
        by (simp add: F_P(1) "*"(1))
          (metis "*"(1) F_P(4) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_sel(1) in_set_conv_decomp
            tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff tF_Cons_iff tF_append_iff)
      finally show \<open>(s, X) \<in> \<F> ?lhs\<close> .
    next
      case F_Q
      have \<open>s1 @ [\<checkmark>(g_r)] \<notin> \<D> (Renaming P f g)\<close> by (meson F_Q(3) is_processT9)
      with F_Q(2-4) obtain t1 r
        where * : \<open>g_r = g r\<close> \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close> \<open>s1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> P\<close>
        by (auto simp add: Renaming_projs append_eq_map_conv tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
          (metis append_Nil2 ftF_Nil is_processT9 tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff strict_ticks_of_memI)
      from "*"(1, 2) \<open>inj_on g \<^bold>\<checkmark>\<^bold>s(P)\<close> have \<open>(THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> g_r = g r) = r\<close>
        by (auto dest: inj_onD)
      with F_Q(5, 6) have \<open>(s2, X) \<in> \<F> (Renaming (Q r) f g')\<close>
        \<open>s2 \<notin> \<D> (Renaming (Q r) f g')\<close> by simp_all
      then obtain t2 where ** : \<open>s2 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') t2\<close> \<open>(t2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g' -` X) \<in> \<F> (Q r)\<close>
        unfolding Renaming_projs by blast
      from "*"(4) "**"(2) have \<open>(map (ev \<circ> of_ev) t1 @ t2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g' -` X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis append_T_imp_tF not_Cons_self2)
      hence \<open>(map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1 @ t2), X) \<in> \<F> ?lhs\<close>
        unfolding F_Renaming by blast
      also have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g') (map (ev \<circ> of_ev) t1 @ t2) = s\<close>
        by (simp add: F_Q(1) "*"(3) "**"(1))
          (metis "*"(3) F_Q(4) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_sel(1) in_set_conv_decomp
            tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff tF_Cons_iff tF_append_iff)
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
        (metis (no_types, opaque_lifting) T_imp_ftF append_Nil2 butlast_snoc
          div_butlast_when_non_tF_iff ftF_Nil
          ftF_iff_tF_butlast ftF_single map_butlast)
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


\<comment>\<open>New in Isabelle26.\<close>
corollary Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_on_RenamingTick :
  \<open>RenamingTick P g \<^bold>;\<^sub>\<checkmark> Q = P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q (g r))\<close> if \<open>inj_on g \<^bold>\<checkmark>\<^bold>s(P)\<close>
proof -
  from inj_on_Renaming_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF that, where g' = id and f = id and Q = \<open>\<lambda>r. Q (g r)\<close>]
  have \<open>P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q (g r)) = RenamingTick P g \<^bold>;\<^sub>\<checkmark> (\<lambda>g_r. Q (g (THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> g_r = g r)))\<close> by simp
  also have \<open>\<dots> = RenamingTick P g \<^bold>;\<^sub>\<checkmark> Q\<close>
  proof (rule mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq[OF refl arg_cong[where f = Q]])
    show \<open>g_r \<in> \<^bold>\<checkmark>\<^bold>s(RenamingTick P g) \<Longrightarrow> g (THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> g_r = g r) = g_r\<close> for g_r
      by (simp add: strict_ticks_of_RenamingTick image_iff)
        (metis (mono_tags, lifting) inj_on_eq_iff that the_equality)
  qed
  finally show \<open>RenamingTick P g \<^bold>;\<^sub>\<checkmark> Q = P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q (g r))\<close> ..
qed


\<comment>\<open>New in Isabelle26.\<close>
corollary Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_RenamingTick_permute_list :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P) \<Longrightarrow> f permutes {..<n} \<Longrightarrow>
   RenamingTick P (permute_list f) \<^bold>;\<^sub>\<checkmark> Q = P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q (permute_list f r))\<close>
  by (intro Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_on_RenamingTick inj_onI)
    (metis is_ticks_lengthD permute_list_compose permute_list_id permutes_inv permutes_inv_o(1))



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

theorem (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) inj_RenamingEv_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
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
        (metis "**"(2,4) append_self_conv ftF_map_tick_iff
          list.map_disc_iff tF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)+
    moreover have \<open>t = ?map u @ (?map v @ t2)\<close> by (simp add: "*"(1) "**"(1))
    moreover have \<open>tF (?map u)\<close> by (simp add: "**"(2) tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
    moreover from "*"(2,3) "**"(1) have \<open>ftF (?map v @ t2)\<close>
      using ftF_append tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff tF_append_iff by blast
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
        from "*"(2) "***"(1) "****"(1) tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff
          T_Q(2) \<open>t_Q11' \<le> t_Q1\<close> is_processT3_TR
        have \<open>u1' = u1' @ []\<close> \<open>tF u1'\<close> \<open>ftF []\<close> \<open>t_Q11' \<in> \<T> Q\<close> by simp_all blast
        with "****"(2) "**"(4) have \<open>u1' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
          unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
        moreover have \<open>t = ?map u1' @ (u2 @ v)\<close> by (simp add: "*"(1) "***"(1) "****"(1))
        moreover have \<open>ftF (u2 @ v)\<close>
          using "*"(2,3) "***"(1) ftF_append tF_append_iff by blast
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
          moreover from "**"(2) "****"(2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tF_imp
          have \<open>tF u1'\<close> by blast
          moreover from D_Q(4) D_T \<open>t_Q1'' \<le> t_Q1\<close> is_processT3_TR
          have \<open>t_Q1'' \<in> \<T> Q\<close> by blast
          ultimately have \<open>u1' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
            unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k using \<open>t_P1 \<in> \<D> P\<close> "****"(2) by blast
          moreover from "*"(1-3) "****"(1)
          have \<open>t = ?map u1' @ (u2 @ v)\<close> \<open>ftF (u2 @ v)\<close>
            by (auto simp add: \<open>u = u1 @ u2\<close> ftF_append)
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
          moreover from D_Q(2) "****"(2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tF_imp
          have \<open>tF u1'\<close> by blast
          moreover from "**"(4) D_T \<open>t_P1'' \<le> t_P1\<close> is_processT3_TR
          have \<open>t_P1'' \<in> \<T> P\<close> by blast
          ultimately have \<open>u1' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
            unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k using \<open>t_Q1 \<in> \<D> Q\<close> "****"(2) by blast
          moreover from "*"(1-3) "****"(1)
          have \<open>t = ?map u1' @ (u2 @ v)\<close> \<open>ftF (u2 @ v)\<close>
            by (auto simp add: \<open>u = u1 @ u2\<close> ftF_append)
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
        from "*"(2) "***"(1) "****"(1) tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff
          T_P(2) \<open>t_P11' \<le> t_P1\<close> is_processT3_TR
        have \<open>u1' = u1' @ []\<close> \<open>tF u1'\<close> \<open>ftF []\<close> \<open>t_P11' \<in> \<T> P\<close> by simp_all blast
        with "****"(2) "**"(4) have \<open>u1' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
          unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
        moreover have \<open>t = ?map u1' @ (u2 @ v)\<close> by (simp add: "*"(1) "***"(1) "****"(1))
        moreover have \<open>ftF (u2 @ v)\<close>
          using "*"(2,3) "***"(1) ftF_append tF_append_iff by blast
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
          moreover from D_P(2) "****"(2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tF_imp
          have \<open>tF u1'\<close> by blast
          moreover from "**"(4) D_T \<open>t_Q1'' \<le> t_Q1\<close> is_processT3_TR
          have \<open>t_Q1'' \<in> \<T> Q\<close> by blast
          ultimately have \<open>u1' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
            unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k using \<open>t_P1 \<in> \<D> P\<close> "****"(2) by blast
          moreover from "*"(1-3) "****"(1)
          have \<open>t = ?map u1' @ (u2 @ v)\<close> \<open>ftF (u2 @ v)\<close>
            by (auto simp add: \<open>u = u1 @ u2\<close> ftF_append)
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
          moreover from "**"(2) "****"(2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tF_imp
          have \<open>tF u1'\<close> by blast
          moreover from D_P(4) D_T \<open>t_P1'' \<le> t_P1\<close> is_processT3_TR
          have \<open>t_P1'' \<in> \<T> P\<close> by blast
          ultimately have \<open>u1' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
            unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k using \<open>t_Q1 \<in> \<D> Q\<close> "****"(2) by blast
          moreover from "*"(1-3) "****"(1)
          have \<open>t = ?map u1' @ (u2 @ v)\<close> \<open>ftF (u2 @ v)\<close>
            by (auto simp add: \<open>u = u1 @ u2\<close> ftF_append)
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
          (metis (no_types) append_Nil2 ftF_Nil map_append ftF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
      with \<open>t \<notin> \<D> ?lhs\<close> show False ..
    qed
    with "*" obtain t_P t_Q X_P X_Q
      where ** : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
        \<open>?fun -` X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P S X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by fast
    from "**"(2, 3) F_T \<open>t' \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> append_Nil2 ftF_Nil
    have \<open>t_P \<notin> \<D> P\<close> unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k' by blast
    from "**"(1, 3) F_T \<open>t' \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> append_Nil2 ftF_Nil
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
          by (metis "**"(1) F_imp_ftF prefixE \<open>tF t_P1\<close> ftF_append_iff
              is_processT7 tF_Nil tF_imp_ftF)
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
          by (metis "**"(2) F_imp_ftF prefixE \<open>tF t_Q1\<close> ftF_append_iff
              is_processT7 tF_Nil tF_imp_ftF)
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
          (metis "*"(1-3) F_T append_Nil2 ftF_Nil)
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

theorem Hiding_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding :
  \<open>(P \<^bold>;\<^sub>\<checkmark> Q) \ S \<sqsubseteq>\<^sub>F\<^sub>D (P \ S) \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \ S)\<close> (is \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
proof (rule failure_divergence_refine_optimizedI)
  let ?th = \<open>\<lambda>t. trace_hide t (ev ` S)\<close> and ?map = \<open>\<lambda>t. map (ev \<circ> of_ev) t\<close>
  fix t assume \<open>t \<in> \<D> ?rhs\<close>
  with D_imp_ftF is_processT9
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
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs intro: ftF_Nil)
      with mem_D_imp_mem_D_Hiding show \<open>?th (?map u') \<in> \<D> ?lhs\<close> .
    next
      assume \<open>isInfHidden_seqRun x P S u'\<close>
      from this isInfHidden_seqRun_imp_tF_seqRun[OF this]
      have \<open>isInfHidden_seqRun (ev \<circ> of_ev \<circ> x) (P \<^bold>;\<^sub>\<checkmark> Q) S (?map u')\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs image_iff)
          (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) list.map_comp map_append seqRun_def)
      thus \<open>?th (?map u') \<in> \<D> ?lhs\<close>
        by (simp add: D_Hiding_seqRun)
          (metis (no_types) append.right_neutral comp_apply
            ftF_Nil tF_map_ev_comp)
    qed
    also have \<open>?th (?map u') = ?map (?th u')\<close>
      by (fact tF_trace_hide_map_ev_comp_of_ev[OF \<open>tF u'\<close>])
    finally show \<open>t \<in> \<D> ?lhs\<close>
      by (simp add: D_P(1, 4) "*"(1) ftF_append is_processT7)
  next
    case D_Q
    from D_Q(2, 3) obtain u' where \<open>u @ [\<checkmark>(r)] = ?th u'\<close> \<open>(u', ev ` S) \<in> \<F> P\<close>
      unfolding T_Hiding D_Hiding by fast
    then obtain u' where \<open>u = ?th u'\<close> \<open>(u' @ [\<checkmark>(r)], ev ` S) \<in> \<F> P\<close>
      by (cases u' rule: rev_cases, simp_all split: if_split_asm)
        (metis Hiding_tF event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) ftF_nonempty_append_imp is_processT2
          not_Cons_self2 tF_Cons_iff tF_append_iff)
    from D_Q(5) obtain v' w' x where * : \<open>v = ?th v' @ w'\<close> \<open>tF v'\<close> \<open>ftF w'\<close>
      \<open>v' \<in> \<D> (Q r) \<or> isInfHidden_seqRun x (Q r) S v'\<close>
      by (blast elim: D_Hiding_seqRunE)
    from "*"(4) have \<open>?th (?map u' @ v') \<in> \<D> ?lhs\<close>
    proof (elim disjE)
      assume \<open>v' \<in> \<D> (Q r)\<close>
      hence \<open>?map u' @ v' \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          (metis F_T \<open>(u' @ [\<checkmark>(r)], ev ` S) \<in> \<F> P\<close> append_T_imp_tF not_Cons_self)
      with mem_D_imp_mem_D_Hiding show \<open>?th (?map u' @ v') \<in> \<D> ?lhs\<close> .
    next
      assume \<open>isInfHidden_seqRun x (Q r) S v'\<close>
      hence \<open>isInfHidden_seqRun x (P \<^bold>;\<^sub>\<checkmark> Q) S (?map u' @ v')\<close>
        by (simp add: seqRun_def image_iff Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          (metis F_T \<open>(u' @ [\<checkmark>(r)], ev ` S) \<in> \<F> P\<close> append_T_imp_tF list.discI)
      thus \<open>?th (?map u' @ v') \<in> \<D> ?lhs\<close>
        by (simp add: D_Hiding_seqRun)
          (metis append.right_neutral filter_append
            ftF_Nil isInfHidden_seqRun_imp_tF)
    qed
    also have \<open>?th (?map u' @ v') = ?map (?th u') @ ?th v'\<close>
      using D_Q(4) Hiding_tF \<open>u = ?th u'\<close> tF_trace_hide_map_ev_comp_of_ev by auto
    finally have \<open>?map (?th u') @ ?th v' \<in> \<D> ?lhs\<close> .
    moreover have \<open>tF (?map (?th u') @ ?th v')\<close>
      by (simp add: "*"(2) Hiding_tF)
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
      (metis F_T T_imp_ftF ftF_Nil is_processT9 self_append_conv)
  thus \<open>(t, X) \<in> \<F> ?lhs\<close>
  proof cases
    case div with subset_div show \<open>(t, X) \<in> \<F> ?lhs\<close>
      by (simp add: in_mono is_processT8)
  next
    case F_P
    from F_P(2, 3) obtain u' where * : \<open>u = ?th u'\<close> \<open>(u', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X \<union> ev ` S) \<in> \<F> P\<close>
      unfolding F_Hiding D_Hiding by fast
    have \<open>tF u'\<close> using "*"(1) F_P(4) Hiding_tF by blast
    have $ : \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (X \<union> ev ` S) = ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X \<union> ev ` S\<close>
      by (auto simp add: image_iff ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
        (metis Int_iff Un_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) image_eqI rangeI)
    from \<open>tF u'\<close> "*"(2) have \<open>(?map u', X \<union> ev ` S) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs "$")
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
      by (simp add: F_Hiding)
        (metis "*"(1) F_P(1) \<open>tF u'\<close> tF_trace_hide_map_ev_comp_of_ev)
  next
    case F_Q
    from F_Q(2, 3) obtain u' where \<open>u @ [\<checkmark>(r)] = ?th u'\<close> \<open>(u', ev ` S) \<in> \<F> P\<close>
      unfolding T_Hiding D_Hiding by fast
    then obtain u' where * : \<open>u = ?th u'\<close> \<open>(u' @ [\<checkmark>(r)], ev ` S) \<in> \<F> P\<close>
      by (cases u' rule: rev_cases, simp_all split: if_split_asm)
        (metis Hiding_tF event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) ftF_nonempty_append_imp is_processT2
          not_Cons_self2 tF_Cons_iff tF_append_iff)
    from F_Q(5, 6) obtain v' where ** : \<open>v = ?th v'\<close> \<open>(v', X \<union> ev ` S) \<in> \<F> (Q r)\<close>
      unfolding F_Hiding D_Hiding by blast
    have \<open>(?map u' @ v', X \<union> ev ` S) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
        (metis "*"(2) "**"(2) F_T append_T_imp_tF list.distinct(1))
    with F_Q(4) show \<open>(t, X) \<in> \<F> ?lhs\<close>
      by (simp add: F_Hiding F_Q(1) "*"(1) "**"(1))
        (metis Hiding_tF filter_append tF_trace_hide_map_ev_comp_of_ev)
  qed
qed

(* 
Hiding_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding (\<lambda>r. (SEQ\<^sub>\<checkmark> l \<in>@ L. P l) r \ S) = SEQ\<^sub>\<checkmark> l \<in>@ L. (\<lambda>r. P l r \ S)
 *)
corollary Hiding_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding :
  \<open>(SEQ\<^sub>\<checkmark> l \<in>@ L. P l) r \ S \<sqsubseteq>\<^sub>F\<^sub>D (SEQ\<^sub>\<checkmark> l \<in>@ L. (\<lambda>r. P l r \ S)) r\<close>
  by (induct L arbitrary: r rule: induct_list012)
    (auto intro: trans_FD[OF Hiding_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding] mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD)



text \<open>If we assume \<^term>\<open>\<bbbF>\<^sub>\<checkmark>(P)\<close>, we can recover the equality (new in Isabelle26).\<close>

theorem finite_ticks_Hiding_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>(P \<^bold>;\<^sub>\<checkmark> Q) \ S = (P \ S) \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \ S)\<close> (is \<open>?lhs = ?rhs\<close>) if \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close>
for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and Q :: \<open>'r \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (rule FD_antisym)
  from Hiding_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding show \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close> .
next
  let ?th = \<open>\<lambda>t. trace_hide t (ev ` S)\<close> and ?map = \<open>\<lambda>t. map (ev \<circ> of_ev) t\<close>
  show \<open>?rhs \<sqsubseteq>\<^sub>F\<^sub>D ?lhs\<close>
  proof (rule failure_divergence_refine_optimizedI)
    assume subset_div : \<open>\<D> ?lhs \<subseteq> \<D> ?rhs\<close>
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close>
    then consider (div) \<open>t \<in> \<D> ?lhs\<close>
      | (not_div) t' where \<open>t = ?th t'\<close> \<open>(t', X \<union> ev ` S) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> \<open>t' \<notin> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
      by (simp add: F_Hiding D_Hiding) (use div mem_D_imp_mem_D_Hiding in blast)
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
    proof cases
      case div with subset_div show \<open>(t, X) \<in> \<F> ?rhs\<close>
        by (simp add: in_mono is_processT8)
    next
      case not_div
      from not_div(2, 3) consider (F_P) u where \<open>t' = ?map u\<close> \<open>(u, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (X \<union> ev ` S)) \<in> \<F> P\<close> \<open>tF u\<close>
        | (F_Q) u r v where \<open>t' = ?map u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF u\<close> \<open>(v, X \<union> ev ` S) \<in> \<F> (Q r)\<close>
        unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by fast
      thus \<open>(t, X) \<in> \<F> ?rhs\<close>
      proof cases
        case F_P
        from F_P(2) have \<open>(?th u, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (P \ S)\<close>
          by (auto simp add: F_Hiding ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_union_image_ev)
        hence \<open>(?map (?th u), X) \<in> \<F> ?rhs\<close>
          by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis F_P(3) Hiding_tF)
        also have \<open>?map (?th u) = t\<close>
          by (metis not_div(1) F_P(1, 3) tF_trace_hide_map_ev_comp_of_ev)
        finally show \<open>(t, X) \<in> \<F> ?rhs\<close> .
      next
        case F_Q
        from mem_T_imp_mem_T_Hiding F_Q(2) have \<open>?th (u @ [\<checkmark>(r)]) \<in> \<T> (P \ S)\<close> .
        also have \<open>?th (u @ [\<checkmark>(r)]) = ?th u @ [\<checkmark>(r)]\<close> by (simp add: image_iff)
        finally have \<open>?th u @ [\<checkmark>(r)] \<in> \<T> (P \ S)\<close> .
        moreover from F_Q(4) have \<open>(?th v, X) \<in> \<F> (Q r \ S)\<close> by (auto simp add: F_Hiding)
        ultimately have \<open>(?map (?th u) @ ?th v, X) \<in> \<F> ?rhs\<close>
          by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis append_T_imp_tF not_Cons_self2)
        also have \<open>?map (?th u) @ ?th v = t\<close>
          by (simp add: not_div(1) F_Q(1, 3) tF_trace_hide_map_ev_comp_of_ev)
        finally show \<open>(t, X) \<in> \<F> ?rhs\<close> .
      qed
    qed
  next
    fix t assume \<open>t \<in> \<D> ?lhs\<close>
    then obtain u v x where * : \<open>t = ?th u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
      \<open>u \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q) \<or> isInfHidden_seqRun_strong x (P \<^bold>;\<^sub>\<checkmark> Q) S u\<close>
      by (blast elim: D_Hiding_seqRunE)
    from "*"(4) have \<open>?th u \<in> \<D> ?rhs\<close>
    proof (elim disjE)
      assume \<open>u \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
      then consider (D_P) u' v' where \<open>u = ?map u' @ v'\<close> \<open>u' \<in> \<D> P\<close> \<open>tF u'\<close> \<open>ftF v'\<close>
        | (D_Q) u' r v' where \<open>u = ?map u' @ v'\<close> \<open>u' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF u'\<close> \<open>v' \<in> \<D> (Q r)\<close>
        unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
      thus \<open>?th u \<in> \<D> ?rhs\<close>
      proof cases
        case D_P
        from mem_D_imp_mem_D_Hiding D_P(2) have \<open>?th u' \<in> \<D> (P \ S)\<close> .
        with D_P(3) have \<open>?map (?th u') \<in> \<D> ?rhs\<close>
          by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
            (metis Hiding_tF append.right_neutral ftF_Nil)
        also have \<open>?map (?th u') = ?th (?map u')\<close>
          by (simp add: D_P(3) tF_trace_hide_map_ev_comp_of_ev)
        finally have \<open>?th (?map u') \<in> \<D> ?rhs\<close> .
        thus \<open>?th u \<in> \<D> ?rhs\<close>
          by (simp add: D_P(1))
            (metis (lifting) "*"(2) D_P(1) filter_map is_processT7 tF_append_iff
              tF_iff_is_map_ev tF_imp_ftF)
      next
        case D_Q
        from mem_T_imp_mem_T_Hiding D_Q(2) have \<open>?th (u' @ [\<checkmark>(r)]) \<in> \<T> (P \ S)\<close> .
        also have \<open>?th (u' @ [\<checkmark>(r)]) = ?th u' @ [\<checkmark>(r)]\<close> by (simp add: image_iff)
        finally have \<open>?th u' @ [\<checkmark>(r)] \<in> \<T> (P \ S)\<close> .
        moreover from mem_D_imp_mem_D_Hiding D_Q(4) have \<open>?th v' \<in> \<D> (Q r \ S)\<close> .
        ultimately have \<open>?map (?th u') @ ?th v' \<in> \<D> ?rhs\<close>
          by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis append_T_imp_tF not_Cons_self2)
        also have \<open>?map (?th u') @ ?th v' = ?th u\<close>
          by (simp add: D_Q(1, 3) tF_trace_hide_map_ev_comp_of_ev)
        finally show \<open>?th u \<in> \<D> ?rhs\<close> .
      qed
    next
      assume assm : \<open>isInfHidden_seqRun_strong x (P \<^bold>;\<^sub>\<checkmark> Q) S u\<close>
      hence \<euro> : \<open>x i \<in> ev ` S\<close> for i by blast
      define U2 :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
        where \<open>U2 \<equiv> {u' |u'. u' \<in> \<T> P \<and> u' \<notin> \<D> P \<and> tF u'}\<close>
      define U3 :: \<open>('a, 's) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
        where \<open>U3 \<equiv> {?map u' @ v' | u' r v'. u' @ [\<checkmark>(r)] \<in> \<T> P \<and> u' \<notin> \<D> P \<and> tF u' \<and> v' \<in> \<T> (Q r) \<and> v' \<notin> \<D> (Q r)}\<close>
      have \<open>seqRun u x i \<in> ?map ` U2 \<union> U3\<close> for i
        using assm[rule_format, of i]
        by (simp add: U2_def U3_def Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs image_iff, safe, simp_all)
          ((auto)[1], metis T_imp_ftF)
      then consider \<open>infinite {i. seqRun u x i \<in> ?map ` U2}\<close>
        | j where \<open>finite {i. seqRun u x i \<in> ?map ` U2}\<close> \<open>\<And>i. j \<le> i \<Longrightarrow> seqRun u x i \<in> U3\<close>
        by (metis (no_types, lifting) Un_iff ex_least_nat_le finite_nat_set_iff_bounded mem_Collect_eq order_class.order_eq_iff)
      thus \<open>?th u \<in> \<D> ?rhs\<close>
      proof cases
        assume \<open>infinite {i. seqRun u x i \<in> ?map ` U2}\<close>
        hence \<open>\<exists>\<^sub>\<infinity>i. seqRun u x i \<in> ?map ` U2\<close>
          by (simp add: frequently_cofinite)
        then obtain f :: \<open>nat \<Rightarrow> nat\<close>
          where $ : \<open>strict_mono f\<close> \<open>\<And>i. seqRun u x (f i) \<in> ?map ` U2\<close>
          by (blast dest: extraction_subseqD[where \<sigma> = id, simplified])
        define g :: \<open>nat \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list\<close>
          where \<open>g i \<equiv> ?map (seqRun u x (f i))\<close> for i
        from "$"(1) have \<open>strict_mono g\<close>
          by (auto intro!: strict_monoI simp add: g_def)
            (metis strict_mono_less strict_mono_map strict_mono_seqRun)
        moreover from "$"(2) have \<open>g i \<in> \<T> P\<close> for i
          by (simp add: g_def U2_def image_iff)
            (metis tF_map_ev_of_ev_eq_iff)
        moreover have \<open>?th (g i) = ?th (g 0)\<close> for i
        proof -
          have \<open>g i = ?map (seqRun u x (f i))\<close> by (simp only: g_def)
          also from assm have \<open>?th \<dots> = ?th (?map u)\<close>
            by (simp add: seqRun_def image_iff filter_empty_conv) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1))
          also from assm have \<open>\<dots> = ?th (?map (seqRun u x (f 0)))\<close>
            by (simp add: seqRun_def image_iff filter_empty_conv) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1))
          also have \<open>?map (seqRun u x (f 0)) = g 0\<close> by (simp only: g_def)
          finally show \<open>?th (g i) = ?th (g 0)\<close> .
        qed
        ultimately have \<open>isInfHiddenRun g P S\<close> by blast
        moreover from assm have \<open>?map (?th u) = ?th (g 0) @ []\<close>
          by (fold tF_trace_hide_map_ev_comp_of_ev[OF \<open>tF u\<close>],
              simp add: g_def seqRun_def image_iff filter_empty_conv)
            (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1))
        moreover have \<open>tF (g 0)\<close> by (simp add: g_def)
        moreover have \<open>ftF []\<close> by simp
        moreover have \<open>g 0 \<in> range g\<close> by simp
        ultimately have \<open>?map (?th u) \<in> \<D> (P \ S)\<close>
          unfolding D_Hiding by blast
        thus \<open>?th u \<in> \<D> ?rhs\<close>
          by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
            (metis "*"(2) \<open>ftF []\<close> append.right_neutral filter_map
              tF_map_ev_comp tF_map_ev_of_ev_eq_iff)
      next
        fix j assume $ : \<open>finite {i. seqRun u x i \<in> ?map ` U2}\<close> \<open>\<And>i. j \<le> i \<Longrightarrow> seqRun u x i \<in> U3\<close>
        let ?pred = \<open>\<lambda>i u' r' v'. seqRun u x (i + j) = ?map u' @ v' \<and> u' @ [\<checkmark>(r')] \<in> \<T> P \<and>
                                     u' \<notin> \<D> P \<and> tF u' \<and> v' \<in> \<T> (Q r') \<and> v' \<notin> \<D> (Q r')\<close>
        define u'_r'_v' where "\<pounds>" : \<open>u'_r'_v' i \<equiv> SOME u'_r'_v'. ?pred i (fst u'_r'_v')
                                                  (fst (snd u'_r'_v')) (snd (snd u'_r'_v'))\<close> for i
        define u' r' v'
          where "\<pounds>\<pounds>" : \<open>u' i \<equiv> fst (u'_r'_v' i)\<close> \<open>r' i \<equiv> fst (snd (u'_r'_v' i))\<close>
            \<open>v' i \<equiv> snd (snd (u'_r'_v' i))\<close> for i
        from "$"(2) have \<open>\<exists>u'_r'_v'. ?pred i (fst u'_r'_v') (fst (snd u'_r'_v')) (snd (snd u'_r'_v'))\<close> for i
          by (simp add: U3_def)
        from someI_ex[OF this, folded "\<pounds>"]
        have $$ : \<open>?pred i (u' i) (r' i) (v' i)\<close> for i by (simp_all add: "\<pounds>\<pounds>")
        show \<open>?th u \<in> \<D> ?rhs\<close>
        proof (cases \<open>finite (range u')\<close>)
          assume \<open>infinite (range u')\<close>
          hence \<open>\<exists>f :: nat \<Rightarrow> _. strict_mono f \<and> range f \<subseteq> {t. \<exists>t'\<in>range u'. t \<le> t'}\<close>
          proof (intro KoenigLemma allI)
            fix i
            have \<open>{t. \<exists>t'\<in>range u'. t = take i t'} \<subseteq> ?map ` {t. t \<le> seqRun u x (i + j)}\<close>
            proof (rule subsetI)
              fix t' assume \<open>t' \<in> {t. \<exists>t'\<in>range u'. t = take i t'}\<close>
              then obtain i' where \<open>t' = take i (u' i')\<close> by blast
              from "$$"[of i'] have \<open>seqRun u x (i' + j) = ?map (u' i') @ v' i'\<close> by argo
              hence \<open>?map (u' i') \<le> seqRun u x (i' + j)\<close> by auto
              from this[THEN mono_take, of i]
              have \<open>?map (take i (u' i')) \<le> seqRun u x (min (i - length u) (i' + j))\<close>
                by (simp add: min.commute take_map split: if_split_asm)
                  (metis prefix_prefix append_take_drop_id take_map)
              also have \<open>\<dots> \<le> seqRun u x (i + j)\<close> by simp
              finally have \<open>?map (take i (u' i')) \<le> seqRun u x (i + j)\<close> .
              with "$$" \<open>t' = take i (u' i')\<close> show \<open>t' \<in> ?map ` {t. t \<le> seqRun u x (i + j)}\<close>
                by (simp add: image_iff)
                  (metis append_take_drop_id map_ev_of_ev_map_ev_of_ev
                    tF_append_iff tF_map_ev_of_ev_same_type_is)
            qed
            moreover have \<open>finite \<dots>\<close> by (simp add: prefixes_fin)
            ultimately show \<open>finite {t. \<exists>t'\<in>range u'. t = take i t'}\<close>
              by (meson finite_subset)
          qed
          then obtain f :: \<open>nat \<Rightarrow> _\<close>
            where $$$ : \<open>strict_mono f\<close> \<open>range f \<subseteq> {t. \<exists>t'\<in>range u'. t \<le> t'}\<close> by blast
          define g :: \<open>nat \<Rightarrow> ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>g \<equiv> ?map \<circ> f \<circ> ((+) (length u))\<close>
          have $$$$ : \<open>length u \<le> length (g i)\<close> for i
            by (simp add: g_def)
              (metis "$$$"(1) add_leE length_strict_mono)
          have \<open>?th (g i) = ?th (?map u)\<close> for i
          proof -
            from "$$$"(2) "$$" obtain i' where \<open>g i \<le> u' i'\<close>
              by (simp add: g_def subset_iff)
                (metis prefixE range_eqI tF_append_iff tF_map_ev_of_ev_same_type_is)
            also from "$$" have \<open>\<dots> \<le> ?map (seqRun u x (i' + j))\<close>
              by (simp add: tF_map_ev_of_ev_same_type_is)
            finally have \<open>g i \<le> ?map (seqRun u x (i' + j))\<close> .
            with "$$$$" obtain i'' where \<open>g i = ?map u @ seqRun [] ((ev \<circ> of_ev) \<circ> x) i''\<close>
              by (auto simp add: less_eq_list_def less_list_def prefix_def map_eq_append_conv seqRun_def append_eq_append_conv2)
                (metis append.right_neutral append_eq_append_conv le_add1 length_append length_map order_antisym_conv,
                  metis (no_types, lifting) add.left_neutral append_eq_conv_conj le_add1 le_add_diff_inverse length_append length_upt take_upt)
            with "\<euro>" show \<open>?th (g i) = ?th (?map u)\<close>
              by (simp add: trace_hide_is_Nil_iff, simp add: image_iff subset_iff)
                (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1))
          qed
          moreover have \<open>strict_mono g\<close>
            by (simp add: g_def "$$$"(1) comp_def strict_mono_map strict_monoD strict_monoI)
          moreover from "$$" "$$$"(2) have \<open>g i \<in> \<T> P\<close> for i
            by (simp add: g_def subset_iff image_iff)
              (metis tF_append_iff map_ev_of_ev_map_ev_of_ev
                is_processT3_TR_append prefixE tF_map_ev_of_ev_eq_iff)
          ultimately have \<open>?th (?map u) \<in> \<D> (P \ S)\<close>
            by (simp add: D_Hiding)
              (metis (lifting) ext Hiding_tF append_Nil2 ftF_Nil
                rangeI tF_map_ev_comp)
          thus \<open>?th u \<in> \<D> ?rhs\<close>
            by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
              (metis (lifting) ext "*"(2) tF_trace_hide_map_ev_comp_of_ev[of u S] append_Nil2
                ftF_Nil map_ev_of_ev_map_ev_of_ev tF_map_ev_comp tF_map_ev_of_ev_same_type_is)
        next
          assume \<open>finite (range u')\<close>
          have \<open>range r' \<subseteq> (\<Union>u''\<in> range u'. {r''. u'' @ [\<checkmark>(r'')] \<in> \<T> P \<and> u'' \<notin> \<D> P})\<close>
            using "$$" by fast
          moreover have \<open>finite \<dots>\<close>
            by (rule finite_UN_I[OF \<open>finite (range u')\<close>])
              (simp add: finite_ticksD \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close>)
          ultimately have \<open>finite (range r')\<close>
            using finite_subset by blast
          have \<open>infinite (range v')\<close>
          proof (rule notI)
            assume \<open>finite (range v')\<close>
            from "$$" have \<open>range (\<lambda>i. seqRun u x (i + j)) \<subseteq>
                            (\<lambda>(u'', v''). u'' @ v'') ` ((?map ` (range u')) \<times> range v')\<close> by auto
            moreover have \<open>finite \<dots>\<close>
              by (simp add: \<open>finite (range u')\<close> \<open>finite (range v')\<close>)
            ultimately have \<open>finite (range (\<lambda>i. seqRun u x (i + j)))\<close>
              by (meson finite_subset)
            moreover have \<open>range (seqRun u x) = range (\<lambda>i. seqRun u x (i + j)) \<union> seqRun u x ` {..j}\<close>
              by (auto simp add: image_iff) presburger
            ultimately have \<open>finite (range (seqRun u x))\<close> by simp
            with infinite_range_seqRun show False ..
          qed
          { assume hyp : \<open>\<forall>u'' \<in> range u'. \<forall>r'' \<in> range r'. finite {i. ?pred i u'' r'' (v' i)}\<close>
            from "$$" have \<open>range v' = (\<Union>u'' \<in> range u'. \<Union>r'' \<in> range r'. v' ` {i. ?pred i u'' r'' (v' i)})\<close>
              by (auto simp add: image_iff)
            also from hyp \<open>finite (range u')\<close> \<open>finite (range r')\<close> have \<open>finite \<dots>\<close> by blast
            finally have \<open>finite (range v')\<close> .
            with \<open>infinite (range v')\<close> have False ..
          }
          then obtain u'' r'' where \<open>infinite {i. ?pred i u'' r'' (v' i)}\<close> by blast
          hence \<open>\<exists>\<^sub>\<infinity>i. ?pred i u'' r'' (v' i)\<close>
            by (simp add: frequently_cofinite)
          then obtain f :: \<open>nat \<Rightarrow> nat\<close>
            where $$$ : \<open>strict_mono f\<close> \<open>\<And>i. ?pred (f i) u'' r'' (v' (f i))\<close>
            by (blast dest: extraction_subseqD[where \<sigma> = id, simplified])
          have \<open>?th (u'' @ [\<checkmark>(r'')]) \<in> \<T> (P \ S)\<close>
            by (rule mem_T_imp_mem_T_Hiding) (simp add: "$$$"(2))
          also have \<open>?th (u'' @ [\<checkmark>(r'')]) = ?th u'' @ [\<checkmark>(r'')]\<close>
            by (simp add: image_iff)
          finally have \<open>?th u'' @ [\<checkmark>(r'')] \<in> \<T> (P \ S)\<close> .
          moreover have \<open>?th (v' (f 0)) \<in> \<D> (Q r'' \ S)\<close>
          proof -
            have \<open>ftF []\<close> by simp
            moreover from "$$$"(2)[of 0, THEN conjunct1, THEN arg_cong[where f = tF]] assm "*"(2)
            have \<open>tF (v' (f 0))\<close>
              by (simp add: tF_seqRun_iff image_iff) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1))
            moreover have \<open>strict_mono (v' \<circ> f)\<close>
            proof (rule strict_monoI)
              fix i1 i2 :: nat assume \<open>i1 < i2\<close>
              hence \<open>f i1 + j < f i2 + j\<close> by (simp add: "$$$"(1) strict_mono_less)                                                                       
              hence \<open>seqRun u x (f i1 + j) < seqRun u x (f i2 + j)\<close> by simp
              with "$$$"(2)[of i1] "$$$"(2)[of i2]
              show \<open>(v' \<circ> f) i1 < (v' \<circ> f) i2\<close> by simp                                                                                                   
            qed                                                                     
            moreover have \<open>(v' \<circ> f) i \<in> \<T> (Q r'')\<close> for i by (simp add: "$$$"(2))
            moreover have \<open>?th ((v' \<circ> f) i) = ?th ((v' \<circ> f) 0)\<close> for i
              using "$$$"(2)[of i, THEN conjunct1, THEN arg_cong[where f = ?th]]
                "$$$"(2)[of 0, THEN conjunct1, THEN arg_cong[where f = ?th]]
              by (simp add: trace_hide_seqRun_eq_iff[THEN iffD2, rule_format, OF "\<euro>"])
            moreover have \<open>v' (f 0) \<in> range (v' \<circ> f)\<close> by simp
            ultimately show \<open>?th (v' (f 0)) \<in> \<D> (Q r'' \ S)\<close>
              unfolding D_Hiding by blast
          qed
          ultimately have \<open>?map (?th u'') @ ?th (v' (f 0)) \<in> \<D> ?rhs\<close>
            by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
              (metis append_T_imp_tF not_Cons_self2)
          also from "$$$"(2)[of 0, THEN conjunct1, THEN arg_cong[where f = ?th, symmetric]] assm
          have \<open>?map (?th u'') @ ?th (v' (f 0)) = ?th u\<close>
            by (simp, subst (asm) tF_trace_hide_map_ev_comp_of_ev, solves \<open>simp add: "$$$"(2)\<close>)
              (simp, use trace_hide_seqRun_eq_iff in blast)
          finally show \<open>?th u \<in> \<D> ?rhs\<close> .
        qed
      qed
    qed
    moreover from "*"(2) Hiding_tF have \<open>tF (?th u)\<close> by blast
    ultimately show \<open>t \<in> \<D> ?rhs\<close>
      unfolding "*"(1) using "*"(3) by (fact is_processT7)
  qed
qed


corollary Hiding_Seq_unit : \<open>P \<^bold>; Q \ S = (P \ S) \<^bold>; (Q \ S)\<close> for P :: \<open>'a process\<close>
  by (simp flip: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_const add: finite_ticks_Hiding_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k finite_ticks_simps)


corollary finite_ticks_Hiding_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>(\<And>l r. l \<in> set (butlast L) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(P l r)) \<Longrightarrow>
   (\<lambda>r. (SEQ\<^sub>\<checkmark> l \<in>@ L. P l) r \ S) = SEQ\<^sub>\<checkmark> l \<in>@ L. (\<lambda>r. P l r \ S)\<close>
proof (induct L rule: induct_list012)
  case 1 show ?case by simp
next
  case 2 show ?case by simp
next
  case (3 l0 l1 L)
  have \<open>(\<lambda>r. (SEQ\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). P l) r \ S) =
        (\<lambda>r. (P l0 r \ S) \<^bold>;\<^sub>\<checkmark> (\<lambda>r. (SEQ\<^sub>\<checkmark> l \<in>@ (l1 # L). P l) r \ S))\<close>
    by (subst MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Cons, subst finite_ticks_Hiding_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      (simp_all add: "3.prems")
  also have \<open>(\<lambda>r. (SEQ\<^sub>\<checkmark> l \<in>@ (l1 # L). P l) r \ S) = SEQ\<^sub>\<checkmark> l \<in>@ (l1 # L). (\<lambda>r. P l r \ S)\<close>
    by (rule "3.hyps"(2)) (simp add: "3.prems")
  finally show ?case by simp
qed

corollary Hiding_MultiSeq_unit :
  \<open>(SEQ l \<in>@ L. P l) \ S = SEQ l \<in>@ L. (P l \ S)\<close>
  (is \<open>?lhs = ?rhs\<close>) for P :: \<open>'b \<Rightarrow> 'a process\<close>
using  finite_ticks_Hiding_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of L \<open>\<lambda>l r. P l\<close>, simplified]
proof (cases \<open>L = []\<close>)
  show \<open>L = [] \<Longrightarrow> ?lhs = ?rhs\<close> by simp
next
  assume \<open>L \<noteq> []\<close>
  hence \<open>?lhs = (SEQ\<^sub>\<checkmark> l \<in>@ L. (\<lambda>r. P l)) () \ S\<close> by simp
  also have \<open>\<dots> = (SEQ\<^sub>\<checkmark> l \<in>@ L. (\<lambda>r. P l \ S)) ()\<close>
    by (rule finite_ticks_Hiding_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[THEN fun_cong]) (simp add: finite_ticks_simps)
  also have \<open>\<dots> = ?rhs\<close> by simp
  finally show \<open>?lhs = ?rhs\<close> .
qed


section \<open>Hiding and Synchronization Product\<close>

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_imp_superset_ev :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u, v), A) \<Longrightarrow>
   {ev a |a. ev a \<in> set u} \<union> {ev a |a. ev a \<in> set v} \<subseteq> {ev a |a. ev a \<in> set t}\<close>
proof (induct t arbitrary: u v)
  case Nil thus ?case by (auto dest: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
next
  case (Cons e t)
  from Cons.prems consider (mv_left) a u' where \<open>e = ev a\<close> \<open>u = ev a # u'\<close>
    \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u', v), A)\<close>
  | (mv_right) a v' where \<open>e = ev a\<close> \<open>v = ev a # v'\<close>
    \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u, v'), A)\<close>
  | (mv_both_ev) a u' v' where \<open>e = ev a\<close> \<open>u = ev a # u'\<close> \<open>v = ev a # v'\<close>
    \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u', v'), A)\<close>
  | (mv_both_tick) r s u' v' where \<open>u = \<checkmark>(r) # u'\<close> \<open>v = \<checkmark>(s) # v'\<close>
    \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u', v'), A)\<close>
    by (cases e) (auto elim: Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE Cons_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
  thus ?case by cases (auto dest!: Cons.hyps)
qed


lemma (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) disjoint_isInfHidden_seqRunL_to_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  assumes \<open>A \<inter> S = {}\<close> and \<open>isInfHidden_seqRun x P A t_P\<close>
    and \<open>t_Q \<in> \<T> Q\<close> and \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
  shows \<open>isInfHidden_seqRun (ev \<circ> of_ev \<circ> x) (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) A t\<close>
proof -
  have tF_x : \<open>tF (map x [0..<i])\<close> for i
    by (metis assms(2) imageE is_ev_def seqRun_def tF_append_iff
        tF_map_tick_comp_iff tF_seqRun_iff)
  define t' where \<open>t' i \<equiv> t @ map (ev \<circ> of_ev) (map x [0..<i])\<close> for i
  from assms(1, 2) have \<open>{a. ev a \<in> set (map x [0..<i])} \<inter> S = {}\<close> for i
    by (simp add: disjoint_iff image_iff) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1))
  from tF_disjoint_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append_tailL[OF tF_x this assms(4)]
  have \<open>seqRun t (ev \<circ> of_ev \<circ> x) i setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((seqRun t_P x i, t_Q), S)\<close> for i
    by (simp add: seqRun_def)
  moreover have \<open>of_ev (x i) \<in> A\<close> for i
    by (metis assms(2) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) image_iff)
  ultimately show \<open>isInfHidden_seqRun (ev \<circ> of_ev \<circ> x) (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) A t\<close>
    using assms(2, 3) by (auto simp add: T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
qed

lemma (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) disjoint_isInfHidden_seqRunR_to_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<lbrakk>A \<inter> S = {}; isInfHidden_seqRun x Q A t_Q; t_P \<in> \<T> P;
    t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<rbrakk> \<Longrightarrow>
   isInfHidden_seqRun (ev \<circ> of_ev \<circ> x) (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) A t\<close>
  by (fold Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual, rule Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disjoint_isInfHidden_seqRunL_to_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    (use setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual in \<open>blast intro: Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual.Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_axioms\<close>)+



lemma (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) disjoint_Hiding_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding_aux :
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
      with \<open>u1' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P1, t_Q1''), S)\<close> D_P(1) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tF_imp
      have \<open>u1' = u1' @ []\<close> \<open>tF u1'\<close> \<open>ftF []\<close>
        \<open>u1' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P1, t_Q1''), S)\<close> \<open>t_P1 \<in> \<D> P\<close>
        by simp_all (blast intro: is_processT3_TR)+
      with \<open>t_Q1'' \<in> \<T> Q\<close> have \<open>u1' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
      moreover have \<open>u @ v = ?th_A u1' @ (u2 @ v)\<close>
        by (simp add: "*"(1) "**"(1) \<open>u1 = ?th_A u1'\<close>)
      ultimately show \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
        unfolding D_Hiding using \<open>tF u\<close> \<open>ftF v\<close> "**"(1) \<open>tF u1'\<close>
        by (auto intro: ftF_append)
    next
      fix t_P_x assume \<open>isInfHidden_seqRun_strong t_P_x P A t_P1\<close>
      hence \<open>isInfHidden_seqRun (ev \<circ> of_ev \<circ> t_P_x) (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) A u1'\<close>
        by (intro disjoint_isInfHidden_seqRunL_to_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
            [OF \<open>A \<inter> S = {}\<close> _ \<open>t_Q1'' \<in> \<T> Q\<close> \<open>u1' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P1, t_Q1''), S)\<close>]) simp
      with "**"(1) \<open>u1 = ?th_A u1'\<close> assms(2, 3) show \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
        unfolding D_Hiding_seqRun by clarify
          (metis append_eq_append_conv2[of u1 \<open>u2 @ v\<close> \<open>u1 @ u2\<close> v]
            isInfHidden_seqRun_imp_tF[of u1' \<open>ev \<circ> of_ev \<circ> t_P_x\<close> \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q\<close> A]
            ftF_append[of u2 v] tF_append_iff[of u1 u2])
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
              ftF_Nil setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tF_imp)
        with left(1) show \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
          by (elim Prefix_Order.prefixE, simp add: D_Hiding "$"(1))
            (metis Hiding_tF assms(2, 3) ftF_append tF_append_iff)
      next
        fix t_P_x assume \<open>isInfHidden_seqRun_strong t_P_x P A t_P1\<close>
        hence \<open>isInfHidden_seqRun (ev \<circ> of_ev \<circ> t_P_x) (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) A u''\<close>
          by (intro disjoint_isInfHidden_seqRunL_to_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
              [OF \<open>A \<inter> S = {}\<close> _ \<open>t_Q1'' \<in> \<T> Q\<close> "$"(2)]) simp
        from left(1) show \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
          by (elim Prefix_Order.prefixE, simp add: D_Hiding_seqRun "$"(1))
            (metis \<open>?this\<close> assms(2, 3) ftF_append
              isInfHidden_seqRun_imp_tF tF_append_iff)
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
              ftF_Nil setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tF_imp)
        with right(1) show \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
          by (elim Prefix_Order.prefixE, simp add: D_Hiding "$"(1))
            (metis Hiding_tF assms(2, 3) ftF_append tF_append_iff)
      next
        fix t_Q_x assume \<open>isInfHidden_seqRun_strong t_Q_x Q A t_Q1'\<close>
        hence \<open>isInfHidden_seqRun (ev \<circ> of_ev \<circ> t_Q_x) (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) A u''\<close>
          by (intro disjoint_isInfHidden_seqRunR_to_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
              [OF \<open>A \<inter> S = {}\<close> _ \<open>t_P1' \<in> \<T> P\<close> "$"(2)]) simp
        from right(1) show \<open>u @ v \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close>
          by (elim Prefix_Order.prefixE, simp add: D_Hiding_seqRun "$"(1))
            (metis \<open>?this\<close> assms(2, 3) ftF_append
              isInfHidden_seqRun_imp_tF tF_append_iff)
      qed
    qed
  qed
qed



theorem (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) disjoint_Hiding_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding :
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
      using "*"(4) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual by blast
    from Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual.disjoint_Hiding_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding_aux
      [OF \<open>A \<inter> S = {}\<close> "*"(2, 3) \<open>t_Q \<in> \<D> (Q \ A)\<close> \<open>t_P \<in> \<T> (P \ A)\<close> this]
    have \<open>u @ v \<in> \<D> (Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Q S P \ A)\<close> .
    also have \<open>Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Q S P = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q\<close> by (fact Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual)
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
          (metis F_T append_self_conv ftF_Nil)
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



theorem (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) disjoint_finite_Hiding_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
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
      moreover from "**"(2) have \<open>tF (?th_A u1)\<close> using Hiding_tF by blast
      moreover have \<open>ftF (?th_A u2 @ v)\<close>
        by (metis D_imp_ftF \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \ A)\<close> calculation(1)
            ftF_append_iff ftF_charn)
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
          (metis image_iff list.set_map tF_iff_is_map_ev)
      have ***** : \<open>{ev a |a. ev a \<in> set (t_P i)} \<union> {ev a |a. ev a \<in> set (t_Q i)} \<subseteq>
                      {ev a |a. ev a \<in> set u} \<union> ev ` A\<close> for i
        by (rule subset_trans[OF setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_imp_superset_ev[OF "****"(3)]])
          (use \<open>set (seqRun u x i) \<subseteq> {ev a |a. ev a \<in> set u} \<union> ev ` A\<close> in blast)
      have ****** : \<open>tF (t_P i)\<close> \<open>tF (t_Q i)\<close> for i
        using tF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff[OF "****"(3)[of i]]
        by (metis "*"(2) "**" event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) imageE tF_seqRun_iff)+

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
        with "****"(3) have \<open>seqRun u x i setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((t_P i, t_Q i), S) \<and>
        seqRun u x j setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((t_P i, t_Q i), S)\<close>
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
            (metis append_take_drop_id tF_append_iff, metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1) in_set_takeD)
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
            by (metis "******"(1) \<open>t_P j = t_P'' 0 @ t' @ t''\<close> tF_append_iff)
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
          by (metis "*"(2) "**" Hiding_tF trace_hide_seqRun_eq_iff)
        moreover have \<open>t = ?th_A (seqRun u x i) @ v\<close>
          by (metis "*"(3) "**" trace_hide_seqRun_eq_iff)
        moreover have \<open>?th_A (seqRun u x i) setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?th_A (t_P i), ?th_A (t_Q i)), S)\<close>
          by (intro setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_trace_hide "****"(3))
        moreover have \<open>?th_A (t_P i) \<in> \<D> (P \ A)\<close>
        proof (unfold D_Hiding, clarify, intro exI conjI)
          show \<open>ftF (?th_A w)\<close>
            by (metis "******"(1) Hiding_ftF \<open>t_P i = t_P'' 0 @ w\<close>
                tF_append_iff tF_imp_ftF)
        next
          show \<open>tF (t_P'' 0)\<close>
            by (metis "******"(1) \<open>t_P i = t_P'' 0 @ w\<close> tF_append_iff)
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
            unfolding T_Hiding using "******"(2) ftF_Nil by blast
        qed
        ultimately show \<open>t \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Q \ A))\<close> unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
      next
        assume \<open>infinite (range t_Q)\<close>
        have \<open>finite {w. \<exists>t'\<in>range t_Q. w = take i t'}\<close> for i
          using "******"(2) "*****"
          by (auto intro!: finite_subset[OF _ "\<pounds>"[of i]] simp add: image_iff subset_iff)
            (metis append_take_drop_id tF_append_iff, metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1) in_set_takeD)
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
            by (metis "******"(2) \<open>t_Q j = t_Q'' 0 @ t' @ t''\<close> tF_append_iff)
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
          by (metis "*"(2) "**" Hiding_tF trace_hide_seqRun_eq_iff)
        moreover have \<open>t = ?th_A (seqRun u x i) @ v\<close>
          by (metis "*"(3) "**" trace_hide_seqRun_eq_iff)
        moreover have \<open>?th_A (seqRun u x i) setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?th_A (t_P i), ?th_A (t_Q i)), S)\<close>
          by (intro setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_trace_hide "****"(3))
        moreover have \<open>?th_A (t_Q i) \<in> \<D> (Q \ A)\<close>
        proof (unfold D_Hiding, clarify, intro exI conjI)
          show \<open>ftF (?th_A w)\<close>
            by (metis "******"(2) Hiding_ftF \<open>t_Q i = t_Q'' 0 @ w\<close>
                tF_append_iff tF_imp_ftF)
        next
          show \<open>tF (t_Q'' 0)\<close>
            by (metis "******"(2) \<open>t_Q i = t_Q'' 0 @ w\<close> tF_append_iff)
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
            unfolding T_Hiding using "******"(1) ftF_Nil by blast
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

subsection \<open>Some Refinements\<close>

context Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k begin

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



subsection \<open>Sequential Composition with STOP\<close>

text \<open>New in Isabelle26.\<close>

lemma (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) Seq_STOP_Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq_STOP :
  \<open>P \<^bold>; STOP ||\<^sub>\<checkmark> (Q \<^bold>; STOP) = P ||\<^sub>\<checkmark> Q \<^bold>; STOP\<close> (is \<open>?lhs = ?rhs\<close>)
proof (rule Process_eq_optimizedI)
  show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
    by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Seq_projs STOP_projs)
      (metis D_T is_processT3_TR_append)
next
  show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
    by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Seq_projs STOP_projs)
      (metis tF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
next
  fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
  then obtain t_P t_Q X_P X_Q where * : \<open>(t_P, X_P) \<in> \<F> (P \<^bold>; STOP)\<close> \<open>t_P \<notin> \<D> (P \<^bold>; STOP)\<close>
    \<open>(t_Q, X_Q) \<in> \<F> (Q \<^bold>; STOP)\<close> \<open>t_Q \<notin> \<D> (Q \<^bold>; STOP)\<close>
    \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), UNIV)\<close> \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P UNIV X_Q\<close>
    by (simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k')
      (metis (no_types) F_T append.right_neutral ftF_Nil)
  from "*"(1-4) have \<open>tF t_P \<and> ((t_P, X_P \<union> range tick) \<in> \<F> P \<or> (\<exists>r. t_P @ [\<checkmark>(r)] \<in> \<T> P))\<close>
    \<open>tF t_Q \<and> ((t_Q, X_Q \<union> range tick) \<in> \<F> Q \<or> (\<exists>s. t_Q @ [\<checkmark>(s)] \<in> \<T> Q))\<close>
    by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Seq_projs STOP_projs append_T_imp_tF)
  thus \<open>(t, X) \<in> \<F> ?rhs\<close>
  proof (elim disjE conjE exE)
    assume ** : \<open>tF t_P\<close> \<open>(t_P, X_P \<union> range tick) \<in> \<F> P\<close> \<open>tF t_Q\<close> \<open>(t_Q, X_Q \<union> range tick) \<in> \<F> Q\<close>
    from "*"(6) have \<open>X \<union> range tick \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (X_P \<union> range tick) UNIV (X_Q \<union> range tick)\<close>
      by (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
    with "*"(5) "**"(2, 4) have \<open>(t, X \<union> range tick) \<in> \<F> (P ||\<^sub>\<checkmark> Q)\<close>
      by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
      by (simp add: F_Seq F_STOP)
        (use "*"(5) "**"(1, 3) tF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff in blast)
  next
    fix s assume ** : \<open>tF t_P\<close> \<open>(t_P, X_P \<union> range tick) \<in> \<F> P\<close> \<open>tF t_Q\<close> \<open>t_Q @ [\<checkmark>(s)] \<in> \<T> Q\<close>
    have \<open>(t_Q, UNIV - {\<checkmark>(s)}) \<in> \<F> Q\<close> by (simp add: "**"(4) is_processT6_TR)
    moreover from "*"(6) have \<open>X \<union> range tick \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (X_P \<union> range tick) UNIV (UNIV - {\<checkmark>(s)})\<close>
      by (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
    ultimately have \<open>(t, X \<union> range tick) \<in> \<F> (P ||\<^sub>\<checkmark> Q)\<close>
      using "*"(5) "**"(2) by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
      by (simp add: F_Seq F_STOP)
        (use "*"(5) "**"(1, 3) tF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff in blast)
  next
    fix r assume ** : \<open>tF t_P\<close> \<open>t_P @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t_Q\<close> \<open>(t_Q, X_Q \<union> range tick) \<in> \<F> Q\<close>
    have \<open>(t_P, UNIV - {\<checkmark>(r)}) \<in> \<F> P\<close> by (simp add: "**"(2) is_processT6_TR)
    moreover from "*"(6) have \<open>X \<union> range tick \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (UNIV - {\<checkmark>(r)}) UNIV (X_Q \<union> range tick)\<close>
      by (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
    ultimately have \<open>(t, X \<union> range tick) \<in> \<F> (P ||\<^sub>\<checkmark> Q)\<close>
      using "*"(5) "**"(4) by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
      by (simp add: F_Seq F_STOP)
        (use "*"(5) "**"(1, 3) tF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff in blast)
  next
    fix r s assume ** : \<open>tF t_P\<close> \<open>t_P @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t_Q\<close> \<open>t_Q @ [\<checkmark>(s)] \<in> \<T> Q\<close>
    show \<open>(t, X) \<in> \<F> ?rhs\<close>
    proof (cases \<open>\<exists>r_s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close>)
      assume \<open>\<exists>r_s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close>
      then obtain r_s where \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close> ..
      with "*"(5) have \<open>t @ [\<checkmark>(r_s)] setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P @ [\<checkmark>(r)], t_Q @ [\<checkmark>(s)]), UNIV)\<close>
        by (simp add: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tick)
      with "**"(2, 4) have \<open>t @ [\<checkmark>(r_s)] \<in> \<T> (P ||\<^sub>\<checkmark> Q)\<close>
        by (auto simp add: T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      thus \<open>(t, X) \<in> \<F> ?rhs\<close> by (auto simp add: F_Seq F_STOP)
    next
      assume \<open>\<nexists>r_s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close>
      with "*"(6) have \<open>X \<union> range tick \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (UNIV - {\<checkmark>(r)}) UNIV (UNIV - {\<checkmark>(s)})\<close>
        by (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
      moreover from "**"(2, 4) have \<open>(t_P, UNIV - {\<checkmark>(r)}) \<in> \<F> P\<close> \<open>(t_Q, UNIV - {\<checkmark>(s)}) \<in> \<F> Q\<close>
        by (simp_all add: is_processT6_TR)
      ultimately have \<open>(t, X \<union> range tick) \<in> \<F> (P ||\<^sub>\<checkmark> Q)\<close>
        using "*"(5) by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      thus \<open>(t, X) \<in> \<F> ?rhs\<close>
        by (simp add: F_Seq F_STOP)
          (use "*"(5) "**"(1, 3) tF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff in blast)
    qed
  qed
next
  fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
  then consider (F) \<open>tF t\<close> \<open>(t, X \<union> range tick) \<in> \<F> (P ||\<^sub>\<checkmark> Q)\<close> \<open>t \<notin> \<D> (P ||\<^sub>\<checkmark> Q)\<close>
    | (T) r_s where \<open>tF t\<close> \<open>t @ [\<checkmark>(r_s)] \<in> \<T> (P ||\<^sub>\<checkmark> Q)\<close> \<open>t @ [\<checkmark>(r_s)] \<notin> \<D> (P ||\<^sub>\<checkmark> Q)\<close>
    by (simp add: Seq_projs STOP_projs) (metis append_T_imp_tF is_processT9 not_Cons_self2)
  thus \<open>(t, X) \<in> \<F> ?lhs\<close>
  proof cases
    case F
    from F(2, 3) obtain t_P t_Q X_P X_Q
      where * : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), UNIV)\<close>
        \<open>X \<union> range tick \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P UNIV X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by force
    from "*"(1, 2)[THEN is_processT5_S7'[where A = \<open>range tick\<close>]] obtain r s where
      \<open>(t_P, X_P \<union> range tick) \<in> \<F> P \<and> (t_Q, X_Q \<union> range tick) \<in> \<F> Q \<or> 
       (t_P, X_P \<union> range tick) \<in> \<F> P \<and> t_Q @ [\<checkmark>(s)] \<in> \<T> Q \<or>
       t_P @ [\<checkmark>(r)] \<in> \<T> P \<and> (t_Q, X_Q \<union> range tick) \<in> \<F> Q \<or>
       t_P @ [\<checkmark>(r)] \<in> \<T> P \<and> t_Q @ [\<checkmark>(s)] \<in> \<T> Q\<close> by auto
    moreover from "*"(3) F(1) tF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff have \<open>tF t_P\<close> \<open>tF t_Q\<close> by blast+
    ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close>
      using "*"(3, 4) by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Seq_projs STOP_projs) blast
  next
    case T
    from T(2, 3) obtain t_P t_Q where ** : \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close>
      \<open>t @ [\<checkmark>(r_s)] setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), UNIV)\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    from "**"(3) obtain t_P' t_Q' r s
      where *** : \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close> \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q' @ [\<checkmark>(s)]\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P', t_Q'), UNIV)\<close>
      by (auto elim: snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
    from "**"(1) "***"(2) have \<open>(t_P', UNIV) \<in> \<F> (P \<^bold>; STOP)\<close>
      by (auto simp add: F_Seq F_STOP)
    moreover from "**"(2) "***"(3) have \<open>(t_Q', UNIV) \<in> \<F> (Q \<^bold>; STOP)\<close>
      by (auto simp add: F_Seq F_STOP)
    moreover have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) UNIV UNIV UNIV\<close>
      by (simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def subset_iff) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
    ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close>
      using "***"(4) by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
  qed
qed




subsection \<open>The Particular Case of Runit\<close>

text \<open>New in Isabelle26.
The study of this particular interpretation is motivated by the fact that
it is involved in the definition of the alphabetized synchronization product.\<close>

subsubsection \<open>First Properties\<close>

text \<open>
Note that when both processes \<^term>\<open>P\<close> and \<^term>\<open>Q\<close> are of type \<^typ>\<open>'a process\<close>,
we have \<^term>\<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q = P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q\<close>.
We further have the equality with \<^term>\<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c Q\<close> (and consequently with \<^term>\<open>P \<lbrakk>A\<rbrakk> Q\<close>).\<close>

lemma Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_is_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t_unit : \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q = P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q\<close>
  by (metis (full_types) Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.inj_tj Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj_def Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj_dual_def ext)

lemma Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_is_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_unit : \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c Q = P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q\<close>
  by (metis (full_types, lifting) ext Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_tj_def Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.inj_tj Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj_def)

lemma Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_is_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t_unit : \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c Q = P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q\<close>
  by (metis Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_is_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_unit Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_is_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t_unit)

lemma SKIPS_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_SKIP : \<open>SKIPS R \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t SKIP s = SKIPS R\<close>
  by (simp add: SKIPS_def Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right)

lemma SKIP_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t_SKIPS : \<open>SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t SKIPS S = SKIPS S\<close>
  by (simp add: SKIPS_def Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_dual.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left)



subsubsection \<open>Projections\<close>

lemma D_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip :
  \<open>\<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip) = {t @ u |t u. tF t \<and> ftF u \<and> t \<in> \<D> P \<and> set t \<inter> ev ` A = {}}\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof (intro set_eqI iffI)
  fix t assume \<open>t \<in> ?lhs\<close>
  then obtain u v t_P t_Skip where * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
    \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((t_P, t_Skip), A)\<close> \<open>t_P \<in> \<D> P\<close> \<open>t_Skip \<in> \<T> Skip\<close>
    by (auto simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs D_SKIP)
  from "*"(2, 4, 6) have \<open>u = t_P \<and> set u \<inter> ev ` A = {}\<close>
    by (fastforce simp add: T_SKIP setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilR_iff
        tF_map_ev_of_ev_same_type_is tF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
  with "*"(1-3, 5) show \<open>t \<in> ?rhs\<close> by fast
next
  fix t assume \<open>t \<in> ?rhs\<close>
  then obtain u v
    where * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close> \<open>u \<in> \<D> P\<close> \<open>set u \<inter> ev ` A = {}\<close> by blast
  from "*"(2, 5) have \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((u, []), A)\<close>
    by (simp add: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilR_iff tF_map_ev_of_ev_same_type_is)
  with "*"(1-4) show \<open>t \<in> ?lhs\<close>
    by (simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs D_SKIP) (blast intro: Nil_elem_T)
qed

corollary D_Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t :
  \<open>\<D> (Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q) = {t @ u |t u. tF t \<and> ftF u \<and> t \<in> \<D> Q \<and> set t \<inter> ev ` A = {}}\<close>
  by (simp flip: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute add: D_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip)



corollary D\<^sub>m\<^sub>i\<^sub>n_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip :
  \<open>\<D>\<^sub>m\<^sub>i\<^sub>n (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip) = {t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P. set t \<inter> ev ` A = {}}\<close> (is \<open>\<D>\<^sub>m\<^sub>i\<^sub>n ?P = ?rhs\<close>)
proof (intro set_eqI iffI)
  fix t assume \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n ?P\<close>
  then obtain u v where * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close> \<open>u \<in> \<D> P\<close> \<open>set u \<inter> ev ` A = {}\<close>
    by (auto simp add: D_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip dest!: D\<^sub>m\<^sub>i\<^sub>n_D)
  from "*"(2, 4, 5) have \<open>u \<in> \<D> ?P\<close>
    by (auto simp add: D_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip intro: ftF_Nil)
  with \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n ?P\<close> have \<open>v = []\<close>
    by (simp add: "*"(1) Divergences\<^sub>m\<^sub>i\<^sub>n_def)
      (metis Prefix_Order.prefixI min_elems_no_list_set_list_set self_append_conv)
  moreover have \<open>u \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P\<close>
  proof (rule ccontr)
    assume \<open>u \<notin> \<D>\<^sub>m\<^sub>i\<^sub>n P\<close>
    with "*"(4) obtain u' where \<open>u' < u\<close> \<open>u' \<in> \<D> P\<close>
      by (metis D\<^sub>m\<^sub>i\<^sub>n_D Divergences\<^sub>m\<^sub>i\<^sub>n_def antisym_conv2 ex_le_mem_min_elems_list_set)
    with "*"(1, 2, 5) have \<open>u' \<in> \<D> ?P\<close>
      by (auto simp add: less_list_def less_eq_list_def prefix_def D_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip)
        (blast intro: ftF_Nil)
    with \<open>u' < u\<close> \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n ?P\<close> show False
      by (simp add: "*"(1) \<open>v = []\<close> Divergences\<^sub>m\<^sub>i\<^sub>n_def min_elems_def)
  qed
  ultimately show \<open>t \<in> ?rhs\<close> by (simp add: "*"(1, 5))
next
  fix t assume \<open>t \<in> ?rhs\<close>
  hence * : \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P\<close> \<open>set t \<inter> ev ` A = {}\<close> by simp_all
  show \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n ?P\<close>
  proof (rule ccontr)
    assume \<open>\<not> t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n ?P\<close>
    moreover from "*" have \<open>t \<in> \<D> ?P\<close>
      by (auto simp add: D_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip intro: D\<^sub>m\<^sub>i\<^sub>n_D ftF_Nil tF_mem_D\<^sub>m\<^sub>i\<^sub>n)
    ultimately obtain t' where \<open>t' < t\<close> \<open>t' \<in> \<D> ?P\<close>
      by (metis D\<^sub>m\<^sub>i\<^sub>n_D antisym_conv2 mem_D_imp_ex_le_mem_D\<^sub>m\<^sub>i\<^sub>n)
    then obtain u v where \<open>t' = u @ v\<close> \<open>u \<in> \<D> P\<close> by (auto simp add: D_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip)
    from \<open>t' = u @ v\<close> \<open>t' < t\<close> have \<open>u < t\<close>
      by (meson Prefix_Order.prefixI order_le_less_trans)
    with \<open>u \<in> \<D> P\<close> \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P\<close> show False
      by (simp add: Divergences\<^sub>m\<^sub>i\<^sub>n_def min_elems_def)
  qed
qed

corollary D\<^sub>m\<^sub>i\<^sub>n_Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t :
  \<open>\<D>\<^sub>m\<^sub>i\<^sub>n (Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q) = {t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n Q. set t \<inter> ev ` A = {}}\<close>
  by (metis D\<^sub>m\<^sub>i\<^sub>n_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip Renaming_id Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute)



lemma T_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip :
  \<open>\<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip) = {t @ u |t u. tF t \<and> ftF u \<and> t \<in> \<D> P \<and> set t \<inter> ev ` A = {}} \<union>
                         {t \<in> \<T> P. set t \<inter> ev ` A = {}}\<close>
  (is \<open>_ = ?div \<union> ?tr\<close>)
proof (intro set_eqI iffI)
  fix t assume \<open>t \<in> \<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)\<close>
  then consider \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)\<close>
    | (tr) t_P t_Skip where \<open>t_P \<in> \<T> P\<close> \<open>t_Skip \<in> \<T> Skip\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((t_P, t_Skip), A)\<close>
    by (auto simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
  thus \<open>t \<in> ?div \<union> ?tr\<close>
  proof cases
    assume \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)\<close>
    hence \<open>t \<in> ?div\<close> by (simp add: D_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip)
    thus \<open>t \<in> ?div \<union> ?tr\<close> ..
  next
    case tr
    from tr(2, 3) have \<open>t = t_P\<close> \<open>set t \<inter> ev ` A = {}\<close>
      by (auto simp add: T_SKIP setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilR_iff tF_map_ev_of_ev_same_type_is
          Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj_def ftF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tickR_iff
          [OF \<open>t \<in> \<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)\<close>[THEN T_imp_ftF], where v = \<open>[]\<close>, simplified])+
    with tr(1) have \<open>t \<in> ?tr\<close> by simp
    thus \<open>t \<in> ?div \<union> ?tr\<close> ..
  qed
next
  show \<open>t \<in> ?div \<union> ?tr \<Longrightarrow> t \<in> \<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)\<close> for t 
  proof (elim UnE)
    fix t assume \<open>t \<in> ?div\<close>
    hence \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)\<close> by (simp add: D_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip)
    thus \<open>t \<in> \<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)\<close> by (fact D_T)
  next
    fix t assume \<open>t \<in> ?tr\<close>
    hence * : \<open>t \<in> \<T> P\<close> \<open>set t \<inter> ev ` A = {}\<close> by simp_all
    define t_Skip :: \<open>'a trace\<close> where \<open>t_Skip \<equiv> (if tF t then [] else [\<checkmark>])\<close>
    from "*" \<open>t \<in> \<T> P\<close>[THEN T_imp_ftF]
    have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((t, t_Skip), A)\<close>
      by (simp add: t_Skip_def setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilR_iff Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj_def
          ftF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tickR_iff[where v = \<open>[]\<close>, simplified])
        (metis (no_types) Int_assoc ftF_E inf_bot_right inf_sup_absorb
          set_append tF_map_ev_of_ev_same_type_is)
    moreover have \<open>t_Skip \<in> \<T> Skip\<close> by (simp add: T_SKIP t_Skip_def)
    ultimately show \<open>t \<in> \<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)\<close>
      using "*"(1) by (auto simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
  qed
qed


corollary T_Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t :
  \<open>\<T> (Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q) = {t @ u |t u. tF t \<and> ftF u \<and> t \<in> \<D> Q \<and> set t \<inter> ev ` A = {}} \<union>
                         {t \<in> \<T> Q. set t \<inter> ev ` A = {}}\<close>
  by (simp flip: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute add: T_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip)




lemma F_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip :
  \<open>\<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip) =
   {(t, X). \<exists>X_P. (t, X_P) \<in> \<F> P \<and> set t \<inter> ev ` A = {} \<and> X \<subseteq> X_P \<union> ev ` A} \<union>
   {(t @ u, X) |t u X. tF t \<and> ftF u \<and> t \<in> \<D> P \<and> set t \<inter> ev ` A = {}}\<close>
  (is \<open>\<F> ?lhs = ?rhs1 \<union> ?rhs2\<close>)
proof (rule subset_antisym)
  { fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close>
    then consider \<open>t \<in> \<D> ?lhs\<close>
      | (fail) t_P X_P t_Skip X_Skip where \<open>t \<notin> \<D> ?lhs\<close>
        \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Skip, X_Skip) \<in> \<F> Skip\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((t_P, t_Skip), A)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj X_P A X_Skip\<close>
      unfolding Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    hence \<open>(t, X) \<in> ?rhs1 \<union> ?rhs2\<close>
    proof cases
      assume \<open>t \<in> \<D> ?lhs\<close>
      hence \<open>(t, X) \<in> ?rhs2\<close> by (simp add: D_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip)
      thus \<open>(t, X) \<in> ?rhs1 \<union> ?rhs2\<close> ..
    next
      case fail
      from \<open>(t, X) \<in> \<F> ?lhs\<close>[THEN F_imp_ftF]
      show \<open>(t, X) \<in> ?rhs1 \<union> ?rhs2\<close>
      proof (elim ftF_E)
        fix t' r assume \<open>t = t' @ [\<checkmark>(r)]\<close>
        with \<open>(t, X) \<in> \<F> ?lhs\<close>[THEN F_T] \<open>t \<notin> \<D> ?lhs\<close>
        have \<open>t \<in> \<T> P\<close> \<open>set t \<inter> ev ` A = {}\<close>
          by (auto simp add: T_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip D_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip)
        with \<open>t = t' @ [\<checkmark>(r)]\<close> have \<open>(t, X) \<in> ?rhs1\<close>
          by simp (meson Un_iff subsetI tick_T_F)
        thus \<open>(t, X) \<in> ?rhs1 \<union> ?rhs2\<close> ..
      next
        assume \<open>tF t\<close>
        with fail(3, 4) have * : \<open>t = t_P \<and> t_Skip = [] \<and> set t \<inter> ev ` A = {}\<close>
          by (auto simp add: ftF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tickR_iff[where v = \<open>[]\<close>, simplified]
              setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilR_iff F_SKIP tF_map_ev_of_ev_same_type_is) blast+
        with fail(3, 5) have \<open>X \<subseteq> X_P \<union> ev ` A\<close>
          by (auto simp add: F_SKIP super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def subset_iff Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj_def)
        with "*" fail(2) have \<open>(t, X) \<in> ?rhs1\<close> by blast
        thus \<open>(t, X) \<in> ?rhs1 \<union> ?rhs2\<close> ..
      qed
    qed
  } 
  thus \<open>\<F> ?lhs \<subseteq> ?rhs1 \<union> ?rhs2\<close> by safe blast
next
  have \<open>?rhs1 \<subseteq> \<F> ?lhs\<close>
  proof safe
    fix t X X_P assume \<open>(t, X_P) \<in> \<F> P\<close> \<open>set t \<inter> ev ` A = {}\<close> \<open>X \<subseteq> X_P \<union> ev ` A\<close>
    from F_imp_ftF this(1) have \<open>ftF t\<close> .
    define t_Skip :: \<open>'a trace\<close> where \<open>t_Skip \<equiv> if tF t then [] else [\<checkmark>]\<close>
    define X_Skip :: \<open>'a refusal\<close> where \<open>X_Skip \<equiv> if tF t then range ev else UNIV\<close>
    have \<open>(t_Skip, X_Skip) \<in> \<F> Skip\<close>
      by (simp add: F_SKIP t_Skip_def X_Skip_def image_iff)
    moreover from \<open>set t \<inter> ev ` A = {}\<close> \<open>ftF t\<close> have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((t, t_Skip), A)\<close>
      by (auto simp add: t_Skip_def setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilR_iff tF_map_ev_of_ev_same_type_is
          ftF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tickR_iff[where v = \<open>[]\<close>, simplified] Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj_def)
        (metis Int_assoc ftF_E inf_bot_right inf_sup_absorb set_append tF_map_ev_of_ev_same_type_is)
    moreover from \<open>X \<subseteq> X_P \<union> ev ` A\<close> have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj X_P A X_Skip\<close>
      by (simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def subset_iff X_Skip_def image_iff Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj_def) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
    ultimately show \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)\<close>
      using \<open>(t, X_P) \<in> \<F> P\<close> by (auto simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
  qed
  moreover have \<open>?rhs2 \<subseteq> \<F> ?lhs\<close>
    by (rule subset_trans[of _ \<open>{(t, X). t \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)}\<close>], simp add: D_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip)
      (auto intro: is_processT8)
  ultimately show \<open>?rhs1 \<union> ?rhs2 \<subseteq> \<F> ?lhs\<close> by simp
qed


corollary F_Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t :
  \<open>\<F> (Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q) =
   {(t, X). \<exists>X_P. (t, X_P) \<in> \<F> Q \<and> set t \<inter> ev ` A = {} \<and> X \<subseteq> X_P \<union> ev ` A} \<union>
   {(t @ u, X) |t u X. tF t \<and> ftF u \<and> t \<in> \<D> Q \<and> set t \<inter> ev ` A = {}}\<close>
  by (simp flip: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute add: F_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip)



lemmas Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip_projs = F_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip D_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip D\<^sub>m\<^sub>i\<^sub>n_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip T_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip
  and Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t_projs = F_Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t D_Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t D\<^sub>m\<^sub>i\<^sub>n_Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t T_Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t





subsubsection \<open>Laws\<close>

theorem RenamingTick_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t :
  \<open>RenamingTick (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q) g = RenamingTick P g \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q\<close>
  (is \<open>?lhs = ?rhs\<close>) for g :: \<open>'r \<Rightarrow> 's\<close>
proof -
  let ?map = \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g)\<close>
  let ?RT  = \<open>\<lambda>P. RenamingTick P g\<close>
  let ?map_ev = \<open>map (ev \<circ> of_ev)\<close>
  let ?map_vim = \<open>\<lambda>X. map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X\<close>

  have $ : \<open>\<And>t. tF t \<Longrightarrow> ?map t = ?map_ev t\<close>
    by (simp add: tF_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is)

  have $$ : \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((u, v), A) \<Longrightarrow>
    ?map t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((?map u, v), A)\<close> for t u v
    by (induct \<open>(Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj :: 'r \<Rightarrow> unit \<Rightarrow> 'r option, u, A, v)\<close> arbitrary: t u v)
      (auto simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj_def)

  show \<open>?lhs = ?rhs\<close>
  proof (rule Process_eq_optimizedI)
    fix t assume \<open>t \<in> \<D> ?lhs\<close>
    then obtain t1 t2 where * : \<open>t = ?map t1 @ t2\<close> \<open>tF t1\<close> \<open>ftF t2\<close> \<open>t1 \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q)\<close>
      unfolding Renaming_projs by blast
    from "*"(4) obtain t11 t12 t_P t_Q
      where ** : \<open>t1 = t11 @ t12\<close> \<open>tF t11\<close> \<open>ftF t12\<close>
        \<open>t11 setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((t_P, t_Q), A)\<close>
        \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
      unfolding Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    from "**"(4) have \<open>?map t11 setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((?map t_P, t_Q), A)\<close> by (fact "$$")
    moreover from "**"(5)
    have \<open>?map t_P \<in> \<D> (?RT P) \<and> t_Q \<in> \<T> Q \<or> ?map t_P \<in> \<T> (?RT P) \<and> t_Q \<in> \<D> Q\<close>
      by (simp add: Renaming_projs)
        (metis "**"(2, 4) append_self_conv ftF_Nil tF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
    ultimately have \<open>?map t11 \<in> \<D> ?rhs\<close>
      unfolding Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs
      using "**"(2) ftF_Nil tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff by blast
    thus \<open>t \<in> \<D> ?rhs\<close>
      by (simp add: "*"(1) "**"(1))
        (metis "*"(2, 3) "**"(1) ftF_append is_processT7
          tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff tF_append_iff)
  next
    fix t assume \<open>t \<in> \<D> ?rhs\<close>
    with D_T obtain t1 t2 t_P t_Q where * : \<open>t = t1 @ t2\<close> \<open>tF t1\<close> \<open>ftF t2\<close>
      \<open>t1 setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((t_P, t_Q), A)\<close>
      \<open>t_P \<in> \<D> (?RT P) \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> (?RT P) \<and> t_P \<notin> \<D> (?RT P) \<and> t_Q \<in> \<D> Q\<close>
      by (simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) blast
    from tF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff[OF "*"(4)]
    have \<open>tF t_P\<close> \<open>tF t_Q\<close> by (simp_all add: "*"(2))
    from "*"(5) show \<open>t \<in> \<D> ?lhs\<close>
    proof (elim disjE conjE)
      assume \<open>t_P \<in> \<D> (?RT P)\<close> \<open>t_Q \<in> \<T> Q\<close>
      from \<open>t_P \<in> \<D> (?RT P)\<close>
      obtain t_P1 t_P2 where ** : \<open>t_P = ?map t_P1 @ t_P2\<close> \<open>tF t_P1\<close> \<open>ftF t_P2\<close> \<open>t_P1 \<in> \<D> P\<close>
        unfolding Renaming_projs by blast
      from "*"(4)[unfolded "**"(1), THEN setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL]
      obtain t11 t12 t_Q1 t_Q2 where *** : \<open>t1 = t11 @ t12\<close> \<open>t_Q = t_Q1 @ t_Q2\<close>
        \<open>t11 setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((?map t_P1, t_Q1), A)\<close> by blast
      from "*"(2) \<open>tF t_Q\<close> have \<open>tF t11\<close> \<open>tF t_Q1\<close> by (simp_all add: "***"(1, 2))
      then obtain t11' :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and t_Q1' :: \<open>'a trace\<close>
        where \<open>tF t11'\<close> \<open>tF t_Q1'\<close> \<open>t11 = ?map_ev t11'\<close> \<open>t_Q1 = ?map_ev t_Q1'\<close> \<open>t_Q1 = t_Q1'\<close>
        by (metis tF_map_ev_comp tF_map_ev_of_ev_eq_iff tF_map_ev_of_ev_same_type_is)
      from tF_imp_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_map_ev_of_ev_iff
        [THEN iffD1, OF this(1) "**"(2) this(2) "***"(3)[unfolded this(3, 4) "$"[OF "**"(2)]]]
      have \<open>t11' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((t_P1, t_Q1'), A)\<close> .
      moreover have \<open>t_Q1' \<in> \<T> Q\<close>
        using "***"(2) \<open>t_Q \<in> \<T> Q\<close> \<open>t_Q1 = t_Q1'\<close> is_processT3_TR_append by blast
      ultimately have \<open>t11' \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q)\<close>
        by (simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          (use "**"(4) \<open>tF t11'\<close> ftF_Nil in blast)
      hence \<open>?map t11' \<in> \<D> ?lhs\<close>
        by (simp add: Renaming_projs)
          (metis ftF_Nil \<open>tF t11'\<close> append.right_neutral)
      thus \<open>t \<in> \<D> ?lhs\<close>
        by (simp add: "*"(1) "***"(1))
          (metis "$" "*"(2, 3) "***"(1) \<open>t11 = ?map_ev t11'\<close> \<open>tF t11'\<close>
            ftF_append is_processT7 tF_append_iff)
    next
      assume \<open>t_P \<in> \<T> (?RT P)\<close> \<open>t_P \<notin> \<D> (?RT P)\<close> \<open>t_Q \<in> \<D> Q\<close>
      from this(1, 2) obtain t_P' where \<open>t_P = ?map t_P'\<close> \<open>t_P' \<in> \<T> P\<close>
        unfolding Renaming_projs by blast
      from \<open>tF t_P\<close> \<open>t_P = ?map t_P'\<close> have \<open>tF t_P'\<close> \<open>t_P = ?map_ev t_P'\<close>
        by (simp_all add: tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff "$")
      from "*"(2) \<open>tF t_Q\<close> obtain t1' :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and t_Q' :: \<open>'a trace\<close>
        where \<open>tF t1'\<close> \<open>tF t_Q'\<close> \<open>t1 = ?map_ev t1'\<close> \<open>t_Q = ?map_ev t_Q'\<close> \<open>t_Q = t_Q'\<close>
        by (metis tF_map_ev_comp tF_map_ev_of_ev_eq_iff tF_map_ev_of_ev_same_type_is)
      from tF_imp_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_map_ev_of_ev_iff
        [THEN iffD1, OF this(1) \<open>tF t_P'\<close> this(2) "*"(4)[unfolded this(3, 4) \<open>t_P = ?map_ev t_P'\<close>]]
      have \<open>t1' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((t_P', t_Q'), A)\<close> .
      with \<open>t_P' \<in> \<T> P\<close> \<open>t_Q \<in> \<D> Q\<close> have \<open>t1' \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q)\<close>
        by (simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs \<open>t_Q = t_Q'\<close>)
          (metis \<open>tF t1'\<close> ftF_Nil append.right_neutral)
      hence \<open>?map t1' \<in> \<D> ?lhs\<close>
        by (simp add: Renaming_projs)
          (metis ftF_Nil \<open>tF t1'\<close> append.right_neutral)
      thus \<open>t \<in> \<D> ?lhs\<close>
        by (simp add: "*"(1) \<open>t1 = ?map_ev t1'\<close> "$" "*"(3) \<open>tF t1'\<close> is_processT7)
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
    define X' where \<open>X' \<equiv> X \<inter> (range ev \<union> tick ` (range g))\<close>
    { fix g_r assume \<open>t @ [\<checkmark>(g_r)] \<in> \<T> ?rhs\<close>
      moreover from \<open>t \<notin> \<D> ?rhs\<close> have \<open>t @ [\<checkmark>(g_r)] \<notin> \<D> ?rhs\<close> by (meson is_processT9)
      ultimately obtain t_P t_Q where * : \<open>t_P \<in> \<T> (?RT P)\<close>
        \<open>t_Q \<in> \<T> Q\<close> \<open>t @ [\<checkmark>(g_r)] setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((t_P, t_Q), A)\<close>
        unfolding Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
      with \<open>t @ [\<checkmark>(g_r)] \<notin> \<D> ?rhs\<close> have \<open>t_P \<notin> \<D> (?RT P)\<close>
        by (auto simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs' intro: ftF_Nil)
      with "*"(1) obtain t_P' where \<open>t_P = ?map t_P'\<close> \<open>t_P' \<in> \<T> P\<close>
        unfolding Renaming_projs by blast
      with "*"(3) have \<open>g_r \<in> range g\<close>
        by (auto simp add: map_eq_append_conv tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj_def
            elim!: snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
    }
    moreover have \<open>(t, X') \<in> \<F> ?rhs\<close>
    proof -
      from \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
      obtain t' where \<open>t = ?map t'\<close> \<open>(t', ?map_vim X) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q)\<close>
        unfolding Renaming_projs by blast
      with \<open>t \<notin> \<D> ?lhs\<close> have \<open>t' \<notin> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q)\<close>
        by (simp add: Renaming_projs Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          (metis (no_types) append.right_neutral ftF_Nil map_append ftF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
      with \<open>(t', map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q)\<close> obtain t_P t_Q X_P X_Q
        where * : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
          \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((t_P, t_Q), A)\<close>
          \<open>?map_vim X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj X_P A X_Q\<close>
        unfolding Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by force
      from \<open>(t', ?map_vim X) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q)\<close>[THEN F_imp_ftF] show \<open>(t, X') \<in> \<F> ?rhs\<close>
      proof (elim ftF_E)
        fix t'' r assume \<open>t' = t'' @ [\<checkmark>(r)]\<close>
        with "*"(3) obtain t_P' t_Q'
          where ** : \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q' @ [\<checkmark>]\<close>
            \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((t_P', t_Q'), A)\<close>
          by (auto simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj_def elim!: snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
        from "$$"[OF "**"(3)] have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((?map t_P, t_Q), A)\<close>
          by (simp add: \<open>t = ?map t'\<close> \<open>t' = t'' @ [\<checkmark>(r)]\<close> "**"(1, 2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tick Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj_def)
        moreover from "*"(1) have \<open>?map t_P \<in> \<T> (?RT P)\<close>
          by (auto simp add: T_Renaming dest: F_T)
        ultimately have \<open>t \<in> \<T> ?rhs\<close>
          by (simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (meson "*"(2) F_T)
        thus \<open>(t, X') \<in> \<F> ?rhs\<close>
          by (simp add: \<open>t = ?map t'\<close> \<open>t' = t'' @ [\<checkmark>(r)]\<close> tick_T_F)
      next
        assume \<open>tF t'\<close>
        with tF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff[OF "*"(3)] have \<open>tF t_P\<close> \<open>tF t_Q\<close> by simp_all
        define X_P' where \<open>X_P' \<equiv> {ev a |a. ev a \<in> X_P} \<union>
          (if \<checkmark> \<in> X_Q then {} else {\<checkmark>(g r) |r. \<checkmark>(r) \<in> X_P \<and> \<checkmark>(g r) \<in> X})\<close>
        have \<open>?map_vim X_P' \<subseteq> X_P\<close>
        proof (rule subsetI)
          show \<open>e \<in> ?map_vim X_P' \<Longrightarrow> e \<in> X_P\<close> for e
            using "*"(4)[THEN set_mp, of \<open>\<checkmark>(of_tick e)\<close>]
            by (cases e) (auto simp add: X_P'_def super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj_def split: if_split_asm)
        qed
        hence \<open>(t_P, ?map_vim X_P') \<in> \<F> P\<close> by (meson "*"(1) is_processT4)
        hence \<open>(?map_ev t_P, X_P') \<in> \<F> (?RT P)\<close>
          by (simp add: F_Renaming) (metis \<open>tF t_P\<close> "$")
        moreover have \<open>X' \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj X_P' A X_Q\<close>
        proof (rule subsetI)
          show \<open>e \<in> X' \<Longrightarrow> e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj X_P' A X_Q\<close> for e
            using "*"(4)[THEN set_mp, of \<open>ev (of_ev e)\<close>] "*"(4)[THEN set_mp, of \<open>\<checkmark>(_)\<close>]
            by (cases e) (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def X'_def X_P'_def Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj_def)
        qed
        ultimately show \<open>(t, X') \<in> \<F> ?rhs\<close>
          by (simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
            (metis (mono_tags, lifting) "$" "*"(2, 3) \<open>t = ?map t'\<close> \<open>tF t_P\<close> "$$")
      qed
    qed
    ultimately have \<open>(t, X' \<union> tick ` (-  range g)) \<in> \<F> ?rhs\<close>
      by (blast intro: is_processT5 F_T)
    also have \<open>X \<subseteq> X' \<union> tick ` (-  range g)\<close>
      by (simp add: X'_def subset_iff image_iff) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust ComplI image_iff)
    finally (is_processT4) show \<open>(t, X) \<in> \<F> ?rhs\<close> .
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?lhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
    define X' where \<open>X' \<equiv> X \<inter> (range ev \<union> tick ` (range g))\<close>
    { fix g_r assume \<open>t @ [\<checkmark>(g_r)] \<in> \<T> ?lhs\<close>
      moreover from \<open>t \<notin> \<D> ?lhs\<close> have \<open>t @ [\<checkmark>(g_r)] \<notin> \<D> ?lhs\<close> by (meson is_processT9)
      ultimately have \<open>g_r \<in> range g\<close>
        by (auto simp add: Renaming_projs append_eq_map_conv tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
    }
    moreover have \<open>(t, X') \<in> \<F> ?lhs\<close>
    proof -
      from \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close> obtain t_P t_Q X_P X_Q
        where * : \<open>(t_P, X_P) \<in> \<F> (?RT P)\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
          \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((t_P, t_Q), A)\<close>
          \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj X_P A X_Q\<close>
        unfolding Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
      with \<open>t \<notin> \<D> ?rhs\<close> have \<open>t_P \<notin> \<D> (?RT P)\<close>
        unfolding Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs' by (blast intro: F_T ftF_Nil)
      with "*"(1) obtain t_P' where ** : \<open>t_P = ?map t_P'\<close> \<open>(t_P', ?map_vim X_P) \<in> \<F> P\<close>
        unfolding Renaming_projs by blast
      from \<open>(t_P', ?map_vim X_P) \<in> \<F> P\<close>[THEN F_imp_ftF] show \<open>(t, X') \<in> \<F> ?lhs\<close>
      proof (elim ftF_E)
        fix t_P'' r assume \<open>t_P' = t_P'' @ [\<checkmark>(r)]\<close> \<open>tF t_P''\<close>
        with "*"(3) obtain t' t_Q' where *** : \<open>t = t' @ [\<checkmark>(g r)]\<close> \<open>t_Q = t_Q' @ [\<checkmark>]\<close>
          \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((?map t_P'', t_Q'), A)\<close>
          by (auto simp add: "**"(1) ftF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tickL_iff
              [OF \<open>(t, X) \<in> \<F> ?rhs\<close>[THEN F_imp_ftF]] Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj_def)
        from \<open>(t, X) \<in> \<F> ?rhs\<close> "***"(1) have \<open>tF t'\<close>
          by (metis  F_imp_ftF ftF_append_iff list.discI)
        have \<open>tF (?map t_P'')\<close> by (simp add: \<open>tF t_P''\<close> tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
        from "*"(2) "***"(2) have \<open>tF t_Q'\<close>
          by (metis F_imp_ftF ftF_append_iff not_Cons_self)
        from tF_imp_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_map_ev_of_ev_iff[THEN iffD2]
          \<open>tF t'\<close> \<open>tF (?map t_P'')\<close> \<open>tF t_Q'\<close> "***"(3)
        have \<open>?map_ev t' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((?map_ev (?map t_P''), ?map_ev t_Q'), A)\<close> .
        also have \<open>?map_ev (?map t_P'') = t_P''\<close>
          by (metis "$" \<open>tF t_P''\<close> tF_map_ev_of_ev_eq_iff)
        also have \<open>?map_ev t_Q' = t_Q'\<close>
          by (simp add: \<open>tF t_Q'\<close> tF_map_ev_of_ev_same_type_is)
        finally have \<open>?map_ev t' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((t_P'', t_Q'), A)\<close> .
        hence \<open>?map_ev t' @ [\<checkmark>(r)] setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((t_P', t_Q), A)\<close>
          by (simp add: \<open>t_P' = t_P'' @ [\<checkmark>(r)]\<close> "***"(2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tick Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj_def)
        hence \<open>?map_ev t' @ [\<checkmark>(r)] \<in> \<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q)\<close>
          by (simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (meson "*"(2) "**"(2) F_T)
        hence \<open>?map (?map_ev t' @ [\<checkmark>(r)]) \<in> \<T> ?lhs\<close> by (auto simp add: T_Renaming)
        also from \<open>tF t'\<close> have \<open>?map (?map_ev t' @ [\<checkmark>(r)]) = t\<close>
          by (simp add: "***"(1) list.map_comp)
            (metis "$" list.map_comp tF_map_ev_comp tF_map_ev_of_ev_eq_iff)
        finally have \<open>t \<in> \<T> ?lhs\<close> .
        with "***"(1) show \<open>(t, X') \<in> \<F> ?lhs\<close> by (simp add: tick_T_F)
      next
        assume \<open>tF t_P'\<close>
        hence \<open>tF t_P\<close> by (simp add: "**"(1) tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
        with setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tF_imp[OF _ "*"(3)]
        have \<open>tF t\<close> \<open>tF t_Q\<close> by simp_all
        from tF_imp_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_map_ev_of_ev_iff[THEN iffD2]
          \<open>tF t\<close> \<open>tF t_P\<close> \<open>tF t_Q\<close> "*"(3)
        have \<open>?map_ev t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((?map_ev t_P, ?map_ev t_Q), A)\<close> .
        also have \<open>?map_ev t_Q = t_Q\<close>
          by (simp add: \<open>tF t_Q\<close> tF_map_ev_of_ev_same_type_is)
        also have \<open>?map_ev t_P = t_P'\<close>
          by (metis "$" "**"(1) \<open>tF t_P'\<close> tF_map_ev_of_ev_eq_iff)
        finally have \<open>?map_ev t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj\<^esub> ((t_P', t_Q), A)\<close> .
        moreover have \<open>?map_vim X' \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj (?map_vim X_P) A X_Q\<close>
        proof (rule subsetI)
          from "*"(4) show \<open>e \<in> ?map_vim X' \<Longrightarrow> e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj (?map_vim X_P) A X_Q\<close> for e
            by (cases e) (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def X'_def Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_tj_def)
        qed
        ultimately have \<open>(?map_ev t, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X') \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q)\<close>
          by (simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis "*"(2) "**"(2))
        hence \<open>(?map (?map_ev t), X') \<in> \<F> ?lhs\<close> by (auto simp add: F_Renaming)
        also have \<open>?map (?map_ev t) = t\<close>
          by (metis "$" \<open>tF t\<close> tF_map_ev_comp tF_map_ev_of_ev_eq_iff)
        finally show \<open>(t, X') \<in> \<F> ?lhs\<close> .
      qed
    qed
    ultimately have \<open>(t, X' \<union> tick ` (-  range g)) \<in> \<F> ?lhs\<close>
      by (blast intro: is_processT5 F_T)
    also have \<open>X \<subseteq> X' \<union> tick ` (-  range g)\<close>
      by (simp add: X'_def subset_iff image_iff) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust ComplI image_iff)
    finally (is_processT4) show \<open>(t, X) \<in> \<F> ?lhs\<close> .
  qed
qed


corollary RenamingTick_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t :
  \<open>RenamingTick (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q) g = P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t RenamingTick Q g\<close>
  by (metis RenamingTick_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t RenamingTick_id Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute)





(* TODO: are the following results useful ? *)

lemma GlobalNdet_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip :
  \<open>\<sqinter>x \<in> S. P x \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip = \<sqinter>x \<in> S. (P x \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)\<close>
  by (simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right)

lemma Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t_GlobalNdet :
  \<open>Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t \<sqinter>x \<in> S. P x = \<sqinter>x \<in> S. (Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t P x)\<close>
  by (simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_dual.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left)


lemma Ndet_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip :
  \<open>P \<sqinter> Q \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip = (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip) \<sqinter> (Q \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)\<close>
  by (fact Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_Ndet_right)

lemma Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Ndet :
  \<open>Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t P \<sqinter> Q = (Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t P) \<sqinter> (Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q)\<close>
  by (fact Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_dual.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_Ndet_left)





theorem (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip_distrib_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_left :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip = ((P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q))\<close> (is \<open>?lhs = ?rhs\<close>)
proof (rule Process_eqI_D\<^sub>m\<^sub>i\<^sub>n_version)
  fix t assume \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n ?lhs\<close>
  hence \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>set t \<inter> ev ` A = {}\<close> by (simp_all add: D\<^sub>m\<^sub>i\<^sub>n_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip)
  from this(1) obtain t_P t_Q
    where * : \<open>tF t\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
      \<open>t_P \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<and> t_Q \<in> \<D>\<^sub>m\<^sub>i\<^sub>n Q \<or> t_P \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<and> t_Q \<in> \<T> Q \<or> t_Q \<in> \<D>\<^sub>m\<^sub>i\<^sub>n Q \<and> t_P \<in> \<T> P\<close>
    by (auto dest: D\<^sub>m\<^sub>i\<^sub>n_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset[THEN set_mp])
  from "*"(2)[THEN setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev_in_set_iff] \<open>set t \<inter> ev ` A = {}\<close>
  have ** : \<open>set t_P \<inter> ev ` A = {}\<close> \<open>set t_Q \<inter> ev ` A = {}\<close> by auto
  from "*"(3) show \<open>t \<in> \<D> ?rhs\<close>
  proof (elim disjE conjE)
    assume \<open>t_P \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P\<close> \<open>t_Q \<in> \<D>\<^sub>m\<^sub>i\<^sub>n Q\<close>
    with "**" have \<open>t_P \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)\<close> \<open>t_Q \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q)\<close>
      by (simp_all add: D\<^sub>m\<^sub>i\<^sub>n_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip D\<^sub>m\<^sub>i\<^sub>n_Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t)
    with "*"(1, 2) show \<open>t \<in> \<D> ?rhs\<close>
      by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        (meson D\<^sub>m\<^sub>i\<^sub>n_subset_D D_T ftF_Nil self_append_conv subset_iff)
  next
    assume \<open>t_P \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P\<close> \<open>t_Q \<in> \<T> Q\<close>
    from \<open>t_P \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P\<close> "**"(1) have \<open>t_P \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)\<close>
      by (simp add: D\<^sub>m\<^sub>i\<^sub>n_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip)
    moreover from \<open>t_Q \<in> \<T> Q\<close> "**"(2) have \<open>t_Q \<in> \<T> (Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q)\<close>
      by (simp add: T_Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t)
    ultimately show \<open>t \<in> \<D> ?rhs\<close>
      using "*"(1, 2) by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        (meson D\<^sub>m\<^sub>i\<^sub>n_subset_D D_T ftF_Nil self_append_conv subset_iff)
  next
    assume \<open>t_Q \<in> \<D>\<^sub>m\<^sub>i\<^sub>n Q\<close> \<open>t_P \<in> \<T> P\<close>
    from \<open>t_Q \<in> \<D>\<^sub>m\<^sub>i\<^sub>n Q\<close> "**"(2) have \<open>t_Q \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q)\<close>
      by (simp add: D\<^sub>m\<^sub>i\<^sub>n_Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t)
    moreover from \<open>t_P \<in> \<T> P\<close> "**"(1) have \<open>t_P \<in> \<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)\<close>
      by (simp add: T_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip)
    ultimately show \<open>t \<in> \<D> ?rhs\<close>
      using "*"(1, 2) by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        (meson D\<^sub>m\<^sub>i\<^sub>n_subset_D D_T ftF_Nil self_append_conv subset_iff)
  qed
next
  fix t assume \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n ?rhs\<close>
  from D\<^sub>m\<^sub>i\<^sub>n_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset[THEN set_mp, OF this]
  obtain t_P t_Q where * : \<open>tF t\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
    \<open>set t_P \<inter> ev ` A = {}\<close> \<open>set t_Q \<inter> ev ` A = {}\<close>
    \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
    by (auto simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip_projs Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t_projs dest!: D\<^sub>m\<^sub>i\<^sub>n_D dest: D_T)
  from "*"(2)[THEN setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev_in_set_iff] "*"(3, 4)
  have \<open>set t \<inter> ev ` A = {}\<close> by auto
  moreover from "*"(1, 2, 5) have \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    by (auto simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k intro: ftF_Nil)
  ultimately show \<open>t \<in> \<D> ?lhs\<close>
    using "*"(1) by (auto simp add: D_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip intro: ftF_Nil)
next
  fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
  from this(1, 2) obtain X'
    where * : \<open>(t, X') \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>set t \<inter> ev ` A = {}\<close> \<open>X \<subseteq> X' \<union> ev ` A\<close>
    by (auto simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip_projs)
  from "*"(1) consider \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    | (fail) t_P t_Q X_P X_Q where \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close> \<open>X' \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P S X_Q\<close>
    unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
  thus \<open>(t, X) \<in> \<F> ?rhs\<close>
  proof cases
    assume \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    from this this[THEN D_imp_ftF] "*"(2) have \<open>t \<in> \<D> ?lhs\<close>
      by (auto elim!: ftF_E simp add: Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip_projs intro: ftF_Nil)
        (metis ftF_single is_processT9)
    with \<open>t \<notin> \<D> ?lhs\<close> have False ..
    thus \<open>(t, X) \<in> \<F> ?rhs\<close> ..
  next
    case fail
    from "*"(2) fail(3)[THEN setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev_in_set_iff]
    have ** : \<open>set t_P \<inter> ev ` A = {}\<close> \<open>set t_Q \<inter> ev ` A = {}\<close> by auto
    from "**"(1) fail(1) have \<open>(t_P, X_P \<union> ev ` A) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)\<close>
      by (auto simp add: F_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip)
    moreover from "**"(2) fail(2) have \<open>(t_Q, X_Q \<union> ev ` A) \<in> \<F> (Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q)\<close>
      by (auto simp add: F_Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t)
    moreover from "*"(3) fail(4) have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (X_P \<union> ev ` A) S (X_Q \<union> ev ` A)\<close>
      by (fastforce simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def subset_iff)
    ultimately show \<open>(t, X) \<in> \<F> ?rhs\<close>
      using fail(3) by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  qed
next
  fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
  then obtain t_P t_Q X_P X_Q
    where * : \<open>(t_P, X_P) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)\<close> \<open>t_P \<notin> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip)\<close>
      \<open>(t_Q, X_Q) \<in> \<F> (Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q)\<close> \<open>t_Q \<notin> \<D> (Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q)\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close> \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P S X_Q\<close>
    by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs') (metis F_T append_Nil2 ftF_Nil)
  from "*"(1, 2) obtain X_P'
    where ** : \<open>(t_P, X_P') \<in> \<F> P\<close> \<open>set t_P \<inter> ev ` A = {}\<close> \<open>X_P \<subseteq> X_P' \<union> ev ` A\<close>
    unfolding Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip_projs by blast
  from "*"(3, 4) obtain X_Q'
    where *** : \<open>(t_Q, X_Q') \<in> \<F> Q\<close> \<open>set t_Q \<inter> ev ` A = {}\<close> \<open>X_Q \<subseteq> X_Q' \<union> ev ` A\<close>
    unfolding Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t_projs by blast
  have \<open>(t, super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P' S X_Q') \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    using "*"(5) "**"(1) "***"(1) by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  moreover from "*"(5)[THEN setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev_in_set_iff] "**"(2) "***"(2)
  have \<open>set t \<inter> ev ` A = {}\<close> by blast
  moreover from "*"(6) "**"(3) "***"(3)
  have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P' S X_Q' \<union> ev ` A\<close>
    by (fastforce simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def subset_iff)
  ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close>
    by (auto simp add: F_Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip)
qed


corollary (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) Skip_Sync\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t_distrib_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_right :
  \<open>Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) = ((P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t Skip) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (Skip \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>u\<^sub>n\<^sub>i\<^sub>t Q))\<close>
  by (metis Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t_Skip_distrib_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_left RenamingTick_id Sync\<^sub>R\<^sub>u\<^sub>n\<^sub>i\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute)



unbundle no option_type_syntax


(*<*)
end
  (*>*)