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


chapter \<open>Non Destructiveness Rules\<close>

(*<*)
theory Sequential_Composition_Generalized_Non_Destructive
  imports "HOL-CSP_RS" CSP_PTick_Monotonicities
begin
  (*<*)


section \<open>Sequential Composition\<close>

subsection \<open>Refinement\<close>

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD :
  \<open>P \<^bold>;\<^sub>\<checkmark> Q \<down> n \<sqsubseteq>\<^sub>F\<^sub>D (P \<down> n) \<^bold>;\<^sub>\<checkmark> (Q \<down> n)\<close> (is \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
proof -
  show \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>
  proof (rule failure_divergence_refine_optimizedI)
    { fix t assume \<open>tF t\<close> and \<open>t \<in> \<D> ?rhs\<close>
      from this(2) consider (D_P) u v where \<open>t = map (ev \<circ> of_ev) u @ v\<close> \<open>u \<in> \<D> (P \<down> n)\<close> \<open>tF u\<close> \<open>ftF v\<close>
        | (D_Q) u r v where \<open>t = map (ev \<circ> of_ev) u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>length u < n\<close> \<open>tF u\<close> \<open>v \<in> \<D> ((Q \<down> n) r)\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
         (metis D_P D_imp_front_tickFree D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI is_processT3_TR_append linorder_less_linear,
           metis D_P D_imp_front_tickFree D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI is_processT7 is_processT9)
      hence \<open>t \<in> \<D> ?lhs\<close>
      proof cases
        case D_P thus \<open>t \<in> \<D> ?lhs\<close>
          by (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE, simp_all add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
            (metis, metis front_tickFree_append length_map tickFree_map_ev_comp)
      next
        case D_Q
        from D_Q(5) show \<open>t \<in> \<D> ?lhs\<close>
        proof (unfold restriction_fun_def, elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
          assume \<open>v \<in> \<D> (Q r)\<close>
          with D_Q(1, 2, 4) have \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          thus \<open>t \<in> \<D> ?lhs\<close> by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        next
          fix w x assume \<open>v = w @ x\<close> \<open>w \<in> \<T> (Q r)\<close> \<open>length w = n\<close> \<open>tF w\<close> \<open>ftF x\<close>
          from D_Q(2, 4) \<open>w \<in> \<T> (Q r)\<close> have \<open>map (ev \<circ> of_ev) u @ w \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
            by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          moreover have \<open>tF (map (ev \<circ> of_ev) u @ w)\<close> by (simp add: \<open>tF w\<close>)
          moreover have \<open>n \<le> length (map (ev \<circ> of_ev) u @ w)\<close>
            by (simp add: \<open>length w = n\<close>)
          ultimately have \<open>map (ev \<circ> of_ev) u @ w \<in> \<D> ?lhs\<close>
            by (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI antisym_conv2)
          with D_Q(1) \<open>tF t\<close> \<open>v = w @ x\<close> is_processT7 show \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q \<down> n)\<close> by fastforce
        qed
      qed
    }
    thus \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
      by (metis D_imp_front_tickFree div_butlast_when_non_tickFree_iff front_tickFree_iff_tickFree_butlast)
  next
    have \<open>(P \<down> n) \<^bold>;\<^sub>\<checkmark> (Q \<down> n) \<sqsubseteq> P \<^bold>;\<^sub>\<checkmark> Q\<close>
      by (simp add: fun_below_iff mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k restriction_fun_def
          restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self)
    thus \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> \<D> ((P \<down> n) \<^bold>;\<^sub>\<checkmark> (Q \<down> n)) \<subseteq> \<D> (P \<^bold>;\<^sub>\<checkmark> Q \<down> n) \<Longrightarrow>
          (t, X) \<in> \<F> ?lhs\<close> for t X
      by (meson F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI in_mono is_processT8 le_approx2)
  qed
qed


corollary restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD :
  \<open>((SEQ\<^sub>\<checkmark> l \<in>@ L. P l) \<down> n) r \<sqsubseteq>\<^sub>F\<^sub>D (SEQ\<^sub>\<checkmark> l \<in>@ L. (P l \<down> n)) r\<close>
proof (induct L arbitrary: r)
  show \<open>((SEQ\<^sub>\<checkmark> l \<in>@ []. P l) \<down> n) r \<sqsubseteq>\<^sub>F\<^sub>D (SEQ\<^sub>\<checkmark> l \<in>@ []. (P l \<down> n)) r\<close> for r
    by (simp add: restriction_fun_def)
next
  fix a L r
  assume hyp: \<open>((SEQ\<^sub>\<checkmark> l \<in>@ L. P l) \<down> n) r \<sqsubseteq>\<^sub>F\<^sub>D (SEQ\<^sub>\<checkmark> l \<in>@ L. (P l \<down> n)) r\<close> for r
  have \<open>((SEQ\<^sub>\<checkmark> l \<in>@ (a # L). P l) \<down> n) r = P a r \<^bold>;\<^sub>\<checkmark> (SEQ\<^sub>\<checkmark> l \<in>@ L. P l) \<down> n\<close>
    by (simp add: restriction_fun_def)
  also have \<open>\<dots> \<sqsubseteq>\<^sub>F\<^sub>D (P a r \<down> n) \<^bold>;\<^sub>\<checkmark> SEQ\<^sub>\<checkmark> l \<in>@ L. (P l \<down> n)\<close>
    by (fact trans_FD[OF restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD[OF idem_FD hyp]])
  also have \<open>\<dots> = (SEQ\<^sub>\<checkmark> l \<in>@ (a # L). (P l \<down> n)) r\<close>
    by (simp add: restriction_fun_def)
  finally show \<open>((SEQ\<^sub>\<checkmark> l \<in>@ (a # L). P l) \<down> n) r \<sqsubseteq>\<^sub>F\<^sub>D \<dots>\<close> .
qed


subsection \<open>Non Destructiveness\<close>

lemma Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_non_destructive :
  \<open>non_destructive (\<lambda>(P, Q :: 'r \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k). P \<^bold>;\<^sub>\<checkmark> Q)\<close>
proof (rule order_non_destructiveI, clarify)
  fix P P' :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and Q Q' :: \<open>'r \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and n
  assume \<open>(P, Q) \<down> n = (P', Q') \<down> n\<close> \<open>0 < n\<close>
  hence \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close>
    by (simp_all add: restriction_prod_def)
  show \<open>P \<^bold>;\<^sub>\<checkmark> Q \<down> n \<sqsubseteq>\<^sub>F\<^sub>D P' \<^bold>;\<^sub>\<checkmark> Q' \<down> n\<close>
  proof (rule leFD_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
    show \<open>t \<in> \<D> (P' \<^bold>;\<^sub>\<checkmark> Q') \<Longrightarrow> t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q \<down> n)\<close> for t
      by (metis (mono_tags, opaque_lifting) \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close> in_mono
                le_ref1 mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD restriction_fun_def restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_self
                restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD)
  next
    show \<open>(s, X) \<in> \<F> (P' \<^bold>;\<^sub>\<checkmark> Q') \<Longrightarrow> (s, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q \<down> n)\<close> for s X
      by (metis (mono_tags, opaque_lifting) \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close>
                failure_refine_def leFD_imp_leF mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD
                restriction_fun_def restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_self
                restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD subset_iff)
  qed
qed



subsection \<open>Setup\<close>

text \<open>
We also introduce a third law: the assumption of constructiveness for \<^term>\<open>g\<close> can be
weakened to non destructiveness if we cannot directly perform a tick on the left.
\<close>

lemma Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>non_destructive f \<Longrightarrow> non_destructive g \<Longrightarrow> non_destructive (\<lambda>x. f x \<^bold>;\<^sub>\<checkmark> g x)\<close>
  \<open>constructive f \<Longrightarrow> constructive g \<Longrightarrow> constructive (\<lambda>x. f x \<^bold>;\<^sub>\<checkmark> g x)\<close>
  \<open>constructive f \<Longrightarrow> non_destructive g \<Longrightarrow> (\<And>x r. \<checkmark>(r) \<notin> (f x)\<^sup>0) \<Longrightarrow> constructive (\<lambda>x. f x \<^bold>;\<^sub>\<checkmark> g x)\<close>
  for f :: \<open>'b :: restriction \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  \<comment> \<open>TODO: this can probably by strengthened with a notion of strict initials\<close>
proof -
  show \<open>non_destructive f \<Longrightarrow> non_destructive g \<Longrightarrow> non_destructive (\<lambda>x. f x \<^bold>;\<^sub>\<checkmark> g x)\<close>
    by (fact non_destructive_comp_non_destructive
        [OF Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_non_destructive non_destructive_prod_codomain, simplified])
next
  show \<open>constructive f \<Longrightarrow> constructive g \<Longrightarrow> constructive (\<lambda>x. f x \<^bold>;\<^sub>\<checkmark> g x)\<close>
    by (fact non_destructive_comp_constructive
        [OF Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_non_destructive constructive_prod_codomain, simplified])
next
  show \<open>constructive (\<lambda>x. f x \<^bold>;\<^sub>\<checkmark> g x)\<close>
    if \<open>constructive f\<close> and \<open>non_destructive g\<close> and \<open>\<And>x r. \<checkmark>(r) \<notin> (f x)\<^sup>0\<close>
  proof (rule order_constructiveI)
    fix x y :: 'b and n assume \<open>x \<down> n = y \<down> n\<close>
    with that(1, 2) have \<open>f x \<down> Suc n = f y \<down> Suc n\<close> and \<open>g x \<down> n = g y \<down> n\<close>
      by (auto dest: non_destructiveD constructiveD)
    show \<open>f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n \<sqsubseteq>\<^sub>F\<^sub>D f y \<^bold>;\<^sub>\<checkmark> g y \<down> Suc n\<close>
    proof (rule leFD_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
      show div : \<open>t \<in> \<D> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close> if \<open>length t \<le> Suc n\<close> and \<open>t \<in> \<D> (f y \<^bold>;\<^sub>\<checkmark> g y)\<close> for t
      proof (cases n)
        assume \<open>n = 0\<close>
        with \<open>length t \<le> Suc n\<close> \<open>t \<in> \<D> (f y \<^bold>;\<^sub>\<checkmark> g y)\<close> \<open>f x \<down> Suc n = f y \<down> Suc n\<close> \<open>\<And>r. \<checkmark>(r) \<notin> (f y)\<^sup>0\<close>
        show \<open>t \<in> \<D> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
          by (auto simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
            (metis D_T D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI add_leE length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
                   length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k length_map order_le_imp_less_or_eq tickFree_map_ev_comp,
              metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI add_leD1 front_tickFree_Nil initials_memI' is_processT3_TR_append
                    le_SucE length_greater_0_conv length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k length_map
                    less_numeral_extra(3) one_is_add order_less_le_trans self_append_conv2 tickFree_map_ev_comp)
      next
        fix k assume \<open>n = Suc k\<close>
        from \<open>t \<in> \<D> (f y \<^bold>;\<^sub>\<checkmark> g y)\<close>
        consider (D_P) u v where \<open>t = map (ev \<circ> of_ev) u @ v\<close> \<open>u \<in> \<D> (f y)\<close> \<open>tF u\<close> \<open>ftF v\<close>
          | (D_Q) u r v where \<open>t = map (ev \<circ> of_ev) u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (f y)\<close> \<open>tF u\<close> \<open>v \<in> \<D> (g y r)\<close>
          unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
        thus \<open>t \<in> \<D> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
        proof cases
          case D_P
          with  \<open>f x \<down> Suc n = f y \<down> Suc n\<close> show \<open>t \<in> \<D> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
            by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
              (metis D_T D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_append length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
                     length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k length_map linorder_not_less
                     not_less_iff_gr_or_eq that(1) tickFree_map_ev_comp trans_less_add1)
        next
          case D_Q
          from \<open>\<checkmark>(r) \<notin> (f y)\<^sup>0\<close> D_Q(2, 3) obtain a u' where \<open>u = ev a # u'\<close>
            by (metis append_Nil event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) initials_memI neq_Nil_conv tickFree_Cons_iff)
          with \<open>length t \<le> Suc n\<close> D_Q(1)
          consider \<open>v = []\<close> \<open>length u = Suc n\<close> | \<open>u' = []\<close> \<open>length v = n\<close> | \<open>length u \<le> n\<close> \<open>length v < n\<close>
            by simp
              (metis (no_types, opaque_lifting) add_cancel_right_right add_leD2 add_le_same_cancel2
                     antisym length_greater_0_conv linorder_not_less not_less_eq_eq trans_le_add1)
          thus \<open>t \<in> \<D> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
          proof cases
            from D_Q(1-3) \<open>f x \<down> Suc n = f y \<down> Suc n\<close>
            show \<open>v = [] \<Longrightarrow> length u = Suc n \<Longrightarrow> t \<in> \<D> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
              by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
                (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI front_tickFree_Nil is_processT3_TR_append le_Suc_eq
                       length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k length_map self_append_conv tickFree_map_ev_comp)
          next
            assume \<open>u' = []\<close> \<open>length v = n\<close>
            from \<open>f x \<down> Suc n = f y \<down> Suc n\<close> \<open>n = Suc k\<close> \<open>u = ev a # u'\<close> \<open>u' = []\<close>
            have \<open>u @ [\<checkmark>(r)] \<in> \<T> (f x)\<close>
              by simp
                (smt (verit, best) D_Q(2) D_T One_nat_def T_F_spec add_Suc_shift append_Cons
                     append_self_conv2 le_add1 le_approx2 length_Cons list.size(3)
                     non_tickFree_tick not_tickFree_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff plus_1_eq_Suc
                     restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self tickFree_append_iff)
            from D_Q(4) consider \<open>tF v\<close> \<open>v \<in> \<T> (g x r)\<close> | \<open>\<not> tF v\<close> \<open>v \<in> \<D> (g x r)\<close>
              by (metis D_T D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI \<open>g x \<down> n = g y \<down> n\<close> \<open>length v = n\<close> dual_order.refl
                  length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k not_tickFree_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff restriction_fun_def)
            thus \<open>t \<in> \<D> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
            proof cases
              assume \<open>tF v\<close> \<open>v \<in> \<T> (g x r)\<close>
              from D_Q(3) \<open>u @ [\<checkmark>(r)] \<in> \<T> (f x)\<close> \<open>v \<in> \<T> (g x r)\<close>
              have \<open>map (ev \<circ> of_ev) u @ v \<in> \<T> (f x \<^bold>;\<^sub>\<checkmark> g x)\<close>
                by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
              moreover have \<open>tF (map (ev \<circ> of_ev) u @ v)\<close> by (simp add: \<open>tF v\<close>)
              moreover have \<open>length (map (ev \<circ> of_ev) u @ v) = Suc n\<close>
                by (simp add: \<open>length v = n\<close> \<open>u = ev a # u'\<close> \<open>u' = []\<close>)
              ultimately show \<open>t \<in> \<D> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
                by (metis D_Q(1) D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
            next
              from \<open>u @ [\<checkmark>(r)] \<in> \<T> (f x)\<close> D_Q(1, 3)
              show \<open>\<not> tF v \<Longrightarrow> v \<in> \<D> (g x r) \<Longrightarrow> t \<in> \<D> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
                by (auto simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
            qed
          next
            assume \<open>length u \<le> n\<close> \<open>length v < n\<close>
            have \<open>u @ [\<checkmark>(r)] \<in> \<T> (f x)\<close>
              by (metis D_Q(2) T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI \<open>f x \<down> Suc n = f y \<down> Suc n\<close> \<open>length u \<le> n\<close> length_append_singleton
                  length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k nat_add_left_cancel_le plus_1_eq_Suc)
            moreover have \<open>v \<in> \<D> (g x r)\<close>
              by (metis D_Q(4) D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI \<open>g x \<down> n = g y \<down> n\<close> \<open>length v < n\<close>
                        length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k restriction_fun_def)
            ultimately have \<open>map (ev \<circ> of_ev) u @ v \<in> \<D> (f x \<^bold>;\<^sub>\<checkmark> g x)\<close>
              by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (use D_Q(3) in blast)
            thus \<open>t \<in> \<D> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
              by (simp add: D_Q(1) D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
          qed
        qed
      qed

      fix t X assume \<open>length t \<le> Suc n\<close> \<open>(t, X) \<in> \<F> (f y \<^bold>;\<^sub>\<checkmark> g y)\<close>
      show \<open>(t, X) \<in> \<F> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
      proof (cases n)
        assume \<open>n = 0\<close>
        with \<open>length t \<le> Suc n\<close> \<open>(t, X) \<in> \<F> (f y \<^bold>;\<^sub>\<checkmark> g y)\<close> \<open>f x \<down> Suc n = f y \<down> Suc n\<close> \<open>\<And>r. \<checkmark>(r) \<notin> (f y)\<^sup>0\<close>
        show \<open>(t, X) \<in> \<F> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
          by (auto simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
            (metis F_T F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI antisym_conv2 append_Nil2 front_tickFree_Nil
                   length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k length_less_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
                   length_map tickFree_map_ev_comp,
              metis add_leE front_tickFree_Nil initials_memI is_processT3_TR_append le_Suc_eq le_ref2T
                    le_zero_eq length_0_conv length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k length_map one_is_add
                    restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_self self_append_conv2 subset_iff tickFree_map_ev_comp,
              metis D_T D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI add_leD1 le_SucE le_imp_less_Suc
                    length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
                    length_map tickFree_map_ev_comp)
      next
        fix k assume \<open>n = Suc k\<close>
        from \<open>(t, X) \<in> \<F> (f y \<^bold>;\<^sub>\<checkmark> g y)\<close> consider \<open>t \<in> \<D> (f y \<^bold>;\<^sub>\<checkmark> g y)\<close>
        | (F_P) u where \<open>t = map (ev \<circ> of_ev) u\<close> \<open>(u, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (f y)\<close> \<open>tF u\<close>
        | (F_Q) u r v where \<open>t = map (ev \<circ> of_ev) u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (f y)\<close> \<open>tF u\<close> \<open>(v, X) \<in> \<F> (g y r)\<close>
        unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by fast
      thus \<open>(t, X) \<in> \<F> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
      proof cases
        from div \<open>length t \<le> Suc n\<close> is_processT8
        show \<open>t \<in> \<D> (f y \<^bold>;\<^sub>\<checkmark> g y) \<Longrightarrow> (t, X) \<in> \<F> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close> by blast
      next
        case F_P
        from \<open>length t \<le> Suc n\<close> consider \<open>length u \<le> n\<close> | \<open>length u = Suc n\<close>
          by (simp add: F_P(1)) linarith
        thus \<open>(t, X) \<in> \<F> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
        proof cases
          assume \<open>length u \<le> n\<close>
          with \<open>f x \<down> Suc n = f y \<down> Suc n\<close> F_P(2)
          have \<open>(u, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (f x)\<close>
            by (metis F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI less_Suc_eq_le
                length_less_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          with F_P(1, 3) have \<open>(t, X) \<in> \<F> (f x \<^bold>;\<^sub>\<checkmark> g x)\<close> by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          thus \<open>(t, X) \<in> \<F> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
            by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        next
          assume \<open>length u = Suc n\<close>
          with F_P \<open>f x \<down> Suc n = f y \<down> Suc n\<close>
          have \<open>t \<in> \<T> (f x \<^bold>;\<^sub>\<checkmark> g x)\<close>
            by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
              (metis F_T T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI le_Suc_eq length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          moreover have \<open>length t = Suc n\<close> by (simp add: F_P(1) \<open>length u = Suc n\<close>)
          moreover have \<open>tF t\<close> by (simp add: F_P(1))
          ultimately have \<open>t \<in> \<D> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
            by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
          thus \<open>(t, X) \<in> \<F> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close> by (fact is_processT8)
        qed
      next
        case F_Q
        from \<open>\<checkmark>(r) \<notin> (f y)\<^sup>0\<close> F_Q(2, 3) obtain a u' where \<open>u = ev a # u'\<close>
            by (metis append_Nil event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) initials_memI neq_Nil_conv tickFree_Cons_iff)
          with \<open>length t \<le> Suc n\<close> F_Q(1)
          consider \<open>v = []\<close> \<open>length u = Suc n\<close> | \<open>u' = []\<close> \<open>length v = n\<close> | \<open>length u \<le> n\<close> \<open>length v < n\<close>
            by simp
              (metis (no_types, opaque_lifting) add_cancel_right_right add_leD2 add_le_same_cancel2
                     antisym length_greater_0_conv linorder_not_less not_less_eq_eq trans_le_add1)
          thus \<open>(t, X) \<in> \<F> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
          proof cases
            from F_Q(1-3) \<open>f x \<down> Suc n = f y \<down> Suc n\<close>
            show \<open>v = [] \<Longrightarrow> length u = Suc n \<Longrightarrow> (t, X) \<in> \<F> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
              by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
                (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI front_tickFree_Nil is_processT3_TR_append le_Suc_eq
                       length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k length_map self_append_conv tickFree_map_ev_comp)
          next
            assume \<open>u' = []\<close> \<open>length v = n\<close>
            from \<open>f x \<down> Suc n = f y \<down> Suc n\<close> \<open>n = Suc k\<close> \<open>u = ev a # u'\<close> \<open>u' = []\<close>
            have \<open>u @ [\<checkmark>(r)] \<in> \<T> (f x)\<close>
              by simp
                (smt (verit, best) F_Q(2) D_T One_nat_def T_F_spec add_Suc_shift append_Cons
                     append_self_conv2 le_add1 le_approx2 length_Cons list.size(3)
                     non_tickFree_tick not_tickFree_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff plus_1_eq_Suc
                     restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self tickFree_append_iff)
            from F_Q(4) consider \<open>tF v\<close> \<open>v \<in> \<T> (g x r)\<close> | \<open>\<not> tF v\<close> \<open>(v, X) \<in> \<F> (g x r)\<close>
              by (metis F_T F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI \<open>g x \<down> n = g y \<down> n\<close> \<open>length v = n\<close> dual_order.refl
                  length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k not_tickFree_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff restriction_fun_def)
            thus \<open>(t, X) \<in> \<F> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
            proof cases
              assume \<open>tF v\<close> \<open>v \<in> \<T> (g x r)\<close>
              from F_Q(3) \<open>u @ [\<checkmark>(r)] \<in> \<T> (f x)\<close> \<open>v \<in> \<T> (g x r)\<close>
              have \<open>map (ev \<circ> of_ev) u @ v \<in> \<T> (f x \<^bold>;\<^sub>\<checkmark> g x)\<close>
                by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
              moreover have \<open>tF (map (ev \<circ> of_ev) u @ v)\<close> by (simp add: \<open>tF v\<close>)
              moreover have \<open>length (map (ev \<circ> of_ev) u @ v) = Suc n\<close>
                by (simp add: \<open>length v = n\<close> \<open>u = ev a # u'\<close> \<open>u' = []\<close>)
              ultimately have \<open>t \<in> \<D> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
                by (metis F_Q(1) D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
              thus \<open>(t, X) \<in> \<F> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close> by (fact is_processT8)
            next
              from \<open>u @ [\<checkmark>(r)] \<in> \<T> (f x)\<close> F_Q(1, 3)
              show \<open>\<not> tF v \<Longrightarrow> (v, X) \<in> \<F> (g x r) \<Longrightarrow> (t, X) \<in> \<F> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
                by (auto simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
            qed
          next
            assume \<open>length u \<le> n\<close> \<open>length v < n\<close>
            have \<open>u @ [\<checkmark>(r)] \<in> \<T> (f x)\<close>
              by (metis F_Q(2) T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI \<open>f x \<down> Suc n = f y \<down> Suc n\<close> \<open>length u \<le> n\<close> length_append_singleton
                  length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k nat_add_left_cancel_le plus_1_eq_Suc)
            moreover have \<open>(v, X) \<in> \<F> (g x r)\<close>
              by (metis F_Q(4) F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI \<open>g x \<down> n = g y \<down> n\<close> \<open>length v < n\<close>
                        length_less_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k restriction_fun_def)
            ultimately have \<open>(map (ev \<circ> of_ev) u @ v, X) \<in> \<F> (f x \<^bold>;\<^sub>\<checkmark> g x)\<close>
              by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (use F_Q(3) in blast)
            thus \<open>(t, X) \<in> \<F> (f x \<^bold>;\<^sub>\<checkmark> g x \<down> Suc n)\<close>
              by (simp add: F_Q(1) F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
          qed
        qed
      qed
    qed
  qed
qed
   

declare Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
  [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset, simp]


text \<open>The third one can be adapted for classical sequential composition.\<close>

lemmas Seq_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_3 =
  Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k(3)[where g = \<open>\<lambda>x r. g x\<close>, simplified] for g

declare Seq_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_3 [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset, simp]




corollary MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>(\<And>l. l \<in> set L \<Longrightarrow> non_destructive (f l)) \<Longrightarrow> non_destructive (\<lambda>x. (SEQ\<^sub>\<checkmark> l \<in>@ L. f l x) r)\<close>
  \<open>(\<And>l. l \<in> set L \<Longrightarrow> constructive (f l)) \<Longrightarrow> constructive (\<lambda>x. (SEQ\<^sub>\<checkmark> l \<in>@ L. f l x) r)\<close>
  \<open>(case L of [] \<Rightarrow> True | l0 # L' \<Rightarrow>
    constructive (f l0) \<and> (\<forall>x r'. \<checkmark>(r') \<notin> (f l0 x r)\<^sup>0) \<and> (\<forall>l\<in>set L'. non_destructive (f l)))
    \<Longrightarrow> constructive (\<lambda>x. (SEQ\<^sub>\<checkmark> l \<in>@ L. f l x) r)\<close>
proof -
  show \<open>(\<And>l. l \<in> set L \<Longrightarrow> constructive (f l)) \<Longrightarrow> constructive (\<lambda>x. (SEQ\<^sub>\<checkmark> l \<in>@ L. f l x) r)\<close>
    by (induct L arbitrary: r; simp add: constructive_fun_iff)
next
  show * : \<open>(\<And>l. l \<in> set L \<Longrightarrow> non_destructive (f l)) \<Longrightarrow>
            non_destructive (\<lambda>x. (SEQ\<^sub>\<checkmark> l \<in>@ L. f l x) r)\<close> for L r
    by (induct L arbitrary: r; simp add: non_destructive_fun_iff)

  show \<open>(case L of [] \<Rightarrow> True | l0 # L' \<Rightarrow>
        constructive (f l0) \<and> (\<forall>x r'. \<checkmark>(r') \<notin> (f l0 x r)\<^sup>0) \<and> (\<forall>l\<in>set L'. non_destructive (f l)))
        \<Longrightarrow> constructive (\<lambda>x. (SEQ\<^sub>\<checkmark> l \<in>@ L. f l x) r)\<close>
    by (auto split: list.split_asm intro: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k(3)
        simp add: constructive_fun_iff non_destructive_fun_iff "*" )
qed


corollary MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_non_destructive :
  \<open>non_destructive (\<lambda>P. (SEQ\<^sub>\<checkmark> l \<in>@ L. P l) r)\<close>
  \<open>non_destructive (\<lambda>P. (SEQ\<^sub>\<checkmark> l \<in>@ L. P l))\<close>
  by (simp_all add: MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k(1)[of L \<open>\<lambda>l x. x l\<close>])


declare MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
  [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset, simp]



(*<*)
end
  (*>*)