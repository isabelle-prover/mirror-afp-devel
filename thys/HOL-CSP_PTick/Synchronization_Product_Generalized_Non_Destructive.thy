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


(*<*)
theory Synchronization_Product_Generalized_Non_Destructive
  imports "HOL-CSP_RS" CSP_PTick_Monotonicities Events_Ticks_CSP_PTick_Laws 
begin
  (*>*)


section \<open>Synchronization Product\<close>

subsection \<open>Refinement\<close>

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_div_oneside :
  assumes \<open>tF u\<close> \<open>ftF v\<close> \<open>t_P \<in> \<D> (P \<down> n)\<close> \<open>t_Q \<in> \<T> (Q \<down> n)\<close>
    \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), A)\<close>
  shows \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<down> n)\<close>
proof (insert assms(3, 4), elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
  from assms(1, 2, 5) show \<open>t_P \<in> \<D> P \<Longrightarrow> t_Q \<in> \<T> Q \<Longrightarrow> u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<down> n)\<close>
    by (auto simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
next
  fix t_Q' t_Q''
  assume * : \<open>t_P \<in> \<D> P\<close> \<open>length t_P \<le> n\<close> \<open>t_Q = t_Q' @ t_Q''\<close>
    \<open>t_Q' \<in> \<T> Q\<close> \<open>length t_Q' = n\<close> \<open>tF t_Q'\<close> \<open>ftF t_Q''\<close>
  from \<open>t_Q = t_Q' @ t_Q''\<close> have \<open>t_Q' \<le> t_Q\<close> by simp
  from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_le_prefixR[OF assms(5) this]
  obtain t_P' t_P'' u' u''
    where ** : \<open>u = u' @ u''\<close> \<open>t_P = t_P' @ t_P''\<close>
      \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q'), A)\<close>
    by (meson Prefix_Order.prefixE)
  from assms(1) \<open>u = u' @ u''\<close> have \<open>tF u'\<close> by auto
  moreover from "*"(1,4) "**"(2,3) have \<open>u' \<in> \<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    by (simp add: T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (metis D_T is_processT3_TR_append)
  moreover have \<open>length t_Q' \<le> length u'\<close>
    using "**"(3) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_imp_lengthLR_le by blast
  ultimately have \<open>u' \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<down> n)\<close>
    by (metis "*"(5) D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI nless_le)
  with "**"(1) assms(1, 2) show \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<down> n)\<close>
    by (metis is_processT7 tickFree_append_iff tickFree_imp_front_tickFree)
next
  fix t_P' t_P''
  assume * : \<open>t_P = t_P' @ t_P''\<close> \<open>t_P' \<in> \<T> P\<close> \<open>length t_P' = n\<close>
    \<open>tF t_P'\<close> \<open>ftF t_P''\<close> \<open>t_Q \<in> \<T> Q\<close> \<open>length t_Q \<le> n\<close>
  from \<open>t_P = t_P' @ t_P''\<close> have \<open>t_P' \<le> t_P\<close> by simp
  from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_le_prefixL[OF assms(5) this]
  obtain t_Q' t_Q'' u' u''
    where ** : \<open>u = u' @ u''\<close> \<open>t_Q = t_Q' @ t_Q''\<close>
      \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q'), A)\<close>
    by (meson Prefix_Order.prefixE)
  from assms(1) \<open>u = u' @ u''\<close> have \<open>tF u'\<close> by auto
  moreover from "*"(2,6) "**"(2,3) have \<open>u' \<in> \<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    by (simp add: T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (metis is_processT3_TR_append)
  moreover have \<open>length t_P' \<le> length u'\<close>
    using "**"(3) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_imp_lengthLR_le by blast
  ultimately have \<open>u' \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<down> n)\<close>
    by (metis "*"(3) D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI nless_le)
  with "**"(1) assms(1, 2) show \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<down> n)\<close>
    by (metis is_processT7 tickFree_append_iff tickFree_imp_front_tickFree)
next
  fix t_P' t_P'' t_Q' t_Q''
  assume $ : \<open>t_P = t_P' @ t_P''\<close> \<open>t_P' \<in> \<T> P\<close> \<open>length t_P' = n\<close>
    \<open>tF t_P'\<close> \<open>ftF t_P''\<close> \<open>t_Q = t_Q' @ t_Q''\<close> \<open>t_Q' \<in> \<T> Q\<close>
    \<open>length t_Q' = n\<close> \<open>tF t_Q'\<close> \<open>ftF t_Q''\<close>
  from "$"(1, 6) have \<open>t_P' \<le> t_P\<close> \<open>t_Q' \<le> t_Q\<close> by simp_all
  from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_le_prefixLR[OF assms(5) this]
  show \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<down> n)\<close>
  proof (elim disjE conjE exE)
    fix u' t_Q''' assume $$ : \<open>u' \<le> u\<close> \<open>t_Q''' \<le> t_Q'\<close>
      \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q'''), A)\<close>
    from "$"(7) "$$"(2) is_processT3_TR have \<open>t_Q''' \<in> \<T> Q\<close> by blast
    with $$(3) \<open>t_P' \<in> \<T> P\<close> have \<open>u' \<in> \<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      by (auto simp add: T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    moreover have \<open>n \<le> length u'\<close>
      using "$"(3) "$$"(3) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_imp_lengthLR_le by blast
    ultimately have \<open>u' \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<down> n)\<close>
      by (metis "$$"(1) D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI Prefix_Order.prefixE
          assms(1) nless_le tickFree_append_iff)
    thus \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<down> n)\<close>
      by (metis "$$"(1) Prefix_Order.prefixE assms(1,2) is_processT7
          tickFree_append_iff tickFree_imp_front_tickFree)
  next
    fix u' t_P''' assume $$ : \<open>u' \<le> u\<close> \<open>t_P''' \<le> t_P'\<close>
      \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P''', t_Q'), A)\<close>
    from "$"(2) "$$"(2) is_processT3_TR have \<open>t_P''' \<in> \<T> P\<close> by blast
    with $$(3) \<open>t_Q' \<in> \<T> Q\<close> have \<open>u' \<in> \<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      by (auto simp add: T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    moreover have \<open>n \<le> length u'\<close>
      using "$"(8) "$$"(3) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_imp_lengthLR_le by blast
    ultimately have \<open>u' \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<down> n)\<close>
      by (metis "$$"(1) D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI Prefix_Order.prefixE
          assms(1) nless_le tickFree_append_iff)
    thus \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<down> n)\<close>
      by (metis "$$"(1) Prefix_Order.prefixE assms(1,2) is_processT7
          tickFree_append_iff tickFree_imp_front_tickFree)
  qed
qed



lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD :
  \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<down> n \<sqsubseteq>\<^sub>F\<^sub>D (P \<down> n) \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> (Q \<down> n)\<close> (is \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
proof (unfold refine_defs, safe)
  show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
    by (unfold D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, safe)
      (solves \<open>simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_div_oneside\<close>,
        metis Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_div_oneside
        Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
  thus \<open>(t, X) \<in> \<F> ((P \<down> n) \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> (Q \<down> n)) \<Longrightarrow> (t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<down> n)\<close> for t X
    by (meson is_processT8 le_approx2 mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self)
qed

text \<open>The equality does not hold in general, but we can establish it
      by adding an assumption over the strict alphabets of the processes.\<close>

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) strict_events_of_subset_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<down> n = (P \<down> n) \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> (Q \<down> n)\<close> (is \<open>?lhs = ?rhs\<close>)
  if \<open>\<^bold>\<alpha>(P) \<subseteq> A \<or> \<^bold>\<alpha>(Q) \<subseteq> A\<close>
proof (rule FD_antisym)
  show \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close> by (fact restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD)
next
  have div : \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
    by (auto simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)

  { fix t u v assume \<open>t = u @ v\<close> \<open>u \<in> \<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>length u = n\<close> \<open>tF u\<close> \<open>ftF v\<close>
    from this(2) consider \<open>u \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      | t_P t_Q where \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close>
        \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), A)\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    hence \<open>t \<in> \<D> ?rhs\<close>
    proof cases
      show \<open>u \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<Longrightarrow> t \<in> \<D> ?rhs\<close>
        by (simp add: \<open>ftF v\<close> \<open>t = u @ v\<close> \<open>tF u\<close> div is_processT7)
    next
      fix t_P t_Q assume \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close>
        and setinter : \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), A)\<close>
      consider \<open>t_P \<in> \<D> P \<or> t_Q \<in> \<D> Q\<close> | \<open>t_P \<notin> \<D> P\<close> \<open>t_Q \<notin> \<D> Q\<close> by blast
      thus \<open>t \<in> \<D> ?rhs\<close>
      proof cases
        assume \<open>t_P \<in> \<D> P \<or> t_Q \<in> \<D> Q\<close>
        with \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> setinter \<open>ftF v\<close> \<open>t = u @ v\<close> \<open>tF u\<close>
        have \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close> by (auto simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        thus \<open>t \<in> \<D> ?rhs\<close> by (fact div)
      next
        assume \<open>t_P \<notin> \<D> P\<close> \<open>t_Q \<notin> \<D> Q\<close>
        with \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> \<open>\<^bold>\<alpha>(P) \<subseteq> A \<or> \<^bold>\<alpha>(Q) \<subseteq> A\<close>
        have \<open>{a. ev a \<in> set t_P} \<subseteq> A \<or> {a. ev a \<in> set t_Q} \<subseteq> A\<close>
          by (auto dest: subsetD intro: strict_events_of_memI)
        with setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subsetL[OF \<open>tF u\<close> _ setinter]
          setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subsetR[OF \<open>tF u\<close> _ setinter]
        have \<open>u = map ev (map of_ev t_P) \<or> u = map ev (map of_ev t_Q)\<close> by blast
        with \<open>length u = n\<close> have \<open>length t_P = n \<or> length t_Q = n\<close> by auto
        moreover from \<open>tF u\<close> tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff[OF setinter]
        have \<open>tF t_P\<close> \<open>tF t_Q\<close> by simp_all
        ultimately have \<open>t_P \<in> \<D> (P \<down> n) \<or> t_Q \<in> \<D> (Q \<down> n)\<close>
          using \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> by (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        moreover from \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close>
        have \<open>t_P \<in> \<T> (P \<down> n)\<close> \<open>t_Q \<in> \<T> (Q \<down> n)\<close>
          by (simp_all add: T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        ultimately show \<open>t \<in> \<D> ?rhs\<close>
          using \<open>ftF v\<close> \<open>t = u @ v\<close> \<open>tF u\<close> setinter by (auto simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      qed
    qed
  } note * = this

  show \<open>?rhs \<sqsubseteq>\<^sub>F\<^sub>D ?lhs\<close>
  proof (unfold refine_defs, safe)
    show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
    proof (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      show \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<Longrightarrow> t \<in> \<D> ?rhs\<close> by (fact div)
    next
      show \<open>\<lbrakk>t = u @ v; u \<in> \<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q); length u = n; tF u; ftF v\<rbrakk>
            \<Longrightarrow> t \<in> \<D> ?rhs\<close> for u v by (fact "*")
    qed
  next
    show \<open>(t, X) \<in> \<F> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for t X
    proof (elim F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      assume \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      then consider \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
        | (fail) t_P t_Q X_P X_Q where \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
          \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), A)\<close>
          \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P A X_Q\<close>
        unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
      thus \<open>(t, X) \<in> \<F> ?rhs\<close>
      proof cases
        from div D_F show \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> by blast
      next
        case fail
        thus \<open>(t, X) \<in> \<F> ?rhs\<close>
          by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      qed
    next
      show \<open>\<lbrakk>t = u @ v; u \<in> \<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q); length u = n; tF u; ftF v\<rbrakk>
            \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for u v by (simp add: "*" is_processT8)
    qed
  qed
qed


corollary restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD :
  \<open>\<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l \<down> n \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. (P l \<down> n)\<close>
proof (induct L rule: induct_list012)
  show \<open>\<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ []. P l \<down> n \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ []. (P l \<down> n)\<close> by simp
next
  show \<open>\<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ [l1]. P l \<down> n \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ [l1]. (P l \<down> n)\<close> for l1
    by (simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Renaming)
next
  fix l1 l2 L
  assume hyp : \<open>\<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l2 # L). P l \<down> n \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l2 # L). (P l \<down> n)\<close>
  show \<open>\<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # l2 # L). P l \<down> n \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # l2 # L). (P l \<down> n)\<close>
    by simp
      (fact trans_FD[OF Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD
          Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD[OF idem_FD hyp]])
qed

text (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) \<open>
The generalization of the lemma
@{thm strict_events_of_subset_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[no_vars]}
is not straightforward. We can already observe with only three processes that
one can not expect the first synchronization to have its strict alphabets
contained in the synchronization set. Therefore, we have to assume the
condition on at least \<^term>\<open>length L - 1\<close> processes.\<close>

corollary strict_events_of_subset_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l \<down> n = (if n = 0 then \<bottom> else \<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. (P l \<down> n))\<close>
  \<comment>\<open>\<open>if n = 0 then \<bottom> else _\<close> is necessary because we can have \<^term>\<open>L = []\<close>.\<close>
  if \<open>\<And>l. l \<in> set (tl L) \<Longrightarrow> \<^bold>\<alpha>(P l) \<subseteq> A\<close>
proof (split if_split, intro conjI impI)
  show \<open>n = 0 \<Longrightarrow> \<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l \<down> n = \<bottom>\<close> by simp
next
  from that show \<open>\<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l \<down> n = \<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. (P l \<down> n)\<close> if \<open>n \<noteq> 0\<close>
  proof (induct L rule: induct_list012)
    case 1 show ?case by (simp add: \<open>n \<noteq> 0\<close>)
  next
    case (2 l1) show ?case by (simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Renaming)
  next
    case (3 l1 l2 L)
    from "3.prems" have * : \<open>\<^bold>\<alpha>(MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k A (l2 # L) P) \<subseteq> A\<close>
      by (intro subset_trans[OF strict_events_of_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset]) auto
    have \<open>\<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # l2 # L). P l \<down> n =
          P l1 \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l2 # L). P l \<down> n\<close> by simp
    also have \<open>\<dots> = (P l1 \<down> n) \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (\<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l2 # L). P l \<down> n)\<close>
      by (simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.strict_events_of_subset_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k "*")
    also have \<open>\<dots> = (P l1 \<down> n) \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l2 # L). (P l \<down> n)\<close>
      using "3.hyps"(2) "3.prems" by auto
    also have \<open>\<dots> = \<^bold>\<lbrakk>A\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # l2 # L). (P l \<down> n)\<close> by simp
    finally show ?case .
  qed
qed


corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P ||\<^sub>\<checkmark> Q \<down> n = (P \<down> n) ||\<^sub>\<checkmark> (Q \<down> n)\<close>
  by (simp add: strict_events_of_subset_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

corollary restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_MultiPar\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ L. P l \<down> n = (if n = 0 then \<bottom> else \<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ L. (P l \<down> n))\<close>
  by (simp add: strict_events_of_subset_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)



subsection \<open>Non Destructiveness\<close>

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_non_destructive :
  \<open>non_destructive (\<lambda>(P, Q). P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
proof (rule order_non_destructiveI, clarify)
  fix P P' :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and Q Q' :: \<open>('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and n
  assume \<open>(P, Q) \<down> n = (P', Q') \<down> n\<close>
  hence \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close>
    by (simp_all add: restriction_prod_def)
  show \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<down> n \<sqsubseteq>\<^sub>F\<^sub>D P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q' \<down> n\<close>
  proof (rule leFD_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
    show \<open>t \<in> \<D> (P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q') \<Longrightarrow> t \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<down> n)\<close> for t
      by (metis (no_types, lifting) \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close> in_mono le_ref1 mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD
          restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_self restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD)
  next
    show \<open>(t, X) \<in> \<F> (P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q') \<Longrightarrow> (t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<down> n)\<close> for t X
      by (metis (no_types, lifting) \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close> le_ref2 mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD
                restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_self restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD subsetD)
  qed
qed



subsection \<open>Setup\<close>

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
  [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset, simp] :
  \<open>non_destructive f \<Longrightarrow> non_destructive g \<Longrightarrow> non_destructive (\<lambda>x. f x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> g x)\<close>
  \<open>constructive f \<Longrightarrow> constructive g \<Longrightarrow> constructive (\<lambda>x. f x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> g x)\<close>
  by (fact non_destructive_comp_non_destructive
      [OF Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_non_destructive non_destructive_prod_codomain, simplified])
    (fact non_destructive_comp_constructive
      [OF Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_non_destructive constructive_prod_codomain, simplified])


lemma MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
  [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset, simp] :
  \<open>(\<And>l. l \<in> set L \<Longrightarrow> non_destructive (f l)) \<Longrightarrow> non_destructive (\<lambda>x. \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. f l x)\<close>
  \<open>(\<And>l. l \<in> set L \<Longrightarrow> constructive (f l)) \<Longrightarrow> constructive (\<lambda>x. \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. f l x)\<close>
  by (induct L rule: induct_list012; simp)+


corollary MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_non_destructive : \<open>non_destructive (\<lambda>P. \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l)\<close>
  by (rule MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k(1)[of L \<open>\<lambda>m x. x m\<close>]) simp




(*<*)
end
  (*>*)