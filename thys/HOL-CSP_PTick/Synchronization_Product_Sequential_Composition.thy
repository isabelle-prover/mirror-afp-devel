(***********************************************************************************
 * Copyright (c) 2026 Université Paris-Saclay
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


chapter \<open>Advanced Laws about Synchronization Product of Sequential Compositions\<close>

text \<open>This is new in Isabelle26.\<close>


(*<*)
theory Synchronization_Product_Sequential_Composition
  imports CSP_PTick_Laws Events_Ticks_CSP_PTick_Laws
begin
  (*>*)




section \<open>LHS Move Together\<close>

lemma SKIPS_FD_lhs_imp_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is :
  \<open>P \<^bold>;\<^sub>\<checkmark> Q = \<sqinter>r \<in> {r. \<checkmark>(r) \<in> P\<^sup>0}. Q r\<close> (is \<open>?lhs = ?rhs\<close>) if \<open>SKIPS R \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  by (subst SKIPS_FD_iff[OF that]) simp


lemma (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) SKIPS_UNIV_FD_lhs_imp_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P1 \<^bold>;\<^sub>\<checkmark> Q1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> P2 \<^bold>;\<^sub>\<checkmark> Q2 = (P1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2) \<^bold>;\<^sub>\<checkmark> (\<lambda>(r1, r2). (Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2))\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>SKIPS UNIV \<sqsubseteq>\<^sub>F\<^sub>D P1\<close> \<open>SKIPS UNIV \<sqsubseteq>\<^sub>F\<^sub>D P2\<close>
proof -
  from that have * : \<open>{r. \<checkmark>(r) \<in> P1\<^sup>0} \<noteq> {}\<close> \<open>{r. \<checkmark>(r) \<in> P2\<^sup>0} \<noteq> {}\<close>
    by (metis SKIPS_FD_SKIPS_iff SKIPS_FD_iff empty_not_UNIV)+
  have \<open>?lhs = \<sqinter>r \<in> {r. \<checkmark>(r) \<in> P1\<^sup>0}. Q1 r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<sqinter>r \<in> {r. \<checkmark>(r) \<in> P2\<^sup>0}. Q2 r\<close>
    by (subst SKIPS_FD_iff[OF that(1)], subst SKIPS_FD_iff[OF that(2)]) simp
  also from "*" have \<open>\<dots> = \<sqinter>r2 \<in> {r. \<checkmark>(r) \<in> P2\<^sup>0}. \<sqinter>r1 \<in> {r. \<checkmark>(r) \<in> P1\<^sup>0}. (Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2)\<close>
    by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right
        intro!: mono_GlobalNdet_eq)
  also have \<open>... = \<sqinter>(r1, r2) \<in> {r. \<checkmark>(r) \<in> P1\<^sup>0} \<times> {r. \<checkmark>(r) \<in> P2\<^sup>0}. (Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2)\<close>
    by (simp flip: GlobalNdet_sets_commute[of \<open>{r. \<checkmark>(r) \<in> P1\<^sup>0}\<close>] add: GlobalNdet_cartprod)
  also from that have \<open>... = ?rhs\<close>
    by (subst (2) SKIPS_FD_iff[OF that(1)], subst (2) SKIPS_FD_iff[OF that(2)])
      (simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.SKIPS_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj_def Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right)
  finally show \<open>?lhs = ?rhs\<close> .
qed




lemma together_lhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_lemma :
  \<open>Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (P1 \<^bold>;\<^sub>\<checkmark> Q1) S (P2 \<^bold>;\<^sub>\<checkmark> Q2) =
   (P1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2) \<^bold>;\<^sub>\<checkmark> (\<lambda>(r1, r2). Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (Q1 r1) S (Q2 r2))\<close>
  (is \<open>?lhs = ?rhs\<close>)
  if \<open>P1\<^sup>0 \<subseteq> ev ` S\<close> \<open>P2\<^sup>0 \<subseteq> ev ` S\<close>
    \<open>\<And>a. ev a \<in> P1\<^sup>0 \<Longrightarrow> ev a \<in> P2\<^sup>0 \<Longrightarrow>
      Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (After.After (\<lambda>P a. STOP) P1 a \<^bold>;\<^sub>\<checkmark> Q1) S (After.After (\<lambda>P a. STOP) P2 a \<^bold>;\<^sub>\<checkmark> Q2) =
     (After.After (\<lambda>P a. STOP) P1 a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r After.After (\<lambda>P a. STOP) P2 a) \<^bold>;\<^sub>\<checkmark> (\<lambda>(r1, r2). Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (Q1 r1) S (Q2 r2))\<close>
    \<open>Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>)\<close>
  for tj :: \<open>'r \<Rightarrow> 's \<Rightarrow> 't option\<close> (infixl \<open>\<otimes>\<checkmark>\<close> 100)
proof -
  interpret Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>(\<otimes>\<checkmark>)\<close> by (fact that(4))

  from that(1, 2) have non_BOT : \<open>P1 \<noteq> \<bottom>\<close> \<open>P2 \<noteq> \<bottom>\<close>
    and non_initial_tick_P : \<open>\<checkmark>(r1) \<notin> P1\<^sup>0\<close> \<open>\<checkmark>(r2) \<notin> P2\<^sup>0\<close> for r1 r2 by auto
  hence no_singl_tick_T_P : \<open>\<not> [\<checkmark>(r1)] \<in> \<T> P1\<close> \<open>\<not> [\<checkmark>(r2)] \<in> \<T> P2\<close> for r1 r2
    by (auto simp add: initials_def)
  show \<open>?lhs = ?rhs\<close>
  proof (rule After.Process_eq_AfterI[where \<Psi> = \<open>\<lambda>P a. STOP\<close>])
    from non_BOT show \<open>?lhs = \<bottom> \<longleftrightarrow> ?rhs = \<bottom>\<close>
      by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_BOT_iff Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_BOT_iff)
        (auto simp add: BOT_iff_Nil_D Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs
          Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs no_singl_tick_T_P Cons_eq_append_conv
          dest: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k elim!: Cons_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
  next
    from non_initial_tick_P non_BOT show \<open>?lhs \<noteq> \<bottom> \<Longrightarrow> ?rhs \<noteq> \<bottom> \<Longrightarrow> ?lhs\<^sup>0 = ?rhs\<^sup>0\<close>
      by (simp add: initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_BOT_iff initials_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_BOT_iff)
        (auto simp add: BOT_iff_Nil_D Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  next
    show \<open>\<R> ?lhs = \<R> ?rhs\<close> if \<open>?lhs \<noteq> \<bottom>\<close> \<open>?rhs \<noteq> \<bottom>\<close>
    proof (intro set_eqI iffI)
      fix X assume \<open>X \<in> \<R> ?lhs\<close>
      with \<open>?lhs \<noteq> \<bottom>\<close> obtain X1 X2
        where * : \<open>X1 \<in> \<R> (P1 \<^bold>;\<^sub>\<checkmark> Q1)\<close> \<open>X2 \<in> \<R> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close>
          \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X1 S X2\<close>
        by (auto simp add: Refusals_def_bis BOT_iff_Nil_D Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs dest: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      from "*"(1, 2) non_BOT have \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1 \<in> \<R> P1\<close> \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2 \<in> \<R> P2\<close>
        by (simp_all add: Refusals_def_bis Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs no_singl_tick_T_P BOT_iff_Nil_D)
      moreover have \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1) S (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2)\<close>
        (is \<open>?S1 \<subseteq> ?S2\<close>)
      proof (rule subsetI)
        show \<open>e \<in> ?S1 \<Longrightarrow> e \<in> ?S2\<close> for e
          using "*"(3)[THEN set_mp, of \<open>ev (of_ev e)\<close>]
          by (cases e, auto simp add: subset_iff ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def image_iff) force+
      qed
      ultimately have \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X \<in> \<R> (P1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close>
        by (fastforce simp add: Refusals_def_bis Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
      thus \<open>X \<in> \<R> ?rhs\<close> by (simp add: Refusals_def_bis Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
    next
      fix X assume \<open>X \<in> \<R> ?rhs\<close>
      with non_BOT have \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X \<in> \<R> (P1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close>
        by (auto simp add: Refusals_def_bis Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs no_singl_tick_T_P BOT_iff_Nil_D Cons_eq_append_conv
            elim!: Cons_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE dest!: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      with non_BOT obtain X1 X2 where \<open>X1 \<in> \<R> P1\<close> \<open>X2 \<in> \<R> P2\<close>
        and * : \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj X1 S X2\<close>
        by (auto simp add: Refusals_def_bis Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs BOT_iff_Nil_D dest: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      have \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1 \<in> \<R> (P1 \<^bold>;\<^sub>\<checkmark> Q1)\<close>
      proof -
        from \<open>X1 \<in> \<R> P1\<close> have \<open>X1 \<union> range tick \<in> \<R> P1\<close>
          by (auto simp add: Refusals_def_bis no_singl_tick_T_P dest: F_T intro!: is_processT5)
        also have \<open>X1 \<union> range tick = ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1 :: ('a, 'r) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)\<close>
        proof (rule set_eqI)
          show \<open>e \<in> X1 \<union> range tick \<longleftrightarrow> e \<in> ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1)\<close> for e
            by (cases e; force simp add: ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def image_iff)
        qed
        finally have \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1 :: ('a, 'r) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<in> \<R> P1\<close>
          by (simp add: Refusals_def_bis Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
        thus \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1 \<in> \<R> (P1 \<^bold>;\<^sub>\<checkmark> Q1)\<close>
          by (simp add: Refusals_def_bis Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
      qed
      moreover have \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2 \<in> \<R> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close>
      proof -
        from \<open>X2 \<in> \<R> P2\<close> have \<open>X2 \<union> range tick \<in> \<R> P2\<close>
          by (auto simp add: Refusals_def_bis no_singl_tick_T_P dest: F_T intro!: is_processT5)
        also have \<open>X2 \<union> range tick = ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2 :: ('a, 's) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)\<close>
        proof (rule set_eqI)
          show \<open>e \<in> X2 \<union> range tick \<longleftrightarrow> e \<in> ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2)\<close> for e
            by (cases e; force simp add: ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def image_iff)
        qed
        finally have \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2 :: ('a, 's) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<in> \<R> P2\<close>
          by (simp add: Refusals_def_bis Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
        thus \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2 \<in> \<R> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close>
          by (simp add: Refusals_def_bis Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
      qed
      moreover have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1) S (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2)\<close>
      proof (rule subsetI)
        show \<open>e \<in> X \<Longrightarrow> e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1) S (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2)\<close> for e
          using "*"[THEN set_mp, of \<open>ev (of_ev e)\<close>]
          by (cases e, simp_all add: subset_iff ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def image_iff )
            (metis IntI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) rangeI, blast)
      qed
      ultimately show \<open>X \<in> \<R> ?lhs\<close>
        by (fastforce simp add: Refusals_def_bis Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
    qed
  next
    fix a assume \<open>?lhs \<noteq> \<bottom>\<close> \<open>?rhs \<noteq> \<bottom>\<close> \<open>?lhs\<^sup>0 = ?rhs\<^sup>0\<close>
    from non_BOT that(1, 2) show \<open>ev a \<in> ?lhs\<^sup>0 \<Longrightarrow>
        After.After (\<lambda>P a. STOP) (P1 \<^bold>;\<^sub>\<checkmark> Q1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> P2 \<^bold>;\<^sub>\<checkmark> Q2) a =
        After.After (\<lambda>P a. STOP) ((P1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2) \<^bold>;\<^sub>\<checkmark> (\<lambda>(r1, r2). Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2)) a\<close>
      apply (auto simp add: After_Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[where \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k = \<open>\<lambda>P a. STOP\<close> and \<Psi>\<^sub>l\<^sub>h\<^sub>s = \<open>\<lambda>P a. STOP\<close> and \<Psi>\<^sub>r\<^sub>h\<^sub>s = \<open>\<lambda>P a. STOP\<close>] BOT_iff_Nil_D Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs no_singl_tick_T_P initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k initials_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k non_initial_tick_P After_Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.intro Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_axioms)
      apply (simp add: AfterDuplicated_same_events.After_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[where \<Psi>\<^sub>\<alpha> = \<open>\<lambda>P a. STOP\<close> and \<Psi>\<^sub>\<beta> = \<open>\<lambda>P a. STOP\<close>] non_initial_tick_P Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k BOT_iff_Nil_D)
      apply (auto simp add: After_Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[where \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k = \<open>\<lambda>P a. STOP\<close> and \<Psi>\<^sub>l\<^sub>h\<^sub>s = \<open>\<lambda>P a. STOP\<close> and \<Psi>\<^sub>r\<^sub>h\<^sub>s = \<open>\<lambda>P a. STOP\<close>] BOT_iff_Nil_D Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k initials_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k After_Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.intro Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_axioms)
      using that(3) by auto
  qed
qed



theorem (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) together_lhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P1 \<^bold>;\<^sub>\<checkmark> Q1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> P2 \<^bold>;\<^sub>\<checkmark> Q2 = (P1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2) \<^bold>;\<^sub>\<checkmark> (\<lambda>(r1, r2). (Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2))\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>A \<subseteq> S\<close>
  \<open>((\<lambda> X. (\<sqinter>a \<in> A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<sqsubseteq>\<^sub>F\<^sub>D P1\<close>
  \<open>((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<sqsubseteq>\<^sub>F\<^sub>D P2\<close>
  using that(2, 3)
proof (induct i arbitrary: P1 P2)
  case 0 thus ?case by (simp add: SKIPS_UNIV_FD_lhs_imp_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
next
  case (Suc i)
  from Suc.prems[THEN anti_mono_initials_FD] \<open>A \<subseteq> S\<close>
  have \<open>P1\<^sup>0 \<subseteq> ev ` A\<close> \<open>P2\<^sup>0 \<subseteq> ev ` A\<close> \<open>P1\<^sup>0 \<subseteq> ev ` S\<close> \<open>P2\<^sup>0 \<subseteq> ev ` S\<close>
    by (auto simp add: subset_iff initials_Ndet initials_Mndetprefix)
  from Suc.prems have * : \<open>(\<sqinter>a \<in> A \<rightarrow> ((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV)) \<sqinter> STOP \<sqsubseteq>\<^sub>F\<^sub>D P1\<close>
    \<open>(\<sqinter>a \<in> A \<rightarrow> ((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV)) \<sqinter> STOP \<sqsubseteq>\<^sub>F\<^sub>D P2\<close> by simp_all
  have \<open>ev a \<in> P1\<^sup>0 \<Longrightarrow> ((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<sqsubseteq>\<^sub>F\<^sub>D After.After (\<lambda>P a. STOP) P1 a\<close>
    \<open>ev a \<in> P2\<^sup>0 \<Longrightarrow> ((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<sqsubseteq>\<^sub>F\<^sub>D After.After (\<lambda>P a. STOP) P2 a\<close> for a
    using "*"[THEN After.mono_After_FD[where a = a and \<Psi> = \<open>\<lambda>P a. STOP\<close>, rotated]] \<open>P1\<^sup>0 \<subseteq> ev ` A\<close> \<open>P2\<^sup>0 \<subseteq> ev ` A\<close>
    by (auto simp add: After.After_Ndet initials_Mndetprefix After.After_Mndetprefix subset_iff image_iff split: if_splits)    
  from Suc.hyps[OF this] have \<open>ev a \<in> P1\<^sup>0 \<Longrightarrow> ev a \<in> P2\<^sup>0 \<Longrightarrow>
    After.After (\<lambda>P a. STOP) P1 a \<^bold>;\<^sub>\<checkmark> Q1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> After.After (\<lambda>P a. STOP) P2 a \<^bold>;\<^sub>\<checkmark> Q2 =
    (After.After (\<lambda>P a. STOP) P1 a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r After.After (\<lambda>P a. STOP) P2 a) \<^bold>;\<^sub>\<checkmark> (\<lambda>(r1, r2). Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2)\<close> for a .
  from together_lhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_lemma[OF \<open>P1\<^sup>0 \<subseteq> ev ` S\<close> \<open>P2\<^sup>0 \<subseteq> ev ` S\<close> this Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_axioms]
  show \<open>P1 \<^bold>;\<^sub>\<checkmark> Q1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> P2 \<^bold>;\<^sub>\<checkmark> Q2 = (P1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2) \<^bold>;\<^sub>\<checkmark> (\<lambda>(r1, r2). Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2)\<close> .
qed


hide_fact together_lhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_lemma

lemma \<open>((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) Q \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  if \<open>((\<lambda>X. \<sqinter>a\<in>A \<rightarrow> X) ^^ i) Q \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
    (* so we are weakening the assumption *)
proof -
  have \<open>((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) Q \<sqsubseteq>\<^sub>F\<^sub>D ((\<lambda>X. \<sqinter>a\<in>A \<rightarrow> X) ^^ i) Q\<close>
    by (induct i, simp_all)
      (meson Ndet_FD_self_left mono_Mndetprefix_FD order_trans)
  with that trans_FD show ?thesis by blast
qed



corollary (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) together_lhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_through_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t :
  \<open>P1 \<^bold>;\<^sub>\<checkmark> Q1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> P2 \<^bold>;\<^sub>\<checkmark> Q2 = (P1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t P2) \<^bold>;\<^sub>\<checkmark> (\<lambda>rs. Q1 (hd rs) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 (tl rs))\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>A \<subseteq> S\<close>
  \<open>((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<sqsubseteq>\<^sub>F\<^sub>D P1\<close>
  \<open>((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<sqsubseteq>\<^sub>F\<^sub>D P2\<close>
proof -
  have * : \<open>rs \<in> \<^bold>\<checkmark>\<^bold>s(P1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t P2) \<Longrightarrow>
           (THE r_s. r_s \<in> \<^bold>\<checkmark>\<^bold>s(P1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2) \<and> rs = fst r_s # snd r_s) = (hd rs, tl rs)\<close> for rs
    find_theorems strict_ticks_of RenamingTick
    by (auto simp flip: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_to_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t simp add: strict_ticks_of_RenamingTick)
  have \<open>P1 \<^bold>;\<^sub>\<checkmark> Q1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> P2 \<^bold>;\<^sub>\<checkmark> Q2 = (P1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2) \<^bold>;\<^sub>\<checkmark> (\<lambda>(r1, r2). (Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2))\<close>
    by (fact together_lhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF that])
  also have \<open>\<dots> = (P1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t P2) \<^bold>;\<^sub>\<checkmark> (\<lambda>rs. (Q1 (hd rs) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 (tl rs)))\<close>
    by (subst inj_on_Renaming_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of \<open>\<lambda>(r, s). r # s\<close> _ _ id id, simplified])
      (auto simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_to_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t prod.case_eq_if "*" intro!: inj_onI mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq)
  finally show \<open>P1 \<^bold>;\<^sub>\<checkmark> Q1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> P2 \<^bold>;\<^sub>\<checkmark> Q2 = \<dots>\<close> .
qed



lemma compower_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_compower_eq_compower :
  \<open>((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r
   ((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) = ((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV)\<close>
  if \<open>A \<subseteq> S\<close>
proof (induct i)
  case 0 from \<open>A \<subseteq> S\<close> show ?case
    by (simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_Ndet_left Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_Ndet_right Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix
        Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_subset Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.SKIPS_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS)
next
  case (Suc i) with \<open>A \<subseteq> S\<close> show ?case
    apply (simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_Ndet_left Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_Ndet_right Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix
        Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_subset)
    apply (simp add: subset_iff)
    apply safe
       apply auto
      apply (simp add: Ndet_aci(4) Ndet_commute mono_Ndet_FD mono_write0_FD)
     apply (simp add: Int_absorb2 that(1))
    by (metis (no_types, lifting) Mndetprefix_empty Ndet_assoc Ndet_id diff_shunt that(1))
qed

lemma compower_FD_compower_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_compower_FD :
  \<open>((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<sqsubseteq>\<^sub>F\<^sub>D
   ((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t
   ((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV)\<close>
  if \<open>A \<subseteq> S\<close>
proof -
  have \<open>((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<sqsubseteq>\<^sub>F\<^sub>D ((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS (UNIV - {[]}))\<close>
    by (induct i)
      (auto simp add: mono_Mndetprefix_FD mono_Ndet_FD SKIPS_FD_SKIPS_iff)
  also have \<open>\<dots> = RenamingTick (((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV)) (\<lambda>(r, s). r # s)\<close>
    apply (induct i)
    by (auto simp add: prod.case_eq_if RenamingTick_Ndet RenamingTick_Mndetprefix intro!: arg_cong[where f = SKIPS])
      (metis (lifting) neq_Nil_conv prod.sel(1, 2) rangeI)
  also have \<open>\<dots> = RenamingTick (((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r ((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV)) (\<lambda>(r, s). r # s)\<close>
    by (fact arg_cong[symmetric, OF compower_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_compower_eq_compower[OF \<open>A \<subseteq> S\<close>]])
  also have \<open>\<dots> = ((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t
                 ((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV)\<close>
    by (metis Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_to_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t)
  finally show ?thesis .
qed



lemma compower_FD_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<lbrakk>L \<noteq> []; \<And>l. l \<in> set L \<Longrightarrow> ((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<sqsubseteq>\<^sub>F\<^sub>D P l\<rbrakk> \<Longrightarrow>
    ((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l\<close> if \<open>A \<subseteq> S\<close>
proof (induct L rule: induct_list012)
  case 1 thus ?case by simp
next
  case (2 l1)
  have \<open>((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<sqsubseteq>\<^sub>F\<^sub>D RenamingTick (((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV)) (\<lambda>r. [r])\<close>
    by (induct i)
      (simp_all add: SKIPS_FD_SKIPS_iff RenamingTick_Ndet RenamingTick_Mndetprefix mono_Mndetprefix_FD mono_Ndet_FD)
  also from "2.prems"(2) have \<open>\<dots> \<sqsubseteq>\<^sub>F\<^sub>D RenamingTick (P l1) (\<lambda>r. [r])\<close>
    by (simp add: mono_Renaming_FD)
  finally show ?case by simp
next
  case (3 l1 l2 L)
  show ?case
    by (simp, rule trans_FD[OF compower_FD_compower_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_compower_FD[OF \<open>A \<subseteq> S\<close>]])
      (auto intro!: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD "3.hyps"(2) simp add: "3.prems"(2))
qed




theorem together_lhs_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. (P l \<^bold>;\<^sub>\<checkmark> Q l) = (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip L R. Q l r)\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>A \<subseteq> S\<close>
  \<open>\<And>l. l \<in> set L \<Longrightarrow> ((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<sqsubseteq>\<^sub>F\<^sub>D P l\<close>
  using that(2)
proof (induct L rule: induct_list012)
  case 1
  show ?case by simp
next
  case (2 l0)
  have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ [l0]. (P l \<^bold>;\<^sub>\<checkmark> Q l) = RenamingTick (P l0 \<^bold>;\<^sub>\<checkmark> Q l0) (\<lambda>r. [r])\<close> by simp
  also have \<open>\<dots> = RenamingTick (P l0) (\<lambda>r. [r]) \<^bold>;\<^sub>\<checkmark> (\<lambda>g_r. RenamingTick (Q l0 (THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P l0) \<and> g_r = [r])) (\<lambda>r. [r]))\<close>
    by (auto intro: inj_on_Renaming_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of \<open>\<lambda>r. [r]\<close>] inj_onI)
  also have \<open>\<dots> = (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ [l0]. P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip [l0] R. Q l r)\<close>
    by (auto intro!: mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq simp add: strict_ticks_of_RenamingTick the_equality)
  finally show ?case .
next
  case (3 l0 l1 L)
  have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l) =
        P l0 \<^bold>;\<^sub>\<checkmark> Q l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l)\<close> by simp
  also have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l) =
             (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip (l1 # L) R. Q l r)\<close>
    by (rule "3.hyps"(2)) (simp add: "3.prems")
  finally have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l) =
                P l0 \<^bold>;\<^sub>\<checkmark> Q l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip (l1 # L) R. Q l r)\<close> .
  also have \<open>\<dots> = (P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). P l) \<^bold>;\<^sub>\<checkmark>
    (\<lambda>rs. Q l0 (hd rs) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (x, y) \<in>@ zip (l1 # L) (tl rs). Q x y)\<close>
    by (auto intro!: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.together_lhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_through_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t[OF \<open>A \<subseteq> S\<close>, of i]
        compower_FD_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF \<open>A \<subseteq> S\<close>] simp add: "3.prems")

  also have \<open>\<dots> = (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip (l0 # l1 # L) R. Q l r)\<close>
  proof (rule mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq)
    show \<open>P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). P l = \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). P l\<close> by simp
  next
    fix R assume \<open>R \<in> \<^bold>\<checkmark>\<^bold>s(P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). P l)\<close>
    from is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
      [THEN is_ticks_lengthD, of _ _ \<open>l0 # l1 # L\<close>, simplified, OF this]
    obtain r0 r1 R' where \<open>R = r0 # r1 # R'\<close> by (metis Suc_length_conv)
    thus \<open>Q l0 (hd R) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip (l1 # L) (tl R). Q l r =
          \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip (l0 # l1 # L) R. Q l r\<close> by simp
  qed
  finally show ?case .
qed


theorem together_lhs_MultiSync_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk> l \<in># mset L. (P l \<^bold>;\<^sub>\<checkmark> Q l) = (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r) \<in># mset (zip L R). Q l r)\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>A \<subseteq> S\<close>
  \<open>\<And>l. l \<in> set L \<Longrightarrow> ((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<sqsubseteq>\<^sub>F\<^sub>D P l\<close>
  using that(2)
proof (induct L rule: induct_list012)
  case 1
  show ?case by simp
next
  case (2 l0)
  have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk> l \<in># mset [l0]. (P l \<^bold>;\<^sub>\<checkmark> Q l) = P l0 \<^bold>;\<^sub>\<checkmark> Q l0\<close> by simp
  also have \<open>\<dots> = RenamingTick (P l0) (\<lambda>r. [r]) \<^bold>;\<^sub>\<checkmark> (\<lambda>g_r. Q l0 (THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P l0) \<and> g_r = [r]))\<close>
    by (auto intro: inj_on_Renaming_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of \<open>\<lambda>r. [r]\<close> _ _ id id, simplified] inj_onI)
  also have \<open>\<dots> = (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ [l0]. P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r) \<in># mset (zip [l0] R). Q l r)\<close>
    by (auto intro!: mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq simp add: strict_ticks_of_RenamingTick the_equality)
  finally show ?case .
next
  case (3 l0 l1 L)
  have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk> l\<in>#mset (l0 # l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l) =
        P l0 \<^bold>;\<^sub>\<checkmark> Q l0 \<lbrakk>S\<rbrakk> \<^bold>\<lbrakk>S\<^bold>\<rbrakk> l\<in>#mset (l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l)\<close> by simp
  also have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk> l\<in>#mset (l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l) =
        \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). P l \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r)\<in>#mset (zip (l1 # L) R). Q l r)\<close>
    by (rule "3.hyps"(2)) (simp add: "3.prems")
  finally have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk> l\<in>#mset (l0 # l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l) =
                    P l0 \<^bold>;\<^sub>\<checkmark> Q l0 \<lbrakk>S\<rbrakk> \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). P l \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r)\<in>#mset (zip (l1 # L) R). Q l r)\<close> .
  also have \<open>\<dots> = (P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). P l) \<^bold>;\<^sub>\<checkmark>
                      (\<lambda>R. Q l0 (hd R) \<lbrakk>S\<rbrakk> \<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r)\<in>#mset (zip (l1 # L) (tl R)). Q l r)\<close>
    by (auto simp flip: Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_is_Sync intro!: Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c.together_lhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_through_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t[OF \<open>A \<subseteq> S\<close>, of i]
        compower_FD_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF \<open>A \<subseteq> S\<close>] simp add: "3.prems")
  also have \<open>\<dots> = (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r) \<in># mset (zip (l0 # l1 # L) R). Q l r)\<close>
  proof (rule mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq)
    show \<open>P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). P l = \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). P l\<close> by simp
  next
    fix R assume \<open>R \<in> \<^bold>\<checkmark>\<^bold>s(P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). P l)\<close>
    from is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
      [THEN is_ticks_lengthD, of _ _ \<open>l0 # l1 # L\<close>, simplified, OF this]
    obtain r0 r1 R' where \<open>R = r0 # r1 # R'\<close> by (metis Suc_length_conv)
    thus \<open>Q l0 (hd R) \<lbrakk>S\<rbrakk> \<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r)\<in>#mset (zip (l1 # L) (tl R)). Q l r =
          \<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r)\<in>#mset (zip (l0 # l1 # L) R). Q l r\<close> by simp
  qed
  finally show ?case .
qed




lemma \<open>SKIPS UNIV \<sqinter> STOP \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l \ I\<close>
  if \<open>A \<subseteq> I\<close> \<open>I \<subseteq> S\<close> \<open>L \<noteq> []\<close> \<open>\<And>l. l \<in> set L \<Longrightarrow> ((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<sqsubseteq>\<^sub>F\<^sub>D P l\<close>
proof -
  have \<open>((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l\<close>
    by (rule compower_FD_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF subset_trans[OF that(1, 2)] that(3, 4)])
  hence \<open>((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \ I \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l \ I\<close>
    by (fact mono_Hiding_FD)
  also have \<open>((\<lambda>X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> STOP) ^^ i) (SKIPS UNIV) \ I = (if i = 0 then SKIPS UNIV else if A = {} then STOP else SKIPS UNIV \<sqinter> STOP)\<close>
    by (induct i)
      (simp_all add: Hiding_SKIPS Hiding_Mndetprefix_subset[OF that(1)]
        Hiding_distrib_Ndet Ndet_aci(4) Ndet_commute split: if_split_asm)
  finally have \<open>\<dots> \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l \ I\<close> (is \<open>?ugly \<sqsubseteq>\<^sub>F\<^sub>D _\<close>) .
  also have \<open>SKIPS UNIV \<sqinter> STOP \<sqsubseteq>\<^sub>F\<^sub>D ?ugly\<close>
    by (simp add: Ndet_FD_self_left Ndet_FD_self_right)
  finally (trans_FD[rotated]) show ?thesis .
qed


lemma \<open> r \<in> \<^bold>\<checkmark>\<^bold>s(\<^bold>|\<^bold>|\<^sub>\<checkmark> l\<in>@L. P l a \ I) \<Longrightarrow> length r = length L\<close>
  by (meson is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k is_ticks_length_def strict_ticks_of_Hiding_subset subset_iff)


lemma nonmt2:\<open>L \<noteq> [] \<Longrightarrow> r \<in> \<^bold>\<checkmark>\<^bold>s(\<^bold>\<lbrakk>UNIV\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l a \ I) \<Longrightarrow> r \<noteq> []\<close> for r a L
  by (metis append_eq_append_conv is_ticks_lengthD is_ticks_length_Hiding
      is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list.size(3) self_append_conv2)

(* 
lemma length_ge_list_le_conv :
  \<open>n \<le> length xs \<Longrightarrow> xs \<le> ys \<longleftrightarrow> take n xs = take n ys \<and> drop n xs \<le> drop n ys\<close>
  by (smt (verit, ccfv_SIG) Prefix_Order.prefixE append_eq_append_conv_if
          append_take_drop_id le_append le_length_mono length_take min.absorb_iff2 order_subst1)
 *)





section \<open>Independent LHS and Waiting RHS\<close>

subsection \<open>General Lemmas\<close>

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL_waitingD :
  \<open>set u1 \<subseteq> ev ` (- A) \<Longrightarrow>
   t setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u1 @ u2, v), A) \<Longrightarrow>
   \<exists>t'. t = map (ev \<circ> of_ev) u1 @ t' \<and>
        t' setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u2, v), A)\<close>
  if \<open>v = [] \<or> hd v \<in> ev ` A\<close>
proof (induct u1 arbitrary: t)
  case Nil from Nil.prems(2) show ?case by simp
next
  case (Cons e u1)
  from Cons.prems(1) obtain a
    where \<open>e = ev a\<close> \<open>a \<notin> A\<close> \<open>set u1 \<subseteq> ev ` (- A)\<close> by auto
  from Cons.prems(2) that obtain t'
    where \<open>t = ev a # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u1 @ u2, v), A)\<close>
    by (cases v)
      (auto simp add: setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps \<open>e = ev a\<close> \<open>a \<notin> A\<close> comp_def image_iff
        split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split_asm if_split_asm)
  from Cons.hyps[OF \<open>set u1 \<subseteq> ev ` (- A)\<close> this(2)] obtain t''
    where  \<open>t = map (ev \<circ> of_ev) (e # u1) @ t''\<close>
      \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u2, v), A)\<close>
    by (auto simp add: \<open>e = ev a\<close> \<open>t = ev a # t'\<close>)
  thus ?case by blast
qed

corollary setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendR_waitingD :
  \<open>u = [] \<or> hd u \<in> ev ` A \<Longrightarrow> set v1 \<subseteq> ev ` (- A) \<Longrightarrow>
   t setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u, v1 @ v2), A) \<Longrightarrow>
   \<exists>t'. t = map (ev \<circ> of_ev) v1 @ t' \<and> t' setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u, v2), A)\<close>
  by (subst setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual, subst (asm) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual)
    (rule setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL_waitingD)



lemma \<open>set u1 \<subseteq> ev ` (- S) \<Longrightarrow> set u1 \<inter> ev ` S = {}\<close> by blast


lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendLR_waitingD :
  \<open>\<lbrakk>set u1 \<inter> ev ` S = {}; set u2 \<inter> ev ` S = {};
   t setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u1 @ v1, u2 @ v2), S)\<rbrakk> \<Longrightarrow>
   \<exists>u v. t = u @ v \<and> u setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u1, u2), S) \<and>
                     v setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((v1, v2), S)\<close>
  if \<open>v1 = [] \<or> hd v1 \<in> ev ` S\<close> \<open>v2 = [] \<or> hd v2 \<in> ev ` S\<close>
proof (induct \<open>(tj, u1, S, u2)\<close> arbitrary: t u1 u2)
  case Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil
  thus ?case by simp
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil a1 u1)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems(1) have \<open>a1 \<notin> S\<close> by (simp add: image_iff)
  with ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems(1, 3) that(2) obtain t'
    where \<open>t = ev a1 # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u1 @ v1, [] @ v2), S)\<close> \<open>set u1 \<inter> ev ` S = {}\<close>
    by (cases v2) (auto simp add: setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.hyps[OF \<open>a1 \<notin> S\<close> this(3) _ this(2)] obtain u v
    where * : \<open>t' = u @ v\<close> \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u1, []), S)\<close>
      \<open>v setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((v1, v2), S)\<close> by auto
  from "*"(1, 2) have \<open>t = (ev a1 # u) @ v\<close> \<open>ev a1 # u setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((ev a1 # u1, []), S)\<close>
    by (simp_all add: \<open>t = ev a1 # t'\<close> \<open>a1 \<notin> S\<close>)
  with "*"(3) show ?case by blast
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil r1 u1)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems(3) that(2) have False by (cases v2) auto
  thus ?case ..
next
  case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev a2 u2)
  from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(2) have \<open>a2 \<notin> S\<close> by (simp add: image_iff)
  with Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(2, 3) that(1) obtain t'
    where \<open>t = ev a2 # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> (([] @ v1, u2 @ v2), S)\<close> \<open>set u2 \<inter> ev ` S = {}\<close>
    by (cases v1) (auto simp add: setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps)
  from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps[OF \<open>a2 \<notin> S\<close> _ this(3) this(2)]
  obtain u v where * : \<open>t' = u @ v\<close> \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> (([], u2), S)\<close>
    \<open>v setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((v1, v2), S)\<close> by auto
  from "*"(1, 2) have \<open>t = (ev a2 # u) @ v\<close> \<open>ev a2 # u setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> (([], ev a2 # u2), S)\<close>
    by (simp_all add: \<open>t = ev a2 # t'\<close> \<open>a2 \<notin> S\<close>)
  with "*"(3) show ?case by blast
next
  case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick r2 u2)
  from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(3) that(1) have False by (cases v1) auto
  thus ?case ..
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev a1 u1 a2 u2)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1, 2)
  have * : \<open>a1 \<notin> S\<close> \<open>a2 \<notin> S\<close> \<open>set u1 \<inter> ev ` S = {}\<close> \<open>set u2 \<inter> ev ` S = {}\<close> by auto
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(3)
  consider (mvL) t' where \<open>t = ev a1 # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u1 @ v1, (ev a2 # u2) @ v2), S)\<close>
    | (mvR) t' where \<open>t = ev a2 # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> (((ev a1 # u1) @ v1, u2 @ v2), S)\<close>
    by (auto simp add: "*"(1, 2))
  thus ?case
  proof cases
    case mvL
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(4)
      [OF "*"(1, 2) "*"(3) ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(2) mvL(2)] obtain u v
      where ** : \<open>t' = u @ v\<close> \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u1, ev a2 # u2), S)\<close>
        \<open>v setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((v1, v2), S)\<close> by blast
    have \<open>t = (ev a1 # u) @ v\<close> \<open>ev a1 # u setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((ev a1 # u1, ev a2 # u2), S)\<close>
      by (simp_all add: mvL(1) "**"(1, 2) "*"(1))
    with "**"(3) show ?thesis by blast
  next
    case mvR
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(5)
      [OF "*"(1, 2) ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1) "*"(4) mvR(2)] obtain u v
      where ** : \<open>t' = u @ v\<close> \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((ev a1 # u1, u2), S)\<close>
        \<open>v setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((v1, v2), S)\<close> by blast
    have \<open>t = (ev a2 # u) @ v\<close> \<open>ev a2 # u setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((ev a1 # u1, ev a2 # u2), S)\<close>
      by (simp_all add: mvR(1) "**"(1, 2) "*"(2))
    with "**"(3) show ?thesis by blast
  qed
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick a1 u1 r2 u2)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(1) have \<open>a1 \<notin> S\<close> by (simp add: image_iff)
  with ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(1, 3) obtain t'
    where \<open>t = ev a1 # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u1 @ v1, (\<checkmark>(r2) # u2) @ v2), S)\<close> \<open>set u1 \<inter> ev ` S = {}\<close>
    by (cases v2) (auto simp add: setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF \<open>a1 \<notin> S\<close> this(3)
      ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(2) this(2)] obtain u v
    where * : \<open>t' = u @ v\<close> \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u1, \<checkmark>(r2) # u2), S)\<close>
      \<open>v setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((v1, v2), S)\<close> by blast
  from "*"(1, 2) have \<open>t = (ev a1 # u) @ v\<close> \<open>ev a1 # u setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((ev a1 # u1, \<checkmark>(r2) # u2), S)\<close>
    by (simp_all add: \<open>t = ev a1 # t'\<close> \<open>a1 \<notin> S\<close>)
  with "*"(3) show ?case by blast
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev r1 u1 a2 u2)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(2) have \<open>a2 \<notin> S\<close> by (simp add: image_iff)
  with tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(2, 3) obtain t'
    where \<open>t = ev a2 # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> (((\<checkmark>(r1) # u1) @ v1, u2 @ v2), S)\<close> \<open>set u2 \<inter> ev ` S = {}\<close>
    by (cases v1) (auto simp add: setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps[OF \<open>a2 \<notin> S\<close> tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1) this(3, 2)] obtain u v
    where * : \<open>t' = u @ v\<close> \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((\<checkmark>(r1) # u1, u2), S)\<close>
      \<open>v setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((v1, v2), S)\<close> by blast
  from "*"(1, 2) have \<open>t = (ev a2 # u) @ v\<close> \<open>ev a2 # u setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((\<checkmark>(r1) # u1, ev a2 # u2), S)\<close>
    by (simp_all add: \<open>t = ev a2 # t'\<close> \<open>a2 \<notin> S\<close>)
  with "*"(3) show ?case by blast
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick r1 u1 r2 u2)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems obtain t' r 
    where * : \<open>t = \<checkmark>(r) # t'\<close> \<open>set u1 \<inter> ev ` S = {}\<close> \<open>set u2 \<inter> ev ` S = {}\<close>
      \<open>tj r1 r2 = Some r\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u1 @ v1, u2 @ v2), S)\<close>
    by (auto split: option.split_asm)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF "*"(4, 2, 3, 5)] obtain u v
    where ** : \<open>t' = u @ v\<close> \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((u1, u2), S)\<close>
      \<open>v setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((v1, v2), S)\<close> by blast
  have \<open>t = (\<checkmark>(r) # u) @ v\<close> \<open>\<checkmark>(r) # u setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((\<checkmark>(r1) # u1, \<checkmark>(r2) # u2), S)\<close>
    by (simp_all add: "*"(1, 4) "**"(1, 2))
  with "**"(3) show ?case by blast
qed




subsection \<open>Specific Lemmas\<close>

lemma indep_lhs_waiting_rhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_lemma1 :
  fixes tj :: \<open>'r \<Rightarrow> 's \<Rightarrow> 't option\<close> (infixl \<open>\<otimes>\<checkmark>\<close> 100)
  fixes P1 :: \<open>('a, 'r') process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and P2 :: \<open>('a, 's') process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assumes \<open>\<alpha>(P1) \<inter> S = {}\<close> \<open>\<alpha>(P2) \<inter> S = {}\<close>
    \<open>\<And>r1. r1 \<in> \<^bold>\<checkmark>\<^bold>s(P1) \<Longrightarrow> (Q1 r1)\<^sup>0 \<subseteq> ev ` S\<close>
    \<open>\<And>r2. r2 \<in> \<^bold>\<checkmark>\<^bold>s(P2) \<Longrightarrow> (Q2 r2)\<^sup>0 \<subseteq> ev ` S\<close>
    \<open>tF t\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t1, t2), S)\<close>
    \<open>t1 \<in> \<D> (P1 \<^bold>;\<^sub>\<checkmark> Q1)\<close> \<open>t2 \<in> \<T> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close>
    \<open>Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>)\<close>
  shows \<open>t \<in> \<D> ((P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2) \<^bold>;\<^sub>\<checkmark> (\<lambda>(r1, r2). Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (Q1 r1) S (Q2 r2)))\<close> (is \<open>t \<in> \<D> ?rhs\<close>)
proof -
  interpret Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>(\<otimes>\<checkmark>)\<close> by (fact assms(9))

  let ?map = \<open>map (ev \<circ> of_ev)\<close>
  have $ : \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((t1, t2), {})\<close>
    if \<open>tF t\<close> \<open>tF t1\<close> \<open>tF t2\<close> \<open>t1 \<in> \<T> P1\<close> \<open>t2 \<in> \<T> P2\<close>
      \<open>?map t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map t1, ?map t2), S)\<close> for t t1 t2
  proof -
    from that(4, 5) \<open>\<alpha>(P1) \<inter> S = {}\<close> \<open>\<alpha>(P2) \<inter> S = {}\<close>
    have \<open>{a. ev a \<in> set t1 \<or> ev a \<in> set t2} \<subseteq> - S\<close>
      by (auto intro: events_of_memI)
    with that(2, 3)[THEN tF_map_ev_of_ev_eq_imp_ev_mem_iff]
    have \<open>{a. ev a \<in> set (?map t1) \<or> ev a \<in> set (?map t2)} \<subseteq> - S\<close> by blast
    from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_events_of
      [OF this, of _ _ S, unfolded Compl_disjoint, THEN iffD1, OF that(6)]
    have \<open>?map t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map t1, ?map t2), {})\<close> .
    thus \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((t1, t2), {})\<close>
      by (fact tF_imp_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_map_ev_of_ev_iff[OF that(1-3), THEN iffD1])
  qed

  from assms(7) consider (D_P1) u1 v1 where \<open>t1 = ?map u1 @ v1\<close> \<open>u1 \<in> \<D> P1\<close> \<open>tF u1\<close> \<open>ftF v1\<close>
    | (D_Q1) u1 r1 v1 where \<open>t1 = ?map u1 @ v1\<close> \<open>u1 @ [\<checkmark>(r1)] \<in> \<T> P1\<close> \<open>u1 @ [\<checkmark>(r1)] \<notin> \<D> P1\<close> \<open>tF u1\<close> \<open>v1 \<in> \<D> (Q1 r1)\<close>
    by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis D_imp_ftF is_processT9)
  thus \<open>t \<in> \<D> ?rhs\<close>
  proof cases
    case D_P1
    from assms(8) consider (T_P2) u2 where \<open>t2 = ?map u2\<close> \<open>u2 \<in> \<T> P2\<close> \<open>tF u2\<close>
      | (T_Q2) u2 r2 v2 where \<open>t2 = ?map u2 @ v2\<close> \<open>u2 @ [\<checkmark>(r2)] \<in> \<T> P2\<close> \<open>u2 @ [\<checkmark>(r2)] \<notin> \<D> P2\<close> \<open>tF u2\<close> \<open>v2 \<in> \<T> (Q2 r2)\<close>
      | (D_P2) u2 v2 where \<open>t2 = ?map u2 @ v2\<close> \<open>u2 \<in> \<D> P2\<close> \<open>tF u2\<close> \<open>ftF v2\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis (no_types) T_imp_ftF is_processT9)
    thus \<open>t \<in> \<D> ?rhs\<close>
    proof cases
      case T_P2
      from assms(6)[unfolded D_P1(1) T_P2(1), THEN setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL]
      obtain u v u2' u2''
        where * : \<open>t = u @ v\<close> \<open>u2 = u2' @ u2''\<close>
          \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map u1, ?map u2'), S)\<close>
          \<open>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((v1, ?map u2''), S)\<close>
        by (auto simp add: map_eq_append_conv)
      have \<open>tF u\<close> by (metis assms(5) "*"(1) tF_append_iff)
      then obtain u' :: \<open>('a, 'r' \<times> 's') trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>tF u'\<close> \<open>u = ?map u'\<close>
        using tF_map_ev_comp tF_map_ev_of_ev_eq_iff by blast
      from T_P2(2, 3) have \<open>tF u1\<close> \<open>tF u2'\<close> \<open>u1 \<in> \<T> P1\<close> \<open>u2' \<in> \<T> P2\<close>
        by (auto simp add: D_P1(2, 3) "*"(2) intro: D_T is_processT3_TR_append) 
      from "$"[OF \<open>tF u'\<close> this "*"(3)[unfolded \<open>u = ?map u'\<close>]]
      have \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1, u2'), {})\<close> .
      with D_P1(2) \<open>tF u'\<close> \<open>u2' \<in> \<T> P2\<close> have \<open>u' \<in> \<D> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close>
        by (auto simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs intro: ftF_Nil)
      with \<open>tF u'\<close> assms(5) \<open>tF u'\<close> show \<open>t \<in> \<D> ?rhs\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs "*"(1) \<open>u = ?map u'\<close> intro: tF_imp_ftF)
    next
      case T_Q2
      from assms(6)[unfolded D_P1(1) T_Q2(1)]
      consider (waitL) t' t'' t''' u1' u1'' v2' v2''
        where \<open>t = t' @ t'' @ t'''\<close> \<open>u1 = u1' @ u1''\<close> \<open>v2 = v2' @ v2''\<close>
          \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map u1', ?map u2), S)\<close>
          \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map u1'', v2'), S)\<close>
        | (waitR) t' t'' t''' v1' v1'' u2' u2''
        where \<open>t = t' @ t'' @ t'''\<close> \<open>v1 = v1' @ v1''\<close> \<open>u2 = u2' @ u2''\<close>
          \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map u1, ?map u2'), S)\<close>
        by (auto simp add: append_eq_append_conv2 map_eq_append_conv
            dest!: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendR)
          (use waitL in blast, use waitR in blast)
      thus \<open>t \<in> \<D> ?rhs\<close>
      proof cases
        case waitL
        have \<open>tF t'\<close> by (metis assms(5) waitL(1) tF_append_iff)
        then obtain t''' :: \<open>('a, 'r' \<times> 's') trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>tF t'''\<close> \<open>t' = ?map t'''\<close>
          using tF_map_ev_comp tF_map_ev_of_ev_eq_iff by blast
        have \<open>u1' \<in> \<T> P1\<close> by (metis D_P1(2) waitL(2) is_processT3_TR_append D_T)
        have \<open>tF u1'\<close> by (metis D_P1(3) waitL(2) tF_append_iff)
        from "$"[OF \<open>tF t'''\<close> \<open>tF u1'\<close> T_Q2(4) \<open>u1' \<in> \<T> P1\<close>
            T_Q2(2)[THEN is_processT3_TR_append] waitL(4)[unfolded \<open>t' = ?map t'''\<close>]]
        have * : \<open>t''' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1', u2), {})\<close> .
        have \<open>r2 \<in> \<^bold>\<checkmark>\<^bold>s(P2)\<close> by (meson T_Q2(2, 3) strict_ticks_of_memI)
        from assms(1) assms(4)[OF \<open>r2 \<in> \<^bold>\<checkmark>\<^bold>s(P2)\<close>] T_Q2(5) D_P1(2)[THEN D_T] D_P1(3)
        have \<open>v2' = [] \<or> hd v2' \<in> ev ` S\<close> \<open>set (?map u1'') \<subseteq> ev ` (- S)\<close>
          by (simp_all add: waitL(2, 3) subset_iff image_iff disjoint_iff events_of_def)
            (metis initials_memI is_processT3_TR_append list.exhaust list.sel(1),
              metis (no_types) ComplI append.assoc event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1)
              in_set_conv_decomp tF_Cons_iff tF_append_iff)
        from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL_waitingD[OF this, of _ _ \<open>[]\<close>, simplified, OF waitL(5)] this(1)
        have \<open>t'' = ?map u1''\<close>
          by (cases v2') (simp_all add: image_iff setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split_asm)
        have \<open>tF (t''' @ ?map u1'')\<close> by (simp add: \<open>tF t'''\<close>)
        have \<open>t''' @ ?map u1'' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1, u2), {})\<close>
          by (unfold waitL(2), rule tF_disjoint_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append_tailL)
            (metis D_P1(3) waitL(2) tF_append_iff, simp, fact "*")
        with D_P1(2) T_Q2(2)[THEN is_processT3_TR_append] \<open>tF (t''' @ ?map u1'')\<close>
        have \<open>t''' @ ?map u1'' \<in> \<D> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close>
          by (simp (no_asm) add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (use ftF_Nil in blast)
        moreover have \<open>t' @ t'' = ?map (t''' @ ?map u1'')\<close>
          by (simp add: \<open>t' = ?map t'''\<close> \<open>t'' = ?map u1''\<close>)
        ultimately have \<open>t' @ t'' \<in> \<D> ?rhs\<close>
          by (simp (no_asm) add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
            (metis Nil_is_map_conv \<open>tF (t''' @ ?map u1'')\<close> append_Nil2 ftF_map_tick_comp_iff)
        with assms(5) is_processT7 waitL(1) show \<open>t \<in> \<D> ?rhs\<close> by fastforce
      next
        case waitR
        have \<open>tF t'\<close> by (metis assms(5) waitR(1) tF_append_iff)
        then obtain t'' :: \<open>('a, 'r' \<times> 's') trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>tF t''\<close> \<open>t' = ?map t''\<close>
          using tF_map_ev_comp tF_map_ev_of_ev_eq_iff by blast
        have \<open>tF u2'\<close> by (metis T_Q2(4) waitR(3) tF_append_iff)
        have \<open>u2' \<in> \<T> P2\<close> by (metis waitR(3) T_Q2(2) is_processT3_TR_append)
        from "$"[OF \<open>tF t''\<close> D_P1(3) \<open>tF u2'\<close> D_P1(2)[THEN D_T] \<open>u2' \<in> \<T> P2\<close>
            waitR(4)[unfolded \<open>t' = ?map t''\<close>]]
        have \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1, u2'), {})\<close> .
        with D_P1(2) \<open>u2' \<in> \<T> P2\<close> \<open>tF t''\<close> have \<open>t'' \<in> \<D> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close>
          by (auto simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs intro: ftF_Nil)
        thus \<open>t \<in> \<D> ?rhs\<close>
          by (simp add: waitR(1) \<open>t' = ?map t''\<close> Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs )
            (metis \<open>tF t''\<close> assms(5) tF_append_iff tF_imp_ftF waitR(1))
      qed
    next
      case D_P2
      from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_le_prefixLR
        [OF assms(6)[unfolded D_P1(1) D_P2(1)] prefixI[OF refl] prefixI[OF refl]]
      consider (leR) t' u2' where \<open>t' \<le> t\<close> \<open>u2' \<le> u2\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map u1, ?map u2'), S)\<close>
        |      (leL) t' u1' where \<open>t' \<le> t\<close> \<open>u1' \<le> u1\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map u1', ?map u2), S)\<close>
        by (simp add: less_eq_list_def prefix_def map_eq_append_conv) blast
      thus \<open>t \<in> \<D> ?rhs\<close>
      proof cases
        case leR
        have \<open>tF t'\<close> by (metis Prefix_Order.prefixE assms(5) leR(1) tF_append_iff)
        then obtain t'' :: \<open>('a, 'r' \<times> 's') trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>tF t''\<close> \<open>t' = ?map t''\<close>
          using tF_map_ev_comp tF_map_ev_of_ev_eq_iff by blast
        from "$"[OF \<open>tF t''\<close> _ _ _ _ leR(3)[unfolded \<open>t' = ?map t''\<close>]] D_P1(2,3) D_P2(2,3) leR(2)
        have \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1, u2'), {})\<close>
          by (metis D_T Prefix_Order.prefixE is_processT3_TR tF_append_iff)
        moreover have \<open>u2' \<in> \<T> P2\<close>
          by (metis leR(2) D_P2(2) is_processT3_TR D_T)
        ultimately have \<open>t'' \<in> \<D> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close>
          using D_P1(2) \<open>tF t''\<close> by (auto simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs intro: ftF_Nil)
        with leR(1) assms(5) show \<open>t \<in> \<D> ?rhs\<close>
          by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs less_eq_list_def prefix_def \<open>t' = ?map t''\<close>)
            (metis \<open>t' = map (ev \<circ> of_ev) t''\<close> \<open>tF t''\<close> tF_imp_ftF)
      next
        case leL
        have \<open>tF t'\<close> by (metis Prefix_Order.prefixE assms(5) leL(1) tF_append_iff)
        then obtain t'' :: \<open>('a, 'r' \<times> 's') trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>tF t''\<close> \<open>t' = ?map t''\<close>
          using tF_map_ev_comp tF_map_ev_of_ev_eq_iff by blast
        from "$"[OF \<open>tF t''\<close> _ _ _ _ leL(3)[unfolded \<open>t' = ?map t''\<close>]] D_P1(2,3) D_P2(2,3) leL(2)
        have \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1', u2), {})\<close> 
          by (metis D_T Prefix_Order.prefixE is_processT3_TR tF_append_iff)
        moreover have \<open>u1' \<in> \<T> P1\<close>
          by (metis leL(2) D_P1(2) is_processT3_TR D_T)
        ultimately have \<open>t'' \<in> \<D> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close>
          using D_P2(2) \<open>tF t''\<close> by (auto simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs intro: ftF_Nil)
        with leL(1) assms(5) show \<open>t \<in> \<D> ?rhs\<close>
          by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs less_eq_list_def prefix_def \<open>t' = ?map t''\<close>)
            (metis \<open>t' = map (ev \<circ> of_ev) t''\<close> \<open>tF t''\<close> tF_imp_ftF)
      qed
    qed
  next
    case D_Q1
    have \<open>r1 \<in> \<^bold>\<checkmark>\<^bold>s(P1)\<close> by (metis D_Q1(2, 3) strict_ticks_of_memI)
    from assms(3)[OF this] D_Q1(5)[THEN D_T]
    have \<open>v1 = [] \<or> hd v1 \<in> ev ` S\<close>
      by (cases v1) (auto simp add: initials_def_bis)
    from assms(1) D_Q1(2)[THEN is_processT3_TR_append] D_Q1(4)
    have \<open>set (?map u1) \<inter> ev ` S = {}\<close>
      by (auto simp add: events_of_def disjoint_iff)
        (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) split_list tF_Cons_iff tF_append_iff)
    from assms(8) consider (T_P2) u2 where \<open>t2 = ?map u2\<close> \<open>u2 \<in> \<T> P2\<close> \<open>tF u2\<close>
      | (T_Q2) u2 r2 v2 where \<open>t2 = ?map u2 @ v2\<close> \<open>u2 @ [\<checkmark>(r2)] \<in> \<T> P2\<close> \<open>u2 @ [\<checkmark>(r2)] \<notin> \<D> P2\<close> \<open>tF u2\<close> \<open>v2 \<in> \<T> (Q2 r2)\<close>
      | (D_P2) u2 v2 where \<open>t2 = ?map u2 @ v2\<close> \<open>u2 \<in> \<D> P2\<close> \<open>tF u2\<close> \<open>ftF v2\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis (no_types) T_imp_ftF is_processT9)
    thus \<open>t \<in> \<D> ?rhs\<close>
    proof cases
      case T_P2
      from D_Q1(4) assms(2) T_P2(2, 3)
      have \<open>set (?map u2) \<inter> ev ` S = {}\<close>
        by (auto simp add: events_of_def disjoint_iff)
          (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) split_list tF_Cons_iff tF_append_iff)
      from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendLR_waitingD
        [OF \<open>v1 = [] \<or> hd v1 \<in> ev ` S\<close> _ \<open>set (?map u1) \<inter> ev ` S = {}\<close> this,
          of \<open>[]\<close>, simplified, OF assms(6)[unfolded D_Q1(1) T_P2(1)]]
      obtain v where \<open>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((v1, []), S)\<close> by blast
      with \<open>v1 = [] \<or> hd v1 \<in> ev ` S\<close> have \<open>v1 = []\<close> by (cases v1) auto
      with D_Q1(5) have \<open>Q1 r1 = \<bottom>\<close> by (simp add: BOT_iff_Nil_D)
      with assms(3)[OF \<open>r1 \<in> \<^bold>\<checkmark>\<^bold>s(P1)\<close>] have False by auto
      thus \<open>t \<in> \<D> ?rhs\<close> ..
    next
      case T_Q2
      have \<open>r2 \<in> \<^bold>\<checkmark>\<^bold>s(P2)\<close> by (meson T_Q2(2,3) strict_ticks_of_memI)
      from assms(4)[OF this] T_Q2(5) have \<open>v2 = [] \<or> hd v2 \<in> ev ` S\<close>
        by (cases v2) (auto simp add: initials_def_bis)
      from assms(2) T_Q2(2)[THEN is_processT3_TR_append] T_Q2(4)
      have \<open>set (?map u2) \<inter> ev ` S = {}\<close>
        by (auto simp add: events_of_def disjoint_iff)
          (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) split_list tF_Cons_iff tF_append_iff)+
      from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendLR_waitingD
        [OF \<open>v1 = [] \<or> hd v1 \<in> ev ` S\<close> \<open>v2 = [] \<or> hd v2 \<in> ev ` S\<close>
          \<open>set (?map u1) \<inter> ev ` S = {}\<close> this assms(6)[unfolded D_Q1(1) T_Q2(1)]]
      obtain u v where * : \<open>t = u @ v\<close> \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map u1, ?map u2), S)\<close>
        \<open>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((v1, v2), S)\<close> by blast
      have \<open>tF u\<close> by (metis assms(5) "*"(1) tF_append_iff)
      then obtain u' :: \<open>('a, 'r' \<times> 's') trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>tF u'\<close> \<open>u = ?map u'\<close>
        using tF_map_ev_comp tF_map_ev_of_ev_eq_iff by blast
      from "$"[OF \<open>tF u'\<close> D_Q1(4) T_Q2(4) D_Q1(2)[THEN is_processT3_TR_append]
          T_Q2(2)[THEN is_processT3_TR_append] "*"(2)[unfolded \<open>u = ?map u'\<close>]]
      have \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1, u2), {})\<close> .
      hence \<open>u' @ [\<checkmark>((r1, r2))] setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1 @ [\<checkmark>(r1)], u2 @ [\<checkmark>(r2)]), {})\<close>
        by (auto intro: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tick simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj_def)
      with D_Q1(2) T_Q2(2) have \<open>u' @ [\<checkmark>((r1, r2))] \<in> \<T> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close>
        by (auto simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
      moreover have \<open>v \<in> \<D> (Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2)\<close>
        by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          (metis "*"(1, 3) D_Q1(5) T_Q2(5) append.right_neutral
            assms(5) tF_append_iff tF_imp_ftF)
      ultimately show \<open>t \<in> \<D> ?rhs\<close>
        using \<open>tF u'\<close> by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs "*"(1) \<open>u = ?map u'\<close>)
    next
      case D_P2
      have \<open>\<alpha>(P2) = UNIV\<close>
        by (metis D_P2(2) empty_iff events_of_is_strict_events_of_or_UNIV)
      with assms(2) have \<open>S = {}\<close> by simp
      with \<open>v1 = [] \<or> hd v1 \<in> ev ` S\<close> have \<open>v1 = []\<close> by simp
      with D_Q1(5) have \<open>Q1 r1 = \<bottom>\<close> by (simp add: BOT_iff_Nil_D)
      with assms(3)[OF \<open>r1 \<in> \<^bold>\<checkmark>\<^bold>s(P1)\<close>] have False by auto
      thus \<open>t \<in> \<D> ?rhs\<close> ..
    qed
  qed
qed




lemma indep_lhs_waiting_rhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_lemma2 :
  fixes P1 :: \<open>('a, 'r') process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and P2 :: \<open>('a, 's') process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assumes common_assms : \<open>\<alpha>(P1) \<inter> S = {}\<close> \<open>\<alpha>(P2) \<inter> S = {}\<close>
    \<open>\<And>r2. r2 \<in> \<^bold>\<checkmark>\<^bold>s(P2) \<Longrightarrow> (Q2 r2)\<^sup>0 \<subseteq> ev ` S\<close>
    \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((t1, t2), S)\<close>
    \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tj X1 S X2\<close>
    and t1_assms : \<open>t1 = map (ev \<circ> of_ev) u1\<close> \<open>(u1, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1) \<in> \<F> P1\<close> \<open>tF u1\<close>
    and t2_assms : \<open>t2 = map (ev \<circ> of_ev) u2 @ v2\<close> \<open>u2 @ [\<checkmark>(r2)] \<in> \<T> P2\<close> \<open>u2 @ [\<checkmark>(r2)] \<notin> \<D> P2\<close> \<open>(v2, X2) \<in> \<F> (Q2 r2)\<close>
  obtains u where \<open>tF u\<close> \<open>t = map (ev \<circ> of_ev) u\<close> \<open>(u, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close>
proof -
  let ?map = \<open>map (ev \<circ> of_ev)\<close>
  have * : \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((t1, t2), {})\<close>
    if \<open>tF t\<close> \<open>tF t1\<close> \<open>tF t2\<close> \<open>t1 \<in> \<T> P1\<close> \<open>t2 \<in> \<T> P2\<close>
      \<open>?map t setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((?map t1, ?map t2), S)\<close> for t t1 t2
  proof -
    from that(4, 5) \<open>\<alpha>(P1) \<inter> S = {}\<close> \<open>\<alpha>(P2) \<inter> S = {}\<close>
    have \<open>{a. ev a \<in> set t1 \<or> ev a \<in> set t2} \<subseteq> - S\<close>
      by (auto intro: events_of_memI)
    with that(2, 3)[THEN tF_map_ev_of_ev_eq_imp_ev_mem_iff]
    have \<open>{a. ev a \<in> set (?map t1) \<or> ev a \<in> set (?map t2)} \<subseteq> - S\<close> by blast
    from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_events_of
      [OF this, of _ _ S, unfolded Compl_disjoint, THEN iffD1, OF that(6)]
    have \<open>?map t setinterleaves\<^sub>\<checkmark>\<^bsub>tj\<^esub> ((?map t1, ?map t2), {})\<close> .
    thus \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((t1, t2), {})\<close>
      by (fact tF_imp_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_map_ev_of_ev_iff[OF that(1-3), THEN iffD1])
  qed
  from t2_assms(2, 3) have \<open>r2 \<in> \<^bold>\<checkmark>\<^bold>s(P2)\<close> by (auto intro: strict_ticks_of_memI)
  have \<open>v2 = []\<close>
  proof (rule ccontr)
    assume \<open>v2 \<noteq> []\<close>
    with t2_assms(4)[THEN F_T] common_assms(3)[OF \<open>r2 \<in> \<^bold>\<checkmark>\<^bold>s(P2)\<close>]
    obtain a v2' where \<open>a \<in> S\<close> \<open>v2 = ev a # v2'\<close>
      by (cases v2) (auto simp add: initials_def_bis)
    have \<open>ev a \<notin> set t1\<close>
      by (metis \<open>a \<in> S\<close> common_assms(1) t1_assms(1-3) F_T disjoint_iff
          events_of_memI tF_map_ev_of_ev_eq_imp_ev_mem_iff)
    moreover have \<open>ev a \<in> set t2\<close>
      by (simp add: t2_assms(1) \<open>v2 = ev a # v2'\<close>)
    ultimately have \<open>setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tj, t1, S, t2) = {}\<close>
      by (meson \<open>a \<in> S\<close> ev_notin_both_sets_imp_empty_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    with common_assms(4) show False by simp
  qed
  with common_assms(4) t2_assms(1) have \<open>tF t\<close>
    using setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tF_imp tF_map_ev_comp by force
  then obtain u :: \<open>('a, 'r' \<times> 's') trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>tF u\<close> \<open>t = map (ev \<circ> of_ev) u\<close>
    using tF_map_ev_comp tF_map_ev_of_ev_eq_iff by blast
  from "*"[OF this(1) t1_assms(3) t2_assms(2)[THEN append_T_imp_tF]
      t1_assms(2)[THEN F_T] t2_assms(2)[THEN is_processT3_TR_append]
      common_assms(4)[unfolded this(2) t1_assms(1) t2_assms(1) \<open>v2 = []\<close>, simplified]]
  have \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1, u2), {})\<close> by simp
  moreover from common_assms(1) t1_assms(2) have \<open>(u1, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1 \<union> ev ` S) \<in> \<F> P1\<close>
    by (auto intro!: is_processT5 dest: F_T simp add: events_of_def disjoint_iff in_set_conv_decomp)
  moreover have \<open>(u2, UNIV - {\<checkmark>(r2)}) \<in> \<F> P2\<close>
    by (simp add: t2_assms(2) is_processT6_TR)
  moreover have \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj
                                 (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1 \<union> ev ` S) {} (UNIV - {\<checkmark>(r2)})\<close>
    (is \<open>?lhs_ref \<subseteq> ?rhs_ref\<close>)
  proof (rule subsetI)
    show \<open>e \<in> ?lhs_ref \<Longrightarrow> e \<in> ?rhs_ref\<close> for e
      using common_assms(5)[THEN set_mp, of \<open>(ev \<circ> of_ev) e\<close>]
      by (cases e) (force simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def image_iff)+
  qed
  ultimately have \<open>(u, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close>
    by (auto simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs simp add: )
  with \<open>tF u\<close> \<open>t = map (ev \<circ> of_ev) u\<close> that show thesis by blast
qed



subsection \<open>The Theorem\<close>

theorem (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) indep_lhs_waiting_rhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P1 \<^bold>;\<^sub>\<checkmark> Q1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> P2 \<^bold>;\<^sub>\<checkmark> Q2 = (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2) \<^bold>;\<^sub>\<checkmark> (\<lambda>(r1, r2). Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2)\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>\<alpha>(P1) \<inter> S = {}\<close> \<open>\<alpha>(P2) \<inter> S = {}\<close>
  \<open>\<And>r1. r1 \<in> \<^bold>\<checkmark>\<^bold>s(P1) \<Longrightarrow> (Q1 r1)\<^sup>0 \<subseteq> ev ` S\<close>
  \<open>\<And>r2. r2 \<in> \<^bold>\<checkmark>\<^bold>s(P2) \<Longrightarrow> (Q2 r2)\<^sup>0 \<subseteq> ev ` S\<close>
for P1 :: \<open>('a, 'r') process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and P2 :: \<open>('a, 's') process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof -
  let ?map = \<open>map (ev \<circ> of_ev)\<close>

  have \<open>(P2 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P1) \<^bold>;\<^sub>\<checkmark> (\<lambda>(r1, r2). Q2 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l Q1 r2) =
        RenamingTick (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2) prod.swap \<^bold>;\<^sub>\<checkmark> (\<lambda>(r2, r1). Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2)\<close>
    by (simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual)
  also have \<open>\<dots> =  RenamingTick (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2) prod.swap \<^bold>;\<^sub>\<checkmark>
                   (\<lambda>g_r. case THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2) \<and> g_r = prod.swap r of (r1, r2) \<Rightarrow> Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2)\<close>
    by (auto intro!: mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq simp add: strict_ticks_of_RenamingTick)
      (metis (mono_tags, lifting) case_prod_conv swap_simp swap_swap the_equality)
  also have \<open>\<dots> = ?rhs\<close>
    by (subst inj_on_Renaming_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of prod.swap \<open>P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2\<close> _ id id, simplified])
      (auto intro: mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq)
  finally have $ : \<open>(P2 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P1) \<^bold>;\<^sub>\<checkmark> (\<lambda>(r1, r2). Q2 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l Q1 r2) = ?rhs\<close> .

  have $$ : \<open>?map t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map t1, ?map t2), S)\<close>
    if \<open>tF t1\<close> \<open>tF t2\<close> \<open>t1 \<in> \<T> P1\<close> \<open>t2 \<in> \<T> P2\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((t1, t2), {})\<close> for t t1 t2
  proof -
    from that(3, 4) \<open>\<alpha>(P1) \<inter> S = {}\<close> \<open>\<alpha>(P2) \<inter> S = {}\<close>
    have \<open>{a. ev a \<in> set t1 \<or> ev a \<in> set t2} \<subseteq> - S\<close>
      by (auto intro: events_of_memI)
    from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_events_of
      [OF this, of _ _ S, unfolded Compl_disjoint, THEN iffD2, OF that(5)]
    have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((t1, t2), S)\<close> .
    thus \<open>?map t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map t1, ?map t2), S)\<close>
      by (blast intro: tF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_map_ev_of_ev that(1, 2))
  qed

  have $$$ : \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((t1, t2), {})\<close>
    if \<open>tF t\<close> \<open>tF t1\<close> \<open>tF t2\<close> \<open>t1 \<in> \<T> P1\<close> \<open>t2 \<in> \<T> P2\<close>
      \<open>?map t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map t1, ?map t2), S)\<close> for t t1 t2
  proof -
    from that(4, 5) \<open>\<alpha>(P1) \<inter> S = {}\<close> \<open>\<alpha>(P2) \<inter> S = {}\<close>
    have \<open>{a. ev a \<in> set t1 \<or> ev a \<in> set t2} \<subseteq> - S\<close>
      by (auto intro: events_of_memI)
    with that(2, 3)[THEN tF_map_ev_of_ev_eq_imp_ev_mem_iff]
    have \<open>{a. ev a \<in> set (?map t1) \<or> ev a \<in> set (?map t2)} \<subseteq> - S\<close> by blast
    from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_restrictable_on_superset_events_of
      [OF this, of _ _ S, unfolded Compl_disjoint, THEN iffD1, OF that(6)]
    have \<open>?map t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map t1, ?map t2), {})\<close> .
    thus \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((t1, t2), {})\<close>
      by (fact tF_imp_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_map_ev_of_ev_iff[OF that(1-3), THEN iffD1])
  qed


  show \<open>?lhs = ?rhs\<close>
  proof (rule Process_eq_optimizedI)
    fix t assume \<open>t \<in> \<D> ?lhs\<close>
    then obtain u v t1 t2 where * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
      \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t1, t2), S)\<close>
      \<open>t1 \<in> \<D> (P1 \<^bold>;\<^sub>\<checkmark> Q1) \<and> t2 \<in> \<T> (P2 \<^bold>;\<^sub>\<checkmark> Q2) \<or> t1 \<in> \<T> (P1 \<^bold>;\<^sub>\<checkmark> Q1) \<and> t2 \<in> \<D> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    from "*"(5) show \<open>t \<in> \<D> ?rhs\<close>
    proof (elim disjE conjE)
      assume \<open>t1 \<in> \<D> (P1 \<^bold>;\<^sub>\<checkmark> Q1)\<close> \<open>t2 \<in> \<T> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close>
      from indep_lhs_waiting_rhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_lemma1
        [OF that "*"(2, 4) this Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_axioms]
      have \<open>u \<in> \<D> ?rhs\<close> .
      thus \<open>t \<in> \<D> ?rhs\<close> by (simp add: "*"(1-3) is_processT7)
    next
      assume \<open>t1 \<in> \<T> (P1 \<^bold>;\<^sub>\<checkmark> Q1)\<close> \<open>t2 \<in> \<D> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close>
      from indep_lhs_waiting_rhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_lemma1
        [OF that(2, 1, 4, 3) "*"(2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual
          [THEN iffD1, OF "*"(4)] this(2, 1) Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual.Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_axioms]
      have \<open>u \<in> \<D> ?rhs\<close> unfolding "$" .
      thus \<open>t \<in> \<D> ?rhs\<close> by (simp add: "*"(1-3) is_processT7)
    qed
  next
    fix t assume \<open>t \<in> \<D> ?rhs\<close>
    then consider (D_P) u v where \<open>t = ?map u @ v\<close> \<open>u \<in> \<D> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close> \<open>tF u\<close> \<open>ftF v\<close>
      | (D_Q) u v r1 r2 where \<open>t = ?map u @ v\<close> \<open>u @ [\<checkmark>((r1, r2))] \<in> \<T> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close>
        \<open>u @ [\<checkmark>((r1, r2))] \<notin> \<D> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close> \<open>tF u\<close> \<open>v \<in> \<D> (Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2)\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis D_imp_ftF is_processT9)
    thus \<open>t \<in> \<D> ?lhs\<close>
    proof cases
      case D_P
      from D_P(2) obtain w x w1 w2 where * : \<open>u = w @ x\<close> \<open>tF w\<close> \<open>ftF x\<close>
        \<open>w setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((w1, w2), {})\<close>
        \<open>w1 \<in> \<D> P1 \<and> w2 \<in> \<T> P2 \<or> w1 \<in> \<T> P1 \<and> w2 \<in> \<D> P2\<close>
        unfolding Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
      from tF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff[THEN iffD1, OF "*"(4)]
      have \<open>tF w1\<close> \<open>tF w2\<close> by (simp_all add: "*"(2))
      from "*"(5) have \<open>?map w \<in> \<D> ?lhs\<close>
      proof (elim disjE conjE)
        assume ** : \<open>w1 \<in> \<D> P1\<close> \<open>w2 \<in> \<T> P2\<close>
        have \<open>?map w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map w1, ?map w2), S)\<close>
          by (simp add: "$$" "*"(4) "**"(1, 2) D_T \<open>tF w1\<close> \<open>tF w2\<close>)
        moreover have \<open>?map w1 \<in> \<D> (P1 \<^bold>;\<^sub>\<checkmark> Q1)\<close>
          by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (use "**"(1) \<open>tF w1\<close> ftF_Nil in blast)
        moreover have \<open>?map w2 \<in> \<T> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close>
          by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis "**"(2) \<open>tF w2\<close>)
        ultimately show \<open>?map w \<in> \<D> ?lhs\<close>
          by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
            (meson ftF_Nil self_append_conv tF_map_ev_comp)
      next
        assume ** : \<open>w1 \<in> \<T> P1\<close> \<open>w2 \<in> \<D> P2\<close>
        have \<open>?map w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map w1, ?map w2), S)\<close>
          by (simp add: "$$" "*"(4) "**"(1, 2) D_T \<open>tF w1\<close> \<open>tF w2\<close>)
        moreover have \<open>?map w1 \<in> \<T> (P1 \<^bold>;\<^sub>\<checkmark> Q1)\<close>
          by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis "**"(1) \<open>tF w1\<close>)
        moreover have \<open>?map w2 \<in> \<D> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close>
          by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (use "**"(2) \<open>tF w2\<close> ftF_Nil in blast)
        ultimately show \<open>?map w \<in> \<D> ?lhs\<close>
          by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
            (meson ftF_Nil self_append_conv tF_map_ev_comp)
      qed
      thus \<open>t \<in> \<D> ?lhs\<close>
        by (simp add: D_P(1, 4) "*"(1) ftF_append is_processT7)
    next
      case D_Q
      from D_Q(2, 3) obtain u1 u2
        where * : \<open>u1 @ [\<checkmark>(r1)] \<in> \<T> P1\<close> \<open>u2 @ [\<checkmark>(r2)] \<in> \<T> P2\<close>
          \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1, u2), {})\<close>
        by (auto simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj_def elim: snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      from D_Q(5) obtain w x w1 w2 where ** : \<open>v = w @ x\<close> \<open>tF w\<close> \<open>ftF x\<close>
        \<open>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((w1, w2), S)\<close>
        \<open>w1 \<in> \<D> (Q1 r1) \<and> w2 \<in> \<T> (Q2 r2) \<or> w1 \<in> \<T> (Q1 r1) \<and> w2 \<in> \<D> (Q2 r2)\<close>
        by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
      have \<open>?map u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map u1, ?map u2), S)\<close>
        by (metis "$$" "*" append_T_imp_tF is_processT3_TR_append list.distinct(1))
      from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF this "**"(4)]
      have \<open>?map u @ w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map u1 @ w1, ?map u2 @ w2), S)\<close> .
      moreover from "*"(1, 2) "**"(5)
      have \<open>?map u1 @ w1 \<in> \<D> (P1 \<^bold>;\<^sub>\<checkmark> Q1) \<and> ?map u2 @ w2 \<in> \<T> (P2 \<^bold>;\<^sub>\<checkmark> Q2) \<or>
            ?map u1 @ w1 \<in> \<T> (P1 \<^bold>;\<^sub>\<checkmark> Q1) \<and> ?map u2 @ w2 \<in> \<D> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis append_T_imp_tF list.discI)
      ultimately have \<open>?map u @ w \<in> \<D> ?lhs\<close>
        by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          (metis "**"(2) append.right_neutral ftF_Nil
            tF_append_iff tF_map_ev_comp)
      with D_Q(1) "**"(1-3) is_processT7 show \<open>t \<in> \<D> ?lhs\<close> by force
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    then obtain t1 t2 X1 X2
      where * : \<open>(t1, X1) \<in> \<F> (P1 \<^bold>;\<^sub>\<checkmark> Q1)\<close> \<open>(t2, X2) \<in> \<F> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t1, t2), S)\<close> \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X1 S X2\<close>
      by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
    with \<open>t \<notin> \<D> ?lhs\<close> have \<open>t1 \<notin> \<D> (P1 \<^bold>;\<^sub>\<checkmark> Q1)\<close> \<open>t2 \<notin> \<D> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close>
      by (auto simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k' dest!: F_T intro: ftF_Nil)
    note * = "*"(1) this(1) "*"(2) this(2) "*"(3, 4)
    from "*"(1, 2) consider (F_P1) u1 where \<open>t1 = ?map u1\<close> \<open>(u1, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1) \<in> \<F> P1\<close> \<open>u1 \<notin> \<D> P1\<close> \<open>tF u1\<close>
      | (F_Q1) u1 r1 v1 where \<open>t1 = ?map u1 @ v1\<close> \<open>u1 @ [\<checkmark>(r1)] \<in> \<T> P1\<close> \<open>u1 @ [\<checkmark>(r1)] \<notin> \<D> P1\<close> \<open>tF u1\<close> \<open>(v1, X1) \<in> \<F> (Q1 r1)\<close>
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis F_imp_ftF is_processT9)
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
    proof cases
      case F_P1
      from "*"(3, 4) consider (F_P2) u2 where \<open>t2 = ?map u2\<close> \<open>(u2, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2) \<in> \<F> P2\<close> \<open>u2 \<notin> \<D> P2\<close> \<open>tF u2\<close>
        | (F_Q2) u2 r2 v2 where \<open>t2 = ?map u2 @ v2\<close> \<open>u2 @ [\<checkmark>(r2)] \<in> \<T> P2\<close> \<open>u2 @ [\<checkmark>(r2)] \<notin> \<D> P2\<close> \<open>tF u2\<close> \<open>(v2, X2) \<in> \<F> (Q2 r2)\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis F_imp_ftF is_processT9)
      thus \<open>(t, X) \<in> \<F> ?rhs\<close>
      proof cases
        case F_P2
        from "*"(5) F_P2(1) have \<open>tF t\<close>
          using setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tF_imp tF_map_ev_comp by blast
        then obtain u :: \<open>('a, 'r' \<times> 's') trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>tF u\<close> \<open>t = ?map u\<close>
          using tF_map_ev_comp tF_map_ev_of_ev_eq_iff by blast
        from "$$$"[OF this(1) F_P1(4) F_P2(4) F_P1(2)[THEN F_T] F_P2(2)[THEN F_T]
            "*"(5)[unfolded this(2) F_P1(1) F_P2(1)]]
        have \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1, u2), {})\<close> .
        moreover from that(1) F_P1(2) have \<open>(u1, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1 \<union> ev ` S) \<in> \<F> P1\<close>
          by (auto intro!: is_processT5 dest: F_T simp add: events_of_def disjoint_iff in_set_conv_decomp)
        moreover from that(2) F_P2(2) have \<open>(u2, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2 \<union> ev ` S) \<in> \<F> P2\<close>
          by (auto intro!: is_processT5 dest: F_T simp add: events_of_def disjoint_iff in_set_conv_decomp)
        moreover have \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj)
                                       (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1 \<union> ev ` S) {} (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2 \<union> ev ` S)\<close>
          (is \<open>?lhs_ref \<subseteq> ?rhs_ref\<close>)
        proof (rule subsetI)
          show \<open>e \<in> ?lhs_ref \<Longrightarrow> e \<in> ?rhs_ref\<close> for e
            using "*"(6)[THEN set_mp, of \<open>(ev \<circ> of_ev) e\<close>]
            by (cases e) (force simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def image_iff)+
        qed
        ultimately have \<open>(u, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close>
          by (auto simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
        with \<open>tF u\<close> \<open>t = ?map u\<close> show \<open>(t, X) \<in> \<F> ?rhs\<close>
          by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
      next
        case F_Q2
        from indep_lhs_waiting_rhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_lemma2
          [of P1 S P2 Q2, OF that(1, 2, 4) "*"(5, 6) F_P1(1, 2, 4) F_Q2(1-3, 5)]
        obtain u where \<open>tF u\<close> \<open>t = ?map u\<close> \<open>(u, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close> by blast
        thus \<open>(t, X) \<in> \<F> ?rhs\<close> by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
      qed
    next
      case F_Q1
      from "*"(3, 4) consider (F_P2) u2 where \<open>t2 = ?map u2\<close> \<open>(u2, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2) \<in> \<F> P2\<close> \<open>u2 \<notin> \<D> P2\<close> \<open>tF u2\<close>
        | (F_Q2) u2 r2 v2 where \<open>t2 = ?map u2 @ v2\<close> \<open>u2 @ [\<checkmark>(r2)] \<in> \<T> P2\<close> \<open>u2 @ [\<checkmark>(r2)] \<notin> \<D> P2\<close> \<open>tF u2\<close> \<open>(v2, X2) \<in> \<F> (Q2 r2)\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis F_imp_ftF is_processT9)
      thus \<open>(t, X) \<in> \<F> ?rhs\<close>
      proof cases
        case F_P2
        have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<lambda>s r. r \<otimes>\<checkmark> s) X2 S X1\<close>
          by (metis "*"(6) super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual)
        from indep_lhs_waiting_rhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_lemma2
          [of P2 S P1 Q1, OF that(2, 1, 3) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual[THEN iffD1, OF "*"(5)]
            this F_P2(1, 2, 4) F_Q1(1, 2, 3, 5)]
        obtain u where \<open>tF u\<close> \<open>t = ?map u\<close> \<open>(u, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (P2 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P1)\<close> by blast
        hence \<open>(t, X) \<in> \<F> ((P2 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P1) \<^bold>;\<^sub>\<checkmark> (\<lambda>(r1, r2). Q2 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l Q1 r2))\<close>
          by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
        with "$" show \<open>(t, X) \<in> \<F> ?rhs\<close> by simp
      next
        case F_Q2
        from F_Q1(2, 3) F_Q2(2, 3) have \<open>r1 \<in> \<^bold>\<checkmark>\<^bold>s(P1)\<close> \<open>r2 \<in> \<^bold>\<checkmark>\<^bold>s(P2)\<close>
          by (simp_all add: strict_ticks_of_memI)
        from "*"(5)[unfolded F_Q1(1) F_Q2(1)]
        consider (waitL) t' t'' t''' u1' u1'' v2' v2''
          where \<open>t = t' @ t'' @ t'''\<close> \<open>u1 = u1' @ u1''\<close> \<open>v2 = v2' @ v2''\<close>
            \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map u1', ?map u2), S)\<close>
            \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map u1'', v2'), S)\<close>
            \<open>t''' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((v1, v2''), S)\<close>
          | (waitR) t' t'' t''' v1' v1'' u2' u2''
          where \<open>t = t' @ t'' @ t'''\<close> \<open>v1 = v1' @ v1''\<close> \<open>u2 = u2' @ u2''\<close>
            \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map u1, ?map u2'), S)\<close>
            \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((v1', ?map u2''), S)\<close>
            \<open>t''' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((v1'', v2), S)\<close>
          by (auto simp add: append_eq_append_conv2 map_eq_append_conv
              dest!: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendR)
            (use waitL in blast, use waitR in blast)
        thus \<open>(t, X) \<in> \<F> ?rhs\<close>
        proof cases
          case waitL
          have \<open>tF t'\<close> using setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tF_imp tF_map_ev_comp waitL(4) by blast
          then obtain t'''' :: \<open>('a, 'r' \<times> 's') trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>tF t''''\<close> \<open>t' = ?map t''''\<close>
            using tF_map_ev_comp tF_map_ev_of_ev_eq_iff by blast
          have \<open>u1' \<in> \<T> P1\<close> using F_Q1(2) is_processT3_TR_append waitL(2) by blast
          have \<open>tF u1'\<close> by (metis F_Q1(4) waitL(2) tF_append_iff)
          from "$$$"[OF \<open>tF t''''\<close> \<open>tF u1'\<close> F_Q2(4) \<open>u1' \<in> \<T> P1\<close>
              F_Q2(2)[THEN is_processT3_TR_append] waitL(4)[unfolded \<open>t' = ?map t''''\<close>]]
          have ** : \<open>t'''' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1', u2), {})\<close> .
          from that(1) F_Q1(2)[THEN is_processT3_TR_append] F_Q1(4)
          have \<open>set (?map u1'') \<subseteq> ev ` (- S)\<close>
            by (auto simp add: waitL(2) disjoint_iff image_iff events_of_def)
              (metis Un_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) set_append split_list
                tF_Cons_iff tF_append_iff)
          from that(4)[OF \<open>r2 \<in> \<^bold>\<checkmark>\<^bold>s(P2)\<close>] F_Q2(5)[THEN F_T]
          have \<open>v2' = [] \<or> hd v2' \<in> ev ` S\<close>
            by (cases v2') (auto simp add: waitL(3) initials_def_bis)
          from this waitL(3) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL_waitingD
            [OF this \<open>set (?map u1'') \<subseteq> ev ` (- S)\<close>, of _ _ \<open>[]\<close>, simplified, OF waitL(5)]
          have *** : \<open>t'' = ?map u1'' \<and> v2' = [] \<and> v2'' = v2\<close>
            by (cases v2') (simp_all add: setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps image_iff
                split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split_asm if_split_asm)
          have \<open>tF (t'''' @ ?map u1'')\<close> by (simp add: \<open>tF t''''\<close>)
          have \<open>t'''' @ ?map u1'' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1, u2), {})\<close>
            by (unfold waitL(2), rule tF_disjoint_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append_tailL)
              (metis F_Q1(4) waitL(2) tF_append_iff, simp, fact "**")
          hence \<open>(t'''' @ ?map u1'') @ [\<checkmark>((r1, r2))] setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1 @ [\<checkmark>(r1)], u2 @ [\<checkmark>(r2)]), {})\<close>
            by (rule setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tick) (simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj_def)
          with F_Q1(2) F_Q2(2) have \<open>(t'''' @ ?map u1'') @ [\<checkmark>((r1, r2))] \<in> \<T> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close>
            by (auto simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          moreover have \<open>t = ?map (t'''' @ ?map u1'') @ t'''\<close>
            by (simp add: waitL(1) \<open>t' = ?map t''''\<close> "***")
          moreover from F_Q1(5) F_Q2(5) waitL(6) "*"(6)
          have \<open>(t''', X) \<in> \<F> (Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2)\<close>
            by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs "***")
          ultimately show \<open>(t, X) \<in> \<F> ?rhs\<close>
            by (simp (no_asm) add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (use \<open>tF (t'''' @ ?map u1'')\<close> in blast)
        next
          case waitR
          have \<open>tF t'\<close> using setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tF_imp tF_map_ev_comp waitR(4) by blast
          then obtain t'''' :: \<open>('a, 'r' \<times> 's') trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>tF t''''\<close> \<open>t' = ?map t''''\<close>
            using tF_map_ev_comp tF_map_ev_of_ev_eq_iff by blast
          have \<open>u2' \<in> \<T> P2\<close> using F_Q2(2) is_processT3_TR_append waitR(3) by blast
          have \<open>tF u2'\<close> by (metis F_Q2(4) waitR(3) tF_append_iff)
          from "$$$"[OF \<open>tF t''''\<close> F_Q1(4) \<open>tF u2'\<close> F_Q1(2)[THEN is_processT3_TR_append]
              \<open>u2' \<in> \<T> P2\<close> waitR(4)[unfolded \<open>t' = ?map t''''\<close>]]
          have ** : \<open>t'''' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1, u2'), {})\<close> .
          from that(2) F_Q2(2)[THEN is_processT3_TR_append] F_Q2(4)
          have \<open>set (?map u2'') \<subseteq> ev ` (- S)\<close>
            by (auto simp add: waitR(3) disjoint_iff image_iff events_of_def)
              (metis Un_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) set_append split_list
                tF_Cons_iff tF_append_iff)
          from that(3)[OF \<open>r1 \<in> \<^bold>\<checkmark>\<^bold>s(P1)\<close>] F_Q1(5)[THEN F_T]
          have \<open>v1' = [] \<or> hd v1' \<in> ev ` S\<close>
            by (cases v1') (auto simp add: waitR(2) initials_def_bis)
          from this waitR(2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendR_waitingD
            [OF this \<open>set (?map u2'') \<subseteq> ev ` (- S)\<close>, of _ _ \<open>[]\<close>, simplified, OF waitR(5)]
          have *** : \<open>t'' = ?map u2'' \<and> v1' = [] \<and> v1'' = v1\<close>
            by (cases v1') (simp_all add: setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps image_iff
                split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split_asm if_split_asm)
          have \<open>tF (t'''' @ ?map u2'')\<close> by (simp add: \<open>tF t''''\<close>)
          have \<open>t'''' @ ?map u2'' setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1, u2), {})\<close>
            by (unfold waitR(3), rule tF_disjoint_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append_tailR)
              (metis F_Q2(4) waitR(3) tF_append_iff, simp, fact "**")
          hence \<open>(t'''' @ ?map u2'') @ [\<checkmark>((r1, r2))] setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1 @ [\<checkmark>(r1)], u2 @ [\<checkmark>(r2)]), {})\<close>
            by (rule setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tick) (simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj_def)
          with F_Q1(2) F_Q2(2) have \<open>(t'''' @ ?map u2'') @ [\<checkmark>((r1, r2))] \<in> \<T> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close>
            by (auto simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          moreover have \<open>t = ?map (t'''' @ ?map u2'') @ t'''\<close>
            by (simp add: waitR(1) \<open>t' = ?map t''''\<close> "***")
          moreover from F_Q1(5) F_Q2(5) waitR(6) "*"(6)
          have \<open>(t''', X) \<in> \<F> (Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2)\<close>
            by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs "***")
          ultimately show \<open>(t, X) \<in> \<F> ?rhs\<close>
            by (simp (no_asm) add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (use \<open>tF (t'''' @ ?map u2'')\<close> in blast)
        qed
      qed
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    from this(1, 2) consider (F_1) u where \<open>t = ?map u\<close> \<open>(u, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close>
      \<open>u \<notin> \<D> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close> \<open>tF u\<close>
    | (F_2) u r1 r2 v where \<open>t = ?map u @ v\<close> \<open>u @ [\<checkmark>((r1, r2))] \<in> \<T> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close>
      \<open>u @ [\<checkmark>((r1, r2))] \<notin> \<D> (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2)\<close>
      \<open>tF u\<close> \<open>(v, X) \<in> \<F> (Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2)\<close> \<open>v \<notin> \<D> (Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2)\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
        (metis (no_types) F_imp_ftF append_Nil2 ftF_Nil is_processT9)
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      case F_1
      have \<open>tF t\<close> by (simp add: F_1(1))
      from F_1(2, 3) obtain u1 u2 X1 X2
        where * : \<open>(u1, X1) \<in> \<F> P1\<close> \<open>u1 \<notin> \<D> P1\<close> \<open>(u2, X2) \<in> \<F> P2\<close> \<open>u2 \<notin> \<D> P2\<close>
          \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1, u2), {})\<close>
          \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj X1 {} X2\<close>
        by (simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          (metis (no_types, lifting) F_1(4) F_T append_self_conv ftF_Nil)
      from F_1(4) tF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff[OF "*"(5)] have \<open>tF u1\<close> \<open>tF u2\<close> by simp_all
      have ** : \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map u1, ?map u2), S)\<close>
        by (unfold F_1(1)) (fact "$$"[OF \<open>tF u1\<close> \<open>tF u2\<close> "*"(1, 3)[THEN F_T] "*"(5)])
      have \<open>t @ [\<checkmark>(r_s)] \<notin> \<T> ?lhs\<close> for r_s
      proof (rule notI)
        assume \<open>t @ [\<checkmark>(r_s)] \<in> \<T> ?lhs\<close>
        from \<open>t \<notin> \<D> ?lhs\<close> have \<open>t @ [\<checkmark>(r_s)] \<notin> \<D> ?lhs\<close> by (meson is_processT9)
        with \<open>tF t\<close> \<open>t @ [\<checkmark>(r_s)] \<in> \<T> ?lhs\<close> obtain u1' u2' r1 r2
          where "\<euro>" : \<open>r1 \<otimes>\<checkmark> r2 = Some r_s\<close> \<open>u1' @ [\<checkmark>(r1)] \<in> \<T> (P1 \<^bold>;\<^sub>\<checkmark> Q1)\<close>
            \<open>u1' @ [\<checkmark>(r1)] \<notin> \<D> (P1 \<^bold>;\<^sub>\<checkmark> Q1)\<close> \<open>u2' @ [\<checkmark>(r2)] \<in> \<T> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close>
            \<open>u2' @ [\<checkmark>(r2)] \<notin> \<D> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((u1', u2'), S)\<close>
          by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs elim!: snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
            (metis (no_types, lifting) ftF_append_iff
              ftF_charn is_processT3_TR_append is_processT9)
        from "\<euro>"(2, 3) obtain u1'' r1' v1'
          where "\<euro>\<euro>" : \<open>u1' @ [\<checkmark>(r1)] = ?map u1'' @ v1'\<close> \<open>u1'' @ [\<checkmark>(r1')] \<in> \<T> P1\<close>
            \<open>u1'' @ [\<checkmark>(r1')] \<notin> \<D> P1\<close> \<open>tF u1''\<close> \<open>v1' \<in> \<T> (Q1 r1')\<close>
          by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs append_eq_map_conv)
            (metis T_imp_ftF is_processT9)
        from "\<euro>\<euro>"(2, 3) have \<open>r1' \<in> \<^bold>\<checkmark>\<^bold>s(P1)\<close> by (metis strict_ticks_of_memI)
        from that(1, 2) "*"(1, 3)[THEN F_T] setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_empty[OF "*"(5)]
        have \<open>set u \<inter> ev ` S = {}\<close> unfolding events_of_def by blast
        with tF_map_ev_of_ev_eq_imp_ev_mem_iff[OF F_1(4, 1)]
        have \<open>set t \<inter> ev ` S = {}\<close> by blast
        with setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev_in_set_iff[OF "\<euro>"(6)]
        have \<open>set u1' \<inter> ev ` S = {}\<close> by blast
        moreover from that(3)[OF \<open>r1' \<in> \<^bold>\<checkmark>\<^bold>s(P1)\<close>] "\<euro>\<euro>"(5)
        have \<open>v1' = [] \<or> hd v1' \<in> ev ` S\<close>
          by (metis in_mono initials_memI list.sel(1) neq_Nil_conv)
        moreover from that(1) "\<euro>\<euro>"(2)[THEN is_processT3_TR_append] "\<euro>\<euro>"(4)
        have \<open>set (?map u1'') \<inter> ev ` S = {}\<close>
          by (auto simp add: events_of_def disjoint_iff)
            (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) split_list_first tF_Cons_iff tF_append_iff)
        ultimately show False
          using "\<euro>\<euro>"(1) by (cases v1')
            (auto simp add: append_eq_map_conv image_iff
              append_eq_append_conv2 append_eq_Cons_conv Cons_eq_append_conv)
      qed
      moreover have \<open>(t, X \<inter> range ev) \<in> \<F> ?lhs\<close>
      proof -
        define X1' :: \<open>('a, 'r) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>X1' \<equiv> {ev a| a. ev a \<in> X1}\<close>
        define X2' :: \<open>('a, 's) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>X2' \<equiv> {ev a| a. ev a \<in> X2}\<close>
        have "\<euro>" : \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1' = X1 \<union> range tick\<close>
        proof (rule set_eqI)
          show \<open>e \<in> ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1' \<longleftrightarrow> e \<in> X1 \<union> range tick\<close> for e
            by (cases e) (force simp add: X1'_def ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def image_iff)+
        qed
        have "\<euro>\<euro>" : \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2' = X2 \<union> range tick\<close>
        proof (rule set_eqI)
          show \<open>e \<in> ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2' \<longleftrightarrow> e \<in> X2 \<union> range tick\<close> for e
            by (cases e) (force simp add: X2'_def ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def image_iff)+
        qed
        from "*"(6)[THEN set_mp, of \<open>\<checkmark>(_)\<close>]
        have \<open>range tick \<subseteq> X1 \<or> range tick \<subseteq> X2\<close>
          by (auto simp add: ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj_def)
        hence \<open>X1 = ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1' \<or> X2 = ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2'\<close>
          unfolding "\<euro>" "\<euro>\<euro>" by blast
        with "*"(1, 3) consider \<open>(u1, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1') \<in> \<F> P1\<close> \<open>(u2, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2') \<in> \<F> P2\<close>
          | \<open>(u1, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1') \<notin> \<F> P1\<close> \<open>(u2, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2') \<in> \<F> P2\<close>
          | \<open>(u1, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1') \<in> \<F> P1\<close> \<open>(u2, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2') \<notin> \<F> P2\<close> by blast
        thus \<open>(t, X \<inter> range ev) \<in> \<F> ?lhs\<close>
        proof cases
          assume \<open>(u1, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1') \<in> \<F> P1\<close> \<open>(u2, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2') \<in> \<F> P2\<close>
          with \<open>tF u1\<close> \<open>tF u2\<close>
          have \<open>(?map u1, X1') \<in> \<F> (P1 \<^bold>;\<^sub>\<checkmark> Q1)\<close> \<open>(?map u2, X2') \<in> \<F> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close>
            by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          moreover have \<open>X \<inter> range ev \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X1' S X2'\<close>
          proof (rule subsetI)
            show \<open>e \<in> X \<inter> range ev \<Longrightarrow> e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X1' S X2'\<close> for e
              using set_mp[OF "*"(6), of \<open>(ev \<circ> of_ev) e\<close>]
              by (cases e) (force simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def X1'_def X2'_def)+
          qed
          ultimately show \<open>(t, X \<inter> range ev) \<in> \<F> ?lhs\<close>
            using "**" by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
        next
          assume \<open>(u1, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1') \<notin> \<F> P1\<close> \<open>(u2, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2') \<in> \<F> P2\<close>
          from is_processT5_S7'[OF "*"(1) this(1)[unfolded "\<euro>"]]
          obtain r1 where \<open>u1 @ [\<checkmark>(r1)] \<in> \<T> P1\<close> by blast
          have \<open>r1 \<in> \<^bold>\<checkmark>\<^bold>s(P1)\<close>
            by (meson "*"(2) \<open>u1 @ [\<checkmark>(r1)] \<in> \<T> P1\<close> is_processT9 strict_ticks_of_memI)
          with add_Compl_initials_in_R[of \<open>{}\<close> \<open>Q1 r1\<close>]
          have \<open>- ev ` S \<in> \<R> (Q1 r1)\<close>
            by (simp add: Refusals_iff is_processT1) (meson compl_mono is_processT4 that(3))
          with \<open>tF u1\<close> \<open>tF u2\<close> \<open>u1 @ [\<checkmark>(r1)] \<in> \<T> P1\<close> \<open>(u2, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2') \<in> \<F> P2\<close>
          have \<open>(?map u1, - ev ` S) \<in> \<F> (P1 \<^bold>;\<^sub>\<checkmark> Q1)\<close> \<open>(?map u2, X2') \<in> \<F> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close>
            by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Refusals_def_bis)
          moreover have \<open>X \<inter> range ev \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (- ev ` S) S X2'\<close>
          proof (rule subsetI)
            show \<open>e \<in> X \<inter> range ev \<Longrightarrow> e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (- ev ` S) S X2'\<close> for e
              using set_mp[OF "*"(6), of \<open>(ev \<circ> of_ev) e\<close>]
              by (cases e) (force simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def X1'_def X2'_def)+
          qed
          ultimately show \<open>(t, X \<inter> range ev) \<in> \<F> ?lhs\<close>
            using "**" by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
        next
          fix r2 assume \<open>(u1, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1') \<in> \<F> P1\<close> \<open>(u2, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X2') \<notin> \<F> P2\<close>
          from is_processT5_S7'[OF "*"(3) this(2)[unfolded "\<euro>\<euro>"]]
          obtain r2 where \<open>u2 @ [\<checkmark>(r2)] \<in> \<T> P2\<close> by blast
          have \<open>r2 \<in> \<^bold>\<checkmark>\<^bold>s(P2)\<close>
            by (meson "*"(4) \<open>u2 @ [\<checkmark>(r2)] \<in> \<T> P2\<close> is_processT9 strict_ticks_of_memI)
          with add_Compl_initials_in_R[of \<open>{}\<close> \<open>Q2 r2\<close>]
          have \<open>- ev ` S \<in> \<R> (Q2 r2)\<close>
            by (simp add: Refusals_iff is_processT1) (meson compl_mono is_processT4 that(4))
          with \<open>tF u1\<close> \<open>tF u2\<close> \<open>(u1, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X1') \<in> \<F> P1\<close> \<open>u2 @ [\<checkmark>(r2)] \<in> \<T> P2\<close>
          have \<open>(?map u1, X1') \<in> \<F> (P1 \<^bold>;\<^sub>\<checkmark> Q1)\<close> \<open>(?map u2, - ev ` S) \<in> \<F> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close>
            by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Refusals_def_bis)
          moreover have \<open>X \<inter> range ev \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X1' S (- ev ` S)\<close>
          proof (rule subsetI)
            show \<open>e \<in> X \<inter> range ev \<Longrightarrow> e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X1' S (- ev ` S)\<close> for e
              using set_mp[OF "*"(6), of \<open>(ev \<circ> of_ev) e\<close>]
              by (cases e) (force simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def X1'_def X2'_def)+
          qed
          ultimately show \<open>(t, X \<inter> range ev) \<in> \<F> ?lhs\<close>
            using "**" by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
        qed
      qed
      ultimately have \<open>(t, X \<inter> range ev \<union> range tick) \<in> \<F> ?lhs\<close>
        by (auto intro: is_processT5 F_T)
      moreover have \<open>X \<subseteq> X \<inter> range ev \<union> range tick\<close>
        by (simp add: subset_iff image_iff) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
      ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close> by (fact is_processT4)
    next
      case F_2
      from F_2(2, 3) obtain u1 u2
        where * : \<open>u1 @ [\<checkmark>(r1)] \<in> \<T> P1\<close> \<open>u2 @ [\<checkmark>(r2)] \<in> \<T> P2\<close>
          \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj\<^esub> ((u1, u2), {})\<close>
        by (auto simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_tj_def
            elim: snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      from F_2(5, 6) obtain v1 v2 X1 X2
        where ** : \<open>(v1, X1) \<in> \<F> (Q1 r1)\<close> \<open>(v2, X2) \<in> \<F> (Q2 r2)\<close>
          \<open>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((v1, v2), S)\<close>
          \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X1 S X2\<close>
        unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
      from F_2(4) tF_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff[OF "*"(3)] have \<open>tF u1\<close> \<open>tF u2\<close> by simp_all
      have \<open>?map u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map u1, ?map u2), S)\<close>
        by (fact "$$"[OF \<open>tF u1\<close> \<open>tF u2\<close> "*"(1, 2)[THEN is_processT3_TR_append] "*"(3)])
      with "**"(3) have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((?map u1 @ v1, ?map u2 @ v2), S)\<close>
        by (auto simp add: F_2(1) intro: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      moreover from "*"(1) "**"(1) \<open>tF u1\<close>
      have \<open>(?map u1 @ v1, X1) \<in> \<F> (P1 \<^bold>;\<^sub>\<checkmark> Q1)\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
      moreover from "*"(2) "**"(2) \<open>tF u2\<close>
      have \<open>(?map u2 @ v2, X2) \<in> \<F> (P2 \<^bold>;\<^sub>\<checkmark> Q2)\<close> by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
      ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close>
        using "**"(4) by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
    qed
  qed
qed


hide_fact indep_lhs_waiting_rhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_lemma1
  indep_lhs_waiting_rhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_lemma2




corollary (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) indep_lhs_waiting_rhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_through_Inter\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t :
  \<open>P1 \<^bold>;\<^sub>\<checkmark> Q1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> P2 \<^bold>;\<^sub>\<checkmark> Q2 = (P1 |||\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t P2) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. Q1 (hd R) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 (tl R))\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>\<alpha>(P1) \<inter> S = {}\<close> \<open>\<alpha>(P2) \<inter> S = {}\<close>
  \<open>\<And>r1. r1 \<in> \<^bold>\<checkmark>\<^bold>s(P1) \<Longrightarrow> (Q1 r1)\<^sup>0 \<subseteq> ev ` S\<close>
  \<open>\<And>r2. r2 \<in> \<^bold>\<checkmark>\<^bold>s(P2) \<Longrightarrow> (Q2 r2)\<^sup>0 \<subseteq> ev ` S\<close>
proof -
  from indep_lhs_waiting_rhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF that]
  have \<open>P1 \<^bold>;\<^sub>\<checkmark> Q1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> P2 \<^bold>;\<^sub>\<checkmark> Q2 = (P1 |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2) \<^bold>;\<^sub>\<checkmark> (\<lambda>(r1, r2). Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2)\<close> .
  also have \<open>\<dots> = RenamingTick (P1 \<lbrakk>{}\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2) (\<lambda>(x, y). x # y) \<^bold>;\<^sub>\<checkmark>
                  (\<lambda>R. case THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P1 \<lbrakk>{}\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2) \<and> R = (case r of (r1, r2) \<Rightarrow> r1 # r2) of (r1, r2) \<Rightarrow> Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2)\<close>
    by (auto intro: inj_on_Renaming_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of \<open>\<lambda>(r1, r2). r1 # r2\<close> _ _ id id, simplified] inj_onI)
  also have \<open>\<dots> = (P1 |||\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t P2) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. Q1 (hd R) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 (tl R))\<close>
  proof (unfold Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_to_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t, rule mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq[OF refl])
    fix R assume \<open>R \<in> \<^bold>\<checkmark>\<^bold>s(P1 |||\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t P2)\<close>
    with Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.strict_ticks_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset[of P1 \<open>{}\<close> P2]
    obtain r R' where \<open>R = r # R'\<close> by (auto simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_tj_def)
    with \<open>R \<in> \<^bold>\<checkmark>\<^bold>s(P1 |||\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t P2)\<close>
    have \<open>(THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P1 \<lbrakk>{}\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2) \<and> R = (case r of (r1, r2) \<Rightarrow> r1 # r2)) = (r, R')\<close>
      by (auto simp flip: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_to_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t simp add: strict_ticks_of_RenamingTick)
    thus \<open>(case THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P1 \<lbrakk>{}\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P2) \<and> R = (case r of (r1, r2) \<Rightarrow> r1 # r2)
                of (r1, r2) \<Rightarrow> Q1 r1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 r2) =
          Q1 (hd R) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q2 (tl R)\<close> by (simp add: \<open>R = r # R'\<close>)
  qed
  finally show ?thesis .
qed



theorem indep_lhs_waiting_rhs_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. (P l \<^bold>;\<^sub>\<checkmark> Q l) = (\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ L. P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip L R. Q l r)\<close>
  if \<open>\<And>l. l \<in> set L \<Longrightarrow> \<alpha>(P l) \<inter> S = {}\<close>
    and \<open>\<And>l r. l \<in> set L \<Longrightarrow> r \<in> \<^bold>\<checkmark>\<^bold>s(P l) \<Longrightarrow> (Q l r)\<^sup>0 \<subseteq> ev ` S\<close>
proof -
  from that have
    \<open>(R \<in> \<^bold>\<checkmark>\<^bold>s(\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ L. P l) \<longrightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip L R. Q l r)\<^sup>0 \<subseteq> ev ` S) \<and>
   \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. (P l \<^bold>;\<^sub>\<checkmark> Q l) = (\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ L. P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip L R. Q l r)\<close> for R
  proof (induct L arbitrary: R rule: induct_list012)
    case 1 show ?case by simp
  next
    case (2 l0)
    show ?case
    proof (intro conjI impI)
      show \<open>R \<in> \<^bold>\<checkmark>\<^bold>s(\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ [l0]. P l) \<Longrightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip [l0] R. Q l r)\<^sup>0 \<subseteq> ev ` S\<close>
        by (auto simp add: strict_ticks_of_RenamingTick initials_Renaming
            dest!: "2.prems"(2)[of l0, simplified] split: if_split_asm)+
    next
      have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ [l0]. (P l \<^bold>;\<^sub>\<checkmark> Q l) = RenamingTick (P l0 \<^bold>;\<^sub>\<checkmark> Q l0) (\<lambda>r. [r])\<close> by simp
      also have \<open>\<dots> = RenamingTick (P l0) (\<lambda>r. [r]) \<^bold>;\<^sub>\<checkmark> (\<lambda>g_r. RenamingTick (Q l0 (THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P l0) \<and> g_r = [r])) (\<lambda>r. [r]))\<close>
        by (auto intro: inj_on_Renaming_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of \<open>\<lambda>r. [r]\<close>] inj_onI)
      also have \<open>\<dots> = (\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ [l0]. P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip [l0] R. Q l r)\<close>
        by (auto intro!: mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq simp add: strict_ticks_of_RenamingTick the_equality)
      finally show \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ [l0]. (P l \<^bold>;\<^sub>\<checkmark> Q l) = \<dots>\<close> by simp
    qed
  next
    case (3 l0 l1 L)
    show ?case
    proof (intro conjI impI)
      fix R assume \<open>R \<in> \<^bold>\<checkmark>\<^bold>s(\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). P l)\<close>
      from is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[THEN is_ticks_lengthD, OF this]
      obtain r0 r1 R' where \<open>R = r0 # r1 # R'\<close> by (metis Suc_length_conv)
      have * : \<open>r1 # R' \<in> \<^bold>\<checkmark>\<^bold>s(\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l) \<Longrightarrow>
      (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip (l1 # L) (r1 # R'). Q l r)\<^sup>0 \<subseteq> ev ` S\<close>
        by (rule "3.hyps"(2)[THEN conjunct1, rule_format]) (simp_all add: "3.prems")
      from \<open>R \<in> \<^bold>\<checkmark>\<^bold>s(\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). P l)\<close>
      show \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip (l0 # l1 # L) R. Q l r)\<^sup>0 \<subseteq> ev ` S\<close>
        by (auto simp add: \<open>R = r0 # r1 # R'\<close> Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_tj_def
            dest!: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.strict_ticks_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset[THEN set_mp]
            "*" "3.prems"(2)[of l0 r0, simplified])+
    next
      have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l) =
        P l0 \<^bold>;\<^sub>\<checkmark> Q l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l)\<close> by simp
      also have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l) =
                 (\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip(l1 # L) R. Q l r)\<close>
        by (rule "3.hyps"(2)[THEN conjunct2]) (simp_all add: "3.prems")
      finally have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l) =
                    P l0 \<^bold>;\<^sub>\<checkmark> Q l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip(l1 # L) R. Q l r)\<close> .
      also have \<open>\<dots> = (P l0 |||\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l) \<^bold>;\<^sub>\<checkmark>
                  (\<lambda>R. Q l0 (hd R) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip (l1 # L) (tl R). Q l r)\<close>
      proof (rule Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.indep_lhs_waiting_rhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_through_Inter\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t)
        show \<open>\<alpha>(P l0) \<inter> S = {}\<close> by (simp add: "3.prems"(1))
      next
        show \<open>\<alpha>(\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l) \<inter> S = {}\<close>
          by (auto dest!: events_of_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset[THEN set_mp]) (use "3.prems"(1) in auto)
      next
        show \<open>r0 \<in> \<^bold>\<checkmark>\<^bold>s(P l0) \<Longrightarrow> (Q l0 r0)\<^sup>0 \<subseteq> ev ` S\<close> for r0 by (simp add: "3.prems"(2))
      next
        show \<open>R \<in> \<^bold>\<checkmark>\<^bold>s(\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l) \<Longrightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip (l1 # L) R. Q l r)\<^sup>0 \<subseteq> ev ` S\<close> for R
          using "3.hyps"(2) "3.prems"(1, 2) by auto
      qed
      also have \<open>\<dots> = (\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip (l0 # l1 # L) R. Q l r)\<close>
      proof (rule mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq)
        show \<open>P l0 |||\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l = \<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). P l\<close> by simp
      next
        fix R assume \<open>R \<in> \<^bold>\<checkmark>\<^bold>s(P l0 |||\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l)\<close>
        from is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
          [THEN is_ticks_lengthD, of _ _ \<open>l0 # l1 # L\<close>, simplified, OF this]
        obtain r0 r1 R' where \<open>R = r0 # r1 # R'\<close> by (metis Suc_length_conv)
        thus \<open>Q l0 (hd R) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip (l1 # L) (tl R). Q l r =
          \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> (l, r) \<in>@ zip (l0 # l1 # L) R. Q l r\<close> by simp
      qed
      finally show \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l) = \<dots>\<close> .
    qed
  qed
  thus ?thesis ..
qed



theorem indep_lhs_waiting_rhs_MultiSync_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk> l \<in># (mset L). (P l \<^bold>;\<^sub>\<checkmark> Q l) = (\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ L. P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r) \<in># mset (zip L R). Q l r)\<close>
  if \<open>\<And>l. l \<in> set L \<Longrightarrow> \<alpha>(P l) \<inter> S = {}\<close>
    and \<open>\<And>l r. l \<in> set L \<Longrightarrow> r \<in> \<^bold>\<checkmark>\<^bold>s(P l) \<Longrightarrow> (Q l r)\<^sup>0 \<subseteq> ev ` S\<close>
proof -
  from that have
    \<open>(R \<in> \<^bold>\<checkmark>\<^bold>s(\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ L. P l) \<longrightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r) \<in># mset (zip L R). Q l r)\<^sup>0 \<subseteq> ev ` S) \<and>
   \<^bold>\<lbrakk>S\<^bold>\<rbrakk> l \<in># (mset L). (P l \<^bold>;\<^sub>\<checkmark> Q l) = (\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ L. P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r) \<in># mset (zip L R). Q l r)\<close> for R
  proof (induct L arbitrary: R rule: induct_list012)
    case 1 show ?case by simp
  next
    case (2 l0)
    show ?case
    proof (intro conjI impI)
      show \<open>R \<in> \<^bold>\<checkmark>\<^bold>s(\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ [l0]. P l) \<Longrightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r) \<in># mset (zip [l0] R). Q l r)\<^sup>0 \<subseteq> ev ` S\<close>
        by (auto simp add: strict_ticks_of_RenamingTick initials_Renaming
            dest!: "2.prems"(2)[of l0, simplified] split: if_split_asm)+
    next
      have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk> l \<in># mset [l0]. (P l \<^bold>;\<^sub>\<checkmark> Q l) = P l0 \<^bold>;\<^sub>\<checkmark> Q l0\<close> by simp
      also have \<open>\<dots> = RenamingTick (P l0) (\<lambda>r. [r]) \<^bold>;\<^sub>\<checkmark> (\<lambda>g_r. Q l0 (THE r. r \<in> \<^bold>\<checkmark>\<^bold>s(P l0) \<and> g_r = [r]))\<close>
        by (auto intro: inj_on_Renaming_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of \<open>\<lambda>r. [r]\<close> _ _ id id, simplified] inj_onI)
      also have \<open>\<dots> = (\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ [l0]. P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r) \<in># mset (zip [l0] R). Q l r)\<close>
        by (auto intro!: mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq simp add: strict_ticks_of_RenamingTick the_equality)
      finally show \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk> l \<in># mset [l0]. (P l \<^bold>;\<^sub>\<checkmark> Q l) = \<dots>\<close> by simp
    qed
  next
    case (3 l0 l1 L)
    show ?case
    proof (intro conjI impI)
      fix R assume \<open>R \<in> \<^bold>\<checkmark>\<^bold>s(\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). P l)\<close>
      from is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[THEN is_ticks_lengthD, OF this]
      obtain r0 r1 R' where \<open>R = r0 # r1 # R'\<close> by (metis Suc_length_conv)
      have * : \<open>r1 # R' \<in> \<^bold>\<checkmark>\<^bold>s(\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l) \<Longrightarrow>
      (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r) \<in># mset (zip (l1 # L) (r1 # R')). Q l r)\<^sup>0 \<subseteq> ev ` S\<close>
        by (rule "3.hyps"(2)[THEN conjunct1, rule_format]) (simp_all add: "3.prems")
      from \<open>R \<in> \<^bold>\<checkmark>\<^bold>s(\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). P l)\<close>
      show \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r) \<in># mset (zip (l0 # l1 # L) R). Q l r)\<^sup>0 \<subseteq> ev ` S\<close>
        by (auto simp add: \<open>R = r0 # r1 # R'\<close> initials_Sync Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_tj_def
            dest!: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.strict_ticks_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset[THEN set_mp]
            "*" "3.prems"(2)[of l0 r0, simplified])+
    next
      have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk> l\<in>#mset (l0 # l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l) =
        P l0 \<^bold>;\<^sub>\<checkmark> Q l0 \<lbrakk>S\<rbrakk> \<^bold>\<lbrakk>S\<^bold>\<rbrakk> l\<in>#mset (l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l)\<close> by simp
      also have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk> l\<in>#mset (l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l) =
        \<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r)\<in>#mset (zip (l1 # L) R). Q l r)\<close>
        by (rule "3.hyps"(2)[THEN conjunct2]) (simp_all add: "3.prems")
      finally have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk> l\<in>#mset (l0 # l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l) =
                    P l0 \<^bold>;\<^sub>\<checkmark> Q l0 \<lbrakk>S\<rbrakk> \<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r)\<in>#mset (zip (l1 # L) R). Q l r)\<close> .
      also have \<open>\<dots> = (P l0 |||\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l) \<^bold>;\<^sub>\<checkmark>
                      (\<lambda>R. Q l0 (hd R) \<lbrakk>S\<rbrakk> \<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r)\<in>#mset (zip (l1 # L) (tl R)). Q l r)\<close>
      proof (fold Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_is_Sync,
          rule Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c.indep_lhs_waiting_rhs_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_through_Inter\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t)
        show \<open>\<alpha>(P l0) \<inter> S = {}\<close> by (simp add: "3.prems"(1))
      next
        show \<open>\<alpha>(\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l) \<inter> S = {}\<close>
          by (auto dest!: events_of_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset[THEN set_mp]) (use "3.prems"(1) in auto)
      next
        show \<open>r0 \<in> \<^bold>\<checkmark>\<^bold>s(P l0) \<Longrightarrow> (Q l0 r0)\<^sup>0 \<subseteq> ev ` S\<close> for r0 by (simp add: "3.prems"(2))
      next
        show \<open>R \<in> \<^bold>\<checkmark>\<^bold>s(\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l) \<Longrightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r)\<in>#mset (zip (l1 # L) R). Q l r)\<^sup>0 \<subseteq> ev ` S\<close> for R
          using "3.hyps"(2) "3.prems"(1, 2) by auto
      qed
      also have \<open>\<dots> = (\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). P l) \<^bold>;\<^sub>\<checkmark> (\<lambda>R. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r) \<in># mset (zip (l0 # l1 # L) R). Q l r)\<close>
      proof (rule mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq)
        show \<open>P l0 |||\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l = \<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). P l\<close> by simp
      next
        fix R assume \<open>R \<in> \<^bold>\<checkmark>\<^bold>s(P l0 |||\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l)\<close>
        from is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
          [THEN is_ticks_lengthD, of _ _ \<open>l0 # l1 # L\<close>, simplified, OF this]
        obtain r0 r1 R' where \<open>R = r0 # r1 # R'\<close> by (metis Suc_length_conv)
        thus \<open>Q l0 (hd R) \<lbrakk>S\<rbrakk> \<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r)\<in>#mset (zip (l1 # L) (tl R)). Q l r =
              \<^bold>\<lbrakk>S\<^bold>\<rbrakk> (l, r)\<in>#mset (zip (l0 # l1 # L) R). Q l r\<close> by simp
      qed
      finally show \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk> l\<in>#mset (l0 # l1 # L). (P l \<^bold>;\<^sub>\<checkmark> Q l) = \<dots>\<close> .
    qed
  qed
  thus ?thesis ..
qed


(*<*)
end
  (*>*)
