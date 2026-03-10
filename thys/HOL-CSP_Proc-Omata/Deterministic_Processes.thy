(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
 *         CNRS, ENS Paris-Saclay, LMF
 * Author: Burkhart Wolff, Université Paris-Saclay,
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

chapter \<open>An Excursion into Determinism\<close>

(*<*)
theory Deterministic_Processes
  imports "HOL-CSP_PTick"
begin
  (*>*)

text \<open>
This chapter is a preliminary work.
Indeed, later in the construction, we will define the notion of Procomata which comes
in different flavours, in particular deterministic ones.
We will establish then that such ProcOmata produce deterministic processes,
a classical notion in CSP that we formalize below.
\<close>

text \<open>
In a word, a deterministic process cannot refuse an event in which it can engage.
More formally, if \<^term>\<open>s @ [e] \<in> \<T> P\<close>, then \<^term>\<open>(s, {e}) \<notin> \<F> (P)\<close>.
In this theory, we follow the proof sketch given in \<^cite>\<open>"roscoe:csp:1998"\<close>
for characterizing deterministic processes as maximal elements for the
failure-divergence refinement \<^term>\<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close>.
Other lemmas are proved with respect to CSP operators.
\<close>


section \<open>Accepts initials\<close>

text \<open>This notion is a weak version of determinism.
      It captures the idea of being deterministic for one step.\<close>

subsection \<open>Definition\<close>

unbundle option_type_syntax

definition accepts_initials :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close> (\<open>determ\<^sup>0\<close>)
  where \<open>determ\<^sup>0 P \<equiv> \<forall>e \<in> P\<^sup>0. {e} \<notin> \<R> P\<close>

lemma accepts_initialsI : \<open>(\<And>e. e \<in> P\<^sup>0 \<Longrightarrow> {e} \<notin> \<R> P) \<Longrightarrow> determ\<^sup>0 P\<close>
  and accepts_initialsD : \<open>determ\<^sup>0 P \<Longrightarrow> e \<in> P\<^sup>0 \<Longrightarrow> {e} \<notin> \<R> P\<close>
  by (simp_all add: accepts_initials_def)


lemma accepts_initials_def_bis:
  \<open>determ\<^sup>0 P \<longleftrightarrow> (\<forall>e \<in> P\<^sup>0. \<forall>X \<in> \<R> P. e \<notin> X)\<close>
  by (auto simp add: accepts_initials_def)
    (metis Refusals_iff Un_upper1 insert_Diff insert_is_Un is_processT4)

lemma accepts_initialsI_bis : \<open>(\<And>e X. e \<in> P\<^sup>0 \<Longrightarrow> X \<in> \<R> P \<Longrightarrow> e \<notin> X) \<Longrightarrow> determ\<^sup>0 P\<close>
  and accepts_initialsD_bis : \<open>determ\<^sup>0 P \<Longrightarrow> e \<in> P\<^sup>0 \<Longrightarrow> X \<in> \<R> P \<Longrightarrow> e \<notin> X\<close>
  by (simp_all add: accepts_initials_def_bis)



subsection \<open>First properties\<close>


lemma accepts_initials_STOP [simp] : \<open>determ\<^sup>0 STOP\<close>
  by (simp add: accepts_initials_def)

lemma accepts_initials_SKIP [simp] : \<open>determ\<^sup>0 (SKIP r)\<close>
  by (simp add: accepts_initials_def Refusals_iff F_SKIP)

lemma not_accepts_initials_BOT [simp] : \<open>\<not> determ\<^sup>0 \<bottom>\<close>
  by (simp add: accepts_initials_def Refusals_iff F_BOT)


lemma accepts_initials_imp_initial_tick_iff_is_SKIP:
  \<open>determ\<^sup>0 P \<Longrightarrow> \<checkmark>(r) \<in> P\<^sup>0 \<longleftrightarrow> P = SKIP r\<close>
proof (rule iffI)
  show \<open>P = SKIP r \<Longrightarrow> \<checkmark>(r) \<in> P\<^sup>0\<close> by simp
next
  assume assms : \<open>determ\<^sup>0 P\<close> \<open>\<checkmark>(r) \<in> P\<^sup>0\<close>
  hence initials_is : \<open>P\<^sup>0 = {\<checkmark>(r)}\<close> 
    by (auto simp add: accepts_initials_def initials_def Refusals_iff subset_iff)
      (metis append_self_conv2 is_processT6_TR_notin singletonD)
  show \<open>P = SKIP r\<close>
  proof (subst SKIP_F_iff[symmetric], unfold failure_refine_def, safe)
    from assms show \<open>(s, X) \<in> \<F> P \<Longrightarrow> (s, X) \<in> \<F> (SKIP r)\<close> for s X
      by (cases s, auto simp add: F_SKIP accepts_initials_def_bis Refusals_iff dest!: F_T)
        (metis initials_is initials_memI singletonD,
          metis T_imp_front_tickFree event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) front_tickFree_Cons_iff
          initials_is initials_memI singletonD)
  qed
qed

lemma accepts_initials_imp_not_initial_tick_iff_is_STOP_or_some_initial_ev:
  \<open>determ\<^sup>0 P \<Longrightarrow> (range tick \<inter> P\<^sup>0 = {}) \<longleftrightarrow> P = STOP \<or> (\<exists>e. ev e \<in> P\<^sup>0)\<close>
  by (simp add: disjoint_iff image_iff)
    (metis accepts_initials_imp_initial_tick_iff_is_SKIP all_not_in_conv event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust
      event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(3) initials_SKIP initials_empty_iff_STOP singletonD)



subsection \<open>Monotonicity\<close>

lemma mono_accepts_initials_F: \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> determ\<^sup>0 P \<Longrightarrow> determ\<^sup>0 Q\<close>
  by (frule anti_mono_initials_F)
    (auto simp add: failure_refine_def accepts_initials_def Refusals_iff subset_iff)

lemma mono_accepts_initials_FD: \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> determ\<^sup>0 P \<Longrightarrow> determ\<^sup>0 Q\<close>
  using leFD_imp_leF mono_accepts_initials_F by blast

lemma mono_accepts_initials: \<open>P \<sqsubseteq> Q \<Longrightarrow> determ\<^sup>0 P \<Longrightarrow> determ\<^sup>0 Q\<close>
  by (drule le_approx_lemma_F, fold failure_refine_def) (rule mono_accepts_initials_F)


lemma restriction_adm_accepts_initials [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset, simp] :
  \<open>adm\<^sub>\<down> (\<lambda>x. determ\<^sup>0 (f x))\<close> if \<open>cont\<^sub>\<down> f\<close>
for f :: \<open>'b :: restriction \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (rule restriction_adm_subst)
  from \<open>cont\<^sub>\<down> f\<close> show \<open>cont\<^sub>\<down> f\<close> .
next
  show \<open>adm\<^sub>\<down> (determ\<^sup>0 :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool)\<close>
  proof (rule restriction_admI)
    fix \<sigma> and \<Sigma> :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    assume \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> \<open>determ\<^sup>0 (\<sigma> n)\<close> for n
    show \<open>determ\<^sup>0 \<Sigma>\<close>
    proof (rule accepts_initialsI)
      fix e assume \<open>e \<in> \<Sigma>\<^sup>0\<close>
      from \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> obtain n0
        where * : \<open>\<Sigma> \<down> Suc (Suc 0) = \<sigma> n0 \<down> Suc (Suc 0)\<close>
        by (blast dest: restriction_tendstoD)
      with \<open>e \<in> \<Sigma>\<^sup>0\<close> have \<open>e \<in> (\<sigma> n0)\<^sup>0\<close>
        by (metis initials_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k nat.distinct(1))
      with \<open>determ\<^sup>0 (\<sigma> n0)\<close> have \<open>{e} \<notin> \<R> (\<sigma> n0)\<close>
        by (fact accepts_initialsD)
      with "*" show \<open>{e} \<notin> \<R> \<Sigma>\<close>
        by (metis Refusals_iff F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_F
            list.size(3) restriction_related_pred)
    qed
  qed
qed



subsection \<open>Behaviour on Operators\<close>

lemma accepts_initials_Mprefix [simp] : \<open>determ\<^sup>0 (\<box>a \<in> A \<rightarrow> P a)\<close>
  by (simp add: accepts_initials_def initials_Mprefix Refusals_iff F_Mprefix)

lemma accepts_initials_write0 [simp] : \<open>determ\<^sup>0 (a \<rightarrow> P)\<close>
  by (simp add: write0_def)

lemma accepts_initials_write [simp] : \<open>determ\<^sup>0 (c\<^bold>!a \<rightarrow> P)\<close>
  by (simp add: write_def)

lemma accepts_initials_read [simp] : \<open>determ\<^sup>0 (c\<^bold>?a\<in>A \<rightarrow> P a)\<close>
  by (simp add: read_def)


lemma accepts_initials_Ndet_iff:
  \<open>determ\<^sup>0 (P \<sqinter> Q) \<longleftrightarrow> determ\<^sup>0 P \<and> determ\<^sup>0 Q \<and> P\<^sup>0 = Q\<^sup>0\<close>
  by (auto simp add: accepts_initials_def initials_Ndet Refusals_iff F_Ndet)
    (metis CollectI F_T Un_iff append_Nil initials_def is_processT1 is_processT5_S7 singletonD)+

lemma accepts_initials_GlobalNdet_iff:
  \<open>determ\<^sup>0 (\<sqinter>a \<in> A. P a) \<longleftrightarrow>
   (\<forall>a \<in> A. determ\<^sup>0 (P a) \<and> (\<forall>b \<in> A. (P a)\<^sup>0 = (P b)\<^sup>0))\<close>
  by (auto simp add: accepts_initials_def initials_GlobalNdet Refusals_iff F_GlobalNdet)
    (metis CollectI append_Nil initials_def is_processT1_TR is_processT5_S7 singletonD)+

lemma accepts_initials_Mndetprefix_iff:
  \<open>determ\<^sup>0 (\<sqinter>a \<in> A \<rightarrow> P a) \<longleftrightarrow> (\<exists>a. A \<subseteq> {a})\<close>
  by (simp add: Mndetprefix_GlobalNdet accepts_initials_GlobalNdet_iff initials_write0) blast

lemma accepts_initials_ndet_write_iff:
  \<open>determ\<^sup>0 (c\<^bold>!\<^bold>!a \<in> A \<rightarrow> P a) \<longleftrightarrow> (\<exists>b. c ` A \<subseteq> {b})\<close>
  by (simp add: ndet_write_def accepts_initials_Mndetprefix_iff)


lemma accepts_initials_SKIPS_iff :
  \<open>determ\<^sup>0 (SKIPS R) \<longleftrightarrow> R = {} \<or> (\<exists>r. R = {r})\<close>
  by (simp add: SKIPS_def accepts_initials_GlobalNdet_iff) blast



lemma accepts_initials_Det : 
  \<open>determ\<^sup>0 (P \<box> Q) \<longleftrightarrow> P = STOP \<or> Q = STOP \<or> range tick \<inter> P\<^sup>0 \<inter> Q\<^sup>0 \<noteq> {} \<or>
                                              range tick \<inter> (P\<^sup>0 \<union> Q\<^sup>0) = {}\<close>
  (is \<open>_ \<longleftrightarrow> ?rhs\<close>) if accepts_initials : \<open>determ\<^sup>0 P\<close> \<open>determ\<^sup>0 Q\<close>
proof (cases \<open>P = \<bottom>\<close>; cases \<open>Q = \<bottom>\<close>)
  show \<open>accepts_initials (P \<box> Q) \<longleftrightarrow> ?rhs\<close> if non_BOT : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close>
  proof (rule iffI)
    show \<open>?rhs \<Longrightarrow> determ\<^sup>0 (P \<box> Q)\<close>
    proof (elim disjE)
      show \<open>P = STOP \<Longrightarrow> determ\<^sup>0 (P \<box> Q)\<close> \<open>Q = STOP \<Longrightarrow> determ\<^sup>0 (P \<box> Q)\<close>
        by (simp_all add: accepts_initials)
    next
      from non_BOT accepts_initials
      show \<open>range tick \<inter> P\<^sup>0 \<inter> Q\<^sup>0 \<noteq> {} \<Longrightarrow> determ\<^sup>0 (P \<box> Q)\<close>
        \<open>range tick \<inter> (P\<^sup>0 \<union> Q\<^sup>0) = {} \<Longrightarrow> determ\<^sup>0 (P \<box> Q)\<close>
        by (simp_all add: accepts_initials_def initials_def Refusals_iff
            Det_projs BOT_iff_Nil_D disjoint_iff)
          (metis append_Nil is_processT6_TR_notin singletonD)
    qed
  next
    have * : \<open>\<lbrakk>Q \<noteq> STOP; \<checkmark>(r) \<in> P\<^sup>0; \<checkmark>(r) \<notin> Q\<^sup>0; determ\<^sup>0 P; determ\<^sup>0 (P \<box> Q)\<rbrakk> \<Longrightarrow> False\<close>
      for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and r
      by (metis Un_iff accepts_initials_imp_initial_tick_iff_is_SKIP ex_in_conv
          initials_Det initials_SKIP initials_empty_iff_STOP singletonD)
    show \<open>determ\<^sup>0 (P \<box> Q) \<Longrightarrow> ?rhs\<close>
      by (simp add: disjoint_iff) (metis "*" Det_commute accepts_initials rangeE)
  qed
qed (use not_accepts_initials_BOT accepts_initials in auto)


lemma accepts_initials_GlobalDet :
  \<open>determ\<^sup>0 (\<box>a \<in> A. P a)\<close> if \<open>\<And>a. a \<in> A \<Longrightarrow> determ\<^sup>0 (P a)\<close>
  \<open>range tick \<inter> (\<Inter>a \<in> A. (P a)\<^sup>0) \<noteq> {} \<or> range tick \<inter> (\<Union>a \<in> A. (P a)\<^sup>0) = {}\<close>
proof (use that(2) in \<open>elim disjE\<close>)
  from that(1) show \<open>range tick \<inter> (\<Inter>a\<in>A. (P a)\<^sup>0) \<noteq> {} \<Longrightarrow> determ\<^sup>0 (\<box>a \<in> A. P a)\<close>
    by (auto simp add: accepts_initials_def initials_GlobalDet Refusals_iff F_GlobalDet)
      (meson is_processT8,
        metis accepts_initials_imp_initial_tick_iff_is_SKIP
        initials_SKIP initials_memI singleton_iff that(1))
next
  from that(1) show \<open>range tick \<inter> (\<Union>a\<in>A. (P a)\<^sup>0) = {} \<Longrightarrow> determ\<^sup>0 (\<box>a \<in> A. P a)\<close>
    by (auto simp add: accepts_initials_def initials_GlobalDet Refusals_iff F_GlobalDet)
      (blast, metis BOT_iff_Nil_D not_accepts_initials_BOT that(1),
        metis UN_I disjoint_iff initials_memI rangeI)
qed


lemma accepts_initials_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>determ\<^sup>0 (P \<^bold>;\<^sub>\<checkmark> Q) \<longleftrightarrow> (\<forall>r. \<checkmark>(r) \<in> P\<^sup>0 \<longrightarrow> determ\<^sup>0 (Q r))\<close> if \<open>determ\<^sup>0 P\<close>
proof (intro iffI allI impI)
  show \<open>determ\<^sup>0 (P \<^bold>;\<^sub>\<checkmark> Q) \<Longrightarrow> \<checkmark>(r) \<in> P\<^sup>0 \<Longrightarrow> determ\<^sup>0 (Q r)\<close> for r
    by (simp add: accepts_initials_imp_initial_tick_iff_is_SKIP \<open>determ\<^sup>0 P\<close>)
next
  have \<open>P \<noteq> \<bottom>\<close> using not_accepts_initials_BOT that by blast
  show \<open>determ\<^sup>0 (P \<^bold>;\<^sub>\<checkmark> Q)\<close> if * : \<open>\<forall>r. \<checkmark>(r) \<in> P\<^sup>0 \<longrightarrow> determ\<^sup>0 (Q r)\<close>
  proof (rule accepts_initialsI)
    fix e assume \<open>e \<in> (P \<^bold>;\<^sub>\<checkmark> Q)\<^sup>0\<close>
    then consider a where \<open>e = ev a\<close> \<open>ev a \<in> P\<^sup>0\<close> | r where \<open>\<checkmark>(r) \<in> P\<^sup>0\<close> \<open>e \<in> (Q r)\<^sup>0\<close>
      by (simp add: initials_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>P \<noteq> \<bottom>\<close>) blast
    thus \<open>{e} \<notin> \<R> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
    proof cases
      from \<open>determ\<^sup>0 P\<close> \<open>P \<noteq> \<bottom>\<close> show \<open>e = ev a \<Longrightarrow> ev a \<in> P\<^sup>0 \<Longrightarrow> {e} \<notin> \<R> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> for a
        unfolding accepts_initials_def_bis Refusals_def_bis
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs BOT_iff_Nil_D ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
          (metis \<open>determ\<^sup>0 P\<close> accepts_initials_imp_initial_tick_iff_is_SKIP event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1)
                 initials_SKIP initials_memI insertI1 singletonD)
    next
      show \<open>\<checkmark>(r) \<in> P\<^sup>0 \<Longrightarrow> e \<in> (Q r)\<^sup>0 \<Longrightarrow> {e} \<notin> \<R> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> for r
        by (simp add: \<open>determ\<^sup>0 P\<close> accepts_initialsD accepts_initials_imp_initial_tick_iff_is_SKIP "*")
    qed
  qed
qed

corollary accepts_initials_Seq :
  \<open>determ\<^sup>0 (P \<^bold>; Q) \<longleftrightarrow> (P\<^sup>0 \<inter> range tick = {} \<or> determ\<^sup>0 Q)\<close> if \<open>determ\<^sup>0 P\<close>
  by (fold Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_const, unfold accepts_initials_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF that]) fast


lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) accepts_initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>determ\<^sup>0 (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> if \<open>determ\<^sup>0 P\<close> \<open>determ\<^sup>0 Q\<close>
proof (rule accepts_initialsI)
  from \<open>determ\<^sup>0 P\<close> \<open>determ\<^sup>0 Q\<close> have \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> by auto
  fix e assume \<open>e \<in> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<^sup>0\<close>
  with \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> consider
    a where \<open>e = ev a\<close> \<open>a \<in> S \<and> ev a \<in> P\<^sup>0 \<and> ev a \<in> Q\<^sup>0 \<or> a \<notin> S \<and> (ev a \<in> P\<^sup>0 \<or> ev a \<in> Q\<^sup>0)\<close>
  | r_s r s where \<open>e = \<checkmark>(r_s)\<close> \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close> \<open>\<checkmark>(r) \<in> P\<^sup>0\<close> \<open>\<checkmark>(s) \<in> Q\<^sup>0\<close>
    by (auto simp add: initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k split: if_split_asm)
  thus \<open>{e} \<notin> \<R> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  proof cases
    fix a assume \<open>e = ev a\<close> \<open>a \<in> S \<and> ev a \<in> P\<^sup>0 \<and> ev a \<in> Q\<^sup>0 \<or> a \<notin> S \<and> (ev a \<in> P\<^sup>0 \<or> ev a \<in> Q\<^sup>0)\<close>
    from this(2) show \<open>{e} \<notin> \<R> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    proof (elim disjE conjE)
      show \<open>{e} \<notin> \<R> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> if \<open>ev a \<in> P\<^sup>0\<close> \<open>ev a \<in> Q\<^sup>0\<close>
      proof (rule notI)
        assume \<open>{e} \<in> \<R> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
        with \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> obtain X_P X_Q
          where \<open>([], X_P) \<in> \<F> P\<close> \<open>([], X_Q) \<in> \<F> Q\<close> \<open>e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P S X_Q\<close>
          by (auto simp add: Refusals_iff F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k BOT_iff_Nil_D dest: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        from this(3) have \<open>ev a \<in> X_P \<or> ev a \<in> X_Q\<close>
          by (auto simp add: \<open>e = ev a\<close> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
        with \<open>ev a \<in> P\<^sup>0\<close> \<open>ev a \<in> Q\<^sup>0\<close> \<open>([], X_P) \<in> \<F> P\<close> \<open>([], X_Q) \<in> \<F> Q\<close> show False
          by (fold Refusals_iff) (metis accepts_initialsD_bis \<open>determ\<^sup>0 P\<close> \<open>determ\<^sup>0 Q\<close>)
      qed
    next
      show \<open>{e} \<notin> \<R> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> if \<open>a \<notin> S\<close> \<open>ev a \<in> P\<^sup>0\<close>
      proof (rule notI)
        assume \<open>{e} \<in> \<R> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
        with \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> obtain X_P X_Q
          where \<open>([], X_P) \<in> \<F> P\<close> \<open>([], X_Q) \<in> \<F> Q\<close> \<open>e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P S X_Q\<close>
          by (auto simp add: Refusals_iff F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k BOT_iff_Nil_D dest: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        from this(3) have \<open>ev a \<in> X_P\<close>
          by (simp add: \<open>e = ev a\<close> \<open>a \<notin> S\<close> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
        with \<open>ev a \<in> P\<^sup>0\<close> \<open>([], X_P) \<in> \<F> P\<close> show False
          by (fold Refusals_iff) (metis accepts_initialsD_bis \<open>determ\<^sup>0 P\<close>)
      qed
    next
      show \<open>{e} \<notin> \<R> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> if \<open>a \<notin> S\<close> \<open>ev a \<in> Q\<^sup>0\<close>
      proof (rule notI)
        assume \<open>{e} \<in> \<R> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
        with \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> obtain X_P X_Q
          where \<open>([], X_P) \<in> \<F> P\<close> \<open>([], X_Q) \<in> \<F> Q\<close> \<open>e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P S X_Q\<close>
          by (auto simp add: Refusals_iff F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k BOT_iff_Nil_D dest: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        from this(3) have \<open>ev a \<in> X_Q\<close>
          by (simp add: \<open>e = ev a\<close> \<open>a \<notin> S\<close> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
        with \<open>ev a \<in> Q\<^sup>0\<close> \<open>([], X_Q) \<in> \<F> Q\<close> show False
          by (fold Refusals_iff) (metis accepts_initialsD_bis \<open>determ\<^sup>0 Q\<close>)
      qed
    qed
  next
    fix r_s r s assume \<open>e = \<checkmark>(r_s)\<close> \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close> \<open>\<checkmark>(r) \<in> P\<^sup>0\<close> \<open>\<checkmark>(s) \<in> Q\<^sup>0\<close>
    show \<open>{e} \<notin> \<R> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    proof (rule notI)
      assume \<open>{e} \<in> \<R> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      with \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> obtain X_P X_Q
        where \<open>([], X_P) \<in> \<F> P\<close> \<open>([], X_Q) \<in> \<F> Q\<close> \<open>e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P S X_Q\<close>
        by (auto simp add: Refusals_iff F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k BOT_iff_Nil_D dest: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      from this(3) have \<open>\<checkmark>(r) \<in> X_P\<close>
        by (simp flip:  \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close> add: \<open>e = \<checkmark>(r_s)\<close> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
          (metis Refusals_iff \<open>([], X_Q) \<in> \<F> Q\<close> \<open>\<checkmark>(s) \<in> Q\<^sup>0\<close> \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close>
            accepts_initials_def_bis inj_tick_join that(2))
      with \<open>\<checkmark>(r) \<in> P\<^sup>0\<close> \<open>([], X_P) \<in> \<F> P\<close> show False
        by (fold Refusals_iff) (metis accepts_initialsD_bis \<open>determ\<^sup>0 P\<close>)
    qed
  qed
qed

corollary accepts_initials_Sync:
  \<open>determ\<^sup>0 P \<Longrightarrow> determ\<^sup>0 Q \<Longrightarrow> determ\<^sup>0 (P \<lbrakk>S\<rbrakk> Q)\<close>
  by (metis Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c.accepts_initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_is_Sync)


lemma accepts_initials_Renaming : \<open>determ\<^sup>0 (Renaming P f g)\<close> if \<open>determ\<^sup>0 P\<close>
proof -
  from \<open>determ\<^sup>0 P\<close> have \<open>P \<noteq> \<bottom>\<close> by auto
  with \<open>determ\<^sup>0 P\<close> show \<open>determ\<^sup>0 (Renaming P f g)\<close>
    by (simp add: accepts_initials_def initials_Renaming Refusals_iff F_Renaming vimage_def BOT_iff_Nil_D)
      (metis (full_types) accepts_initials_def Refusals_iff accepts_initials_def_bis mem_Collect_eq)
qed


lemma accepts_initials_Throw_iff : \<open>determ\<^sup>0 (P \<Theta> a \<in> A. Q a) \<longleftrightarrow> determ\<^sup>0 P\<close>
  using D_F by (auto simp add: accepts_initials_def initials_Throw Refusals_iff F_Throw)



lemma accepts_initials_Sliding:
  \<open>determ\<^sup>0 P \<Longrightarrow> determ\<^sup>0 Q \<Longrightarrow> determ\<^sup>0 (P \<rhd> Q) \<longleftrightarrow>
   P = STOP \<or> P\<^sup>0 \<subseteq> Q\<^sup>0 \<and> (range tick \<inter> P\<^sup>0 \<noteq> {} \<or> range tick \<inter> Q\<^sup>0 = {})\<close>
  by (auto simp add: Sliding_def accepts_initials_Ndet_iff accepts_initials_Det initials_Det)




(* lemma accepts_initials_Interrupt: \<open>accepts_initials (P \<triangle> Q) \<longleftrightarrow> accepts_initials P \<and> (\<checkmark> \<notin> P\<^sup>0 \<or> accepts_initials Q)\<close>
  apply (cases \<open>P = \<bottom>\<close>, solves \<open>auto simp add: Interrupt_BOT_absorb(2) not_accepts_initials_BOT\<close>)
  apply (cases \<open>Q = \<bottom>\<close>, solves \<open>auto simp add: Interrupt_BOT_absorb(1) not_accepts_initials_BOT\<close>)
  apply (simp add: accepts_initials_def initials_Interrupt Refusals_iff F_Interrupt BOT_iff_D)
  apply safe
  oops *)


(* lemma accepts_initials_Hiding: \<open>accepts_initials P \<Longrightarrow> accepts_initials (P \ S)\<close>
  oops
 *)




subsection \<open>Characterizations with After\<close>

context After
begin

text \<open>Interesting results about the fact that we can express a process
      with \<^const>\<open>Mprefix\<close> and \<^const>\<open>After\<close>\<close>

lemma leFD_SKIPS_Det_Mprefix_After:
  \<open>P \<sqsubseteq>\<^sub>F\<^sub>D SKIPS {r. \<checkmark>(r) \<in> P\<^sup>0} \<box> (\<box>a \<in> {a. ev a \<in> P\<^sup>0} \<rightarrow> P after a)\<close> (is \<open>P \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
proof (unfold failure_divergence_refine_def failure_refine_def divergence_refine_def, safe)
  show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> P\<close> for s
    by (auto simp add: D_Det D_SKIPS D_Mprefix D_After)
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> P\<close> for s X
  proof (cases s)
    show \<open>s = [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> P\<close>
      by (simp add: F_Det SKIPS_projs STOP_projs F_Mprefix  
          F_After disjoint_iff image_iff split: if_split_asm)
        (metis initials_memI append_Nil event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust is_processT1_TR is_processT5_S7,
          metis CollectD append.left_neutral initials_def is_processT6_TR_notin)
  next
    show \<open>s = e # s' \<Longrightarrow> (s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> P\<close> for e s'
      by (auto simp add: F_Det SKIPS_projs STOP_projs F_Mprefix  
          F_After disjoint_iff image_iff split: if_split_asm)
        (metis CollectD append_butlast_last_id initials_def last_ConsL list.distinct(1) tick_T_F)
  qed
qed


lemma accepts_initials_imp_eq_Mprefix_After:
  \<open>P = (  if \<exists>r. \<checkmark>(r) \<in> P\<^sup>0 then SKIP (THE r. \<checkmark>(r) \<in> P\<^sup>0)
        else \<box>a \<in> {e. ev e \<in> P\<^sup>0} \<rightarrow> P after a)\<close> (is \<open>P = ?rhs\<close>)
  if \<open>determ\<^sup>0 P\<close>
proof -
  from not_accepts_initials_BOT \<open>determ\<^sup>0 P\<close> have non_BOT: \<open>P \<noteq> \<bottom>\<close> by blast
  note initial_tick_iff_is_SKIP = accepts_initials_imp_initial_tick_iff_is_SKIP[OF \<open>determ\<^sup>0 P\<close>]

  have * : \<open>?rhs = (SKIPS {r. \<checkmark>(r) \<in> P\<^sup>0}) \<box>
                   (\<box>a \<in> {e. ev e \<in> P\<^sup>0} \<rightarrow> P after a)\<close> (is \<open>?rhs = ?rhs_bis\<close>)
    by (simp, rule impI, elim exE, simp add: initial_tick_iff_is_SKIP)

  show \<open>P = ?rhs\<close>
  proof (rule FD_antisym)
    show \<open>P \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close> by (unfold "*") (fact leFD_SKIPS_Det_Mprefix_After)
  next
    show \<open>?rhs \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
    proof (unfold failure_divergence_refine_def failure_refine_def divergence_refine_def, safe)
      from non_BOT show \<open>s \<in> \<D> P \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
        by (cases s; simp add: D_Det D_SKIP D_STOP D_Mprefix BOT_iff_Nil_D
            image_iff D_After initial_tick_iff_is_SKIP)
          (metis BOT_iff_tick_D initials_memI D_T D_imp_front_tickFree event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2)
            event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust front_tickFree_Cons_iff initials_SKIP non_BOT singletonD)
    next
      have * : \<open>\<exists>r. \<checkmark>(r) \<in> P\<^sup>0 \<Longrightarrow> \<exists>!r. \<checkmark>(r) \<in> P\<^sup>0\<close>
        by (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(2) initial_tick_iff_is_SKIP initials_SKIP singletonD)
      show \<open>(t, X) \<in> \<F> P \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for t X
      proof (cases t)
        from "*" show \<open>t = [] \<Longrightarrow> (t, X) \<in> \<F> P \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close>
          by (simp add: add: F_Mprefix disjoint_iff image_iff initial_tick_iff_is_SKIP)
            (metis (lifting) \<open>determ\<^sup>0 P\<close> Refusals_iff[of X P]
              accepts_initialsD_bis[of P _ X] the_equality[of \<open>\<lambda>r. P = SKIP r\<close>])
      next
        from "*" show \<open>t = e # t' \<Longrightarrow> (t, X) \<in> \<F> P \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for e t'
          by (cases e, simp_all add: F_Mprefix F_After disjoint_iff image_iff initial_tick_iff_is_SKIP)
            (metis F_T event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) initials_SKIP initials_memI singletonD,
              metis (mono_tags, lifting) F_T initial_tick_iff_is_SKIP initials_memI the_equality)
      qed
    qed
  qed
qed



theorem is_some_Mprefix_iff:
  \<open>(\<exists>A Q. P = \<box>a \<in> A \<rightarrow> Q a) \<longleftrightarrow> range tick \<inter> P\<^sup>0 = {} \<and> accepts_initials P\<close>
  for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (intro iffI exI)
  show \<open>\<exists>A Q. P = Mprefix A Q \<Longrightarrow> range tick \<inter> P\<^sup>0 = {} \<and> accepts_initials P\<close>
    by (auto simp add: initials_Mprefix image_iff disjoint_iff)
next
  from accepts_initials_imp_eq_Mprefix_After
  show \<open>range tick \<inter> P\<^sup>0 = {} \<and> accepts_initials P \<Longrightarrow>
        P = \<box>a \<in> {e. ev e \<in> P\<^sup>0} \<rightarrow> P after a\<close>
    by (meson disjoint_iff rangeI)
qed


lemma tick_not_initial_imp_STOP_Ndet_Mndetprefix_After_FD:
  \<open>range tick \<inter> P\<^sup>0 = {} \<Longrightarrow> STOP \<sqinter> (\<box>a \<in> {e. ev e \<in> P\<^sup>0} \<rightarrow> P after a) \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  by (cases \<open>P = \<bottom>\<close>, solves \<open>simp\<close>,
      auto simp add: refine_defs Ndet_projs F_STOP Mprefix_projs After_projs BOT_iff_Nil_D)
    (metis initials_memI F_T Int_iff empty_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust neq_Nil_conv rangeI,
      metis initials_memI D_T disjoint_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust neq_Nil_conv rangeI)

\<comment> \<open>With this we could obtain something about \<^const>\<open>CHAOS\<close> and \<^const>\<open>tickFree\<close>
    and \<^term>\<open>\<D> P = {}\<close> but we already have this.\<close>

lemma \<open>lifelock_free P \<longleftrightarrow> \<D> P = {} \<and> (\<forall>t \<in> \<T> P. tF t)\<close>
  using lifelock_free_is_non_terminating non_terminating_is_right nonterminating_implies_div_free by blast



lemma STOP_Ndet_SKIPS_Ndet_Mprefix_After_leF :
  \<open>STOP \<sqinter> SKIPS {r. \<checkmark>(r) \<in> P\<^sup>0} \<sqinter> (\<box>a \<in> {e. ev e \<in> P\<^sup>0} \<rightarrow> P after a) \<sqsubseteq>\<^sub>F P\<close>
  (is \<open>_ \<sqinter> ?lhs1 \<sqinter> ?lhs2 \<sqsubseteq>\<^sub>F P\<close>)
proof (unfold failure_refine_def, safe)
  fix t X assume \<open>(t, X) \<in> \<F> P\<close>
  then consider \<open>t = []\<close> | r where \<open>t = [\<checkmark>(r)]\<close> \<open>r \<in> {r. \<checkmark>(r) \<in> P\<^sup>0}\<close>
    | a t' where \<open>t = ev a # t'\<close> \<open>a \<in> {a. ev a \<in> P\<^sup>0}\<close>
    by (cases t, simp_all) (metis F_T F_imp_front_tickFree event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust
        front_tickFree_Cons_iff initials_memI is_ev_def)
  thus \<open>(t, X) \<in> \<F> (STOP \<sqinter> ?lhs1 \<sqinter> ?lhs2)\<close>
  proof cases
    show \<open>t = [] \<Longrightarrow> (t, X) \<in> \<F> (STOP \<sqinter> ?lhs1 \<sqinter> ?lhs2)\<close> by (simp add: F_Ndet F_STOP)
  next
    fix r assume \<open>t = [\<checkmark>(r)]\<close>
    with \<open>(t, X) \<in> \<F> P\<close> have \<open>(t, X) \<in> \<F> (?lhs1)\<close>
      by (auto simp add: F_SKIPS intro!: initials_memI' F_T)
    thus \<open>(t, X) \<in> \<F> (STOP \<sqinter> ?lhs1 \<sqinter> ?lhs2)\<close> by (simp add: F_Ndet)
  next
    fix a t' assume \<open>t = ev a # t'\<close>
    with \<open>(t, X) \<in> \<F> P\<close> have \<open>(t, X) \<in> \<F> ?lhs2\<close>
      by (auto simp add: F_Mprefix F_After intro!: initials_memI F_T)
    thus \<open>(t, X) \<in> \<F> (STOP \<sqinter> ?lhs1 \<sqinter> ?lhs2)\<close> by (simp add: F_Ndet)
  qed
qed

lemma non_BOT_imp_Mprefix_After_leD :
  \<open>\<box>a \<in> {e. ev e \<in> P\<^sup>0} \<rightarrow> P after a \<sqsubseteq>\<^sub>D P\<close> (is \<open>_?lhs \<sqsubseteq>\<^sub>D P\<close>) if \<open>P \<noteq> \<bottom>\<close>
proof (unfold divergence_refine_def, rule subsetI)
  fix t assume \<open>t \<in> \<D> P\<close>
  with \<open>P \<noteq> \<bottom>\<close> obtain a t' where \<open>t = ev a # t'\<close>
    by (cases t, simp add: BOT_iff_Nil_D, simp add: BOT_iff_tick_D)
      (metis D_imp_front_tickFree event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust front_tickFree_Cons_iff is_ev_def)
  with \<open>t \<in> \<D> P\<close> show \<open>t \<in> \<D> ?lhs\<close>
    by (auto simp add: D_Mprefix D_After intro: D_T initials_memI)
qed

lemma non_BOT_imp_STOP_Ndet_SKIPS_Ndet_Mprefix_After_leFD :
  \<open>P \<noteq> \<bottom> \<Longrightarrow> STOP \<sqinter> SKIPS {r. \<checkmark>(r) \<in> P\<^sup>0} \<sqinter> (\<box>a \<in> {e. ev e \<in> P\<^sup>0} \<rightarrow> P after a) \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  by (rule leF_leD_imp_leFD[OF STOP_Ndet_SKIPS_Ndet_Mprefix_After_leF])
    (use non_BOT_imp_Mprefix_After_leD Ndet_D_self_right trans_D in blast)




theorem singl_initial_imp_equals_prefix_After:
  \<open>P = (if UNIV \<notin> \<R> P then a \<rightarrow> P after a else STOP \<sqinter> (a \<rightarrow> P after a))\<close>
  if initials_is : \<open>initials P = {ev a}\<close>
proof (split if_split, intro conjI impI)
  assume not_all_refusals : \<open>UNIV \<notin> \<R> P\<close>
  have $ : \<open>e \<noteq> ev a \<Longrightarrow> [e] \<notin> \<T> P\<close> for e using initials_is unfolding initials_def by auto
  { assume \<open>{ev a} \<in> \<R> P\<close>
    from is_processT5[rule_format, of \<open>[]\<close> \<open>{ev a}\<close> P \<open>UNIV - {ev a}\<close>, folded Refusals_iff,
        simplified this T_F_spec, simplified, rule_format, OF "$", simplified]
    have \<open>UNIV \<in> \<R> P\<close> .
    with not_all_refusals have False by simp
  } hence not_in_refusal: \<open>{ev a} \<notin> \<R> P\<close> by blast
  show \<open>P = a \<rightarrow> P after a\<close>
    by (unfold write0_def, subst accepts_initials_imp_eq_Mprefix_After)
      (solves \<open>simp add: accepts_initials_def initials_is not_in_refusal\<close>,
        auto simp add: that(1) intro: mono_Mprefix_eq)
next
  assume all_refusals : \<open>\<not> UNIV \<notin> \<R> P\<close>
  from tick_not_initial_imp_STOP_Ndet_Mndetprefix_After_FD[of P]
  have *  : \<open>STOP \<sqinter> (a \<rightarrow> P after a) \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
    by (simp add: that(1) Mprefix_singl image_iff)
  from leFD_SKIPS_Det_Mprefix_After[of P] all_refusals
  have ** : \<open>P \<sqsubseteq>\<^sub>F\<^sub>D STOP \<sqinter> (a \<rightarrow> P after a)\<close>
    by (auto simp add: refine_defs that(1) write0_projs Mprefix_projs
        Ndet_projs STOP_projs Refusals_iff)
      (meson is_processT4 subset_UNIV)
  from "**" "*" show \<open>P = STOP \<sqinter> (a \<rightarrow> P after a)\<close> by (fact FD_antisym)
qed


lemma \<open>{ev e} \<notin> \<R> P \<Longrightarrow> ev e \<in> P\<^sup>0\<close>
  by (simp add: Refusals_iff initials_def) 
    (metis is_processT1_TR is_processT5_S7 self_append_conv2 singletonD)

end



section \<open>Deterministic process\<close>

subsection \<open>Definition\<close>

definition deterministic :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close> (\<open>determ\<close>)
  where \<open>determ P \<equiv> \<forall> s e. s @ [e] \<in> \<T> P \<longrightarrow> (s, {e}) \<notin> \<F> (P)\<close>

lemma deterministicI : \<open>(\<And>t e. t @ [e] \<in> \<T> P \<Longrightarrow> (t, {e}) \<notin> \<F> (P)) \<Longrightarrow> determ P\<close>
  and deterministicD : \<open>determ P \<Longrightarrow> t @ [e] \<in> \<T> P \<Longrightarrow> (t, {e}) \<notin> \<F> (P)\<close>
  by (simp_all add: deterministic_def)

lemma deterministic_STOP [simp] : \<open>determ STOP\<close>
  and deterministic_SKIP [simp] : \<open>determ (SKIP r)\<close>
  by (simp_all add: deterministic_def T_STOP SKIP_projs)

lemma deterministic_div_free : \<open>determ P \<Longrightarrow> \<D> P = {}\<close>
  by (auto simp add: deterministic_def)
    (metis D_T D_imp_front_tickFree append_butlast_last_id div_butlast_when_non_tickFree_iff
      front_tickFree_single is_processT7 is_processT8 tickFree_Nil)

lemma not_deterministic_BOT [simp] : \<open>\<not> determ \<bottom>\<close>
  using BOT_iff_Nil_D deterministic_div_free by blast


subsection \<open>Monotonicity\<close>

lemma mono_deterministic_F: \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> determ P \<Longrightarrow> determ Q\<close>
  by (meson T_F_spec deterministic_def failure_refine_def subset_iff)

lemma mono_deterministic_FD: \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> determ P \<Longrightarrow> determ Q\<close>
  using leFD_imp_leF mono_deterministic_F by blast

lemma mono_deterministic: \<open>P \<sqsubseteq> Q \<Longrightarrow> determ P \<Longrightarrow> determ Q\<close>
  using le_approx_imp_le_ref mono_deterministic_FD by auto


lemma restriction_adm_deterministic [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset, simp] :
  \<open>adm\<^sub>\<down> (\<lambda>x. determ (f x))\<close> if \<open>cont\<^sub>\<down> f\<close>
for f :: \<open>'b :: restriction \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (rule restriction_adm_subst)
  from \<open>cont\<^sub>\<down> f\<close> show \<open>cont\<^sub>\<down> f\<close> .
next
  show \<open>adm\<^sub>\<down> (determ :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool)\<close>
  proof (rule restriction_admI)
    fix \<sigma> and \<Sigma> :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    assume \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> \<open>determ (\<sigma> n)\<close> for n
    show \<open>determ \<Sigma>\<close>
    proof (rule deterministicI)
      fix t e assume \<open>t @ [e] \<in> \<T> \<Sigma>\<close>
      from \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> obtain n0
        where * : \<open>\<Sigma> \<down> Suc (length (t @ [e])) = \<sigma> n0 \<down> Suc (length (t @ [e]))\<close>
        by (blast dest: restriction_tendstoD)
      with \<open>t @ [e] \<in> \<T> \<Sigma>\<close> have \<open>t @ [e] \<in> \<T> (\<sigma> n0)\<close>
        by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_T)
      with \<open>deterministic (\<sigma> n0)\<close> have \<open>(t, {e}) \<notin> \<F> (\<sigma> n0)\<close>
        by (fact deterministicD)
      with "*" show \<open>(t, {e}) \<notin> \<F> \<Sigma>\<close>
        by (metis F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_F
            length_append_singleton restriction_related_pred)
    qed
  qed
qed



subsection \<open>Characterization as Maximal\<close>

subsubsection \<open>Some preliminary work\<close>

definition is_process\<^sub>T :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set \<Rightarrow> bool\<close>
  where \<open>is_process\<^sub>T T \<equiv>
         [] \<in> T \<and> (\<forall>t \<in> T. ftF t) \<and> (\<forall>t u. t @ u \<in> T \<longrightarrow> t \<in> T) \<and>
         (\<forall>t r e. t @ [\<checkmark>(r)] \<in> T \<longrightarrow> e \<noteq> \<checkmark>(r) \<longrightarrow> t @ [e] \<notin> T)\<close>

typedef ('a, 'r) process\<^sub>T = \<open>{T :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set . is_process\<^sub>T T}\<close>
proof (rule exI)
  show \<open>{[]} \<in> {T. is_process\<^sub>T T}\<close> unfolding is_process\<^sub>T_def by simp
qed

setup_lifting type_definition_process\<^sub>T


lift_definition Traces\<^sub>T ::
  \<open>('a, 'r) process\<^sub>T \<Rightarrow> ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close> (\<open>\<T>\<^sub>T\<close>)
  is \<open>\<lambda>P. Rep_process\<^sub>T P\<close> .

lemma Process\<^sub>T_eq_spec : \<open>T = U \<longleftrightarrow> \<T>\<^sub>T T = \<T>\<^sub>T U\<close>
  by (simp add: Rep_process\<^sub>T_inject Traces\<^sub>T.rep_eq)

lemma is_process\<^sub>T_1 : \<open>[] \<in> \<T>\<^sub>T P\<close>
  and is_process\<^sub>T_2 : \<open>s \<in> \<T>\<^sub>T P \<Longrightarrow> ftF s\<close>
  and is_process\<^sub>T_3 : \<open>s @ t \<in> \<T>\<^sub>T P \<Longrightarrow> s \<in> \<T>\<^sub>T P\<close>
  and is_process\<^sub>T_4 : \<open>s @ [\<checkmark>(r)] \<in> \<T>\<^sub>T P \<Longrightarrow> e \<noteq> \<checkmark>(r) \<Longrightarrow> s @ [e] \<notin> \<T>\<^sub>T P\<close>
  by (transfer, meson Rep_process\<^sub>T[simplified, unfolded is_process\<^sub>T_def])+


lemmas is_process\<^sub>T_def_bis = is_process\<^sub>T_def[of \<open>Rep_process\<^sub>T _\<close>, folded Traces\<^sub>T.rep_eq]



lift_definition process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T ::
  \<open>('a, 'r) process\<^sub>T \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  is \<open>\<lambda>T. ({(s, X). s \<in> \<T>\<^sub>T T \<and> X \<subseteq> - {e. s @ [e] \<in> \<T>\<^sub>T T}}, {})\<close>
  by (auto simp add: is_process_def FAILURES_def DIVERGENCES_def
      intro: is_process\<^sub>T_1 is_process\<^sub>T_2 is_process\<^sub>T_3)
    (meson is_process\<^sub>T_4)



lemma F_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T :
  \<open>\<F> (process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T T) = {(s, X). s \<in> \<T>\<^sub>T T \<and> X \<subseteq> - {e. s @ [e] \<in> \<T>\<^sub>T T}}\<close>
  and D_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T :
  \<open>\<D> (process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T T) = {}\<close>
  and T_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T :
  \<open>\<T> (process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T T) = \<T>\<^sub>T T\<close>
  by (simp_all add: Failures_def FAILURES_def Divergences_def DIVERGENCES_def
      Traces_def TRACES_def process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T.rep_eq) blast

lemmas process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T_projs = F_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T
  D_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T T_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T


subsubsection \<open>Now the big results\<close>

lemma bij_betw_det :
  \<open>bij_betw process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T UNIV {P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k. determ P}\<close>
  (is \<open>bij_betw process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T ?S1 ?S2\<close>)
proof (intro bij_betw_imageI)
  show \<open>inj_on process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T ?S1\<close>
    by (rule inj_onI) (auto simp add: Process_eq_spec process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T_projs Process\<^sub>T_eq_spec)
next
  show \<open>process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T ` ?S1 = ?S2\<close>
  proof (intro subset_antisym subsetI; clarify)
    show \<open>determ (process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T P)\<close> for P :: \<open>('a, 'r) process\<^sub>T\<close>
      by (rule deterministicI) (simp add: process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T_projs)
  next
    fix P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    assume det : \<open>deterministic P\<close>
    hence * : \<open>Rep_process\<^sub>T (Abs_process\<^sub>T (\<T> P)) = \<T> P\<close>
      by (intro Abs_process\<^sub>T_inverse)
        (simp add: deterministic_def is_process\<^sub>T_def is_processT2_TR,
          metis T_F_spec is_processT3 is_processT6_notin singletonD)
    show \<open>P \<in> process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T ` ?S1\<close>
    proof (subst image_iff, rule bexI)
      show \<open>P = process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T (Abs_process\<^sub>T (\<T> P))\<close>
        by (auto intro!: Process_eq_optimizedI simp add: process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T_projs
            Traces\<^sub>T_def "*" det deterministic_div_free subset_iff F_T)
          (meson det deterministic_def empty_subsetI insert_subset is_processT,
            use is_processT5_S7 in blast) 
    next
      show \<open>Abs_process\<^sub>T (\<T> P) \<in> ?S1\<close> by (simp add: Traces\<^sub>T_def "*")
    qed
  qed
qed



lemma SKIPS_is_GlobalDet_SKIP : \<open>SKIPS R = \<box>r \<in> R. SKIP r\<close>
  by (auto simp add: Process_eq_spec SKIPS_projs GlobalDet_projs SKIP_projs)

lemma SKIP_Ndet_SKIP_is_SKIP_Det_SKIP : \<open>SKIP r \<sqinter> SKIP s = SKIP r \<box> SKIP s\<close>
  by (auto simp add: Process_eq_spec Det_projs Ndet_projs SKIP_projs)


theorem P_FD_some_det :
  \<comment> \<open>In the generalization, since several terminations may occur after
      the same trace in the initial process, we have to specify a choice.\<close>
  fixes termination_choice :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'r\<close>
  assumes \<open>\<And>t. \<exists>r. t @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> termination_choice t \<in> {r. t @ [\<checkmark>(r)] \<in> \<T> P}\<close>
  defines \<open>T \<equiv> {t \<in> \<T> P. \<forall>t' < t. (\<exists>r. t' @ [\<checkmark>(r)] \<in> \<T> P) \<longrightarrow> t = t' @ [\<checkmark>(termination_choice t')]}\<close>
  shows \<open>P \<sqsubseteq>\<^sub>F\<^sub>D process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T (Abs_process\<^sub>T T)\<close>
proof (unfold failure_divergence_refine_def failure_refine_def divergence_refine_def, intro conjI)
  show \<open>\<D> (process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T (Abs_process\<^sub>T T)) \<subseteq> \<D> P\<close> by (simp add: D_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T)
next
  have * : \<open>T \<in> {T. is_process\<^sub>T T}\<close>
    by (auto simp add: T_def is_process\<^sub>T_def T_imp_front_tickFree intro: is_processT3_TR_append)
      (metis prefix_prefix append_eq_first_pref_spec less_list_def nless_le self_append_conv,
        metis less_self)

  show \<open>\<F> (process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T (Abs_process\<^sub>T T)) \<subseteq> \<F> P\<close>
  proof safe
    fix s X assume \<open>(s, X) \<in> \<F> (process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T (Abs_process\<^sub>T T))\<close>
    hence \<open>s \<in> \<T> P\<close>
      by (simp add: F_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T Traces\<^sub>T_def Abs_process\<^sub>T_inverse[OF "*"]) (simp add: T_def)
    show \<open>(s, X) \<in> \<F> P\<close>
    proof (cases \<open>\<exists>r. s @ [\<checkmark>(r)] \<in> \<T> P\<close>)
      assume \<open>\<exists>r. s @ [\<checkmark>(r)] \<in> \<T> P\<close>
      hence \<open>s @ [\<checkmark>(termination_choice s)] \<in> \<T> P\<close> by (metis assms(1) mem_Collect_eq)
      with \<open>(s, X) \<in> \<F> (process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T (Abs_process\<^sub>T T))\<close> have \<open>\<checkmark>(termination_choice s) \<notin> X\<close>
        unfolding F_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T Traces\<^sub>T.abs_eq Abs_process\<^sub>T_inverse[OF "*"]
        by (simp add: subset_iff T_def)
          (metis prefix_snoc append_T_imp_tickFree nless_le
            non_tickFree_tick not_Cons_self2 tickFree_append_iff)
      with \<open>s @ [\<checkmark>(termination_choice s)] \<in> \<T> P\<close> show \<open>(s, X) \<in> \<F> P\<close>
        by (metis  is_processT6_TR_notin)
    next
      assume \<open>\<nexists>r. s @ [\<checkmark>(r)] \<in> \<T> P\<close>
      with \<open>(s, X) \<in> \<F> (process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T (Abs_process\<^sub>T T))\<close> have \<open>X \<subseteq> - {e. s @ [e] \<in> \<T> P}\<close>
        unfolding F_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T Traces\<^sub>T.abs_eq Abs_process\<^sub>T_inverse[OF "*"]
        by (simp add: subset_iff T_def)
          (metis prefix_snoc append_T_imp_tickFree nless_le
            non_tickFree_tick not_Cons_self2 tickFree_append_iff)
      with is_processT5_S7[OF \<open>s \<in> \<T> P\<close>] show \<open>(s, X) \<in> \<F> P\<close> by blast
    qed
  qed
qed



theorem deterministic_iff_maximal_for_leFD:
  \<open>determ P \<longleftrightarrow> (\<forall>Q. P \<sqsubseteq>\<^sub>F\<^sub>D Q \<longrightarrow> P = Q)\<close> for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  \<comment> \<open>see TPC, chapter 9)\<close>
proof (intro iffI allI impI)
  fix Q assume \<open>determ P\<close> and \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  from \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close> have no_div : \<open>\<D> P = {}\<close> \<open>\<D> Q = {}\<close> and F_subset : \<open>\<F> Q \<subseteq> \<F> P\<close>
    by (simp_all add: \<open>determ P\<close> deterministic_div_free refine_defs)

  have same_T : \<open>\<T> P = \<T> Q\<close>
  proof (rule subset_antisym)
    show \<open>\<T> P \<subseteq> \<T> Q\<close>
    proof (rule ccontr)
      assume \<open>\<not> \<T> P \<subseteq> \<T> Q\<close>
      then obtain s e where * : \<open>s @ [e] \<in> min_elems (\<T> P - \<T> Q)\<close>
        by (metis DiffD2 Diff_eq_empty_iff Nil_elem_T elem_min_elems min_elems4 rev_exhaust)
      hence \<open>s \<in> \<T> Q\<close> unfolding min_elems_def 
        by simp (metis DiffI T_F_spec is_processT3 less_self)
      with "*" have \<open>(s, {e}) \<in> \<F> Q\<close> 
        by (metis Diff_iff elem_min_elems is_processT5_S7 singletonD)
      from set_mp[OF F_subset this] have \<open>(s, {e}) \<in> \<F> P\<close> .
      moreover have \<open>(s, {e}) \<notin> \<F> P\<close> by (metis "*" Diff_iff \<open>determ P\<close> deterministicD elem_min_elems)
      ultimately show False by blast
    qed
  next
    show \<open>\<T> Q \<subseteq> \<T> P\<close> by (simp add: F_subset F_subset_imp_T_subset)
  qed

  have same_F : \<open>\<F> P = \<F> Q\<close>
  proof (rule subset_antisym)
    show \<open>\<F> P \<subseteq> \<F> Q\<close>
    proof (rule ccontr)
      assume \<open>\<not> \<F> P \<subseteq> \<F> Q\<close>
      then obtain s X where * : \<open>(s, X) \<in> \<F> P - \<F> Q\<close> \<open>X \<noteq> {}\<close> 
        by (metis DiffI T_F_spec same_T subrelI)

      have \<open>e \<in> X \<Longrightarrow> s @ [e] \<notin> \<T> P\<close> for e
        by (metis "*"(1) DiffD1 \<open>determ P\<close> deterministicD insert_Diff insert_is_Un is_processT4 sup_ge1)
      thus False by (metis "*"(1) DiffE F_T is_processT5_S7 same_T)
    qed
  next
    show \<open>\<F> Q \<subseteq> \<F> P\<close> by (fact F_subset)
  qed
  show \<open>P = Q\<close> by (simp add: Process_eq_spec failure_refine_def divergence_refine_def no_div same_F)

next
  define termination_choice where \<open>termination_choice s \<equiv> (SOME r. s @ [\<checkmark>(r)] \<in> \<T> P)\<close> for s
  have $ : \<open>\<exists>r. s @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> termination_choice s \<in> {r. s @ [\<checkmark>(r)] \<in> \<T> P}\<close> for s
    by (simp add: termination_choice_def) (meson someI)

  define T where \<open>T \<equiv> {s \<in> \<T> P. \<forall>s' < s. (\<exists>r. s' @ [\<checkmark>(r)] \<in> \<T> P) \<longrightarrow> s = s' @ [\<checkmark>(termination_choice s')]}\<close>
  have * : \<open>T \<in> {T. is_process\<^sub>T T}\<close>
    by (auto simp add: T_def is_process\<^sub>T_def T_imp_front_tickFree intro: is_processT3_TR_append)
      (metis prefix_prefix append_eq_first_pref_spec less_list_def nless_le self_append_conv,
        metis less_self)
  assume maximal : \<open>\<forall>Q. P \<sqsubseteq>\<^sub>F\<^sub>D Q \<longrightarrow> P = Q\<close>
  with "$" P_FD_some_det T_def have \<open>P = process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_of_process\<^sub>T (Abs_process\<^sub>T T)\<close> by blast
  moreover have \<open>Abs_process\<^sub>T T \<in> {P. \<forall>s r e. s @ [\<checkmark>(r)] \<in> \<T>\<^sub>T P \<longrightarrow> e \<noteq> \<checkmark>(r) \<longrightarrow> s @ [e] \<notin> \<T>\<^sub>T P}\<close>
    by (simp add: Traces\<^sub>T_def Abs_process\<^sub>T_inverse[OF "*"])
      (metis "*" is_process\<^sub>T_def mem_Collect_eq)
  ultimately show \<open>determ P\<close> using bij_betwE[OF bij_betw_det] by blast
qed


lemma \<open>determ P \<Longrightarrow> X \<in> \<R> P \<Longrightarrow> X \<subseteq> - P\<^sup>0\<close>
  unfolding deterministic_def Refusals_iff initials_def
  by auto (metis insert_Diff insert_is_Un process_charn self_append_conv2 sup_ge1)




text \<open>We have the immediate powerful corollaries.\<close>

corollary (in After) deterministic_process_eq_SKIPS_Det_Mprefix_After :
  \<open>determ P \<Longrightarrow> P = SKIPS {r. \<checkmark>(r) \<in> P\<^sup>0} \<box> (\<box>a \<in> {a. ev a \<in> P\<^sup>0} \<rightarrow> P after a)\<close>
  by (simp add: deterministic_iff_maximal_for_leFD leFD_SKIPS_Det_Mprefix_After)


lemma deterministic_imp_initial_tick_iff_eq_SKIP [simp] :
  \<open>determ P \<Longrightarrow> \<checkmark>(r) \<in> P\<^sup>0 \<longleftrightarrow> P = SKIP r\<close>
  by (meson deterministic_iff_maximal_for_leFD dual_order.refl initial_tick_iff_FD_SKIP)


lemma deterministic_imp_constraints_on_initials :
  \<open>determ P \<Longrightarrow> P\<^sup>0 = {} \<or> {a. ev a \<in> P\<^sup>0} = {} \<and> (\<exists>r. P\<^sup>0 = {\<checkmark>(r)}) \<or>
                {a. ev a \<in> P\<^sup>0} \<noteq> {} \<and> {r. \<checkmark>(r) \<in> P\<^sup>0} = {}\<close>
  by auto (metis deterministic_imp_initial_tick_iff_eq_SKIP event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust initials_SKIP)


corollary (in After) deterministic_process_eq_SKIP_or_Mprefix_After :
  \<open>determ P \<Longrightarrow> P = (if \<exists>r. \<checkmark>(r) \<in> P\<^sup>0 then SKIP (THE r. P\<^sup>0 = {\<checkmark>(r)})
                     else \<box>a \<in> {a. ev a \<in> P\<^sup>0} \<rightarrow> P after a)\<close>
  by (subst deterministic_process_eq_SKIPS_Det_Mprefix_After)
    (auto simp add: inj_on_eq_iff[OF inj_SKIP])



subsection \<open>Characterization with After\<close>

lemma (in AfterExt) deterministic_iff_accepts_initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e:
  \<open>determ P \<longleftrightarrow> (\<forall>t \<in> \<T> P. tF t \<longrightarrow> determ\<^sup>0 (P after\<^sub>\<T> t))\<close>
proof (intro iffI ballI impI)
  show \<open>determ P \<Longrightarrow> t \<in> \<T> P \<Longrightarrow> tF t \<Longrightarrow> determ\<^sup>0 (P after\<^sub>\<T> t)\<close> for t
    by (rule accepts_initialsI)
      (simp add: initials_def Refusals_iff T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq F_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq deterministic_def)
next
  show \<open>determ P\<close> if \<open>\<forall>t\<in>\<T> P. tF t \<longrightarrow> determ\<^sup>0 (P after\<^sub>\<T> t)\<close>
  proof (rule deterministicI)
    fix t e assume \<open>t @ [e] \<in> \<T> P\<close>
    have \<open>t \<in> \<T> P\<close> and \<open>tF t\<close>
      by (meson prefixI \<open>t @ [e] \<in> \<T> P\<close> is_processT3_TR)
        (use \<open>t @ [e] \<in> \<T> P\<close> append_T_imp_tickFree in blast)
    with \<open>t \<in> \<T> P\<close> that[rule_format, OF this] show \<open>t @ [e] \<in> \<T> P \<Longrightarrow> (t, {e}) \<notin> \<F> P\<close>
      by (simp add: accepts_initials_def Refusals_iff initials_def T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq F_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq)
  qed
qed



subsection \<open>Operators preserving Determinism\<close>

lemma deterministic_Mprefix_iff :
  \<open>determ (\<box>a \<in> A \<rightarrow> P a) \<longleftrightarrow> (\<forall>a \<in> A. determ (P a))\<close>
  by (auto simp add: deterministic_def Mprefix_projs) (metis append_Cons)

corollary deterministic_write0_iff : \<open>determ (a \<rightarrow> P) \<longleftrightarrow> determ P\<close>
  unfolding write0_def by (simp add: deterministic_Mprefix_iff)

corollary deterministic_write_iff  : \<open>determ (c\<^bold>!a \<rightarrow> P) \<longleftrightarrow> determ P\<close>
  unfolding write_def by (simp add: deterministic_Mprefix_iff)

corollary deterministic_inj_on_read_iff :
  \<open>inj_on c A \<Longrightarrow> determ (c\<^bold>?a \<in> A \<rightarrow> P a) \<longleftrightarrow> (\<forall>a \<in> A. determ (P a))\<close>
  unfolding read_def by (simp add: deterministic_Mprefix_iff)



lemma deterministic_inj_Renaming :
  \<open>determ (Renaming P f g)\<close> if \<open>inj f\<close> \<open>inj g\<close> \<open>determ P\<close>
proof (rule deterministicI)
  have $ : \<open>inj (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close> by (simp add: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inj_map that(1,2))
  fix t e
  assume \<open>t @ [e] \<in> \<T> (Renaming P f g)\<close>
  then obtain t1 where * : \<open>t1 \<in> \<T> P\<close> \<open>t @ [e] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1\<close>
    by (simp add: T_Renaming deterministic_div_free[OF \<open>determ P\<close>]) blast
  have \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` {e}) \<in> \<F> P \<Longrightarrow> t \<noteq> map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close> for s1 
  proof (rule ccontr, clarify)
    assume assms : \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` {e}) \<in> \<F> P\<close> \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close> 
    from assms(2) "*"(2) have \<open>t1 = s1 @ [inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) e]\<close>
      by (cases t1 rule: rev_cases; simp)
        (metis (mono_tags, opaque_lifting) "$" inj_map_eq_map inv_f_f)
    from deterministicD[OF \<open>deterministic P\<close> "*"(1)[unfolded this]]
    have \<open>(s1, {inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) e}) \<notin> \<F> P\<close> .
    also have \<open>{inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) e} = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` {e}\<close>
      using inj_vimage_singleton[OF "$", of e] "*"(2)
        \<open>t1 = s1 @ [inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) e]\<close> by (auto simp add: "$")
    finally have \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` {e}) \<notin> \<F> P\<close> .
    with assms(1) show False by simp
  qed
  thus \<open>(t, {e}) \<notin> \<F> (Renaming P f g)\<close>
    by (auto simp add: F_Renaming deterministic_div_free[OF \<open>determ P\<close>])
qed

lemma deterministic_bij_Renaming_iff :
  \<open>determ (Renaming P f g) \<longleftrightarrow> determ P\<close> if \<open>bij f\<close> and \<open>bij g\<close>
proof (rule iffI)
  show \<open>determ (Renaming P f g) \<Longrightarrow> determ P\<close>
    by (metis Renaming_inv bij_betw_def deterministic_iff_maximal_for_leFD
        mono_Renaming_FD \<open>bij f\<close> \<open>bij g\<close>)
next
  show \<open>determ P \<Longrightarrow> determ (Renaming P f g)\<close>
    by (simp add: bij_is_inj deterministic_inj_Renaming \<open>bij f\<close> \<open>bij g\<close>)
qed



lemma deterministic_Throw : \<open>determ (P \<Theta> a \<in> A. Q a)\<close>
  if \<open>determ P\<close> \<open>\<And>a. a \<in> A \<Longrightarrow> a \<in> \<alpha>(P) \<Longrightarrow> determ (Q a)\<close>
proof (subst Throw_is_restrictable_on_events_of)
  show \<open>determ (Throw P (A \<inter> \<alpha>(P)) Q)\<close>
  proof (rule deterministicI)
    fix t e assume \<open>t @ [e] \<in> \<T> (P \<Theta> a \<in> (A \<inter> \<alpha>(P)). Q a)\<close>
    moreover from \<open>determ P\<close> have \<open>\<D> P = {}\<close>
      by (simp add: deterministic_div_free)
    ultimately consider
      (traceL) \<open>t @ [e] \<in> \<T> P\<close> \<open>e \<notin> ev ` (A \<inter> \<alpha>(P))\<close> \<open>set t \<inter> ev ` (A \<inter> \<alpha>(P)) = {}\<close>
      | (traceR) t1 a t2 where \<open>t @ [e] = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
        \<open>set t1 \<inter> ev ` (A \<inter> \<alpha>(P)) = {}\<close> \<open>a \<in> A\<close> \<open>a \<in> \<alpha>(P)\<close> \<open>t2 \<in> \<T> (Q a)\<close>
      unfolding T_Throw by auto
    thus \<open>(t, {e}) \<notin> \<F> (P \<Theta> a \<in> (A \<inter> \<alpha>(P)). Q a)\<close>
    proof cases
      case traceL
      from traceL(1) \<open>determ P\<close> have \<open>(t, {e}) \<notin> \<F> P\<close>
        by (simp add: deterministicD)
      with traceL(3) show \<open>(t, {e}) \<notin> \<F> (P \<Theta> a \<in> (A \<inter> \<alpha>(P)). Q a)\<close>
        by (auto simp add: F_Throw \<open>\<D> P = {}\<close>)
    next
      case traceR
      from traceR(1) consider \<open>t2 = []\<close> \<open>t = t1\<close> \<open>e = ev a\<close>
        | t2' where \<open>t2 = t2' @ [e]\<close> \<open>t = t1 @ ev a # t2'\<close>
        by (cases t2 rule: rev_cases) simp_all
      thus \<open>(t, {e}) \<notin> \<F> (P \<Theta> a \<in> (A \<inter> \<alpha>(P)). Q a)\<close>
      proof cases
        assume \<open>t2 = []\<close> \<open>t = t1\<close> \<open>e = ev a\<close>
        from \<open>determ P\<close> traceR(2) have \<open>(t1, {ev a}) \<notin> \<F> P\<close>
          by (simp add: deterministicD)
        with traceR(3) show \<open>(t, {e}) \<notin> \<F> (P \<Theta> a \<in> (A \<inter> \<alpha>(P)). Q a)\<close>
          by (auto simp add: \<open>t = t1\<close> \<open>e = ev a\<close> \<open>\<D> P = {}\<close> F_Throw)
      next
        fix t2' assume \<open>t2 = t2' @ [e]\<close> \<open>t = t1 @ ev a # t2'\<close>
        from traceR(4, 5) have \<open>determ (Q a)\<close>
          by (rule \<open>\<And>a. a \<in> A \<Longrightarrow> a \<in> \<alpha>(P) \<Longrightarrow> determ (Q a)\<close>)
        with \<open>t2 = t2' @ [e]\<close> have \<open>(t2', {e}) \<notin> \<F> (Q a)\<close>
          using traceR(6) by (simp add: deterministicD)
        with traceR(3-5) show \<open>(t, {e}) \<notin> \<F> (P \<Theta> a \<in> (A \<inter> \<alpha>(P)). Q a)\<close>
          by (simp add: \<open>t = t1 @ ev a # t2'\<close> \<open>\<D> P = {}\<close> F_Throw Throw_T_third_clause_breaker)
      qed
    qed
  qed
qed



lemma T_snoc_tick_imp_no_continuation_if_deterministic : 
  \<open>u = [] \<and> e = \<checkmark>(r)\<close> if \<open>determ P\<close> \<open>t @ u @ [e] \<in> \<T> P\<close> \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close>
proof -
  have * : \<open>t @ [e] \<in> \<T> P \<Longrightarrow> e = \<checkmark>(r)\<close> for e
    by (metis deterministicD is_processT6_TR_notin singletonD that(1, 3))
  show \<open>u = [] \<and> e = \<checkmark>(r)\<close>
  proof (cases u)
    from "*" that(2) show \<open>u = [] \<Longrightarrow> u = [] \<and> e = \<checkmark>(r)\<close> by auto
  next
    fix e' u'
    assume \<open>u = e' # u'\<close>
    with that(2) have \<open>t @ [e'] \<in> \<T> P\<close>
      by simp (metis F_T T_F append.assoc append_Cons append_Nil is_processT3)
    hence False
      by (metis "*" T_imp_front_tickFree \<open>u = e' # u'\<close> event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) front_tickFree_append_iff
          not_Cons_self snoc_eq_iff_butlast that(2) tickFree_Cons_iff)
    thus \<open>u = [] \<and> e = \<checkmark>(r)\<close> by simp
  qed
qed

lemma T_snoc_ev_imp_no_tick_continuation_if_deterministic : 
  \<open>u \<noteq> [] \<and> is_ev (hd u) \<or> is_ev e\<close> if \<open>determ P\<close> \<open>t @ u @ [e] \<in> \<T> P\<close> \<open>t @ [ev a] \<in> \<T> P\<close>
proof -
  have \<open>t @ [e] \<in> \<T> P \<Longrightarrow> is_ev e\<close> for e
    by (metis T_snoc_tick_imp_no_continuation_if_deterministic append.left_neutral
        event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.discI(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust that(1,3))
  thus \<open>u \<noteq> [] \<and> is_ev (hd u) \<or> is_ev e\<close>
    by (metis T_imp_front_tickFree append_eq_appendI front_tickFree_append_iff
        list.exhaust_sel not_Cons_self snoc_eq_iff_butlast that(2) tickFree_Cons_iff)
qed



lemma deterministic_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>determ (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
  if \<open>determ P\<close> \<open>\<And>r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> determ (Q r)\<close>
proof (rule deterministicI)
  fix t e assume \<open>t @ [e] \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
  moreover from \<open>determ P\<close> have \<open>\<D> P = {}\<close>
    by (simp add: deterministic_div_free)
  ultimately consider a u where \<open>e = ev a\<close> \<open>t = map (ev \<circ> of_ev) u\<close> \<open>u @ [ev a] \<in> \<T> P\<close> \<open>tF u\<close>
    | u v r where \<open>t @ [e] = map (ev \<circ> of_ev) u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF u\<close> \<open>v \<in> \<T> (Q r)\<close> \<open>v \<noteq> []\<close>
    by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs append_eq_map_conv append_eq_append_conv2 Cons_eq_append_conv)
      (metis Nil_is_append_conv append.right_neutral append_Nil not_Cons_self, blast,
        metis Cons_eq_appendI append_eq_appendI eq_Nil_appendI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) is_processT3_TR_append)
  thus \<open>(t, {e}) \<notin> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
  proof cases
    show \<open>e = ev a \<Longrightarrow> t = map (ev \<circ> of_ev) u \<Longrightarrow> u @ [ev a] \<in> \<T> P \<Longrightarrow> tF u \<Longrightarrow> (t, {e}) \<notin> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> for a u
      by (auto simp add: tickFree_map_ev_of_ev_inj \<open>\<D> P = {}\<close> Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def map_eq_append_conv)
        (meson deterministicD empty_subsetI insertI1 insert_subset is_processT4 \<open>determ P\<close>,
          meson T_snoc_tick_imp_no_continuation_if_deterministic event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) \<open>determ P\<close>)
  next
    fix u v r assume \<open>t @ [e] = map (ev \<circ> of_ev) u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF u\<close> \<open>v \<in> \<T> (Q r)\<close> \<open>v \<noteq> []\<close>
    from this(1, 5) obtain v' where \<open>v = v' @ [e]\<close> \<open>t = map (ev \<circ> of_ev) u @ v'\<close>
      by (cases v rule: rev_cases) simp_all
    from \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> T_snoc_tick_imp_no_continuation_if_deterministic[OF \<open>determ P\<close>]
    have * : \<open>map (ev \<circ> of_ev) u @ v' = map (ev \<circ> of_ev) w @ x \<and> w @ [\<checkmark>(s)] \<in> \<T> P \<Longrightarrow> w = u \<and> s = r\<close> for w x s
      by (auto simp add: append_eq_append_conv2 map_eq_append_conv append_eq_map_conv append_T_imp_tickFree
                  dest!: tickFree_map_ev_of_ev_inj[THEN iffD1, rotated 2]) blast+
    have \<open>determ (Q r)\<close>
      by (metis \<open>\<D> P = {}\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> empty_iff strict_ticks_of_memI that(2))
    with \<open>v = v' @ [e]\<close> \<open>v \<in> \<T> (Q r)\<close>
    have \<open>(v', {e}) \<notin> \<F> (Q r)\<close> by (simp add: deterministicD)
    { fix v'' assume \<open>(u @ v'', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k {e}) \<in> \<F> P\<close> \<open>tF v''\<close> \<open>v' = map (ev \<circ> of_ev) v''\<close>
      have \<open>v'' = []\<close>
        by (metis F_T F_imp_front_tickFree T_snoc_tick_imp_no_continuation_if_deterministic \<open>(u @ v'', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k {e}) \<in> \<F> P\<close>
            \<open>tF v''\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> front_tickFree_charn front_tickFree_nonempty_append_imp non_tickFree_tick \<open>determ P\<close>)
      with \<open>(u @ v'', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k {e}) \<in> \<F> P\<close> have \<open>(u, {\<checkmark>(r)}) \<in> \<F> P\<close>
        by (simp add: ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
          (meson UNIV_I UnCI empty_subsetI insert_subset is_processT4 rev_image_eqI)
      hence False by (simp add: \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> deterministicD \<open>determ P\<close>)
    }
    with "*" \<open>(v', {e}) \<notin> \<F> (Q r)\<close> show \<open>(t, {e}) \<notin> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs \<open>\<D> P = {}\<close> \<open>t = map (ev \<circ> of_ev) u @ v'\<close> append_eq_map_conv \<open>tF u\<close>
                        dest!: tickFree_map_ev_of_ev_inj[THEN iffD1, rotated 2])+
  qed
qed


corollary deterministic_Seq : \<open>determ P \<Longrightarrow> determ Q \<Longrightarrow> determ (P \<^bold>; Q)\<close>
  by (metis Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_const deterministic_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)




lemma (in After) initial_imp_deterministic_After:
  \<open>ev e \<in> P\<^sup>0 \<Longrightarrow> determ P \<Longrightarrow> determ (P after e)\<close>
  unfolding deterministic_def by (simp add: After_projs)

lemma (in AfterExt) initial_imp_deterministic_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>e \<in> P\<^sup>0 \<Longrightarrow> (case e of \<checkmark>(r) \<Rightarrow> determ (\<Omega> P r)) \<Longrightarrow>
   determ P \<Longrightarrow> determ (P after\<^sub>\<checkmark> e)\<close>
  unfolding deterministic_def by (cases e) (simp_all add: T_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k F_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k)



subsection \<open>Operators not (always) preserving Determinism\<close>


lemma deterministic_imp_accepts_initials : \<open>determ P \<Longrightarrow> determ\<^sup>0 P\<close>
  by (simp add: Refusals_iff accepts_initials_def deterministic_def initials_def)

corollary deterministic_SKIPS_iff : \<open>determ (SKIPS R) \<longleftrightarrow> R = {} \<or> (\<exists>r. R = {r})\<close>
  by (metis SKIPS_empty SKIPS_singl_is_SKIP accepts_initials_SKIPS_iff
      deterministic_SKIP deterministic_STOP deterministic_imp_accepts_initials)




lemma deterministic_Det: 
  \<open>determ P \<Longrightarrow> determ Q \<Longrightarrow>
   range tick \<inter> P\<^sup>0 \<inter> Q\<^sup>0 \<noteq> {} \<or> P\<^sup>0 \<inter> Q\<^sup>0 = {} \<and> range tick \<inter> (P\<^sup>0 \<union> Q\<^sup>0) = {} \<Longrightarrow> determ (P \<box> Q)\<close>
proof (elim disjE conjE)
  show \<open>determ P \<Longrightarrow> determ Q \<Longrightarrow> range tick \<inter> P\<^sup>0 \<inter> Q\<^sup>0 \<noteq> {} \<Longrightarrow> determ (P \<box> Q)\<close>
    by (auto simp add: deterministic_def Det_projs SKIP_projs)
next
  show \<open>\<lbrakk>determ P; determ Q; P\<^sup>0 \<inter> Q\<^sup>0 = {}; range tick \<inter> (P\<^sup>0 \<union> Q\<^sup>0) = {}\<rbrakk> \<Longrightarrow> determ (P \<box> Q)\<close>
    by (auto simp add: deterministic_def Det_projs disjoint_iff deterministic_div_free initials_def)
      (metis F_T append_Cons append_Nil is_processT3_TR_append neq_Nil_conv)+
qed




section \<open>Application to Operational Semantics\<close>


lemma (in OpSemFD) tickFree_trace_trans_preserves_deterministic:
  \<open>(P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<^sub>F\<^sub>D\<leadsto>\<^sup>* t Q \<Longrightarrow> tF t \<Longrightarrow> deterministic P \<Longrightarrow> deterministic Q\<close>
proof (induct rule: trace_trans.induct)
  show \<open>P \<^sub>F\<^sub>D\<leadsto>\<^sub>\<tau> P' \<Longrightarrow> deterministic P \<Longrightarrow> deterministic P'\<close> for P P' :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    using deterministic_iff_maximal_for_leFD by blast
next
  show \<open>tF [\<checkmark>(r)] \<Longrightarrow> deterministic P\<close>
    for r :: \<open>'r\<close> and P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> by simp
next
  fix a P P' and t :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and P'' :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assume \<open>P \<^sub>F\<^sub>D\<leadsto>\<^bsub>a\<^esub> P'\<close> \<open>tF (ev a # t)\<close> \<open>deterministic P\<close>
    \<open>tF t \<Longrightarrow> deterministic P' \<Longrightarrow> deterministic P''\<close>
  from \<open>P \<^sub>F\<^sub>D\<leadsto>\<^bsub>a\<^esub> P'\<close> \<open>deterministic P\<close> have \<open>deterministic P'\<close>
    using deterministic_iff_maximal_for_leFD ev_trans_is initial_imp_deterministic_After by blast
  with \<open>tF t \<Longrightarrow> deterministic P' \<Longrightarrow> deterministic P''\<close> \<open>tickFree (ev a # t)\<close>
  show \<open>deterministic P''\<close> by simp
qed

lemma deterministic_imp_Refusals_iff: \<open>deterministic P \<Longrightarrow> X \<in> \<R> P \<longleftrightarrow> X \<inter> P\<^sup>0 = {}\<close>
  by (auto simp add: Refusals_iff initials_def deterministic_def disjoint_iff)
    (metis append_Nil empty_subsetI insert_subset process_charn,
      metis Nil_elem_T append_Nil is_processT5_S7)


lemma (in OpSemFD) deterministic_F_trace_trans_reality_check:
  \<open>deterministic P \<Longrightarrow> tF t \<Longrightarrow>
   (t, X) \<in> \<F> (P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<longleftrightarrow> (\<exists>Q. (P \<^sub>F\<^sub>D\<leadsto>\<^sup>*t Q) \<and> X \<inter> Q\<^sup>0 = {})\<close>
  by (simp add: F_trace_trans_reality_check)
    (metis deterministic_imp_Refusals_iff tickFree_trace_trans_preserves_deterministic)



lemma \<open>\<not> deterministic ((a \<rightarrow> SKIP undefined) \<box> SKIP undefined)\<close>
  by (metis Det_commute FD_iff_eq_Ndet Sliding_SKIP Sliding_def Un_insert_right initials_write0 insertI1
      singletonD deterministic_iff_maximal_for_leFD event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(4) initials_Det initials_SKIP)


(*<*)
end
  (*>*)
