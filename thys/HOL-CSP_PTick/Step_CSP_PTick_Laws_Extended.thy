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
theory Step_CSP_PTick_Laws_Extended
  imports Basic_CSP_PTick_Laws Step_CSP_PTick_Laws
    Non_Deterministic_CSP_PTick_Distributivity
begin
  (*>*)

unbundle option_type_syntax


section \<open>Extended step Laws\<close>

subsection \<open>Sequential Composition\<close>

lemma Mndetprefix_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k: \<open>\<sqinter>a \<in> A \<rightarrow> P a \<^bold>;\<^sub>\<checkmark> Q = \<sqinter>a \<in> A \<rightarrow> (P a \<^bold>;\<^sub>\<checkmark> Q)\<close>
  by (auto simp add: Mndetprefix_GlobalNdet Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right
      write0_def Mprefix_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k intro: mono_GlobalNdet_eq)


subsection \<open>Synchronization Product\<close>

subsubsection \<open>Behaviour of \<^const>\<open>SKIPS\<close>\<close>

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) SKIPS_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS :
  \<open>SKIPS R \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIPS S = \<sqinter>(r, s) \<in> R \<times> S. (case r \<otimes>\<checkmark> s of \<lfloor>r_s\<rfloor> \<Rightarrow> SKIP r_s | \<diamond> \<Rightarrow> STOP)\<close>
  by (simp add: SKIPS_def Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right)
    (simp add: GlobalNdet_cartprod[of R S \<open>\<lambda>r s. case r \<otimes>\<checkmark> s of \<diamond> \<Rightarrow> STOP | \<lfloor>r_s\<rfloor> \<Rightarrow> SKIP r_s\<close>]
      GlobalNdet_sets_commute[of R S \<open>\<lambda>r s. case r \<otimes>\<checkmark> s of \<diamond> \<Rightarrow> STOP | \<lfloor>r_s\<rfloor> \<Rightarrow> SKIP r_s\<close>])


text \<open>In order for the right-hand side to be rewritten as a SKIPS, an assumption is required:
      the ticks involved must be able to be combined.\<close>

lemma GlobalNdet_prod_SKIP_is_SKIPS :
  \<open>\<sqinter>(r, s) \<in> R \<times> S. SKIP \<lceil>tick_join r s\<rceil> =
   SKIPS ((the \<circ> (\<lambda>(r, s). tick_join r s)) ` (R \<times> S))\<close>
  by (simp add: SKIPS_def mono_GlobalNdet_eq2 split_def)


lemma GlobalNdet_prod_case_SKIP_STOP_is_GlobalNdet_prod_SKIP_iff :
  \<open>\<sqinter>(r, s) \<in> R \<times> S. (case tick_join r s of \<diamond> \<Rightarrow> STOP | \<lfloor>r_s\<rfloor> \<Rightarrow> SKIP r_s) =
   \<sqinter>(r, s) \<in> R \<times> S. SKIP \<lceil>tick_join r s\<rceil>
   \<longleftrightarrow> (\<forall>r s. r \<in> R \<longrightarrow> s \<in> S \<longrightarrow> tick_join r s \<noteq> \<diamond>)\<close>
  (is \<open>?lhs1 = ?lhs2 \<longleftrightarrow> ?rhs\<close>)
proof (rule iffI)
  show \<open>?rhs \<Longrightarrow> ?lhs1 = ?lhs2\<close>
    by (force intro: mono_GlobalNdet_eq)
next
  have \<open>UNIV \<in> \<R> ?lhs2 \<longleftrightarrow> R = {} \<or> S = {}\<close>
    by (simp add: Refusals_iff F_GlobalNdet F_SKIP)
  moreover have \<open>UNIV \<in> \<R> ?lhs1 \<longleftrightarrow> R = {} \<or> S = {} \<or> (\<exists>r s. r \<in> R \<and> s \<in> S \<and> tick_join r s = \<diamond>)\<close>
    by (auto simp add: Refusals_iff F_GlobalNdet F_SKIP F_STOP split: option.split)
  ultimately show \<open>?lhs1 = ?lhs2 \<Longrightarrow> ?rhs\<close> by (metis empty_iff)
qed

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) SKIPS_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS_bis :
  \<open>SKIPS R \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIPS S = SKIPS ((the \<circ> (\<lambda>(r, s). r \<otimes>\<checkmark> s)) ` (R \<times> S))\<close>
  if \<open>\<And>r s. r \<in> R \<Longrightarrow> s \<in> S \<Longrightarrow> r \<otimes>\<checkmark> s \<noteq> \<diamond>\<close>
  by (unfold SKIPS_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS, fold GlobalNdet_prod_SKIP_is_SKIPS)
    (simp add: SKIPS_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS GlobalNdet_prod_case_SKIP_STOP_is_GlobalNdet_prod_SKIP_iff that)


lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale)
  SKIPS_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP [simp] : \<open>SKIPS R \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> STOP = STOP\<close>
  and STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS [simp] : \<open>STOP \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIPS S = STOP\<close>
  by (fact SKIPS_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS[where S = \<open>{}\<close>, simplified]
      SKIPS_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS[where R = \<open>{}\<close>, simplified])+




subsubsection \<open>Derived step Laws with Non-Determinism\<close>

context Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale begin

lemma Mprefix_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix :
  \<open>\<box>a\<in>A \<rightarrow> P a |||\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b =
   (\<box>a\<in>A \<rightarrow> (P a |||\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b)) \<box> (\<box>b\<in>B \<rightarrow> (\<box>a \<in> A \<rightarrow> P a |||\<^sub>\<checkmark> Q b))\<close>
  by (fact Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix[where S = \<open>{}\<close>, simplified])

lemma Mprefix_Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix : \<open>\<box>a\<in>A \<rightarrow> P a ||\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b = \<box>x\<in>(A \<inter> B) \<rightarrow> (P x ||\<^sub>\<checkmark> Q x)\<close>
  by (fact Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix[where S = \<open>UNIV\<close>, simplified])

lemma Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_subset :
  \<open>\<lbrakk>A \<subseteq> S; B \<subseteq> S\<rbrakk> \<Longrightarrow> \<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b  = \<box>x\<in>(A \<inter> B) \<rightarrow> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)\<close>
  by (fact Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_bis[of \<open>{}\<close> S A \<open>{}\<close> B, simplified])

lemma Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_indep :
  \<open>\<lbrakk>A \<inter> S = {}; B \<inter> S = {}\<rbrakk> \<Longrightarrow>
   \<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b =
   (\<box>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b)) \<box> (\<box>b\<in>B \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b))\<close>
  by (fact Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_bis[of A S \<open>{}\<close> B \<open>{}\<close>, simplified])

lemma Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_left :
  \<open>\<lbrakk>A \<inter> S = {}; B \<subseteq> S\<rbrakk> \<Longrightarrow> \<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b = \<box>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b)\<close>
  by (fact Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_bis[of A S \<open>{}\<close> \<open>{}\<close> B, simplified])

lemma Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_right :
  \<open>\<lbrakk>A \<subseteq> S; B \<inter> S = {}\<rbrakk> \<Longrightarrow> \<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b = \<box>b\<in>B \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close>
  by (fact Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_bis[of \<open>{}\<close> S A B \<open>{}\<close>, simplified])


lemma Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP : \<open>\<box>a \<in> A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP = \<box>a \<in> (A - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)\<close>
  by (subst Mprefix_empty[symmetric], subst Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix, simp)

lemma STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix : \<open>STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b \<in> B \<rightarrow> Q b = \<box>b \<in> (B - S) \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close>
  by (subst Mprefix_empty[symmetric], subst Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix, simp)



paragraph \<open>Mixing deterministic and non deterministic prefix choices\<close>

lemma Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix :
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<box>b \<in> B \<rightarrow> Q b) =
   (  if A = {} then STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<box>b \<in> B \<rightarrow> Q b)
    else \<sqinter>a\<in>A. (if a \<in> S then STOP else (a \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<box>b \<in> B \<rightarrow> Q b)))) \<box>
                (\<box>b\<in>(B - S) \<rightarrow> ((a \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) \<box>
                (if a \<in> B \<inter> S then (a \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a)) else STOP))\<close>
  unfolding Mndetprefix_GlobalNdet Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right
    write0_def Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix
  by (auto simp add: Mprefix_singl insert_Diff_if Int_insert_left
      intro: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>])

lemma Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix :
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<sqinter>b \<in> B \<rightarrow> Q b) =
   (  if B = {} then (\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP
    else \<sqinter>b\<in>B. (if b \<in> S then STOP else (b \<rightarrow> ((\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b))) \<box>
                (\<box>a\<in>(A - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (b \<rightarrow> Q b))) \<box>
                (if b \<in> A \<inter> S then (b \<rightarrow> (P b \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) else STOP))\<close>
  unfolding Mndetprefix_GlobalNdet Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left
    write0_def Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix
  by (subst Det_commute)
    (auto simp add: Diff_triv Mprefix_singl Mprefix_is_STOP_iff disjoint_iff
      intro!: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>] split: if_split_asm)


text \<open>In particular, we can obtain the theorem for \<^const>\<open>Mndetprefix\<close> synchronized with \<^const>\<open>STOP\<close>.\<close>

lemma Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP :
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP =
   (  if A \<inter> S = {} then \<sqinter>a \<in> A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)
    else (\<sqinter>a \<in> (A - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)) \<sqinter> STOP)\<close>
  (is \<open>?lhs = (if A \<inter> S = {} then ?rhs1 else ?rhs2 \<sqinter> STOP)\<close>)
proof -
  have \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP =
        \<sqinter>a\<in>A. (if a \<in> S then STOP else (a \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)))\<close> (is \<open>?lhs = ?rhs'\<close>)
    by (subst Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix[where B = \<open>{}\<close>, simplified])
      (auto intro: mono_GlobalNdet_eq)
  also have \<open>?rhs' = (if A \<inter> S = {} then ?rhs1 else ?rhs2 \<sqinter> STOP)\<close>
  proof (split if_split, intro conjI impI)
    show \<open>A \<inter> S = {} \<Longrightarrow> ?rhs' = ?rhs1\<close>
      by (auto simp add: Mndetprefix_GlobalNdet intro!: mono_GlobalNdet_eq)
  next
    show \<open>?rhs' = ?rhs2 \<sqinter> STOP\<close> if \<open>A \<inter> S \<noteq> {}\<close>
    proof (cases \<open>A - S = {}\<close>)
      show \<open>?rhs' = ?rhs2 \<sqinter> STOP\<close> if \<open>A - S = {}\<close>
        by (simp add: \<open>A - S = {}\<close> GlobalNdet_is_STOP_iff)
          (use \<open>A - S = {}\<close> in blast)
    next
      show \<open>?rhs' = ?rhs2 \<sqinter> STOP\<close> if \<open>A - S \<noteq> {}\<close>
      proof (subst Int_Diff_Un[symmetric],
          subst GlobalNdet_factorization_union
          [OF \<open>A \<inter> S \<noteq> {}\<close> \<open>A - S \<noteq> {}\<close>, symmetric])
        have \<open>(\<sqinter>a\<in>(A \<inter> S). (if a \<in> S then STOP else (a \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP))))
              = STOP\<close> (is \<open>?fact1 = STOP\<close>)
          by (simp add: GlobalNdet_is_STOP_iff)
        moreover have \<open>(\<sqinter>a\<in>(A - S). (if a \<in> S then STOP else (a \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP))))
                       = ?rhs2\<close> (is \<open>?fact2 = ?rhs2\<close>)
          by (auto simp add: Mndetprefix_GlobalNdet intro: mono_GlobalNdet_eq)
        ultimately show \<open>?fact1 \<sqinter> ?fact2 = ?rhs2 \<sqinter> STOP\<close> by (metis Ndet_commute)
      qed
    qed
  qed
  finally show \<open>?lhs = (if A \<inter> S = {} then ?rhs1 else ?rhs2 \<sqinter> STOP)\<close> .
qed

lemma STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix :
  \<open>STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<sqinter>b \<in> B \<rightarrow> Q b)  =
   (  if B \<inter> S = {} then \<sqinter>b \<in> B \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)
    else (\<sqinter>b \<in> (B - S) \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) \<sqinter> STOP)\<close>
  (is \<open>?lhs = (if B \<inter> S = {} then ?rhs1 else ?rhs2 \<sqinter> STOP)\<close>)
proof -
  have \<open>STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<sqinter>b \<in> B \<rightarrow> Q b) =
        \<sqinter>b\<in>B. (if b \<in> S then STOP else (b \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)))\<close> (is \<open>?lhs = ?rhs'\<close>)
    by (subst Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix[where A = \<open>{}\<close>, simplified])
      (auto intro: mono_GlobalNdet_eq)
  also have \<open>?rhs' = (if B \<inter> S = {} then ?rhs1 else ?rhs2 \<sqinter> STOP)\<close>
  proof (split if_split, intro conjI impI)
    show \<open>B \<inter> S = {} \<Longrightarrow> ?rhs' = ?rhs1\<close>
      by (auto simp add: Mndetprefix_GlobalNdet intro!: mono_GlobalNdet_eq)
  next
    show \<open>?rhs' = ?rhs2 \<sqinter> STOP\<close> if \<open>B \<inter> S \<noteq> {}\<close>
    proof (cases \<open>B - S = {}\<close>)
      show \<open>?rhs' = ?rhs2 \<sqinter> STOP\<close> if \<open>B - S = {}\<close>
        by (simp add: \<open>B - S = {}\<close> GlobalNdet_is_STOP_iff)
          (use \<open>B - S = {}\<close> in blast)
    next
      show \<open>?rhs' = ?rhs2 \<sqinter> STOP\<close> if \<open>B - S \<noteq> {}\<close>
      proof (subst Int_Diff_Un[symmetric],
          subst GlobalNdet_factorization_union
          [OF \<open>B \<inter> S \<noteq> {}\<close> \<open>B - S \<noteq> {}\<close>, symmetric])
        have \<open>(\<sqinter>b\<in>(B \<inter> S). (if b \<in> S then STOP else (b \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b))))
              = STOP\<close> (is \<open>?fact1 = STOP\<close>)
          by (simp add: GlobalNdet_is_STOP_iff)
        moreover have \<open>(\<sqinter>b\<in>(B - S). (if b \<in> S then STOP else (b \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b))))
                       = ?rhs2\<close> (is \<open>?fact2 = ?rhs2\<close>)
          by (auto simp add: Mndetprefix_GlobalNdet intro: mono_GlobalNdet_eq)
        ultimately show \<open>?fact1 \<sqinter> ?fact2 = ?rhs2 \<sqinter> STOP\<close> by (metis Ndet_commute)
      qed
    qed
  qed
  finally show \<open>?lhs = (if B \<inter> S = {} then ?rhs1 else ?rhs2 \<sqinter> STOP)\<close> .
qed


corollary Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_subset :
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<box>b \<in> B \<rightarrow> Q b) =
   (  if A \<subseteq> B then \<sqinter> a \<in> A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a)
    else (\<sqinter>a \<in> (A \<inter> B) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a)) \<sqinter> STOP)\<close>
  (is \<open>?lhs = (if A \<subseteq> B then ?rhs1 else ?rhs2)\<close>) if \<open>A \<subseteq> S\<close> \<open>B \<subseteq> S\<close>
proof (cases \<open>A = {}\<close>)
  show \<open>A = {} \<Longrightarrow> ?lhs = (if A \<subseteq> B then ?rhs1 else ?rhs2)\<close>
    by (simp add: Mprefix_is_STOP_iff STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix \<open>B \<subseteq> S\<close>)
next
  from \<open>A \<subseteq> S\<close> have  * : \<open>a \<in> A \<Longrightarrow> a \<in> S\<close> for a by blast
  from \<open>B \<subseteq> S\<close> have ** : \<open>B - S = {}\<close> \<open>b \<in> B \<and> b \<in> S \<longleftrightarrow> b \<in> B\<close> for b by auto
  assume \<open>A \<noteq> {}\<close>
  have \<open>?lhs = \<sqinter>a\<in>A. (if a \<in> B then (a \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a)) else STOP)\<close> (is \<open>?lhs = ?rhs'\<close>)
    by (auto simp add: Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix "*" "**" \<open>A \<noteq> {}\<close> intro: mono_GlobalNdet_eq)
  also have \<open>?rhs' = (if A \<subseteq> B then ?rhs1 else ?rhs2)\<close>
  proof (split if_split, intro conjI impI)
    show \<open>A \<subseteq> B \<Longrightarrow> ?rhs' = \<sqinter>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a)\<close>
      by (auto simp add: Mndetprefix_GlobalNdet intro!: mono_GlobalNdet_eq)
  next
    show \<open>?rhs' = (\<sqinter>a\<in>(A \<inter> B) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a)) \<sqinter> STOP\<close> if \<open>\<not> A \<subseteq> B\<close>
    proof (cases \<open>A \<inter> B = {}\<close>)
      show \<open>A \<inter> B = {} \<Longrightarrow> ?rhs' = (\<sqinter>a\<in>(A \<inter> B) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a)) \<sqinter> STOP\<close>
        by (auto simp add: GlobalNdet_is_STOP_iff)
    next
      assume \<open>A \<inter> B \<noteq> {}\<close>
      from \<open>\<not> A \<subseteq> B\<close> have \<open>A - B \<noteq> {}\<close> by blast
      show \<open>?rhs' = (\<sqinter>a\<in>(A \<inter> B) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a)) \<sqinter> STOP\<close>
        by (auto simp add: Mndetprefix_GlobalNdet GlobalNdet_is_STOP_iff
            simp flip: GlobalNdet_factorization_union
            [OF \<open>A \<inter> B \<noteq> {}\<close> \<open>A - B \<noteq> {}\<close>, unfolded Int_Diff_Un]
            intro!: arg_cong2[where f = \<open>(\<sqinter>)\<close>] mono_GlobalNdet_eq)
    qed
  qed
  finally show \<open>?lhs = (if A \<subseteq> B then ?rhs1 else ?rhs2)\<close> by simp
qed


corollary Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_subset :
  \<open>\<box>a \<in> A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<sqinter>b \<in> B \<rightarrow> Q b =
   (  if B \<subseteq> A then \<sqinter>b \<in> B \<rightarrow> (P b \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)
    else (\<sqinter>b \<in> (A \<inter> B) \<rightarrow> (P b \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) \<sqinter> STOP)\<close>
  (is \<open>?lhs = (if B \<subseteq> A then ?rhs1 else ?rhs2)\<close>) if \<open>A \<subseteq> S\<close> \<open>B \<subseteq> S\<close>
proof (cases \<open>B = {}\<close>)
  show \<open>B = {} \<Longrightarrow> ?lhs = (if B \<subseteq> A then ?rhs1 else ?rhs2)\<close>
    by (simp add: Mprefix_is_STOP_iff Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP \<open>A \<subseteq> S\<close>)
next
  from \<open>B \<subseteq> S\<close> have  * : \<open>b \<in> B \<Longrightarrow> b \<in> S\<close> for b by blast
  from \<open>A \<subseteq> S\<close> have ** : \<open>A - S = {}\<close> \<open>a \<in> A \<and> a \<in> S \<longleftrightarrow> a \<in> A\<close> for a by auto
  assume \<open>B \<noteq> {}\<close>
  have \<open>?lhs = \<sqinter>b\<in>B. (if b \<in> A then (b \<rightarrow> (P b \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) else STOP)\<close> (is \<open>?lhs = ?rhs'\<close>)
    by (auto simp add: Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix "*" "**" \<open>B \<noteq> {}\<close> intro: mono_GlobalNdet_eq)
  also have \<open>?rhs' = (if B \<subseteq> A then ?rhs1 else ?rhs2)\<close>
  proof (split if_split, intro conjI impI)
    show \<open>B \<subseteq> A \<Longrightarrow> ?rhs' = \<sqinter>b\<in>B \<rightarrow> (P b \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close>
      by (auto simp add: Mndetprefix_GlobalNdet intro!: mono_GlobalNdet_eq)
  next
    show \<open>?rhs' = (\<sqinter>a\<in>(A \<inter> B) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a)) \<sqinter> STOP\<close> if \<open>\<not> B \<subseteq> A\<close>
    proof (cases \<open>A \<inter> B = {}\<close>)
      show \<open>A \<inter> B = {} \<Longrightarrow> ?rhs' = (\<sqinter>a\<in>(A \<inter> B) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a)) \<sqinter> STOP\<close>
        by (auto simp add: GlobalNdet_is_STOP_iff)
    next
      assume \<open>A \<inter> B \<noteq> {}\<close>
      hence \<open>B \<inter> A \<noteq> {}\<close> by blast 
      from \<open>\<not> B \<subseteq> A\<close> have \<open>B - A \<noteq> {}\<close> by blast
      show \<open>?rhs' = (\<sqinter>a\<in>(A \<inter> B) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a)) \<sqinter> STOP\<close>
        by (auto simp add: Mndetprefix_GlobalNdet GlobalNdet_is_STOP_iff
            simp flip: Int_commute GlobalNdet_factorization_union
            [OF \<open>B \<inter> A \<noteq> {}\<close> \<open>B - A \<noteq> {}\<close>, unfolded Int_Diff_Un]
            intro!: arg_cong2[where f = \<open>(\<sqinter>)\<close>] mono_GlobalNdet_eq)
    qed
  qed
  finally show \<open>?lhs = (if B \<subseteq> A then ?rhs1 else ?rhs2)\<close> by simp
qed



corollary Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_indep :
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<box>b \<in> B \<rightarrow> Q b) =
   (  if A = {} then \<box>b\<in>B \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)
    else \<sqinter>a\<in>A. (a \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<box>b \<in> B \<rightarrow> Q b))) \<box>
                (\<box>b\<in>B \<rightarrow> ((a \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)))\<close>
  if \<open>A \<inter> S = {}\<close> and \<open>B \<inter> S = {}\<close>
proof (cases \<open>A = {}\<close>)
  show \<open>A = {} \<Longrightarrow> ?thesis\<close>
    by (simp add: Diff_triv STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix \<open>B \<inter> S = {}\<close>)
next
  from that(1) have  * : \<open>a \<in> A \<Longrightarrow> a \<notin> S\<close> for a by blast
  from that(2) have ** : \<open>B - S = B\<close> by blast
  show ?thesis if \<open>A \<noteq> {}\<close>
    by (simp add: Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix \<open>A \<noteq> {}\<close>)   
      (rule mono_GlobalNdet_eq, simp add: "*" "**")
qed

corollary Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_indep :
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<sqinter>b \<in> B \<rightarrow> Q b) =
   (  if B = {} then \<box>a \<in> A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)
    else \<sqinter>b\<in>B. (b \<rightarrow> ((\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) \<box>
                (\<box>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (b \<rightarrow> Q b))))\<close>
  if \<open>A \<inter> S = {}\<close> \<open>B \<inter> S = {}\<close>
proof (cases \<open>B = {}\<close>)
  show \<open>B = {} \<Longrightarrow> ?thesis\<close>
    by (simp add: Diff_triv Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP \<open>A \<inter> S = {}\<close>)
next
  from that(2) have  * : \<open>b \<in> B \<Longrightarrow> b \<notin> S\<close> for b by blast
  from that(1) have ** : \<open>A - S = A\<close> by blast
  show ?thesis if \<open>B \<noteq> {}\<close>
    by (simp add: Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix \<open>B \<noteq> {}\<close>)   
      (rule mono_GlobalNdet_eq, simp add: "*" "**")
qed


corollary Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_left :
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<box>b \<in> B \<rightarrow> Q b) =
   (  if A = {} then STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<box>b \<in> B \<rightarrow> Q b)
    else \<sqinter>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<box>b \<in> B \<rightarrow> Q b)))\<close>
  if \<open>A \<inter> S = {}\<close> and \<open>B \<subseteq> S\<close>
proof (cases \<open>A = {}\<close>)
  show \<open>A = {} \<Longrightarrow> ?thesis\<close> by simp
next
  from that(1) have   * : \<open>a \<in> A \<Longrightarrow> a \<notin> S\<close> for a by blast
  from that(2) have  ** : \<open>B - S = {}\<close> by blast
  show ?thesis if \<open>A \<noteq> {}\<close>
    by (simp add: Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix \<open>A \<noteq> {}\<close>, unfold Mndetprefix_GlobalNdet)
      (rule mono_GlobalNdet_eq, simp add: "*" "**")
qed

corollary Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_right :
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<box>b \<in> B \<rightarrow> Q b) =
   (  if A = {} then STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<box>b \<in> B \<rightarrow> Q b)
    else \<box>b\<in>B \<rightarrow> ((\<sqinter>a\<in>A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b))\<close>
  if \<open>A \<subseteq> S\<close> and \<open>B \<inter> S = {}\<close>
proof (cases \<open>A = {}\<close>)
  show \<open>A = {} \<Longrightarrow> ?thesis\<close> by simp
next
  from that(1) have   * : \<open>a \<in> A \<Longrightarrow> a \<in> S\<close> for a by blast
  from that(2) have  ** : \<open>B - S = B\<close> by blast
  show ?thesis if \<open>A \<noteq> {}\<close>
    by (simp add: Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix \<open>A \<noteq> {}\<close>,
        simp add: Mndetprefix_GlobalNdet Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right \<open>A \<noteq> {}\<close>
        flip: GlobalNdet_Mprefix_distr)
      (rule mono_GlobalNdet_eq, use "*" "**" in auto)
qed

corollary Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_left :
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<sqinter>b \<in> B \<rightarrow> Q b) =
   (  if B = {} then (\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP
    else \<box>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<sqinter>b \<in> B \<rightarrow> Q b)))\<close>
  if \<open>A \<inter> S = {}\<close> \<open>B \<subseteq> S\<close>
proof (cases \<open>B = {}\<close>)
  show \<open>B = {} \<Longrightarrow> ?thesis\<close> by simp
next
  from that(2) have   * : \<open>b \<in> B \<Longrightarrow> b \<in> S\<close> for b by blast
  from that(1) have  ** : \<open>A - S = A\<close> by blast
  show ?thesis if \<open>B \<noteq> {}\<close>
    by (simp add: Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix \<open>B \<noteq> {}\<close>,
        simp add: Mndetprefix_GlobalNdet Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left \<open>B \<noteq> {}\<close>
        flip: GlobalNdet_Mprefix_distr)
      (rule mono_GlobalNdet_eq, use "*" "**" in auto)
qed

corollary Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_right :
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<sqinter>b \<in> B \<rightarrow> Q b) =
   (  if B = {} then (\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP
    else \<sqinter>b\<in>B \<rightarrow> ((\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b))\<close>
  if \<open>A \<subseteq> S\<close> \<open>B \<inter> S = {}\<close>
proof (cases \<open>B = {}\<close>)
  show \<open>B = {} \<Longrightarrow> ?thesis\<close> by simp
next
  from that(2) have   * : \<open>b \<in> B \<Longrightarrow> b \<notin> S\<close> for b by blast
  from that(1) have  ** : \<open>A - S = {}\<close> by blast
  show ?thesis if \<open>B \<noteq> {}\<close>
    by (simp add: Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix \<open>B \<noteq> {}\<close>,
        unfold Mndetprefix_GlobalNdet)
      (rule mono_GlobalNdet_eq, simp add: "*" "**")
qed



corollary Mndetprefix_Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix :
  \<open>\<sqinter>a \<in> A \<rightarrow> P a ||\<^sub>\<checkmark> \<box>b \<in> B \<rightarrow> Q b =
   (if A \<subseteq> B then \<sqinter>a \<in> A \<rightarrow> (P a ||\<^sub>\<checkmark> Q a) else (\<sqinter>a \<in> (A \<inter> B) \<rightarrow> (P a ||\<^sub>\<checkmark> Q a)) \<sqinter> STOP)\<close>
  by (simp add: Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_subset)

corollary Mprefix_Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix :
  \<open>\<box>a \<in> A \<rightarrow> P a ||\<^sub>\<checkmark> \<sqinter>b \<in> B \<rightarrow> Q b =
   (if B \<subseteq> A then \<sqinter>b \<in> B \<rightarrow> (P b ||\<^sub>\<checkmark> Q b) else (\<sqinter>b \<in> (A \<inter> B) \<rightarrow> (P b ||\<^sub>\<checkmark> Q b)) \<sqinter> STOP)\<close>
  by (simp add: Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_subset)

corollary Mndetprefix_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix :
  \<open>\<sqinter>a \<in> A \<rightarrow> P a |||\<^sub>\<checkmark> \<box>b \<in> B \<rightarrow> Q b =
   (  if A = {} then \<box>b \<in> B \<rightarrow> RenamingTick (Q b \<^bold>; STOP) (\<lambda>s. the (tick_join (g s) s))
    else \<sqinter>a\<in>A. (a \<rightarrow> (P a |||\<^sub>\<checkmark> \<box>b \<in> B \<rightarrow> Q b)) \<box>
                (\<box>b\<in>B \<rightarrow> (a \<rightarrow> P a |||\<^sub>\<checkmark> Q b)))\<close>
  by (simp add: Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_indep
      Mprefix_Seq STOP_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of _ g])

corollary Mprefix_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix :
  \<open>\<box>a \<in> A \<rightarrow> P a |||\<^sub>\<checkmark> \<sqinter>b \<in> B \<rightarrow> Q b =
   (  if B = {} then \<box>a \<in> A \<rightarrow> RenamingTick (P a \<^bold>; STOP) (\<lambda>r. the (tick_join r (g r)))
    else \<sqinter>b\<in>B. (b \<rightarrow> (\<box>a \<in> A \<rightarrow> P a |||\<^sub>\<checkmark> Q b)) \<box>
                (\<box>a\<in>A \<rightarrow> (P a |||\<^sub>\<checkmark> b \<rightarrow> Q b)))\<close>
  by (simp add: Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_indep
      Mprefix_Seq Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP[of _ g])



paragraph \<open>Mixing two non deterministic prefix choices\<close>

lemma Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix :
  \<open>\<sqinter>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<sqinter>b\<in>B \<rightarrow> Q b =
   (  if A = {} then   if B \<inter> S = {} then \<sqinter>b\<in>B \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)
                     else (\<sqinter>x \<in> (B - S) \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)) \<sqinter> STOP
    else   if B = {} then   if A \<inter> S = {} then \<sqinter>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)
                          else (\<sqinter>x \<in>(A - S) \<rightarrow> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)) \<sqinter> STOP
         else \<sqinter>b\<in>B. \<sqinter>a\<in>A.
              (if a \<in> S then STOP else a \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q b)) \<box>
              (if b \<in> S then STOP else b \<rightarrow> (a \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) \<box>
              (if a = b \<and> b \<in> S then b \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b) else STOP))\<close>
  (is \<open>?lhs = (  if A = {} then if B \<inter> S = {} then ?mv_right else ?mv_right' \<sqinter> STOP
               else   if B = {} then if A \<inter> S = {} then ?mv_left else ?mv_left' \<sqinter> STOP
                    else ?huge_mess)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>A = {} \<Longrightarrow> ?lhs = (if B \<inter> S = {} then ?mv_right else ?mv_right' \<sqinter> STOP)\<close>
    by (auto simp add: STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix intro: mono_Mndetprefix_eq)
next
  show \<open>?lhs = (if B = {} then if A \<inter> S = {} then ?mv_left else ?mv_left' \<sqinter> STOP else ?huge_mess)\<close> if \<open>A \<noteq> {}\<close>
  proof (split if_split, intro conjI impI)
    show \<open>B = {} \<Longrightarrow> ?lhs = (if A \<inter> S = {} then ?mv_left else ?mv_left' \<sqinter> STOP)\<close>
      by (auto simp add: Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP intro: mono_Mndetprefix_eq)
  next
    assume \<open>B \<noteq> {}\<close>
    have \<open>?lhs = \<sqinter>b\<in>B. \<sqinter>a\<in>A. (a \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (b \<rightarrow> Q b))\<close>
      by (simp add: Mndetprefix_GlobalNdet \<open>A \<noteq> {}\<close> \<open>B \<noteq> {}\<close>
          Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right)
    also have \<open>\<dots> = ?huge_mess\<close>
      by (auto simp add: write0_def Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix Diff_triv Mprefix_is_STOP_iff
          intro!: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>])
    finally show \<open>?lhs = ?huge_mess\<close> .
  qed
qed


lemma Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_subset :
  \<open>\<sqinter>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<sqinter>b\<in>B \<rightarrow> Q b =
   (  if \<exists>b. A = {b} \<and> B = {b}
    then (THE b. B = {b}) \<rightarrow> (P (THE a. A = {a}) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (THE b. B = {b}))
    else (\<sqinter>x \<in> (A \<inter> B) \<rightarrow> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)) \<sqinter> STOP)\<close>
  (is \<open>?lhs = (if ?cond then ?rhs1 else ?rhs2)\<close>) if \<open>A \<subseteq> S\<close> \<open>B \<subseteq> S\<close>
proof (split if_split, intro conjI impI)
  show \<open>?cond \<Longrightarrow> ?lhs = ?rhs1\<close>
    by (elim exE, simp add: write0_def)
      (subst Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_subset, use \<open>A \<subseteq> S\<close> in simp_all)
next
  assume \<open>\<not> ?cond\<close>
  let ?term = \<open>\<lambda>a b. (b \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b))\<close>
  have \<open>?lhs = \<sqinter>b\<in>B. \<sqinter>a\<in>A. (if a = b then ?term a b else STOP)\<close>
    (is \<open>?lhs = \<sqinter>b\<in>B. \<sqinter>a\<in>A. ?rhs' b a\<close>)
  proof (cases \<open>A = {} \<or> B = {}\<close>)
    from \<open>A \<subseteq> S\<close> \<open>B \<subseteq> S\<close> show \<open>A = {} \<or> B = {} \<Longrightarrow> ?lhs = (\<sqinter>b\<in>B. \<sqinter>a\<in>A. ?rhs' b a)\<close>
      by (elim disjE) (simp_all add: Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix
          Int_absorb2 Mndetprefix_is_STOP_iff Ndet_is_STOP_iff)
  next
    show \<open>\<not> (A = {} \<or> B = {}) \<Longrightarrow> ?lhs = (\<sqinter>b\<in>B. \<sqinter>a\<in>A. ?rhs' b a)\<close>
      by (simp add: Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix)
        (intro mono_GlobalNdet_eq, use \<open>A \<subseteq> S\<close> \<open>B \<subseteq> S\<close> in auto)
  qed

  also have \<open>(\<sqinter>b\<in>B. \<sqinter>a\<in>A. ?rhs' b a) = ?rhs2\<close>
  proof (cases \<open>B \<inter> A = {}\<close>)
    assume \<open>B \<inter> A = {}\<close>
    hence \<open>A \<inter> B = {}\<close> by blast
    hence \<open>(\<sqinter>b\<in>B. \<sqinter>a\<in>A. ?rhs' b a) = STOP\<close> by (auto simp add: GlobalNdet_is_STOP_iff)
    thus \<open>(\<sqinter>b\<in>B. \<sqinter>a\<in>A. ?rhs' b a) = ?rhs2\<close> by (auto simp add: \<open>A \<inter> B = {}\<close>)
  next
    show \<open>(\<sqinter>b\<in>B. \<sqinter>a\<in>A. ?rhs' b a) = ?rhs2\<close> if \<open>B \<inter> A \<noteq> {}\<close>
    proof (cases \<open>B - A = {}\<close>)
      assume \<open>B - A = {}\<close>
      hence \<open>A \<inter> B = B\<close> by blast
      have \<open>(\<sqinter>a\<in>A. ?rhs' b a) = (if A = {b} then ?term b b else ?term b b \<sqinter> STOP)\<close>
        (is \<open>(\<sqinter>a\<in>A. ?rhs' b a) = ?rhs'' b\<close>) if \<open>b \<in> B\<close> for b
      proof (cases \<open>A \<inter> {b} = {}\<close>)
        from \<open>B - A = {}\<close> \<open>b \<in> B\<close>
        show \<open>A \<inter> {b} = {} \<Longrightarrow> (\<sqinter>a\<in>A. ?rhs' b a) = ?rhs'' b\<close> by auto
      next
        show \<open>(\<sqinter>a\<in>A. ?rhs' b a) = ?rhs'' b\<close> if \<open>A \<inter> {b} \<noteq> {}\<close>
        proof (cases \<open>A - {b} = {}\<close>)
          show \<open>A - {b} = {} \<Longrightarrow> (\<sqinter>a\<in>A. ?rhs' b a) = ?rhs'' b\<close>
            using \<open>A \<inter> {b} \<noteq> {}\<close> by auto
        next
          show \<open>\<sqinter>a\<in>A. ?rhs' b a = ?rhs'' b\<close> if \<open>A - {b} \<noteq> {}\<close>
            using \<open>A - {b} \<noteq> {}\<close> \<open>A \<inter> {b} \<noteq> {}\<close>
            by (auto simp add: GlobalNdet_is_STOP_iff
                simp flip: GlobalNdet_factorization_union
                [OF \<open>A \<inter> {b} \<noteq> {}\<close> \<open>A - {b} \<noteq> {}\<close>, unfolded Int_Diff_Un]
                intro: arg_cong2[where f = \<open>(\<sqinter>)\<close>])
        qed
      qed
      hence \<open>(\<sqinter>b \<in> B. \<sqinter>a \<in> A. ?rhs' b a) = \<sqinter>b \<in> B. ?rhs'' b\<close>
        by (fact mono_GlobalNdet_eq)
      also have \<open>(\<sqinter>b \<in> B. ?rhs'' b) = ?rhs2\<close>
      proof -
        from \<open>\<not> ?cond\<close> have \<open>(\<sqinter>b \<in> B. ?rhs'' b) = \<sqinter>b \<in> B. ?term b b \<sqinter> STOP\<close>
          by (metis Diff_eq_empty_iff Int_commute \<open>A \<inter> B = B\<close>
              \<open>B - A = {}\<close> subset_singleton_iff \<open>B \<inter> A \<noteq> {}\<close>)
        also have \<open>\<dots> = (\<sqinter>b \<in> B. ?term b b) \<sqinter> STOP\<close>
          by (simp add: Process_eq_spec Ndet_projs GlobalNdet_projs STOP_projs)
        finally show \<open>(\<sqinter>b \<in> B. ?rhs'' b) = ?rhs2\<close>
          by (simp add: Mndetprefix_GlobalNdet \<open>A \<inter> B = B\<close>)
      qed
      finally show \<open>(\<sqinter>b \<in> B. \<sqinter>a \<in> A. ?rhs' b a) = ?rhs2\<close> .
    next
      assume \<open>B - A \<noteq> {}\<close>
      have \<open>\<sqinter>a\<in>A. (if a = b then ?term a b else STOP) =
            (if b \<in> A then if A = {b} then ?term b b else (?term b b) \<sqinter> STOP else STOP)\<close>
        if \<open>b \<in> B\<close> for b
      proof (split if_split, intro conjI impI)
        show \<open>\<sqinter>a\<in>A. (if a = b then ?term a b else STOP) =
              (if A = {b} then ?term b b else (?term b b) \<sqinter> STOP)\<close> if \<open>b \<in> A\<close>
        proof (split if_split, intro conjI impI)
          show \<open>A = {b} \<Longrightarrow> \<sqinter>a \<in> A. (if a = b then ?term a b else STOP) = ?term b b\<close> by simp
        next
          assume \<open>A \<noteq> {b}\<close>
          with \<open>b \<in> A\<close> have \<open>insert b A = A\<close> \<open>A - {b} \<noteq> {}\<close> by auto
          show \<open>A \<noteq> {b} \<Longrightarrow> \<sqinter>a\<in>A. (if a = b then ?term a b else STOP) = ?term b b \<sqinter> STOP\<close>
            by (auto simp add: GlobalNdet_is_STOP_iff intro!: arg_cong2[where f = \<open>(\<sqinter>)\<close>]
                simp flip: GlobalNdet_factorization_union
                [of \<open>{b}\<close>, OF _ \<open>A - {b} \<noteq> {}\<close>, simplified, unfolded \<open>insert b A = A\<close>])
        qed
      next
        show \<open>b \<notin> A \<Longrightarrow> \<sqinter>a\<in>A. (if a = b then ?term a b else STOP) = STOP\<close>
          by (auto simp add: GlobalNdet_is_STOP_iff)
      qed

      hence \<open>\<sqinter>b \<in> B. \<sqinter>a\<in>A. ?rhs' b a =
             \<sqinter>b \<in> B. (if b \<in> A then if A = {b} then ?term b b else (?term b b) \<sqinter> STOP else STOP)\<close>
        by (fact mono_GlobalNdet_eq)
      also from \<open>B - A \<noteq> {}\<close> have \<open>\<dots> = (\<sqinter>b \<in> B. (if b \<in> A then ?term b b else STOP)) \<sqinter> STOP\<close>
        by (simp add: Process_eq_spec GlobalNdet_projs, safe)
          (simp_all add: GlobalNdet_projs STOP_projs Ndet_projs split: if_split_asm, auto)
      also have \<open>\<dots> = ?rhs2\<close>
      proof (fold GlobalNdet_factorization_union
          [OF \<open>B \<inter> A \<noteq> {}\<close> \<open>B - A \<noteq> {}\<close>, unfolded Int_Diff_Un])
        have \<open>\<sqinter>b\<in>(B \<inter> A). (if b \<in> A then ?term b b else STOP) =
              \<sqinter>b\<in>(B \<inter> A). ?term b b\<close> by (auto intro: mono_GlobalNdet_eq)
        moreover have \<open>\<sqinter>b\<in>(B - A). (if b \<in> A then ?term b b else STOP) = STOP\<close>
          by (simp add: GlobalNdet_is_STOP_iff)
        ultimately show \<open>(\<sqinter>b\<in>(B \<inter> A). (if b \<in> A then ?term b b else STOP)) \<sqinter>
                         (\<sqinter>b\<in>(B - A). (if b \<in> A then ?term b b else STOP)) \<sqinter> STOP = ?rhs2\<close>
          by (metis Mndetprefix_GlobalNdet Int_commute Ndet_assoc Ndet_id)
      qed
      finally show \<open>(\<sqinter>b \<in> B. \<sqinter>a \<in> A. ?rhs' b a) = ?rhs2\<close> .
    qed
  qed
  finally show \<open>?lhs = ?rhs2\<close> .
qed


lemma Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_indep :
  \<open>A \<inter> S = {} \<Longrightarrow> B \<inter> S = {} \<Longrightarrow>
   \<sqinter>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<sqinter>b\<in>B \<rightarrow> Q b =
   (  if A = {} then \<sqinter>b\<in>B \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)
    else   if B = {} then \<sqinter>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)
         else \<sqinter>b\<in>B. \<sqinter>a\<in>A.
              ((a \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q b))) \<box>
              ((b \<rightarrow> (a \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b))))\<close>
  by (simp add: Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix)
    (auto simp add: Mndetprefix_GlobalNdet Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left
      Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right disjoint_iff write0_def
      Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix Int_assoc insert_Diff_if
      intro!: mono_GlobalNdet_eq)


lemma Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_left :
  \<open>\<sqinter>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<sqinter>b\<in>B \<rightarrow> Q b = \<sqinter>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<sqinter>b\<in>B \<rightarrow> Q b)\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>A \<inter> S = {}\<close> \<open>B \<subseteq> S\<close>
proof -
  let ?rhs' = \<open>\<sqinter>b\<in>B. \<sqinter>a\<in>A. a \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q b)\<close>
  have \<open>?lhs = (  if A = {} then   if B \<inter> S = {} then \<sqinter>b\<in>B \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)
                                 else (\<sqinter>x\<in>(B - S) \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)) \<sqinter> STOP
                else   if B = {} then   if A \<inter> S = {} then \<sqinter>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)
                                      else (\<sqinter>x\<in>(A - S) \<rightarrow> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)) \<sqinter> STOP
                     else \<sqinter>b\<in>B. \<sqinter>a\<in>A.
                          (if a \<in> S then STOP else (a \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q b))) \<box>
                          (if b \<in> S then STOP else (b \<rightarrow> (a \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b))) \<box>
                          (if a = b \<and> b \<in> S then b \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b) else STOP))\<close>
    (is \<open>?lhs = (if A = {} then ?rhs1 else if B = {} then ?rhs2 else ?rhs3)\<close>)
    by (fact Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix)
  also from \<open>B \<subseteq> S\<close> have \<open>?rhs1 = STOP\<close>
    by (auto simp add: Ndet_is_STOP_iff Mndetprefix_GlobalNdet GlobalNdet_is_STOP_iff)
  also from \<open>A \<inter> S = {}\<close> have \<open>?rhs2 = \<sqinter>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)\<close> by presburger
  also from \<open>A \<inter> S = {}\<close> \<open>B \<subseteq> S\<close>
  have \<open>?rhs3 = \<sqinter>b\<in>B. \<sqinter>a\<in>A. a \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q b)\<close>
    by (intro mono_GlobalNdet_eq) auto
  finally have \<open>?lhs = (  if A = {} then STOP
                        else   if B = {} then \<sqinter>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)
                             else ?rhs')\<close> .
  moreover have \<open>B \<noteq> {} \<Longrightarrow> ?rhs' = \<sqinter>a\<in>A. a \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<sqinter>b\<in>B. b \<rightarrow> Q b)\<close>
    by (subst GlobalNdet_sets_commute)
      (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left write0_GlobalNdet)
  moreover have \<open>\<dots> = \<sqinter>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<sqinter>b\<in>B \<rightarrow> Q b)\<close>
    by (simp add: Mndetprefix_GlobalNdet)
  ultimately show \<open>?lhs = ?rhs\<close> by simp
qed

end


corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_right :
  \<open>\<sqinter>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<sqinter>b\<in>B \<rightarrow> Q b = \<sqinter>b\<in>B \<rightarrow> (\<sqinter>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>A \<subseteq> S\<close> \<open>B \<inter> S = {}\<close>
  by (subst (1 2) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
    (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_left that)



(*<*)
end
  (*>*)